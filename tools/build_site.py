#!/usr/bin/env python3
"""Build the committed, network-independent static GitHub Pages tree.

Install once: npm ci; python3 -m pip install -r site-src/requirements.txt
Then: python3 tools/build_site.py
Add papers through site-src/catalog.json and the matching HTML fragments.
"""
from pathlib import Path
from html import escape, unescape
import argparse
import hashlib
import importlib.util
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from urllib.parse import quote
import xml.etree.ElementTree as ET
from bs4 import BeautifulSoup

try:
    from .site_catalog import (CatalogError, GENERATED_MANIFEST, document_for,
                              generated_page_paths, is_ownership_file,
                              load_catalog, paper_documents, paper_page_path,
                              safe_relative_path, sitemap_filename)
except ImportError:
    from site_catalog import (CatalogError, GENERATED_MANIFEST, document_for,
                             generated_page_paths, is_ownership_file,
                             load_catalog, paper_documents, paper_page_path,
                             safe_relative_path, sitemap_filename)

DEFAULT_ROOT=Path(__file__).resolve().parents[1]
ROOT=DEFAULT_ROOT
DOCS=ROOT/'docs'
SOURCE=ROOT/'site-src'
CATALOG={}
LANGUAGES=[]
FIELDS_BY_SLUG={}
figures=None
REPO=''
LABELS={
 'general':{'ja':'一般向け','en':'General readers'},
 'student':{'ja':'理工系の学生・卒業者向け','en':'STEM students & graduates'},
 'expert':{'ja':'専門家向け','en':'Experts'},
}
DEFAULT_DESCRIPTIONS={
 'general':{'ja':'研究の問いと主要な結果を、具体例から理解します。','en':'Understand the research question and main results through accessible examples.'},
 'student':{'ja':'基礎知識から、研究で用いる考え方と計算をたどります。','en':'Connect foundational knowledge to the concepts and calculations used in the research.'},
 'expert':{'ja':'定義、仮定、計算、検証の範囲を詳しく確認します。','en':'Examine the definitions, assumptions, calculations, and scope of verification.'},
}
BUILD_STATS={}
GENERATED_PAGES=set()
MANAGED_FILES={}

def configure(root):
    global ROOT,DOCS,SOURCE,CATALOG,LANGUAGES,FIELDS_BY_SLUG,figures,REPO
    ROOT=Path(root).resolve();DOCS=ROOT/'docs';SOURCE=ROOT/'site-src'
    CATALOG=load_catalog(ROOT)
    LANGUAGES=CATALOG['languages']
    FIELDS_BY_SLUG={field['slug']:field for field in CATALOG['fields']}
    spec=importlib.util.spec_from_file_location('site_figures',SOURCE/'figures.py')
    figures=importlib.util.module_from_spec(spec);spec.loader.exec_module(figures)
    REPO=f"https://github.com/{CATALOG['owner']}/{CATALOG['repository']}"
    BUILD_STATS.clear();GENERATED_PAGES.clear();MANAGED_FILES.clear()

def tr(lang,ja,en):return ja if lang=='ja' else en
def url(page,target):return quote(os.path.relpath(DOCS/target,(DOCS/page).parent).replace(os.sep,'/'),safe='/')
def papath(p,lang,name='index'):return paper_page_path(p,lang,name)
def ea(s):return escape(str(s),quote=True)

def contained_path(base,relative):
    relative=safe_relative_path(relative)
    path=base/relative
    if path.is_symlink() or not path.resolve().is_relative_to(base.resolve()):
        raise CatalogError(f'Generated path escapes its root or is a symlink: {relative}')
    return path

def record_generated(path,role):
    MANAGED_FILES[path]={'path':path,'role':role,'sha256':hashlib.sha256((DOCS/path).read_bytes()).hexdigest()}

def write(page,html):
    path=contained_path(DOCS,page);path.parent.mkdir(parents=True,exist_ok=True);path.write_text(html,encoding='utf-8')
    GENERATED_PAGES.add(page)
    record_generated(page,'page')

def language_alternates(page,lang):
    if page=='index.html' or page in {code+'/index.html' for code in LANGUAGES}:
        targets={code:code+'/index.html' for code in LANGUAGES}
        targets['x-default']='index.html'
    else:
        targets={lang:page}
    return '\n'.join(f'<link rel="alternate" hreflang="{code}" href="{ea(CATALOG["public_base_url"]+target)}">' for code,target in sorted(targets.items()))

def build_sitemap():
    namespace='http://www.sitemaps.org/schemas/sitemap/0.9'
    ET.register_namespace('',namespace)
    root=ET.Element('{'+namespace+'}urlset')
    for path in sorted(GENERATED_PAGES):
        entry=ET.SubElement(root,'{'+namespace+'}url')
        ET.SubElement(entry,'{'+namespace+'}loc').text=CATALOG['public_base_url']+path
    ET.indent(root,space='  ')
    filename=sitemap_filename(CATALOG)
    ET.ElementTree(root).write(DOCS/filename,encoding='utf-8',xml_declaration=True)
    record_generated(filename,'sitemap')

def audience_description(p,audience,lang):
    return p.get('audience_descriptions',{}).get(audience,{}).get(lang,DEFAULT_DESCRIPTIONS[audience][lang])

def reading_label(p,audience,lang,card=False):
    minutes=p.get('reading_times',{}).get(audience)
    if not minutes:return tr(lang,'冒頭にTL;DR','TL;DR first')
    if card:
        return tr(lang,'目安 ','Approx. ')+str(minutes)+tr(lang,'分 · 冒頭にTL;DR',' min · TL;DR first')
    return tr(lang,'精読の目安：','Reading guide: ')+str(minutes)+tr(lang,'分',' min')

def document_label(document):
    label=document['label']
    if 'page_count' in document:label+=f" · {document['page_count']} pages"
    return label

def source_url(p,kind='blob'):
    if not p.get('source_path'):return None
    reference=p.get('source_ref') or p.get('release') or 'main'
    return f"{REPO}/{kind}/{quote(reference,safe='')}/{quote(p['source_path'],safe='/')}"

def article_tokens(fragment,p,page,file):
    def replace(match):
        token=match.group(1)
        literal='{{'+token+'}}'
        if token=='SOURCE_ROOT':
            target=source_url(p)
            if target is None:
                raise CatalogError(f'{file}: {{{{SOURCE_ROOT}}}} requires source_path for {p["field"]}/{p["slug"]} version {p["version"]}')
            return target
        identifier={'PAPER_PDF':'main','SUPP_PDF':'supplement'}.get(token)
        if identifier is None and token.startswith('DOCUMENT:'):
            identifier=token.split(':',1)[1]
        if identifier is None:
            raise CatalogError(f'{file}: unknown article token {literal}')
        document=document_for(p,identifier)
        if document is None:
            raise CatalogError(f'{file}: {literal} requires registered document id {identifier!r} for {p["field"]}/{p["slug"]} version {p["version"]}')
        return url(page,document['path'])
    return re.sub(r'\{\{([^{}]+)\}\}',replace,fragment)

def scope_section(p,lang):
    paragraphs=p.get('scope',{}).get(lang)
    if paragraphs is None:
        paragraphs=[tr(lang,'研究の前提、結果、検証の範囲は、各解説と原論文で確認できます。','Consult each introduction and the original paper for the assumptions, results, and scope of verification.')]
    if not isinstance(paragraphs,list):raise ValueError(f"scope.{lang} must be a list for {p['slug']}")
    return '<section><h2>'+tr(lang,'すべての説明が扱う範囲','Scope shared by all introductions')+'</h2>'+''.join('<p>'+ea(text)+'</p>' for text in paragraphs)+'</section>'

def render_math(html):
    expressions=[]
    def collect(match):
        display=match.group(1)=='['
        expressions.append({'tex':unescape(match.group(2)),'display':display})
        return f'<!--RENDERED_MATH_{len(expressions)-1}-->'
    html=re.sub(r'\\([\[(])(.*?)\\[\])]',collect,html,flags=re.S)
    if not expressions:return html,0
    result=subprocess.run([os.environ.get('NODE_BINARY','node'),str(SOURCE/'render-math.cjs')],input=json.dumps(expressions),text=True,capture_output=True)
    if result.returncode:
        raise RuntimeError('Math rendering failed: '+result.stderr)
    values=json.loads(result.stdout)
    for i,value in enumerate(values):html=html.replace(f'<!--RENDERED_MATH_{i}-->',value)
    return html,len(expressions)

def shell(page,lang,title,description,body):
    home=url(page,f'{lang}/index.html')
    canon=CATALOG['public_base_url']+page
    return f'''<!doctype html>
<html lang="{lang}"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>{ea(title)} · Physics</title><meta name="description" content="{ea(description)}">
<meta name="theme-color" content="#091d3b"><meta name="color-scheme" content="light">
<link rel="icon" href="{url(page,'assets/favicon.svg')}" type="image/svg+xml">
<link rel="stylesheet" href="{url(page,'assets/site.css')}">
{language_alternates(page,lang)}
<link rel="canonical" href="{ea(canon)}">
<meta property="og:type" content="article"><meta property="og:title" content="{ea(title)}"><meta property="og:description" content="{ea(description)}">
<script defer src="{url(page,'assets/site.js')}"></script></head><body>
<a class="skip" href="#main">{tr(lang,'本文へ移動','Skip to content')}</a><div class="progress" aria-hidden="true"></div>
<header class="site-header"><div class="header-inner"><a class="brand" href="{home}"><svg viewBox="0 0 36 36" aria-hidden="true"><circle cx="18" cy="18" r="14" fill="#15375e"/><ellipse cx="18" cy="18" rx="16" ry="7" fill="none" stroke="#17a4bf" stroke-width="2" transform="rotate(-25 18 18)"/><circle cx="28" cy="13" r="3" fill="#d9892c"/></svg>PHYSICS <small>{tr(lang,'研究と対話','Research & understanding')}</small></a><nav class="header-links" aria-label="{tr(lang,'共通ナビゲーション','Site navigation')}"><a href="{home}">{tr(lang,'論文一覧','Papers')}</a><a class="source-nav" href="{REPO}">GitHub</a></nav></div></header>
{body}
<footer class="site-footer"><div class="footer-inner"><div>PHYSICS · Papers and reading guides, organized by field.<br>Browse each paper for its research and available materials.</div><div><a href="{home}">Papers</a> · <a href="{REPO}">GitHub</a></div></div></footer></body></html>'''

def audience_nav(p,page,lang,current=None):
    result=f'<nav class="audience-bar" aria-label="Reading levels"><div class="audience-inner"><span class="audience-label">{tr(lang,"この論文を読む：","Read this paper:")}</span>'
    for a in p['audiences']:
        current_attr=' aria-current="page"' if a==current else ''
        result+=f'<a href="{url(page,papath(p,lang,a))}"{current_attr}>{ea(LABELS[a][lang])}</a>'
    result+='</div></nav>'
    return result

def downloads(p,page,lang):
    buttons=[]
    for document in paper_documents(p):
        extension=Path(document['path']).suffix.lstrip('.').upper()
        badge=f' <span class="pdf-icon">{ea(extension)}</span>' if extension else ''
        style='button' if not buttons else 'button secondary'
        buttons.append(f'<a class="{style}" href="{url(page,document["path"])}">{ea(document_label(document))}{badge}</a>')
    source=source_url(p,'tree')
    if source:buttons.append(f'<a class="button secondary" href="{ea(source)}">Source files</a>')
    if p.get('release'):
        release=f"{REPO}/releases/tag/{quote(p['release'],safe='')}"
        buttons.append(f'<a class="button secondary" href="{ea(release)}">Release downloads</a>')
    if not buttons:return ''
    intro=p.get('downloads_intro','The available research materials are listed below.')
    return f'''<section class="download-panel" id="downloads"><h2>Paper materials</h2>
<p>{ea(intro)}</p><div class="button-row">{''.join(buttons)}</div></section>'''

def build_article(p,lang,audience):
    page=papath(p,lang,audience)
    file=SOURCE/'content'/f"{p.get('content_prefix','')}{audience}-{lang}.html"
    soup=BeautifulSoup(file.read_text(), 'html.parser')
    source_text=soup.get_text(' ',strip=True)
    article=soup.article
    if article is None or article.h1 is None:
        raise CatalogError(f'{file}: an article element with an h1 heading is required')
    title=article.h1.get_text(' ',strip=True)
    header=article.find('header',class_='article-header')
    tldr=article.select_one('.tldr')
    if tldr is None or tldr.h2 is None:raise CatalogError(f'{file}: a TL;DR section with an h2 heading is required')
    tldr.extract()
    tldr.h2.string=tr(lang,'TL;DR — 先に要点','TL;DR — The essentials')
    intro=[]
    if header:
        for el in list(header.find_all('p',recursive=False)):
            if not set(el.get('class',[]))&{'eyebrow','edition'}:intro.append(str(el))
        header.decompose()
    article.insert(0,tldr)
    for index,element in enumerate(intro):article.insert(index+1,BeautifulSoup(element,'html.parser'))
    for placeholder in list(article.select('[data-figure]')):
        fid=placeholder['data-figure']
        replacement=BeautifulSoup(figures.figure(fid,lang),'html.parser')
        placeholder.replace_with(replacement)
    for table in list(article.find_all('table')):
        if 'table-scroll' not in table.parent.get('class',[]):
            wrap=soup.new_tag('div',attrs={'class':'table-scroll','tabindex':'0'})
            table.wrap(wrap)
    toc=[]
    for i,h in enumerate(article.find_all('h2')):
        if not h.get('id'):
            parent=h.find_parent('section')
            h['id']=(parent.get('id')+'-heading') if parent and parent.get('id') else f'section-{i}'
        toc.append((h['id'],h.get_text(' ',strip=True)))
    fragment=str(article)
    fragment=article_tokens(fragment,p,page,file)
    fragment,mathcount=render_math(fragment)
    headings=''.join(f'<li><a href="#{ea(i)}">{ea(t)}</a></li>' for i,t in toc)
    metadata=''.join('<span>'+ea(p[key])+'</span>' for key in ('author','date') if p.get(key))
    metadata+='<span>'+ea(reading_label(p,audience,lang))+'</span>'
    hero=f'''<section class="hero article-hero"><div class="hero-inner"><div class="path"><a href="{url(page,lang+'/index.html')}">Physics</a> / <a href="{url(page,lang+'/'+p['field']+'/index.html')}">{ea(FIELDS_BY_SLUG[p['field']]['name'][lang])}</a> / <a href="{url(page,papath(p,lang))}">{ea(p.get("short_title") or p["title"])}</a></div><p class="eyebrow">{ea(LABELS[audience][lang])}</p><h1>{ea(title)}</h1><div class="meta">{metadata}</div></div></section>'''
    top=hero+audience_nav(p,page,lang,audience)
    bottomlinks=''.join(f'<a href="{url(page,papath(p,lang,a))}"><strong>{ea(LABELS[a][lang])}</strong><span>{ea(audience_description(p,a,lang))}</span></a>' for a in p['audiences'])
    materials=''.join(f'<a href="{url(page,document["path"])}">{ea(document_label(document))}</a>' for document in paper_documents(p))
    toc_materials=f'<div class="toc-tools">{materials}</div>' if materials else ''
    body=top+f'''<main id="main" class="reading-layout"><aside class="toc"><details open><summary>{tr(lang,'このページの目次','On this page')}</summary><ol>{headings}</ol>{toc_materials}</details></aside><div class="article-content" lang="{lang}">{fragment}{series_navigation(p,page,lang)}{downloads(p,page,lang)}<nav class="end-nav" aria-label="{tr(lang,'他の読み方','Other reading levels')}">{bottomlinks}</nav></div></main>'''
    write(page,shell(page,lang,title,p['summary'][lang],body))
    plain=BeautifulSoup(fragment,'html.parser').get_text(' ',strip=True)
    BUILD_STATS[page]={'source_text_characters_including_tex':len(source_text),'source_words_including_tex':len(source_text.split()),'math_expressions':mathcount,'display_equations':len(article.select('.equation')),'figures':len(article.select('figure.diagram')),'tables':len(article.select('table')),'h2_sections':len(toc)}

def reader_cards(p,page,lang):
    return '<div class="catalog-grid">'+''.join(f'''<section class="reader-card {a}"><div class="eyebrow" style="color:var(--muted)">{tr(lang,'読み方','Reading level')} {i+1:02d}</div><h3>{ea(LABELS[a][lang])}</h3><p>{ea(audience_description(p,a,lang))}</p><p class="subtle">{ea(reading_label(p,a,lang,card=True))}</p><a href="{url(page,papath(p,lang,a))}">{tr(lang,'この説明を読む','Read this introduction')} →</a></section>''' for i,a in enumerate(p['audiences']))+'</div>'

def series_navigation(p,page,lang):
    if not p.get('series'):return ''
    members=[item for item in CATALOG['papers'] if item.get('series')==p['series']]
    if len(members)<2:return ''
    items=[]
    for item in members:
        label=f"Paper {item['series_order']} — {item['title']}"
        if (item['field'],item['slug'])==(p['field'],p['slug']):
            items.append(f'<li><span aria-current="page">{ea(label)}</span></li>')
        else:
            items.append(f'<li><a href="{url(page,papath(item,lang))}">{ea(label)}</a></li>')
    return '<section class="series-nav"><h2>Research series</h2><ol class="series-list">'+''.join(items)+'</ol></section>'

def paper_index_list(papers,page,lang):
    if not papers:return '<p>No papers are currently listed in this field.</p>'
    items=[]
    for p in papers:
        summary=p.get('summary',{}).get(lang,'')
        description='<p>'+ea(summary)+'</p>' if summary else ''
        label=(f"Paper {p['series_order']} — " if p.get('series') else '')+p['title']
        items.append(f'<li><h3><a href="{url(page,papath(p,lang))}">{ea(label)}</a></h3>{description}</li>')
    return '<ul class="paper-index">'+''.join(items)+'</ul>'

def collection_index(page,lang,field=None):
    title=field['name'][lang] if field else 'Physics research'
    subtitle=field['summary'][lang] if field else 'Research papers and reading guides, organized by field. Explore each paper and its available materials.'
    body=f'''<section class="hero"><div class="hero-inner"><p class="eyebrow">Physics / Research archive</p><h1>{ea(title)}</h1><p class="lead">{ea(subtitle)}</p></div></section><main id="main" class="catalog">'''
    if field:
        papers=[p for p in CATALOG['papers'] if p['field']==field['slug']]
        body+='<section class="catalog-intro"><h2>Papers</h2>'+paper_index_list(papers,page,lang)+'</section>'
    else:
        body+='<section class="catalog-intro"><h2>Fields and papers</h2><p>Select a field or a paper to explore its reading guides and materials.</p></section>'
        for item in CATALOG['fields']:
            papers=[p for p in CATALOG['papers'] if p['field']==item['slug']]
            body+=f'<section class="catalog-intro"><h2><a href="{url(page,lang+"/"+item["slug"]+"/index.html")}">{ea(item["name"][lang])}</a></h2>'
            if item['summary'][lang]:body+='<p>'+ea(item['summary'][lang])+'</p>'
            body+=paper_index_list(papers,page,lang)+'</section>'
        if not CATALOG['fields']:body+='<p>No research fields are currently listed.</p>'
    body+='</main>'
    write(page,shell(page,lang,title,subtitle,body))

def catalog_page(lang,field=None,paper=None):
    if paper is None:
        page=f"{lang}/{field['slug']}/index.html" if field else f'{lang}/index.html'
        collection_index(page,lang,field)
        return
    p=paper;page=papath(p,lang);title=p['title'];summary=p['summary'][lang]
    subtitle=p.get('subtitle','')
    body=f'''<section class="hero"><div class="hero-inner"><div class="path"><a href="{url(page,lang+'/index.html')}">Physics</a> / <a href="{url(page,lang+'/'+p['field']+'/index.html')}">{ea(FIELDS_BY_SLUG[p['field']]['name'][lang])}</a></div><h1>{ea(title)}</h1><p class="lead">{ea(subtitle)}</p></div></section><main id="main" class="catalog">'''
    body+='<section class="tldr catalog-summary"><h2>TL;DR</h2>'
    if summary:body+='<p>'+ea(summary)+'</p>'
    body+='<p>Three English guides cover the same research at different reading levels, including its assumptions, results, and open questions.</p></section>'
    metadata=[p[key] for key in ('author',) if p.get(key)]
    metadata.extend(p[key] for key in ('date',) if p.get(key))
    graphic=figures.figure(p['hero_figure'],lang) if p.get('hero_figure') else ''
    if graphic:
        body+=f'<section class="paper-feature"><div class="art">{graphic}</div><div class="info"><h2>About this paper</h2><p>{ea(subtitle)}</p><p class="subtle">{ea(" · ".join(metadata))}</p></div></section>'
    else:
        body+='<p class="catalog-intro">'+ea(' · '.join(metadata))+'</p>'
    body+=series_navigation(p,page,lang)+reader_cards(p,page,lang)+scope_section(p,lang)+downloads(p,page,lang)
    body+='</main>'
    write(page,shell(page,lang,title,summary or subtitle or title,body))

def root_index():
    collection_index('index.html','en')

def read_generated_manifest():
    path=ROOT/GENERATED_MANIFEST
    if not path.exists():return {}
    try:manifest=json.loads(path.read_text(encoding='utf-8'))
    except (OSError,json.JSONDecodeError) as exc:
        raise CatalogError(f'Cannot read generated-file manifest {path}: {exc}') from exc
    if not isinstance(manifest,dict) or manifest.get('schema_version')!=1 or not isinstance(manifest.get('files'),list):
        raise CatalogError(f'{path}: expected schema_version 1 and a files list')
    records={}
    page_pattern=re.compile(r'(?:index\.html|en/index\.html|en/[a-z0-9-]+/index\.html|en/[a-z0-9-]+/[a-z0-9-]+/(?:index|general|student|expert)\.html)\Z')
    for entry in manifest['files']:
        if not isinstance(entry,dict):raise CatalogError(f'{path}: file records must be objects')
        name=safe_relative_path(entry.get('path'),'generated manifest path')
        role=entry.get('role');digest=entry.get('sha256')
        if name in records or role not in {'page','document','sitemap'}:
            raise CatalogError(f'{path}: duplicate path or invalid role for {name}')
        if not isinstance(digest,str) or not re.fullmatch(r'[a-f0-9]{64}',digest):
            raise CatalogError(f'{path}: invalid SHA-256 for {name}')
        if is_ownership_file(name) or name=='.nojekyll' or name.startswith('assets/'):
            raise CatalogError(f'{path}: protected manual or shared asset path {name}')
        if role=='page' and not page_pattern.fullmatch(name):
            raise CatalogError(f'{path}: unrecognized generated-page path {name}')
        if role=='sitemap' and ('/' in name or not name.endswith('.xml')):
            raise CatalogError(f'{path}: unrecognized sitemap path {name}')
        records[name]=entry
    return records

def copy_documents(existing_docs):
    for paper in CATALOG['papers']:
        for document in paper_documents(paper):
            label=f'{paper["field"]}/{paper["slug"]} version {paper["version"]}, document {document["id"]}'
            if document.get('source_path'):
                origin=contained_path(ROOT,document['source_path'])
            else:
                origin=contained_path(existing_docs,document['path'])
            if not origin.is_file():
                raise CatalogError(f'{label}: registered document file is missing: {origin}')
            data=origin.read_bytes()
            actual=hashlib.sha256(data).hexdigest()
            if document.get('sha256') and actual!=document['sha256']:
                raise CatalogError(f'{label}: SHA-256 mismatch for {origin}; expected {document["sha256"]}, got {actual}')
            destination=contained_path(DOCS,document['path'])
            destination.parent.mkdir(parents=True,exist_ok=True)
            destination.write_bytes(data)
            record_generated(document['path'],'document')

def publish_generated_files(existing_docs,previous):
    """Publish staged outputs; remove only unchanged, previously owned files."""
    removed=[];stale=[]
    # Validate every destination before replacing any existing output.
    for relative in MANAGED_FILES:
        contained_path(existing_docs,relative)
    for relative in previous:
        contained_path(existing_docs,relative)
    # A changed obsolete output requires explicit reconciliation. Check the
    # complete stale set before replacing even the first current output.
    for relative,record in previous.items():
        if relative in MANAGED_FILES:continue
        target=contained_path(existing_docs,relative)
        if not target.exists():continue
        if not target.is_file() or hashlib.sha256(target.read_bytes()).hexdigest()!=record['sha256']:
            raise CatalogError(f'Obsolete generated file was modified: {relative}. Reconcile it with {GENERATED_MANIFEST} before building; existing outputs and the manifest were left unchanged.')
        stale.append((relative,target))
    for relative in sorted(MANAGED_FILES):
        source=DOCS/relative;target=contained_path(existing_docs,relative)
        target.parent.mkdir(parents=True,exist_ok=True)
        with tempfile.NamedTemporaryFile(dir=target.parent,prefix='.site-build-',delete=False) as stream:
            temporary=Path(stream.name)
            try:
                stream.write(source.read_bytes())
                stream.flush()
            except BaseException:
                temporary.unlink(missing_ok=True)
                raise
        try:os.replace(temporary,target)
        finally:temporary.unlink(missing_ok=True)
    for relative,target in stale:
        target.unlink();removed.append(relative)
        parent=target.parent
        while parent!=existing_docs:
            try:parent.rmdir()
            except OSError:break
            parent=parent.parent
    manifest={'schema_version':1,'files':[MANAGED_FILES[path] for path in sorted(MANAGED_FILES)]}
    (ROOT/GENERATED_MANIFEST).write_text(json.dumps(manifest,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    return removed

def build(root=DEFAULT_ROOT):
    """Build a repository tree without network requests or changes to research."""
    global DOCS
    configure(root)
    existing_docs=DOCS
    previous=read_generated_manifest()
    with tempfile.TemporaryDirectory(prefix='physics-site-build-') as directory:
        DOCS=Path(directory)/'docs';DOCS.mkdir()
        try:
            copy_documents(existing_docs)
            for paper in CATALOG['papers']:
                for lang in paper['languages']:
                    for audience in paper['audiences']:build_article(paper,lang,audience)
                    catalog_page(lang,paper=paper)
            for lang in LANGUAGES:
                catalog_page(lang)
                for field in CATALOG['fields']:catalog_page(lang,field=field)
            root_index()
            expected=generated_page_paths(CATALOG)
            if GENERATED_PAGES!=expected:
                raise CatalogError(f'Generated HTML pages differ from the selected catalog: {sorted(GENERATED_PAGES ^ expected)}')
            build_sitemap()
            removed=publish_generated_files(existing_docs,previous)
        finally:
            DOCS=existing_docs
    (DOCS/'.nojekyll').touch()
    (SOURCE/'build-stats.json').write_text(json.dumps(BUILD_STATS,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    return {'pages':len(GENERATED_PAGES),'sitemap':sitemap_filename(CATALOG),
            'documents':sum(record['role']=='document' for record in MANAGED_FILES.values()),
            'deleted_generated_files':removed,
            'articles':dict(BUILD_STATS)}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root',type=Path,default=DEFAULT_ROOT,help='Repository root (defaults to the directory containing tools/)')
    args=parser.parse_args()
    try:result=build(args.root)
    except (CatalogError,OSError) as exc:parser.exit(1,f'Build failed: {exc}\n')
    print(json.dumps(result,ensure_ascii=False,indent=2))

if __name__=='__main__':main()
