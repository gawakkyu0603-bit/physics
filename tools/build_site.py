#!/usr/bin/env python3
"""Build the committed, network-independent static GitHub Pages tree.

Install once: npm ci; python3 -m pip install -r site-src/requirements.txt
Then: python3 tools/build_site.py
Add papers through site-src/catalog.json and the matching HTML fragments.
"""
from pathlib import Path
from html import escape, unescape
import importlib.util
import json
import os
import re
import shutil
import subprocess
import sys
import xml.etree.ElementTree as ET
from bs4 import BeautifulSoup

ROOT=Path(__file__).resolve().parents[1]
DOCS=ROOT/'docs'
SOURCE=ROOT/'site-src'
CATALOG=json.loads((SOURCE/'catalog.json').read_text())
LANGUAGES=CATALOG.get('languages',['en'])
if LANGUAGES!=['en']:
    raise ValueError('Public research introductions are configured for English only')
for paper in CATALOG['papers']:
    if paper.get('languages')!=LANGUAGES:
        raise ValueError('Each paper must use the configured English publication language')
FIELDS_BY_SLUG={field['slug']:field for field in CATALOG['fields']}
spec=importlib.util.spec_from_file_location('figures',SOURCE/'figures.py')
figures=importlib.util.module_from_spec(spec);spec.loader.exec_module(figures)
REPO=f"https://github.com/{CATALOG['owner']}/{CATALOG['repository']}"
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

def tr(lang,ja,en):return ja if lang=='ja' else en
def url(page,target):return os.path.relpath(DOCS/target,(DOCS/page).parent).replace(os.sep,'/')
def papath(p,lang,name='index'):return f"{lang}/{p['field']}/{p['slug']}/{name}.html"
def ea(s):return escape(str(s),quote=True)
def write(page,html):
    path=DOCS/page;path.parent.mkdir(parents=True,exist_ok=True);path.write_text(html,encoding='utf-8')
    GENERATED_PAGES.add(page)

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
    paths=set(GENERATED_PAGES)
    for paper in CATALOG['papers']:
        paths.update([paper['main_pdf'],paper['supplement_pdf']])
    for path in sorted(paths):
        entry=ET.SubElement(root,'{'+namespace+'}url')
        ET.SubElement(entry,'{'+namespace+'}loc').text=CATALOG['public_base_url']+path
    ET.indent(root,space='  ')
    ET.ElementTree(root).write(DOCS/'sitemap.xml',encoding='utf-8',xml_declaration=True)

def write_indexnow_key():
    config=json.loads((SOURCE/'indexnow.json').read_text())
    key=config['key']
    if not re.fullmatch(r'[0-9a-f]{32}',key):
        raise ValueError('IndexNow verification key must be 32 lowercase hex characters')
    if config['site_url']!=CATALOG['public_base_url'] or config['key_location']!=CATALOG['public_base_url']+key+'.txt':
        raise ValueError('IndexNow site and key location must match the catalog public URL')
    (DOCS/(key+'.txt')).write_text(key+'\n',encoding='utf-8')

def audience_description(p,audience,lang):
    return p.get('audience_descriptions',{}).get(audience,{}).get(lang,DEFAULT_DESCRIPTIONS[audience][lang])

def reading_label(p,audience,lang,card=False):
    minutes=p.get('reading_times',{}).get(audience)
    if not minutes:return tr(lang,'冒頭にTL;DR','TL;DR first')
    if card:
        return tr(lang,'目安 ','Approx. ')+str(minutes)+tr(lang,'分 · 冒頭にTL;DR',' min · TL;DR first')
    return tr(lang,'精読の目安：','Reading guide: ')+str(minutes)+tr(lang,'分',' min')

def pdf_label(p,kind,lang):
    title=tr(lang,'論文本体','Paper') if kind=='main' else tr(lang,'補足資料','Supplement')
    count=p.get('page_counts',{}).get(kind)
    return title if count is None else title+' · '+str(count)+tr(lang,'ページ',' pages')

def collection_summary(papers,lang):
    if len(papers)==1:
        p=papers[0];name=p.get('short_title') or p['title']
        collection=tr(lang,f'現在の収録論文は{name}第{p["version"]}版です。',f'The current collection contains {name} Version {p["version"]}. ')
    elif papers:
        collection=tr(lang,f'現在{len(papers)}件の論文を収録しています。',f'The current collection contains {len(papers)} papers. ')
    else:
        collection=tr(lang,'この分野の収録論文を準備しています。','Papers for this field are being prepared. ')
    return 'Papers are organized by field, paper, and version. '+collection+'Three English introductions cover the same research at different reading levels.'

def root_collection_summary(papers):
    if len(papers)==1:
        p=papers[0];name=p.get('short_title') or p['title']
        en=f'{name} Version {p["version"]} is available here as a research collection with three reading levels.'
    else:
        en=f'Explore {len(papers)} research papers through three reading levels.' if papers else 'Research papers and their reading guides are being prepared.'
    return ea(en)

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
<footer class="site-footer"><div class="footer-inner"><div>PHYSICS · {tr(lang,'論文と再現資料を、分野ごとに。','Papers and reproduction materials, organized by field.')}<br>{tr(lang,'原論文・説明記事・検証記録を対応させた研究アーカイブ。','A research archive connecting papers, explanations, and verification records.')}</div><div><a href="{home}">{tr(lang,'論文一覧','Papers')}</a> · <a href="{REPO}">GitHub</a></div></div></footer></body></html>'''

def audience_nav(p,page,lang,current=None):
    result=f'<nav class="audience-bar" aria-label="Reading levels"><div class="audience-inner"><span class="audience-label">{tr(lang,"この論文を読む：","Read this paper:")}</span>'
    for a in p['audiences']:
        current_attr=' aria-current="page"' if a==current else ''
        result+=f'<a href="{url(page,papath(p,lang,a))}"{current_attr}>{ea(LABELS[a][lang])}</a>'
    result+='</div></nav>'
    return result

def downloads(p,page,lang):
    main=url(page,p['main_pdf']);supp=url(page,p['supplement_pdf'])
    release=f"{REPO}/releases/tag/{p['release']}"
    source=f"{REPO}/tree/{p['release']}/{p['source_path']}"
    intro=tr(lang,f'説明記事は第{p["version"]}版に基づきます。証明の全展開、全コード、個別結果の追跡には原論文と補足資料を参照してください。PDFは投稿原稿と同じファイルです。',f'These explanations follow Version {p["version"]}. Consult the paper and supplement for complete derivations, source code, and individual result records. The PDFs are unchanged copies of the submitted manuscript.')
    return f'''<section class="download-panel" id="downloads"><h2>{tr(lang,'原論文・再現資料を読む','Read the paper and reproduction materials')}</h2>
<p>{ea(intro)}</p>
<div class="button-row"><a class="button" href="{main}">{ea(pdf_label(p,'main',lang))} <span class="pdf-icon">PDF</span></a><a class="button secondary" href="{supp}">{ea(pdf_label(p,'supplement',lang))} <span class="pdf-icon">PDF</span></a><a class="button secondary" href="{source}">{tr(lang,'原稿・コード・データ','Source, code & data')}</a><a class="button secondary" href="{release}">{tr(lang,'版付き公開一式','Versioned release')}</a></div></section>'''

def explorer(lang):
    points=' '.join(f'{60+560*(i/100):.2f},{230-180*((i/100)**2+(1-i/100)**2):.2f}' for i in range(101))
    return f'''<section class="explorer return-explorer" id="ideal-return"><h2>{tr(lang,'動かして確かめる：理想的な二群の帰還','Explore the ideal return of two groups')}</h2>
<p>{tr(lang,'初期状態を純粋状態とし、各群の可逆操作をすべて戻して元の状態への帰還を測ります。位相を保った通常の全体反転では帰還確率は1です。二つの直交する荷の群の間の位相が選択によって失われる理想模型では、重みの偏りによって帰還率が変わります。','Start from a pure state, undo all reversible operations in each group, and project onto the initial state. An ideal full ordinary inverse returns it with probability one. If selection removes phase coherence between two orthogonal charge groups, the ideal return probability depends on their relative weights.')}</p>
<div class="controls"><div><label for="group-weight">{tr(lang,'第1群の重み','Weight of group 1')} <strong data-weight>0.50</strong></label><input id="group-weight" type="range" min="0" max="1" step="0.01" value="0.5"><div>{tr(lang,'第2群の重み：','Weight of group 2: ')}<strong data-other>0.50</strong></div></div><div class="result"><span>{tr(lang,'選択後の理想帰還確率','Ideal return after selection')}</span><output for="group-weight" aria-live="polite">0.5000</output><small>{tr(lang,'0.5 = 50%、1 = 100%','0.5 = 50%; 1 = 100%')}</small></div></div>
<svg class="mini-plot" viewBox="0 0 680 275" role="img" aria-labelledby="return-plot-title"><title id="return-plot-title">{tr(lang,'二群の重みと理想帰還確率。等しい重みで最小の0.5、片群だけなら1。','Ideal return versus the two group weights. Minimum 0.5 at equal weights; one when only one group is present.')}</title><path d="M60 35V230H630" fill="none" stroke="#6a8c9c" stroke-width="2"/><path d="M60 50H620" fill="none" stroke="#8b6bb9" stroke-width="2" stroke-dasharray="7 5"/><polyline points="{points}" fill="none" stroke="#007d94" stroke-width="4"/><circle data-curve-dot cx="340" cy="140" r="7" fill="#c36615" stroke="white" stroke-width="2"/><g fill="#264d63" font-size="17"><text x="42" y="56" text-anchor="end">1</text><text x="42" y="146" text-anchor="end">0.5</text><text x="42" y="235" text-anchor="end">0</text><text x="60" y="257" text-anchor="middle">0</text><text x="340" y="257" text-anchor="middle">0.5</text><text x="620" y="257" text-anchor="middle">1</text><text x="350" y="31" text-anchor="middle">{tr(lang,'紫の破線：通常の理想反転','Purple dashed line: ideal ordinary inverse')}</text></g></svg>
<details><summary>{tr(lang,'計算の式を見る','Show the calculation')}</summary><p class="formula">\\(F=w^2+(1-w)^2\\)</p><p>{tr(lang,'たとえば w = 0.5 なら 0.25 + 0.25 = 0.5。これは群の重みの式であり、別に述べた装置の吸収確率ではありません。','For example, w = 0.5 gives 0.25 + 0.25 = 0.5. Here w is a group weight, not the absorption probability in the separate device protocol.')}</p></details>
<p class="tiny">{tr(lang,'説明用の理想計算です。約66%／97%という較正付き実験設計の上限・下限とは別の値で、観測結果ではありません。','An ideal mathematical illustration, separate from the approximately 66% / 97% bounds of the calibrated experimental design; these are not measurements.')}</p><noscript><p>{tr(lang,'スライダーにはJavaScriptが必要です。等しい重みの場合は0.5000です。','The slider requires JavaScript. At equal weights the value is 0.5000.')}</p></noscript></section>'''

def build_article(p,lang,audience):
    page=papath(p,lang,audience)
    file=SOURCE/'content'/f"{p.get('content_prefix','')}{audience}-{lang}.html"
    soup=BeautifulSoup(file.read_text(), 'html.parser')
    source_text=soup.get_text(' ',strip=True)
    article=soup.article
    title=article.h1.get_text(' ',strip=True)
    header=article.find('header',class_='article-header')
    tldr=article.select_one('.tldr')
    if tldr is None:raise ValueError(f'Missing TL;DR in {file}')
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
    if p.get('interactive_return',False):
        target=article.find(id='figure-general-echo') if audience=='general' else article.find(id='figure-expert-readout-design') if audience=='expert' else article.find(id='student-test')
        if target is None:
            target=article.find(id='student-return')
        if target is None:
            target=article.find_all('section')[-2]
        target.insert_after(BeautifulSoup(explorer(lang),'html.parser'))
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
    source=f"{REPO}/blob/{p['release']}/{p['source_path']}"
    fragment=fragment.replace('{{PAPER_PDF}}',url(page,p['main_pdf'])).replace('{{SUPP_PDF}}',url(page,p['supplement_pdf'])).replace('{{SOURCE_ROOT}}',source)
    fragment,mathcount=render_math(fragment)
    headings=''.join(f'<li><a href="#{ea(i)}">{ea(t)}</a></li>' for i,t in toc)
    hero=f'''<section class="hero article-hero"><div class="hero-inner"><div class="path"><a href="{url(page,lang+'/index.html')}">Physics</a> / <a href="{url(page,lang+'/'+p['field']+'/index.html')}">{ea(FIELDS_BY_SLUG[p['field']]['name'][lang])}</a> / <a href="{url(page,papath(p,lang))}">{ea(p.get("short_title") or p["title"])}</a></div><p class="eyebrow">{ea(LABELS[audience][lang])} · Version {p['version']}</p><h1>{ea(title)}</h1><div class="meta"><span>{ea(p['author'])}</span><span>{ea(p['date'])}</span><span>{tr(lang,'研究プレプリント','Research preprint')}</span><span>{ea(reading_label(p,audience,lang))}</span></div></div></section>'''
    top=hero+audience_nav(p,page,lang,audience)
    bottomlinks=''.join(f'<a href="{url(page,papath(p,lang,a))}"><strong>{ea(LABELS[a][lang])}</strong><span>{ea(audience_description(p,a,lang))}</span></a>' for a in p['audiences'])
    provenance=tr(lang,f'本ページは第{p["version"]}版の説明記事です。原論文の仮定、結果、未解決課題を区別しています。著者の原稿と説明記事の範囲は公開資料で確認できます。',f'This page explains Version {p["version"]}, distinguishing its assumptions, results, and open problems. The paper and publication records document their scope.')
    body=top+f'''<main id="main" class="reading-layout"><aside class="toc"><details open><summary>{tr(lang,'このページの目次','On this page')}</summary><ol>{headings}</ol><div class="toc-tools"><a href="{url(page,p['main_pdf'])}">{tr(lang,'論文本体 PDF','Paper PDF')}</a><a href="{url(page,p['supplement_pdf'])}">{tr(lang,'補足資料 PDF','Supplement PDF')}</a></div></details></aside><div class="article-content" lang="{lang}">{fragment}{downloads(p,page,lang)}<nav class="end-nav" aria-label="{tr(lang,'他の読み方','Other reading levels')}">{bottomlinks}</nav><p class="status-line">{provenance} <a href="{REPO}/blob/{p['release']}/{p['field']}/{p['archive_slug']}/v{p['version']}/VERIFICATION.md">{tr(lang,'検証範囲','Verification scope')}</a></p></div></main>'''
    write(page,shell(page,lang,title,p['summary'][lang],body))
    plain=BeautifulSoup(fragment,'html.parser').get_text(' ',strip=True)
    BUILD_STATS[page]={'source_text_characters_including_tex':len(source_text),'source_words_including_tex':len(source_text.split()),'math_expressions':mathcount,'display_equations':len(article.select('.equation')),'figures':len(article.select('figure.diagram')),'tables':len(article.select('table')),'h2_sections':len(toc)}

def reader_cards(p,page,lang):
    return '<div class="catalog-grid">'+''.join(f'''<section class="reader-card {a}"><div class="eyebrow" style="color:var(--muted)">{tr(lang,'読み方','Reading level')} {i+1:02d}</div><h3>{ea(LABELS[a][lang])}</h3><p>{ea(audience_description(p,a,lang))}</p><p class="subtle">{ea(reading_label(p,a,lang,card=True))}</p><a href="{url(page,papath(p,lang,a))}">{tr(lang,'この説明を読む','Read this introduction')} →</a></section>''' for i,a in enumerate(p['audiences']))+'</div>'

def catalog_page(lang,field=None,paper=None):
    papers=[paper] if paper else [p for p in CATALOG['papers'] if field is None or p['field']==field['slug']]
    if paper:page=papath(paper,lang);title=paper['title'];subtitle=paper['summary'][lang]
    elif field:page=f"{lang}/{field['slug']}/index.html";title=field['name'][lang];subtitle=field['summary'][lang]
    else:page=f'{lang}/index.html';title=tr(lang,'物理を、理解できるかたちで。','Physics, made understandable.');subtitle=tr(lang,'研究の核心から、数式と検証まで。前提知識に合った入口で読み、同じ論文を違う深さから確かめるためのアーカイブです。','From the central idea to the mathematics and tests. Choose an entry point that fits your background, then examine the same research at greater depth.')
    body=f'''<section class="hero"><div class="hero-inner"><p class="eyebrow">Physics / {tr(lang,'研究アーカイブ','Research archive')}</p><h1>{ea(title)}</h1><p class="lead">{ea(subtitle)}</p><div class="meta"><span>English research guides</span><span>{tr(lang,'3つの読み方','Three reading levels')}</span><span>{tr(lang,'原論文と再現資料','Papers & reproduction materials')}</span></div></div></section><main id="main" class="catalog">'''
    body+=f'<section class="tldr catalog-summary"><h2>TL;DR</h2><p>{ea(collection_summary(papers,lang))}</p></section>'
    for p in papers:
        graphic=figures.figure(p['hero_figure'],lang) if p.get('hero_figure') else ''
        art=f'<div class="art">{graphic}</div>' if graphic else ''
        feature_style='' if graphic else ' style="grid-template-columns:1fr"'
        if not paper:
            body+=f'''<section class="paper-feature"{feature_style}>{art}<div class="info"><span class="field-tag">{ea(FIELDS_BY_SLUG[p['field']]['name'][lang])}</span><h2>{ea(p['title'])}</h2><p>{ea(p['subtitle'])}</p><p>{ea(p['summary'][lang])}</p><p class="subtle">{ea(p['author'])} · Version {p['version']} · {p['date']}</p><a class="button" href="{url(page,papath(p,lang))}">{tr(lang,'論文の入口へ','Explore this paper')} →</a></div></section>'''
        else:
            body+=f'<p class="catalog-intro">{ea(p["subtitle"])}<br>{ea(p["author"])} · Version {p["version"]} · {p["date"]}</p>'
        body+=reader_cards(p,page,lang)
        if paper:
            body+=scope_section(p,lang)+downloads(p,page,lang)
    body+=f'<p class="status-line">{tr(lang,"論文は著者の研究プレプリントです。著者・AIの貢献と再現確認の範囲は原論文および公開資料に記載されています。","The paper is an author research preprint. The manuscript and publication records disclose the author’s and AI’s contributions and the scope of reproduction checks.")}</p></main>'
    write(page,shell(page,lang,title,subtitle,body))

def root_index():
    page='index.html'
    body=f'''<section class="hero"><div class="hero-inner"><p class="eyebrow">Open research / Three reading levels</p><h1>Physics, made understandable.</h1><p class="lead">Research papers, clear explanations, and reproduction materials.</p></div></section><main id="main" class="catalog"><section class="catalog-summary"><h2>TL;DR</h2><p>{root_collection_summary(CATALOG['papers'])}</p><p>Choose a guide for general readers, STEM students and graduates, or experts. Each guide connects the research question to its assumptions, results, and open problems.</p></section>'''
    for paper in CATALOG['papers']:
        body+=f'<section class="catalog-intro"><h2><a href="{url(page,papath(paper,"en"))}">{ea(paper["title"])}</a></h2><p>{ea(paper["summary"]["en"])}</p></section>'+reader_cards(paper,page,'en')
    body+='<p><a class="button" href="en/index.html">Browse the research collection →</a></p></main>'
    write(page,shell(page,'en','Physics · Research archive','Physics papers, English reading guides, and reproduction materials organized by field.',body))

def main():
    DOCS.mkdir(exist_ok=True)
    for p in CATALOG['papers']:
        for lang in p['languages']:
            for audience in p['audiences']:build_article(p,lang,audience)
            catalog_page(lang,paper=p)
    for lang in LANGUAGES:
        catalog_page(lang)
        for field in CATALOG['fields']:catalog_page(lang,field=field)
    root_index()
    build_sitemap()
    write_indexnow_key()
    (DOCS/'.nojekyll').touch()
    (SOURCE/'build-stats.json').write_text(json.dumps(BUILD_STATS,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps({'pages':len(GENERATED_PAGES),'articles':BUILD_STATS},ensure_ascii=False,indent=2))
if __name__=='__main__':main()
