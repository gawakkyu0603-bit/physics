#!/usr/bin/env python3
"""Check configured pages, links, math, identifiers, figures and source PDF bytes."""
from pathlib import Path
from urllib.parse import urlparse,unquote
import hashlib
import json
import re
import xml.etree.ElementTree as ET
from bs4 import BeautifulSoup
ROOT=Path(__file__).resolve().parents[1]
DOCS=ROOT/'docs'
catalog=json.loads((ROOT/'site-src/catalog.json').read_text())
languages=catalog.get('languages',['en'])
errors=[];checks={'html_pages':0,'article_pages':0,'local_links':0,'paper_source_links':0,'configured_languages':languages}
pages={p:BeautifulSoup(p.read_text(),'html.parser') for p in DOCS.rglob('*.html') if not p.name.startswith('_qa')}
expected_pages={'index.html'}
for lang in languages:
    expected_pages.add(lang+'/index.html')
    expected_pages.update(f"{lang}/{field['slug']}/index.html" for field in catalog['fields'])
for paper in catalog['papers']:
    if paper.get('languages')!=languages:errors.append([paper['slug'],'paper languages differ from the site configuration'])
    for lang in paper['languages']:
        expected_pages.add(f"{lang}/{paper['field']}/{paper['slug']}/index.html")
        expected_pages.update(f"{lang}/{paper['field']}/{paper['slug']}/{audience}.html" for audience in paper['audiences'])
actual_pages={str(path.relative_to(DOCS)) for path in pages}
if actual_pages!=expected_pages:
    errors.append(['site pages','published pages differ from the configured catalog',
                   {'missing':sorted(expected_pages-actual_pages),'extra':sorted(actual_pages-expected_pages)}])
canonical_pages={}
alternate_sets={}
for path,soup in pages.items():
    checks['html_pages']+=1
    raw=path.read_text()
    rel=str(path.relative_to(DOCS))
    if soup.html.get('lang') not in languages:errors.append([rel,'page language is not configured for publication'])
    if len(languages)==1 and soup.select('.language,.lang-switch'):
        errors.append([rel,'unexpected language switch on a single-language site'])
    canonical=soup.select('head link[rel="canonical"]')
    expected_canonical=catalog['public_base_url']+rel
    if len(canonical)!=1 or canonical[0].get('href')!=expected_canonical:
        errors.append([rel,'canonical URL does not match the published page'])
    canonical_pages[expected_canonical]=soup
    alternates=soup.select('head link[rel="alternate"][hreflang]')
    alternate_sets[expected_canonical]={n['hreflang']:n.get('href','') for n in alternates}
    if len(alternate_sets[expected_canonical])!=len(alternates):
        errors.append([rel,'duplicate hreflang language'])
    expected_languages=set(languages)|{'x-default'} if rel=='index.html' or rel in {lang+'/index.html' for lang in languages} else {soup.html.get('lang')}
    if set(alternate_sets[expected_canonical])!=expected_languages:
        errors.append([rel,'hreflang set does not cover the published language versions'])
    if expected_canonical not in alternate_sets[expected_canonical].values():
        errors.append([rel,'hreflang set omits the page itself'])
    ids=[n['id'] for n in soup.select('[id]')]
    if len(ids)!=len(set(ids)):errors.append([rel,'duplicate HTML IDs'])
    if len(soup.select('h1'))!=1:errors.append([rel,'expected one h1'])
    if soup.select('.katex-error'):errors.append([rel,'KaTeX error'])
    if re.search(r'\{\{[A-Z_]+\}\}|data-figure=',raw):errors.append([rel,'unfilled content token'])
    for el in soup.select('[href],script[src],img[src],iframe[src]'):
        link=el.get('href',el.get('src',''));u=urlparse(link)
        if u.scheme or u.netloc:
            prefix=f"/{catalog['owner']}/{catalog['repository']}/blob/"
            if u.netloc=='github.com' and u.path.startswith(prefix):
                parts=u.path[len(prefix):].split('/',1)
                if len(parts)==2:
                    target=ROOT/unquote(parts[1]);checks['paper_source_links']+=1
                    if not target.exists():errors.append([rel,'missing source',str(target.relative_to(ROOT))])
            continue
        target=(path.parent/unquote(u.path)).resolve() if u.path else path
        checks['local_links']+=1
        if not target.exists():errors.append([rel,'missing local file',link]);continue
        if u.fragment and target.suffix=='.html' and target in pages:
            if not pages[target].find(id=unquote(u.fragment)):errors.append([rel,'missing fragment',link])
    if soup.select_one('.article-content'):
        checks['article_pages']+=1
        first=soup.select_one('.article-content article').find(recursive=False)
        if first is None or 'tldr' not in first.get('class',[]):errors.append([rel,'TL;DR must be first article block'])
        if not first.h2 or 'TL;DR' not in first.h2.text:errors.append([rel,'missing visible TL;DR heading'])
        for fig in soup.select('figure.diagram'):
            if not fig.select_one('svg title') or not fig.figcaption:errors.append([rel,'unlabelled figure',fig.get('id')])
checks['hreflang_links']=0
for canonical,alternates in alternate_sets.items():
    for language,target in alternates.items():
        checks['hreflang_links']+=1
        parsed=urlparse(target)
        if parsed.scheme!='https' or not parsed.netloc:
            errors.append([canonical,'hreflang URL must be absolute HTTPS',target])
        elif target not in canonical_pages:
            errors.append([canonical,'hreflang target has no published canonical page',target])
        else:
            if alternate_sets[target]!=alternates:
                errors.append([canonical,'hreflang targets do not share the same reciprocal set',target])
            if language!='x-default' and canonical_pages[target].html.get('lang')!=language:
                errors.append([canonical,'hreflang target language differs',language,target])
try:
    sitemap=ET.parse(DOCS/'sitemap.xml')
    namespace='{http://www.sitemaps.org/schemas/sitemap/0.9}'
    if sitemap.getroot().tag!=namespace+'urlset':
        errors.append(['sitemap.xml','incorrect sitemap root or namespace'])
    sitemap_urls=[n.text or '' for n in sitemap.findall(namespace+'url/'+namespace+'loc')]
    checks['sitemap_urls']=len(sitemap_urls)
    if len(sitemap_urls)!=len(set(sitemap_urls)):
        errors.append(['sitemap.xml','duplicate URL'])
    expected_urls=set(canonical_pages)
    for paper in catalog['papers']:
        for key in ['main_pdf','supplement_pdf']:
            expected_urls.add(catalog['public_base_url']+paper[key])
            if not (DOCS/paper[key]).is_file():errors.append([paper['slug'],'missing sitemap PDF',paper[key]])
    if set(sitemap_urls)!=expected_urls:
        errors.append(['sitemap.xml','URL coverage differs from HTML canonical pages and registered PDFs',
                       {'missing':sorted(expected_urls-set(sitemap_urls)),'extra':sorted(set(sitemap_urls)-expected_urls)}])
except (OSError,ET.ParseError) as exc:
    errors.append(['sitemap.xml','cannot read a valid XML sitemap',str(exc)])
for paper in catalog['papers']:
    for audience in paper['audiences']:
        for lang in paper['languages']:
            article=pages.get(DOCS/lang/paper['field']/paper['slug']/(audience+'.html'))
            if article is None or not article.select_one('.article-content article'):
                errors.append([paper['slug'],audience,lang,'configured reading guide is missing'])
            elif not article.select('article section') or not article.select('figure.diagram'):
                errors.append([paper['slug'],audience,lang,'reading guide lacks sections or figures'])
checks['pdf_sha256']={}
expected={'cat-v4-main.pdf':'5b3539369c18b900a207c1bf8e55e3261a7e9599b6cd8be8181f7c814c68fc7a','cat-v4-supplement.pdf':'96c59915ad3bdafbad4da6b79bb9974f3ba7a644544205070691383fa16b46a8'}
for name,want in expected.items():
    got=hashlib.sha256((DOCS/'downloads'/name).read_bytes()).hexdigest();checks['pdf_sha256'][name]=got
    if got!=want:errors.append([name,'PDF differs from version 4'])
result={'checks':checks,'error_count':len(errors),'errors':errors}
(ROOT/'site-src/verification.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
print(json.dumps(result,ensure_ascii=False,indent=2))
raise SystemExit(1 if errors else 0)
