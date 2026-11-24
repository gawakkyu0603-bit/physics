#!/usr/bin/env python3
"""Check links, language pairing, math, identifiers, figures and source PDF bytes."""
from pathlib import Path
from urllib.parse import urlparse,unquote
import hashlib
import json
import re
from bs4 import BeautifulSoup
ROOT=Path(__file__).resolve().parents[1]
DOCS=ROOT/'docs'
catalog=json.loads((ROOT/'site-src/catalog.json').read_text())
errors=[];checks={'html_pages':0,'local_links':0,'paper_source_links':0,'paired_articles':0}
pages={p:BeautifulSoup(p.read_text(),'html.parser') for p in DOCS.rglob('*.html') if not p.name.startswith('_qa')}
for path,soup in pages.items():
    checks['html_pages']+=1
    raw=path.read_text()
    rel=str(path.relative_to(DOCS))
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
        first=soup.select_one('.article-content article').find(recursive=False)
        if first is None or 'tldr' not in first.get('class',[]):errors.append([rel,'TL;DR must be first article block'])
        if not first.h2 or 'TL;DR' not in first.h2.text:errors.append([rel,'missing visible TL;DR heading'])
        for fig in soup.select('figure.diagram'):
            if not fig.select_one('svg title') or not fig.figcaption:errors.append([rel,'unlabelled figure',fig.get('id')])
for paper in catalog['papers']:
    for audience in paper['audiences']:
        pair=[pages[DOCS/lang/paper['field']/paper['slug']/(audience+'.html')] for lang in ['ja','en']]
        checks['paired_articles']+=1
        for selector,attribute in [('figure.diagram','id'),('article section','id')]:
            a,b=([n.get(attribute) for n in soup.select(selector)] for soup in pair)
            if a!=b:errors.append([paper['slug'],audience,'language structure differs',selector])
        a,b=([n.get_text() for n in soup.select('.equation annotation[encoding="application/x-tex"]')] for soup in pair)
        if a!=b:errors.append([paper['slug'],audience,'displayed equations differ'])
checks['pdf_sha256']={}
expected={'cat-v4-main.pdf':'5b3539369c18b900a207c1bf8e55e3261a7e9599b6cd8be8181f7c814c68fc7a','cat-v4-supplement.pdf':'96c59915ad3bdafbad4da6b79bb9974f3ba7a644544205070691383fa16b46a8'}
for name,want in expected.items():
    got=hashlib.sha256((DOCS/'downloads'/name).read_bytes()).hexdigest();checks['pdf_sha256'][name]=got
    if got!=want:errors.append([name,'PDF differs from version 4'])
result={'checks':checks,'error_count':len(errors),'errors':errors}
(ROOT/'site-src/verification.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
print(json.dumps(result,ensure_ascii=False,indent=2))
raise SystemExit(1 if errors else 0)
