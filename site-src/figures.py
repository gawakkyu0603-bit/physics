"""Render registered explanatory SVGs. Figures do not alter research data."""
from html import escape
from pathlib import Path
import re

def figure(fid, lang):
    if lang != 'en':
        raise ValueError('English reading guides only')
    if not re.fullmatch(r'[a-z0-9-]+', fid):
        raise ValueError('Invalid figure identifier')
    base = Path(__file__).resolve().parent / 'figures'
    svg = (base / (fid + '.svg')).read_text(encoding='utf-8').strip()
    import json
    metadata = json.loads((base / (fid + '.json')).read_text(encoding='utf-8'))
    heading = escape(metadata['title'])
    description = escape(metadata['description'])
    return f'<figure class="diagram" id="figure-{fid}"><div class="diagram-scroll" tabindex="0" aria-label="{heading}">{svg}</div><div class="scroll-hint">On a small screen, scroll the diagram horizontally.</div><figcaption><strong>{heading}</strong>{description}</figcaption></figure>'
