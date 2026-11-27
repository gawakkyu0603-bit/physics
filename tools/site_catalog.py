"""Shared catalog validation, document registration, and live-version selection.

Paths in ``documents`` are relative to docs/. Optional source paths are relative
to the repository root. This module performs no writes and no network requests.
"""
from copy import deepcopy
from pathlib import Path, PurePosixPath
import json
import re
from urllib.parse import urlsplit


class CatalogError(ValueError):
    """A catalog cannot be used safely or has an ambiguous publication choice."""


AUDIENCES = ('general', 'student', 'expert')
GENERATED_MANIFEST = 'site-src/generated-files.json'
_SLUG = re.compile(r'[a-z0-9]+(?:-[a-z0-9]+)*\Z')
_NUMERIC_VERSION = re.compile(r'[0-9]+(?:\.[0-9]+)*\Z')


def safe_relative_path(value, label='path'):
    """Return a plain, traversal-free POSIX path, without resolving symlinks."""
    if not isinstance(value, str) or not value or value != value.strip():
        raise CatalogError(f'{label} must be a nonempty relative path')
    if ('\\' in value or any(ord(c) < 32 for c in value)
            or any(c in value for c in '?#') or value.startswith('/')
            or any(part in ('', '.', '..') for part in value.split('/'))
            or ':' in value):
        raise CatalogError(f'{label} must be a safe relative POSIX path: {value!r}')
    return PurePosixPath(value).as_posix()


def is_ownership_file(path):
    """Keep manually maintained service-verification files outside generation."""
    name = PurePosixPath(path).name
    return bool(re.fullmatch(r'google[^/]*\.html', name, re.I)
                or name.lower() == 'bingsiteauth.xml'
                or re.fullmatch(r'[a-f0-9]{32}\.txt', name, re.I))


def _slug(value, label):
    if not isinstance(value, str) or not _SLUG.fullmatch(value):
        raise CatalogError(f'{label} must be a lowercase, hyphen-separated slug')
    return value


def _english(value, label, default=''):
    if value is None:
        return default
    if isinstance(value, dict):
        value = value.get('en')
    if not isinstance(value, str):
        raise CatalogError(f'{label} must be an English string or an en mapping')
    return value


def _numeric_version(value):
    if not _NUMERIC_VERSION.fullmatch(value):
        return None
    parts = tuple(int(part) for part in value.split('.'))
    while len(parts) > 1 and parts[-1] == 0:
        parts = parts[:-1]
    return parts


def select_latest_papers(papers):
    """Select one version per field/slug; reject tied or unspecified ordering.

    Dotted numeric versions compare as integer tuples (10 > 2). Equivalent
    versions such as 4 and 4.0 are duplicates. A series containing nonnumeric
    versions requires a unique integer version_order on every version in that
    series. Numeric-only series always use their numeric versions; an optional
    version_order does not override that ordering.
    """
    groups = {}
    for paper in papers:
        groups.setdefault((paper['field'], paper['slug']), []).append(paper)
    selected = []
    for (field, slug), versions in groups.items():
        label = f'{field}/{slug}'
        seen_versions = set()
        for paper in versions:
            version = str(paper['version'])
            numeric = _numeric_version(version)
            identity = ('numeric', numeric) if numeric is not None else ('text', version)
            if identity in seen_versions:
                raise CatalogError(f'{label}: duplicate or equivalent version {version!r}')
            seen_versions.add(identity)
        explicit = any(_numeric_version(str(p['version'])) is None for p in versions)
        if explicit:
            seen_orders = set()
            for paper in versions:
                order = paper.get('version_order')
                if not isinstance(order, int) or isinstance(order, bool):
                    raise CatalogError(f'{label}: every version requires integer version_order when the series contains nonnumeric versions')
                if order in seen_orders:
                    raise CatalogError(f'{label}: duplicate version_order {order}')
                seen_orders.add(order)
            latest = max(versions, key=lambda p: p['version_order'])
        else:
            latest = max(versions, key=lambda p: _numeric_version(str(p['version'])))
        selected.append(latest)
    # Preserve the position of each research series in the catalogue while
    # ordering its members by scientific sequence, independently of versions.
    series = {}
    for index, paper in enumerate(selected):
        if paper.get('series'):
            series.setdefault(paper['series'], []).append(index)
    for name, positions in series.items():
        members = [selected[i] for i in positions]
        orders = [p['series_order'] for p in members]
        if len(set(orders)) != len(orders):
            raise CatalogError(f'Duplicate research-series position in {name!r}')
        for index, paper in zip(positions, sorted(members, key=lambda p: p['series_order'])):
            selected[index] = paper
    return selected


def paper_page_path(paper, lang, name='index'):
    return f"{lang}/{paper['field']}/{paper['slug']}/{name}.html"


def generated_page_paths(catalog):
    paths = {'index.html'}
    for lang in catalog['languages']:
        paths.add(f'{lang}/index.html')
        for field in catalog['fields']:
            paths.add(f"{lang}/{field['slug']}/index.html")
    for paper in catalog['papers']:
        for lang in paper['languages']:
            paths.add(paper_page_path(paper, lang))
            paths.update(paper_page_path(paper, lang, audience) for audience in paper['audiences'])
    return paths


def sitemap_filename(catalog):
    value = safe_relative_path(catalog.get('sitemap_filename', 'sitemap.xml'), 'sitemap_filename')
    if '/' in value or not value.endswith('.xml') or is_ownership_file(value):
        raise CatalogError('sitemap_filename must be a root-level XML filename distinct from ownership files')
    return value


def paper_documents(paper):
    return paper.get('documents', [])


def document_for(paper, identifier):
    return next((document for document in paper_documents(paper) if document['id'] == identifier), None)


def _normalize_documents(paper, label):
    if 'documents' in paper:
        documents = paper['documents']
    else:
        documents = []
        for identifier, key, title in [('main', 'main_pdf', 'Paper'), ('supplement', 'supplement_pdf', 'Supplement')]:
            if not paper.get(key):
                continue
            document = {'id': identifier, 'label': title, 'path': paper[key]}
            count = paper.get('page_counts', {}).get(identifier)
            if count is None and identifier == 'supplement':
                count = paper.get('page_counts', {}).get('supplement')
            if count is not None:
                document['page_count'] = count
            documents.append(document)
    if not isinstance(documents, list):
        raise CatalogError(f'{label}.documents must be a list')
    normalized, identifiers = [], set()
    for item in documents:
        if not isinstance(item, dict):
            raise CatalogError(f'{label}.documents entries must be objects')
        document = deepcopy(item)
        identifier = _slug(document.get('id'), f'{label}.documents.id')
        if identifier in identifiers:
            raise CatalogError(f'{label}: duplicate document id {identifier!r}')
        identifiers.add(identifier)
        document['label'] = _english(document.get('label'), f'{label}.documents[{identifier}].label')
        if not document['label'].strip():
            raise CatalogError(f'{label}.documents[{identifier}].label must not be empty')
        document['path'] = safe_relative_path(document.get('path'), f'{label}.documents[{identifier}].path')
        if is_ownership_file(document['path']):
            raise CatalogError(f'{label}: an ownership-verification file cannot be a generated document')
        if 'source_path' in document:
            document['source_path'] = safe_relative_path(document['source_path'], f'{label}.documents[{identifier}].source_path')
        if 'sha256' in document:
            digest = document['sha256']
            if not isinstance(digest, str) or not re.fullmatch(r'[a-fA-F0-9]{64}', digest):
                raise CatalogError(f'{label}.documents[{identifier}].sha256 must contain 64 hexadecimal characters')
            document['sha256'] = digest.lower()
        if 'page_count' in document:
            count = document['page_count']
            if not isinstance(count, int) or isinstance(count, bool) or count < 1:
                raise CatalogError(f'{label}.documents[{identifier}].page_count must be a positive integer')
        normalized.append(document)
    return normalized


def normalize_catalog(data):
    if not isinstance(data, dict):
        raise CatalogError('Catalog must be a JSON object')
    catalog = deepcopy(data)
    for key in ('owner', 'repository'):
        if not isinstance(catalog.get(key), str) or not re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9_.-]*', catalog[key]):
            raise CatalogError(f'{key} must be a GitHub owner or repository name')
    base = catalog.get('public_base_url')
    parsed = urlsplit(base) if isinstance(base, str) else None
    if (parsed is None or parsed.scheme != 'https' or not parsed.netloc
            or parsed.username or parsed.password or parsed.query or parsed.fragment
            or not base.endswith('/')):
        raise CatalogError('public_base_url must be an absolute HTTPS URL ending in /, without credentials, query, or fragment')
    catalog['languages'] = catalog.get('languages', ['en'])
    if catalog['languages'] != ['en']:
        raise CatalogError('Public reading guides must use languages=["en"]')
    catalog['sitemap_filename'] = sitemap_filename(catalog)
    fields = catalog.get('fields')
    if not isinstance(fields, list):
        raise CatalogError('fields must be a list')
    known_fields = set()
    for field in fields:
        if not isinstance(field, dict):
            raise CatalogError('fields entries must be objects')
        slug = _slug(field.get('slug'), 'field.slug')
        if slug in known_fields:
            raise CatalogError(f'Duplicate field slug {slug!r}')
        known_fields.add(slug)
        field['name'] = {'en': _english(field.get('name'), f'field {slug}.name', slug)}
        field['summary'] = {'en': _english(field.get('summary'), f'field {slug}.summary')}
    papers = catalog.get('papers')
    if not isinstance(papers, list):
        raise CatalogError('papers must be a list')
    for paper in papers:
        if not isinstance(paper, dict):
            raise CatalogError('papers entries must be objects')
        _slug(paper.get('field'), 'paper.field')
        _slug(paper.get('slug'), 'paper.slug')
        label = f"paper {paper['field']}/{paper['slug']}"
        if paper['field'] not in known_fields:
            raise CatalogError(f'{label}: field is not registered')
        if not isinstance(paper.get('title'), str) or not paper['title'].strip():
            raise CatalogError(f'{label}.title must be a nonempty string')
        version = paper.get('version')
        if isinstance(version, bool) or not isinstance(version, (str, int)) or not str(version).strip():
            raise CatalogError(f'{label}.version must be a nonempty string or integer')
        paper['version'] = str(version).strip()
        paper['languages'] = paper.get('languages', catalog['languages'][:])
        if paper['languages'] != catalog['languages']:
            raise CatalogError(f'{label}: languages must match the English publication language')
        paper['audiences'] = paper.get('audiences', list(AUDIENCES))
        if (not isinstance(paper['audiences'], list) or len(paper['audiences']) != 3
                or not all(isinstance(audience, str) for audience in paper['audiences'])
                or set(paper['audiences']) != set(AUDIENCES)):
            raise CatalogError(f'{label}: audiences must contain general, student, and expert exactly once')
        if 'archive_slug' in paper:
            _slug(paper['archive_slug'], f'{label}.archive_slug')
        if 'source_path' in paper:
            paper['source_path'] = safe_relative_path(paper['source_path'], f'{label}.source_path')
        for key in ('source_ref', 'release'):
            if key in paper and (not isinstance(paper[key], str) or not paper[key].strip()
                                 or any(ord(c) < 32 for c in paper[key])):
                raise CatalogError(f'{label}.{key} must be a nonempty reference string')
        prefix = paper.get('content_prefix', '')
        if not isinstance(prefix, str) or not re.fullmatch(r'[A-Za-z0-9_.-]*', prefix):
            raise CatalogError(f'{label}.content_prefix must be a safe filename prefix')
        paper['content_prefix'] = prefix
        paper['summary'] = {'en': _english(paper.get('summary'), f'{label}.summary')}
        for key in ('subtitle', 'author', 'date', 'short_title'):
            if key in paper and not isinstance(paper[key], str):
                raise CatalogError(f'{label}.{key} must be a string')
        if 'series' in paper or 'series_order' in paper:
            _slug(paper.get('series'), f'{label}.series')
            order = paper.get('series_order')
            if isinstance(order, bool) or not isinstance(order, int) or order < 1:
                raise CatalogError(f'{label}.series_order must be a positive integer')
        for key in ('status_label', 'publication_note', 'downloads_intro'):
            if key in paper:
                paper[key] = _english(paper[key], f'{label}.{key}')
        if 'scope' in paper:
            scope = paper['scope']
            if not isinstance(scope, dict) or not isinstance(scope.get('en'), list) or not all(isinstance(s, str) for s in scope['en']):
                raise CatalogError(f'{label}.scope must contain an en list of paragraphs')
        paper['documents'] = _normalize_documents(paper, label)
    catalog['all_papers'] = papers
    catalog['papers'] = select_latest_papers(papers)
    prefixes = {}
    for paper in catalog['papers']:
        prefix = paper['content_prefix']
        identity = f"{paper['field']}/{paper['slug']}"
        if prefix in prefixes:
            raise CatalogError(f'Active papers {prefixes[prefix]} and {identity} share content_prefix {prefix!r}; each active paper requires its own article fragments')
        prefixes[prefix] = identity
    reserved = generated_page_paths(catalog) | {catalog['sitemap_filename'], '.nojekyll'}
    destinations = set()
    for paper in catalog['papers']:
        for document in paper_documents(paper):
            path = document['path']
            if path in reserved or path in destinations or path.startswith('assets/'):
                raise CatalogError(f'Duplicate or reserved active document path: {path}')
            destinations.add(path)
    return catalog


def load_catalog(root):
    path = Path(root) / 'site-src' / 'catalog.json'
    try:
        data = json.loads(path.read_text(encoding='utf-8'))
    except (OSError, json.JSONDecodeError) as exc:
        raise CatalogError(f'Cannot read catalog {path}: {exc}') from exc
    return normalize_catalog(data)
