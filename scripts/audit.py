#!/usr/bin/env python3
"""Strict audit for the declared Airy1Gumbel theorem inventory.

The source inventory covers `theorem`/`lemma` declarations, including
attribute-prefixed ones (`@[simp] lemma ...` with same-line attributes)."""
import argparse
import hashlib
import json
import re
from pathlib import Path

ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def without_comments(source):
    out = []
    depth = 0
    i = 0
    while i < len(source):
        if source.startswith('/-', i):
            depth += 1
            i += 2
        elif depth and source.startswith('-/', i):
            depth -= 1
            i += 2
        elif depth:
            if source[i] == '\n':
                out.append('\n')
            i += 1
        elif source.startswith('--', i):
            j = source.find('\n', i)
            i = len(source) if j < 0 else j
        else:
            out.append(source[i])
            i += 1
    if depth:
        raise ValueError('Unclosed source comment')
    return ''.join(out)


def inventory(root):
    names = []
    modules = []
    for p in sorted((root / 'Airy1Gumbel').rglob('*.lean')):
        source = without_comments(p.read_text())
        if re.search(r'\b(sorry|admit|axiom|unsafe|implemented_by|extern)\b', source):
            raise ValueError(f'Forbidden proof escape in {p.name}')
        # Fail closed on a new namespace layout until this inventory is extended.
        if re.findall(r'^namespace\s+(\S+)', source, re.M) != ['Airy1Gumbel']:
            raise ValueError(f'Unexpected namespace layout in {p.name}')
        if re.search(r'^\s*private\b', source, re.M):
            raise ValueError('Private declarations need an environment-level inventory')
        found = re.findall(r"^\s*(?:@\[[^\n\]]*\]\s*)*(?:theorem|lemma)\s+([\w.'\u0080-\uffff]+)", source, re.M)
        names.extend('Airy1Gumbel.' + n for n in found)
        modules.append('.'.join(p.relative_to(root).with_suffix('').parts))
    if not names or len(names) != len(set(names)):
        raise ValueError('Empty or duplicate source theorem inventory')
    imports = re.findall(r'^import\s+(\S+)', (root / 'Airy1Gumbel.lean').read_text(), re.M)
    if set(imports) != set(modules) or len(imports) != len(set(imports)):
        raise ValueError('Umbrella module does not import exactly the project modules')
    expected = re.findall(r'^#print axioms\s+(\S+)\s*$', (root / 'AxiomCheck.lean').read_text(), re.M)
    if set(expected) != set(names) or len(expected) != len(names):
        raise ValueError('AxiomCheck inventory differs from source declarations')
    return expected


def validate_transcript(text, expected):
    pattern = re.compile(r"'(.+)' depends on axioms:\s*\[([^\]]*)\]", re.M)
    matches = list(pattern.finditer(text))
    result = {}
    for match in matches:
        name = match.group(1)
        axioms = [a.strip() for a in match.group(2).split(',') if a.strip()]
        if set(axioms) - ALLOWED:
            raise ValueError(f'Disallowed axioms for {name}: {sorted(set(axioms) - ALLOWED)}')
        if name in result:
            raise ValueError(f'Duplicate theorem in live transcript: {name}')
        result[name] = axioms
    if set(result) != set(expected) or len(expected) != len(set(expected)):
        raise ValueError('Live theorem names differ from the exact expected inventory')
    remainder = pattern.sub('', text).strip()
    if remainder:
        raise ValueError('Unexpected output outside the live axiom declarations')
    return result


def source_hashes(root):
    paths = [root / x for x in ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json',
                               'Airy1Gumbel.lean', 'AxiomCheck.lean', 'README.md',
                               'scripts/audit.py', 'scripts/test_audit.py']]
    paths += sorted((root / 'Airy1Gumbel').rglob('*.lean'))
    return {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}


def _toml_tables(text, table):
    """The `[[table]]` entries of a lakefile.toml as dicts of their simple keys
    (strings and string arrays). Uses `tomllib` when available (Python >= 3.11) and a
    small fallback parser otherwise (for Python 3.10)."""
    try:
        import tomllib
    except ImportError:
        tomllib = None
    if tomllib is not None:
        return list(tomllib.loads(text).get(table, []))
    out, cur = [], None
    for raw in text.splitlines():
        line = raw.split('#', 1)[0].strip()
        if not line:
            continue
        if line.startswith('['):
            cur = {} if line.replace(' ', '') == f'[[{table}]]' else None
            if cur is not None:
                out.append(cur)
            continue
        if cur is None or '=' not in line:
            continue
        key, val = (s.strip() for s in line.split('=', 1))
        if val.startswith('['):
            cur[key] = re.findall(r'"([^"]*)"', val)
        elif val.startswith('"'):
            cur[key] = val.strip('"')
    return out


def _dep_dir(root, req):
    """Where Lake put a required package: its `path`, else `.lake/packages/<name>` of this
    package or, for a package used as a path dependency, of an enclosing package."""
    if 'path' in req:
        return root / req['path']
    for base in [root, *root.resolve().parents]:
        cand = base / '.lake' / 'packages' / req['name']
        if cand.is_dir():
            return cand
    return root / '.lake' / 'packages' / req['name']


def lake_lib_roots(pkg_dir):
    """Top-level module roots that a Lake package's `lean_lib`s provide
    (name, or roots / globs), read from its lakefile.toml or lakefile.lean."""
    roots = set()
    toml_file, lean_file = pkg_dir / 'lakefile.toml', pkg_dir / 'lakefile.lean'
    if toml_file.exists():
        for lib in _toml_tables(toml_file.read_text(), 'lean_lib'):
            for r in list(lib.get('roots', [lib['name']])) + list(lib.get('globs', [])):
                roots.add(str(r).split('.')[0].strip('«»'))
    elif lean_file.exists():
        src = lean_file.read_text()
        roots.update(m.strip('«»') for m in re.findall(r'^\s*lean_lib\s+(«[^»]+»|[A-Za-z_][\w]*)', src, re.M))
        for block in re.findall(r'(?:roots|globs)\s*:=\s*#\[([^\]]*)\]', src):
            roots.update(t.split('.')[0] for t in re.findall(r'`([A-Za-z_][\w.]*)', block))
    return roots


def check_requires(root, source_paths):
    """Fail closed on a declared-but-unused Lake dependency: every `[[require]]`
    in lakefile.toml must provide a library root that some package source
    imports."""
    imports = set()
    for p in source_paths:
        for mod in re.findall(r'^import\s+(\S+)', without_comments(p.read_text()), re.M):
            imports.add(mod.split('.')[0])
    unused = []
    for req in _toml_tables((root / 'lakefile.toml').read_text(), 'require'):
        name = req['name']
        pkg_dir = _dep_dir(root, req)
        roots = lake_lib_roots(pkg_dir)
        if not roots:
            raise ValueError(f'Cannot read the libraries of required package {name} at {pkg_dir}')
        if not roots & imports:
            unused.append(name)
    if unused:
        raise ValueError(f'Declared but unused Lake requirement(s): {unused}')


def main():
    p = argparse.ArgumentParser()
    p.add_argument('transcript', type=Path)
    p.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[1])
    p.add_argument('--json', action='store_true')
    p.add_argument('--receipt', type=Path)
    args = p.parse_args()
    names = inventory(args.root)
    check_requires(args.root, sorted((args.root / 'Airy1Gumbel').rglob('*.lean'))
                   + [args.root / 'Airy1Gumbel.lean'])
    actual = validate_transcript(args.transcript.read_text(), names)
    result = {'status': 'PASS', 'theorems': actual, 'source_sha256': source_hashes(args.root),
              'scope': 'Gumbel limit of the normalized maximum of a constructed Airy_1 process; the final '
                       'headline gumbel_limit_continuum_real_normalized_airy1_final2 assumes the three '
                       'named inputs Airy1FddPositive, GOELeftTail and CubicStrongMixing'}
    if args.receipt:
        receipt = json.loads(args.receipt.read_text())
        if not re.fullmatch(r'[0-9a-f]{40}', receipt.get('candidate_commit', '')):
            raise ValueError('Receipt does not name a full candidate commit')
        if receipt.get('source_sha256') != result['source_sha256']:
            raise ValueError('Receipt source inventory/hashes differ from the current package')
        if receipt.get('theorems') != actual:
            raise ValueError('Receipt theorem/axiom inventory differs from the live transcript')
        if receipt.get('positive_transcript_sha256') != hashlib.sha256(args.transcript.read_bytes()).hexdigest():
            raise ValueError('Receipt positive transcript hash differs')
        if receipt.get('negative_control', {}).get('status') != 'PASS: negative control rejected':
            raise ValueError('Receipt lacks the checked negative-control outcome')
    print(json.dumps(result, indent=2) if args.json else f'PASS: {len(actual)} exact theorem names; approved axioms only')


if __name__ == '__main__':
    main()
