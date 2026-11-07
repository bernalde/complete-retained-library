#!/usr/bin/env python3
"""Check the root Lake layout and unchanged published sources without building."""
import hashlib
import json
from pathlib import Path
import re
import tomllib

from verify_snapshot import verify

ROOT = Path(__file__).resolve().parents[1]
ARCHIVE_SHA256 = 'e737a06098a579abc4d1186ca6237d3b91f29bd57e8c52cb15a0a5906184ca81'
CHANGED_ORIGINAL_FILES = {'README.md', 'RIGHTS.md', 'snapshot-manifest.json'}
ADDED_FILES = {'lean-toolchain', 'lake-manifest.json', 'lakefile.toml',
               'baseline-archive.json', 'distribution.json',
               'scripts/verify_root_layout.py', 'tests/test_root_layout.py'}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def payload_paths(root):
    """Visit payload paths; leave only a real root checkout's Git metadata to Git."""
    paths = []

    def visit(directory):
        for path in directory.iterdir():
            require(not path.is_symlink(), 'symlink in root layout')
            if path.name == '.git':
                require(directory == root, 'nested Git metadata in root layout')
                require(path.is_dir(), 'root Git metadata must be a real directory')
                continue
            require(path.is_dir() or path.is_file(), 'nonregular path in root layout')
            paths.append(path)
            if path.is_dir():
                visit(path)

    visit(root)
    return paths


def verify_root_layout(root=ROOT):
    root = Path(root)
    # Do not hide development products behind an exclusion or a Git ignore.
    # Every directory must be a parent of an explicitly listed payload file.
    payload = json.loads((root / 'snapshot-manifest.json').read_text())
    allowed_paths = {row['path'] for row in payload['files']} | {'snapshot-manifest.json'}
    allowed_dirs = {parent.as_posix() for name in allowed_paths
                    for parent in Path(name).parents if parent.as_posix() != '.'}
    paths = payload_paths(root)
    for path in paths:
        if path.is_dir():
            require(path.relative_to(root).as_posix() in allowed_dirs,
                    'directory outside root layout allowlist')
    # In a checkout the unchanged verifier also binds the Git index and staged
    # blobs to the payload. Root Git metadata is never treated as payload.
    result = verify(root)
    provenance = json.loads((root / 'baseline-archive.json').read_text())
    rows = provenance['files']
    require(provenance['archive_sha256'] == ARCHIVE_SHA256, 'baseline archive identity')
    require(provenance['archive_members'] == len(rows) == 620, 'baseline member count')
    require(len({row['path'] for row in rows}) == 620, 'duplicate baseline member')
    baseline_names = {row['path'] for row in rows}
    actual_names = {p.relative_to(root).as_posix() for p in paths if p.is_file()}
    require(actual_names == baseline_names | ADDED_FILES, 'root layout file allowlist')
    for row in rows:
        if row['path'] in CHANGED_ORIGINAL_FILES:
            continue
        data = (root / row['path']).read_bytes()
        require(len(data) == row['bytes'] and hashlib.sha256(data).hexdigest() == row['sha256'],
                'changed original published member: ' + row['path'])
    for name in ('lean-toolchain', 'lake-manifest.json'):
        require((root / name).read_bytes() == (root / 'lean-modern' / name).read_bytes(),
                'root pin differs from nested pin: ' + name)
    nested = tomllib.loads((root / 'lean-modern/lakefile.toml').read_text())
    current = tomllib.loads((root / 'lakefile.toml').read_text())
    expected = dict(nested)
    expected['lean_lib'] = [dict(row, srcDir='lean-modern') for row in nested['lean_lib']]
    expected['lean_lib'].append({'name': 'SourceProcedure',
                                'srcDir': 'companions/ch09-source-procedure',
                                'roots': ['Chapter09SourceProcedure']})
    require(current == expected, 'root configuration differs from literal derivation')
    manifest = json.loads((root / 'lake-manifest.json').read_text())
    require(current['name'] == manifest['name'], 'root package name mismatch')
    libraries = nested['lean_lib']
    modules = {p.stem for p in (root / 'lean-modern').glob('*.lean')}
    require(len(libraries) == len({x['name'] for x in libraries}) == 596,
            'baseline library count')
    require({x['name'] for x in libraries} == modules, 'library/module mapping')
    for library in current['lean_lib']:
        for module in library.get('roots', [library['name']]):
            source = root / library['srcDir'] / (module.replace('.', '/') + '.lean')
            require(source.is_file(), 'missing configured module: ' + module)
    targets = current['defaultTargets']
    extra_safe = sorted(modules - set(targets) - {'MkCSChallenge'})
    require(len(targets) == len(set(targets)) == 591, 'default target count')
    require(len(modules - {'MkCSChallenge'}) == 595, 'safe module inventory')
    require(extra_safe == ['ConeMigration', 'MigrationListChain', 'MkCSSolution', 'MkCSStatement'],
            'additional safe module inventory')
    require('SourceProcedure' not in targets, 'companion unexpectedly default')
    # The original verifier already checks all 595 baseline safe closures.
    # Add the companion source and checker as import-graph nodes, without
    # interpreting graph membership as theorem or transitive-axiom evidence.
    sources = {name: root / 'lean-modern' / (name + '.lean') for name in modules}
    for name in ('Chapter09SourceProcedure', 'CheckSourceProcedure'):
        sources[name] = root / 'companions/ch09-source-procedure' / (name + '.lean')
    imports = {}
    for name, path in sources.items():
        source = re.sub(r'/\-.*?\-/', '', path.read_text(), flags=re.S)
        source = re.sub(r'--[^\n]*', '', source)
        names = {part for line in re.findall(r'^\s*(?:public\s+)?import\s+([^\n]+)', source, re.M)
                 for part in line.split()}
        imports[name] = names & sources.keys()
    for start in ('Chapter09SourceProcedure', 'CheckSourceProcedure'):
        seen, pending = set(), [start]
        while pending:
            name = pending.pop()
            if name not in seen:
                seen.add(name)
                pending.extend(imports[name] - seen)
        require('MkCSChallenge' not in seen, 'challenge enters companion closure')
    metadata = json.loads((root / 'distribution.json').read_text())
    snapshot = json.loads((root / 'snapshot-manifest.json').read_text())
    require(metadata['public_release_authorized'] is False and
            snapshot['public_release_authorized'] is False, 'new payload release authorization')
    result.update(root_configuration_matches_derivation=True,
                  root_libraries=len(current['lean_lib']), safe_baseline_modules=595,
                  unchanged_original_members=620-len(CHANGED_ORIGINAL_FILES),
                  original_compiler_inputs_exact=599,
                  additional_safe_targets=extra_safe,
                  companion_and_checker_exact=True, companion_is_default=False,
                  companion_challenge_isolated=True,
                  public_release_authorized=False,
                  reservoir_indexing='not established', proof_build='not performed')
    return result


if __name__ == '__main__':
    try:
        print(json.dumps({'passed': True, **verify_root_layout()}, indent=2))
    except Exception as error:
        print(json.dumps({'passed': False, 'error_type': type(error).__name__}))
        raise SystemExit(1)
