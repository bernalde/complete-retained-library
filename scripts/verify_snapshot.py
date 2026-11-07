#!/usr/bin/env python3
"""Check the public payload and preserved Lean inputs; no proof build or writes."""
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import subprocess
import tomllib

from check_public_snapshot import classify

ROOT = Path(__file__).resolve().parents[1]


def digest(data):
    return hashlib.sha256(data).hexdigest()


def verify(root=ROOT):
    root = Path(root)
    payload = json.loads((root / 'snapshot-manifest.json').read_text())
    entries = payload['files']
    if not entries or len({row['path'] for row in entries}) != len(entries):
        raise ValueError('empty or duplicate file allowlist')
    listed = set()
    expected_files = {}
    for row in entries:
        name = row['path']
        relative = PurePosixPath(name)
        if relative.is_absolute() or '..' in relative.parts or str(relative) != name:
            raise ValueError('invalid allowlist path')
        path = root / name
        if any(part.is_symlink() for part in (path, *path.parents)):
            raise ValueError('symlink in payload: ' + name)
        data = path.read_bytes()
        if len(data) != row['bytes'] or digest(data) != row['sha256']:
            raise ValueError('payload hash or size mismatch: ' + name)
        if classify(name, data):
            raise ValueError('finite privacy check failed: ' + name)
        expected_files[name] = data
        listed.add(name)
    # The manifest cannot contain its own digest. Publication binds it separately.
    listed.add('snapshot-manifest.json')
    expected_files['snapshot-manifest.json'] = (root / 'snapshot-manifest.json').read_bytes()
    if classify('snapshot-manifest.json', expected_files['snapshot-manifest.json']):
        raise ValueError('finite privacy check failed for manifest')
    if (root / '.git').exists():
        result = subprocess.run(['git', '-C', str(root), 'ls-files', '--stage', '-z'],
                                capture_output=True, check=True)
        staged = {}
        for record in result.stdout.split(b'\0'):
            if not record:
                continue
            metadata, name = record.split(b'\t', 1)
            mode, oid, stage = metadata.decode('ascii').split()
            if mode not in {'100644', '100755'} or stage != '0':
                raise ValueError('nonregular or unmerged Git entry')
            staged[name.decode('utf-8')] = oid
        tracked = set(staged)
        if tracked != listed:
            raise ValueError('Git index differs from the payload allowlist')
        # Read immutable staged blobs as well as working files. Check sizes
        # before loading the batch so a staged replacement cannot exhaust RAM.
        by_oid = {}
        for name, oid in staged.items():
            data = expected_files[name]
            if oid in by_oid and by_oid[oid] != data:
                raise ValueError('inconsistent staged object')
            by_oid[oid] = data
        oids = sorted(by_oid)
        requests = ('\n'.join(oids) + '\n').encode('ascii')
        metadata = subprocess.check_output(['git', '-C', str(root), 'cat-file', '--batch-check'], input=requests)
        records = metadata.splitlines()
        if len(records) != len(oids):
            raise ValueError('incomplete Git object metadata')
        for oid, record in zip(oids, records):
            fields = record.decode('ascii').split()
            if fields != [oid, 'blob', str(len(by_oid[oid]))]:
                raise ValueError('staged object type or size mismatch')
        objects = subprocess.check_output(['git', '-C', str(root), 'cat-file', '--batch'], input=requests)
        cursor = 0
        for oid in oids:
            end = objects.index(b'\n', cursor)
            header = objects[cursor:end].decode('ascii').split()
            size = len(by_oid[oid])
            if header != [oid, 'blob', str(size)]:
                raise ValueError('staged object header mismatch')
            start = end + 1
            if objects[start:start+size] != by_oid[oid] or objects[start+size:start+size+1] != b'\n':
                raise ValueError('staged blob differs from allowlisted working file')
            cursor = start + size + 1
        if cursor != len(objects):
            raise ValueError('unexpected Git object batch data')
    else:
        actual = {str(path.relative_to(root)) for path in root.rglob('*') if path.is_file()}
        if actual != listed:
            raise ValueError('directory differs from the payload allowlist')

    project = root / 'lean-modern'
    inputs = json.loads((root / 'lean-inputs.json').read_text())['compiler_input_sha256']
    if len(inputs) != 599:
        raise ValueError('qualified input count mismatch')
    for name, expected in inputs.items():
        if digest((project / name).read_bytes()) != expected:
            raise ValueError('qualified input mismatch: ' + name)
    modules = {path.stem for path in project.glob('*.lean')}
    expected_modules = {Path(name).stem for name in inputs if name.endswith('.lean')}
    if modules != expected_modules or len(modules) != 596:
        raise ValueError('module inventory mismatch')
    if (project / 'lean-toolchain').read_text().strip() != 'leanprover/lean4:v4.35.0':
        raise ValueError('toolchain mismatch')
    configuration = tomllib.loads((project / 'lakefile.toml').read_text())
    targets = configuration['defaultTargets']
    if len(targets) != 591 or len(set(targets)) != 591 or not set(targets) <= modules:
        raise ValueError('default target inventory mismatch')
    if 'MkCSChallenge' in targets:
        raise ValueError('comparison challenge in default targets')
    closure = {}
    external = {'Mathlib', 'Batteries', 'Lean', 'Std', 'Init', 'Qq', 'Aesop', 'Plausible', 'ProofWidgets', 'ImportGraph', 'Cli'}
    for module in modules:
        # The preserved sources use ordinary single-line import declarations.
        # Drop block/line comments so prose is not treated as an import.
        source = (project / (module + '.lean')).read_text()
        source = re.sub(r'/\-.*?\-/', '', source, flags=re.S)
        source = re.sub(r'--[^\n]*', '', source)
        imports = {name for line in re.findall(r'^\s*(?:public\s+)?import\s+([^\n]+)', source, re.M) for name in line.split()}
        missing = {name for name in imports if name not in modules and name.split('.')[0] not in external}
        if missing:
            raise ValueError('unresolved import in ' + module + ': ' + ', '.join(sorted(missing)))
        closure[module] = imports & modules
    for module in modules - {'MkCSChallenge'}:
        seen = set()
        queue = [module]
        while queue:
            current = queue.pop()
            if current in seen:
                continue
            seen.add(current)
            queue.extend(closure[current] - seen)
        if 'MkCSChallenge' in seen:
            raise ValueError('challenge dependency in ' + module)
    return {'payload_files': len(listed), 'qualified_inputs': len(inputs),
            'modules': len(modules), 'default_targets': len(targets),
            'challenge_isolated': True, 'proof_build': 'not performed'}


if __name__ == '__main__':
    try:
        print(json.dumps({'passed': True, **verify()}, indent=2))
    except Exception as error:
        # Never echo arbitrary file contents or a credential from a parser error.
        print(json.dumps({'passed': False, 'error_type': type(error).__name__}))
        raise SystemExit(1)
