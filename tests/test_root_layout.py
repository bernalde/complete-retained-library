"""Exercise clean source snapshots and disposable allowlisted Git checkouts."""
import hashlib
import json
from pathlib import Path, PurePosixPath
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from verify_root_layout import verify_root_layout


class RootLayoutTests(unittest.TestCase):
    def copy(self, parent, source=ROOT, name='snapshot'):
        target = Path(parent) / name
        target.mkdir()
        manifest = json.loads((source / 'snapshot-manifest.json').read_text())
        names = {row['path'] for row in manifest['files']} | {'snapshot-manifest.json'}
        for name in sorted(names):
            relative = PurePosixPath(name)
            if (relative.is_absolute() or '..' in relative.parts or
                    '.git' in relative.parts or str(relative) != name):
                raise ValueError('invalid fixture allowlist path')
            original = source / name
            if original.is_symlink() or not original.is_file():
                raise ValueError('fixture source is not a regular file')
            path = target / name
            path.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(original, path)
        return target

    def git(self, target, *args):
        return subprocess.check_output(['git', '-C', str(target), *args],
                                       stderr=subprocess.DEVNULL)

    def checkout(self, parent, name='checkout'):
        root = self.copy(parent, name=name)
        self.git(root, 'init', '-q')
        self.git(root, 'add', '--', '.')
        self.git(root, '-c', 'user.name=Synthetic Test',
                 '-c', 'user.email=synthetic@example.org',
                 'commit', '-qm', 'Allowlisted public software fixture')
        return root

    def rebind(self, root, name):
        manifest_path = root / 'snapshot-manifest.json'
        manifest = json.loads(manifest_path.read_text())
        data = (root / name).read_bytes()
        for row in manifest['files']:
            if row['path'] == name:
                row.update(bytes=len(data), sha256=hashlib.sha256(data).hexdigest())
        manifest_path.write_text(json.dumps(manifest))

    def test_exact_root_layout(self):
        result = verify_root_layout(ROOT)
        self.assertEqual(result['safe_baseline_modules'], 595)
        self.assertEqual(result['root_libraries'], 597)

    def test_real_git_checkout_passes(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = self.checkout(tmp)
            self.assertTrue((root / '.git').is_dir())
            self.assertEqual(verify_root_layout(root)['qualified_inputs'], 599)

    def test_allowlisted_fixture_does_not_inherit_checkout_metadata(self):
        with tempfile.TemporaryDirectory() as tmp:
            checkout = self.checkout(tmp)
            root = self.copy(tmp, source=checkout)
            self.assertFalse((root / '.git').exists())
            self.assertEqual(len([p for p in root.rglob('*') if p.is_file()]), 627)
            self.assertEqual(verify_root_layout(root)['qualified_inputs'], 599)

    def test_checkout_staged_substitution_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = self.checkout(tmp)
            path = root / 'README.md'
            original = path.read_bytes()
            path.write_bytes(b'X' + original[1:])
            self.git(root, 'add', '--', 'README.md')
            path.write_bytes(original)
            with self.assertRaisesRegex(ValueError, 'staged blob differs'):
                verify_root_layout(root)

    def test_checkout_unlisted_source_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = self.checkout(tmp)
            (root / 'Extra.lean').write_text('-- synthetic unlisted source\n')
            with self.assertRaisesRegex(ValueError, 'root layout file allowlist'):
                verify_root_layout(root)

    def test_nested_git_directory_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = self.copy(tmp)
            (root / 'docs/.git').mkdir()
            with self.assertRaisesRegex(ValueError, 'nested Git metadata'):
                verify_root_layout(root)

    def test_root_git_symlink_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = self.copy(tmp)
            (root / '.git').symlink_to(root / 'docs', target_is_directory=True)
            with self.assertRaisesRegex(ValueError, 'symlink in root layout'):
                verify_root_layout(root)

    def test_root_git_file_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = self.copy(tmp)
            (root / '.git').write_text('synthetic worktree metadata\n')
            with self.assertRaisesRegex(ValueError, 'root Git metadata must be a real directory'):
                verify_root_layout(root)

    def test_extra_source_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = self.copy(tmp)
            (root / 'Extra.lean').write_text('-- synthetic unlisted source\n')
            with self.assertRaisesRegex(ValueError, 'directory differs'):
                verify_root_layout(root)

    def test_empty_cache_directory_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = self.copy(tmp)
            (root / '.lake').mkdir()
            with self.assertRaisesRegex(ValueError, 'directory outside root layout allowlist'):
                verify_root_layout(root)

    def test_unlisted_symlink_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = self.copy(tmp)
            (root / 'extra-link').symlink_to(root / 'README.md')
            with self.assertRaisesRegex(ValueError, 'symlink in root layout'):
                verify_root_layout(root)

    def test_cache_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = self.copy(tmp)
            (root / '.lake').mkdir()
            (root / '.lake/cache.txt').write_text('synthetic cache')
            with self.assertRaisesRegex(ValueError, 'directory outside root layout allowlist'):
                verify_root_layout(root)

    def test_rebound_root_mapping_change_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = self.copy(tmp)
            path = root / 'lakefile.toml'
            path.write_text(path.read_text().replace('srcDir = "lean-modern"', 'srcDir = "."', 1))
            self.rebind(root, 'lakefile.toml')
            with self.assertRaisesRegex(ValueError, 'literal derivation'):
                verify_root_layout(root)

    def test_rebound_companion_change_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = self.copy(tmp)
            name = 'companions/ch09-source-procedure/CheckSourceProcedure.lean'
            path = root / name
            path.write_bytes(path.read_bytes() + b'\n-- synthetic changed checker\n')
            self.rebind(root, name)
            with self.assertRaisesRegex(ValueError, 'changed original published member'):
                verify_root_layout(root)


if __name__ == '__main__':
    unittest.main()
