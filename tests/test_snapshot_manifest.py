"""Exercise release-byte binding using disposable copies of this source payload."""
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from verify_snapshot import verify


class ManifestTests(unittest.TestCase):
    def candidate(self, directory):
        target = Path(directory) / 'snapshot'
        target.mkdir()
        manifest = json.loads((ROOT / 'snapshot-manifest.json').read_text())
        for name in [row['path'] for row in manifest['files']] + ['snapshot-manifest.json']:
            path = target / name
            path.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT / name, path)
        self.git(target, 'init', '-q')
        self.git(target, 'add', '.')
        return target

    def git(self, target, *args):
        return subprocess.check_output(['git', '-C', str(target), *args], stderr=subprocess.DEVNULL)

    def test_exact_staged_and_working_payload_passes(self):
        with tempfile.TemporaryDirectory() as directory:
            target = self.candidate(directory)
            self.assertEqual(verify(target)['qualified_inputs'], 599)

    def test_staged_substitution_is_rejected_when_worktree_is_restored(self):
        with tempfile.TemporaryDirectory() as directory:
            target = self.candidate(directory)
            path = target / 'README.md'
            original = path.read_bytes()
            # Preserve length so the batch size check alone cannot find it.
            replacement = b'X' + original[1:]
            self.assertNotEqual(original, replacement)
            path.write_bytes(replacement)
            self.git(target, 'add', 'README.md')
            path.write_bytes(original)
            with self.assertRaisesRegex(ValueError, 'staged blob differs'):
                verify(target)

    def test_working_substitution_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            target = self.candidate(directory)
            (target / 'README.md').write_text('synthetic altered public text')
            with self.assertRaisesRegex(ValueError, 'payload hash or size mismatch'):
                verify(target)

    def test_allowlist_update_does_not_permit_private_paths(self):
        with tempfile.TemporaryDirectory() as directory:
            target = self.candidate(directory)
            path = target / 'private' / 'notes.txt'
            path.parent.mkdir()
            data = b'synthetic private note'
            path.write_bytes(data)
            manifest_path = target / 'snapshot-manifest.json'
            manifest = json.loads(manifest_path.read_text())
            manifest['files'].append(dict(path='private/notes.txt', bytes=len(data),
                                          sha256=hashlib.sha256(data).hexdigest()))
            manifest_path.write_text(json.dumps(manifest))
            self.git(target, 'add', '-f', '.')
            with self.assertRaisesRegex(ValueError, 'finite privacy check failed'):
                verify(target)


if __name__ == '__main__':
    unittest.main()
