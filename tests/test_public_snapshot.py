import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest import mock

import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
from check_public_snapshot import classify, scan


class PrivacyTests(unittest.TestCase):

    def test_literal_detection(self):
        for key in ('DWAVE_API_TOKEN', 'QCI_TOKEN'):
            self.assertIn('credential-shaped-literal', classify('receipt.json', json.dumps({key: 'synthetic-secret-123'}).encode()))
        self.assertNotIn('credential-shaped-literal', classify('receipt.json', b'{"QCI_TOKEN": "[REDACTED]"}'))

    def test_public_metadata_is_not_credential(self):
        self.assertEqual(classify('references.json', b'{"doi":"10.1000/example", "author_email":"author@example.org", "sha256":"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"}'), [])

    def test_deny_paths_and_records(self):
        for path in ('.usage/raw/log.json', 'planning/correspondence/recipients.csv', '.env.production', 'capture.jsonl', 'bundle.zip', 'audit/receipt.json', 'sources/paper.pdf', 'revisions/source.tex', 'planning/recipients.csv', 'private/notes.txt'):
            self.assertTrue(classify(path, b''))
        self.assertIn('conversation-record', classify('capture.json', b'[{"role":"user","content":"synthetic"}]'))
        self.assertTrue(classify('link', b'target', '120000'))

    def test_scan_uses_index_preserves_worktree_and_index(self):
        with tempfile.TemporaryDirectory() as tmp:
            def git(*args):
                return subprocess.check_output(['git', '-C', tmp, *args], stderr=subprocess.DEVNULL)
            git('init', '-q')
            path = Path(tmp) / 'receipt.json'
            path.write_text(json.dumps(dict(zip(['QCI_TOKEN'], ['synthetic-' + 'secret-in-index']))))
            git('add', 'receipt.json')
            path.write_text('{}')
            before = git('ls-files', '--stage')
            result = scan(tmp)
            self.assertEqual(result['findings'][0]['categories'], ['credential-shaped-literal'])
            self.assertEqual(before, git('ls-files', '--stage'))
            self.assertEqual(path.read_text(), '{}')
            self.assertNotIn('synthetic-secret-in-index', json.dumps(result))


    def new_repo(self, tmp):
        def git(*args):
            return subprocess.check_output(['git', '-C', tmp, *args], stderr=subprocess.DEVNULL)
        git('init', '-q')
        git('config', 'user.name', 'Synthetic Test')
        git('config', 'user.email', 'synthetic@example.org')
        return git

    def test_path_preflight_never_reads_blobs(self):
        with tempfile.TemporaryDirectory() as tmp:
            git = self.new_repo(tmp)
            path = Path(tmp) / '.usage' / 'raw' / 'receipt.json'
            path.parent.mkdir(parents=True)
            path.write_text('{}')
            git('add', '-f', '.')
            original = subprocess.check_output
            calls = []
            def record(argv, **kwargs):
                calls.append(argv)
                return original(argv, **kwargs)
            with mock.patch('check_public_snapshot.subprocess.check_output', side_effect=record):
                result = scan(tmp)
            self.assertEqual(result['content_scan'], 'not run because path preflight failed')
            self.assertFalse(any('cat-file' in call for call in calls))

    def test_history_on_other_ref_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            git = self.new_repo(tmp)
            path = Path(tmp) / 'public.txt'
            path.write_text('safe first snapshot')
            git('add', '.')
            git('commit', '-qm', 'first')
            first = git('rev-parse', 'HEAD').decode().strip()
            self.assertFalse(scan(tmp)['findings'])
            path.write_text('safe second snapshot')
            git('add', '.')
            git('commit', '-qm', 'second')
            git('tag', 'retained-history')
            git('checkout', '-q', '--detach', first)
            result = scan(tmp)
            self.assertEqual(result['ref_reachable_commits'], 2)
            self.assertEqual(result['content_scan'], 'not run because history preflight failed')

    def test_committed_tree_cannot_be_cleared_by_staged_removal(self):
        with tempfile.TemporaryDirectory() as tmp:
            git = self.new_repo(tmp)
            path = Path(tmp) / 'public.txt'
            path.write_text('safe original')
            git('add', '.')
            git('commit', '-qm', 'first')
            path.write_text('safe staged replacement')
            git('add', '.')
            self.assertIn('index-does-not-match-bootstrap-commit', scan(tmp)['findings'][0]['categories'])

    def test_size_bound_rejects_without_loading_blob(self):
        with tempfile.TemporaryDirectory() as tmp:
            git = self.new_repo(tmp)
            (Path(tmp) / 'large.txt').write_text('x' * 33)
            git('add', '.')
            original = subprocess.check_output
            calls = []
            def record(argv, **kwargs):
                calls.append(argv)
                return original(argv, **kwargs)
            with mock.patch('check_public_snapshot.subprocess.check_output', side_effect=record):
                result = scan(tmp, max_blob_bytes=32)
            self.assertEqual(result['findings'][0]['categories'], ['blob-exceeds-inspection-bound'])
            self.assertFalse(any('blob' in call for call in calls))
            self.assertFalse(scan(tmp, max_blob_bytes=33)['findings'])

    def test_shallow_clone_is_not_a_history_free_snapshot(self):
        with tempfile.TemporaryDirectory() as tmp:
            source = Path(tmp) / 'source'
            source.mkdir()
            git = self.new_repo(str(source))
            (source / 'public.txt').write_text('first safe tree')
            git('add', '.')
            git('commit', '-qm', 'first')
            (source / 'public.txt').write_text('second safe tree')
            git('add', '.')
            git('commit', '-qm', 'second')
            target = Path(tmp) / 'shallow'
            subprocess.check_output(['git', '-c', 'protocol.file.allow=always', 'clone',
                                     '-q', '--depth=1', source.as_uri(), str(target)],
                                    stderr=subprocess.DEVNULL)
            result = scan(str(target))
            self.assertIn('shallow-history-not-accepted', result['findings'][0]['categories'])
            self.assertEqual(result['content_scan'], 'not run because history preflight failed')

    def test_test_source_contains_no_credential_literal(self):
        self.assertNotIn('credential-shaped-literal', classify('test.py', Path(__file__).read_bytes()))


if __name__ == '__main__':
    unittest.main()
