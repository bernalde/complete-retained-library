#!/usr/bin/env python3
"""Fail-closed preflight of a candidate public Git index; never modifies it.

This privacy gate is not a rights clearance or historical-repository scanner.
Use on a separate history-free snapshot, with a separately reviewed allowlist.
Findings expose only paths and categories, never matched bytes.
"""
import argparse
import json
import re
import subprocess
from pathlib import PurePosixPath

TOKEN = re.compile(rb'\b(?:gh[pousr]_[A-Za-z0-9]{36,255}|github_pat_[A-Za-z0-9_]{50,255}|sk-(?:proj-|svcacct-)?[A-Za-z0-9_-]{40,255}|AKIA[0-9A-Z]{16})\b|-----BEGIN (?:RSA |EC |OPENSSH |DSA )?PRIVATE KEY-----')
ASSIGNMENT = re.compile(rb'''(?i)["']?(?:DWAVE_API_TOKEN|QCI_TOKEN|[A-Z0-9_]*(?:API_KEY|ACCESS_TOKEN|SECRET_KEY|PASSWORD))["']?\s*[:=]\s*["']([^"'\r\n]{8,})["']''')
SAFE_MARKERS = {b'[REDACTED]', b'<redacted>', b'REDACTED', b'not recorded'}

def classify_path(path, mode='100644'):
    parts = PurePosixPath(path).parts
    reasons = []
    if mode not in {'100644', '100755'}:
        reasons.append('nonregular-or-unmerged-entry')
    if any(p in {'.usage', '.git', '.codex', '.claude', '.aws', '.ssh', '.agents', '.vscode', '.idea', 'private', 'correspondence'} for p in parts):
        reasons.append('private-path')
    if parts and parts[0] in {'audit', 'planning', 'sources', 'revisions', 'preservation'}:
        reasons.append('private-research-input-path')
    if any(p.startswith('.env') or p in {'.netrc', '.npmrc', '.pypirc', '.git-credentials', 'auth.json', 'credentials', 'credentials.json', 'token.json', 'id_rsa', 'id_ed25519'} for p in parts):
        reasons.append('credential-config-path')
    if path.lower().endswith(('.jsonl', '.pem', '.key', '.zip', '.tar', '.tar.gz', '.tgz', '.7z')):
        reasons.append('raw-capture-or-unreviewed-container')
    return sorted(set(reasons))

def classify(path, data, mode='100644'):
    reasons = classify_path(path, mode)
    if TOKEN.search(data) or any(m.group(1) not in SAFE_MARKERS for m in ASSIGNMENT.finditer(data)):
        reasons.append('credential-shaped-literal')
    try:
        obj = json.loads(data)
    except (ValueError, UnicodeDecodeError):
        obj = None
    stack = [obj]
    while stack:
        value = stack.pop()
        if isinstance(value, dict):
            if value.get('role') in ('user', 'assistant') or value.get('type') in ('session_meta', 'response_item'):
                reasons.append('conversation-record')
            if any(k in value for k in ('conversation_id', 'apiKeySource', 'messaging_socket_path')):
                reasons.append('private-session-metadata')
            stack.extend(value.values())
        elif isinstance(value, list):
            stack.extend(value)
    return sorted(set(reasons))

MAX_BLOB_BYTES = 16 * 1024 * 1024

def scan(repo, max_blob_bytes=MAX_BLOB_BYTES):
    if not isinstance(max_blob_bytes, int) or max_blob_bytes < 1:
        raise ValueError('invalid blob size bound')
    def git(*args):
        return subprocess.check_output(['git', '-C', repo, *args], stderr=subprocess.DEVNULL)
    findings = []
    entries = []
    for row in git('ls-files', '--stage', '-z').split(b'\0'):
        if not row:
            continue
        meta, raw_path = row.split(b'\t', 1)
        mode, oid, stage = meta.decode('ascii').split()
        path = raw_path.decode('utf-8', errors='strict')
        entries.append((path, oid))
        reasons = classify_path(path, mode)
        if stage != '0':
            reasons.append('nonregular-or-unmerged-entry')
        if reasons:
            findings.append({'path': path, 'categories': sorted(set(reasons))})
    if not entries:
        raise ValueError('empty index')
    result = {'scope': 'pre-publication bootstrap snapshot; finite privacy check, no rights clearance',
              'files': len(entries), 'findings': findings, 'max_blob_bytes': max_blob_bytes}
    if findings:
        result['content_scan'] = 'not run because path preflight failed'
        result['history_scan'] = 'not run because path preflight failed'
        return result
    if git('rev-parse', '--is-shallow-repository').strip() != b'false':
        findings.append({'path': '<repository-history>', 'categories': ['shallow-history-not-accepted']})
        result['content_scan'] = 'not run because history preflight failed'
        return result
    # Include detached HEAD as well as every branch/tag/stash/other local ref.
    has_head = subprocess.run(['git', '-C', repo, 'rev-parse', '--verify', 'HEAD'],
                              stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL).returncode == 0
    count = int(git('rev-list', '--count', '--all', *(['HEAD'] if has_head else [])).strip())
    result['ref_reachable_commits'] = count
    if count > 1:
        findings.append({'path': '<repository-history>', 'categories': ['not-a-history-free-bootstrap-snapshot']})
        result['content_scan'] = 'not run because history preflight failed'
        return result
    if count == 1:
        # A clean index cannot clear a different already-committed root tree.
        difference = subprocess.run(['git', '-C', repo, 'diff', '--cached', '--quiet', 'HEAD'],
                                    stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL).returncode
        if difference:
            findings.append({'path': '<repository-history>', 'categories': ['index-does-not-match-bootstrap-commit']})
            result['content_scan'] = 'not run because history preflight failed'
            return result
    result['content_scan'] = 'completed within per-blob bound'
    for path, oid in entries:
        size = int(git('cat-file', '-s', oid).strip())
        if size > max_blob_bytes:
            findings.append({'path': path, 'categories': ['blob-exceeds-inspection-bound']})
            continue
        # OIDs identify immutable bytes; size is checked before loading content.
        data = git('cat-file', 'blob', oid)
        if len(data) != size or len(data) > max_blob_bytes:
            raise ValueError('blob size mismatch')
        reasons = classify(path, data)
        if reasons:
            findings.append({'path': path, 'categories': reasons})
    return result

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repository', default='.')
    args = parser.parse_args()
    try:
        result = scan(args.repository)
    except Exception as error:
        print(json.dumps({'passed': False, 'error_type': type(error).__name__}))
        return 2
    result['passed'] = not result['findings']
    print(json.dumps(result, indent=2))
    return 0 if result['passed'] else 1

if __name__ == '__main__':
    raise SystemExit(main())
