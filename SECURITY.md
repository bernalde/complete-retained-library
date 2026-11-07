# Security

Do not post credentials, account exports or private correspondence in issues,
pull requests or build logs. Never commit local environment files or keys.

For a suspected credential exposure, revoke or rotate the credential at its
provider first. Use GitHub's private vulnerability reporting when available, or
contact the maintainer through the professional contact information on the
SECQUOIA lab website. Do not include a token value in the initial message.

This repository is a curated source snapshot. The earlier research repository
and its history remain private. A pre-publication source scan is a bounded
check, not a guarantee against every possible secret encoding or vulnerability.

Before exporting a new bootstrap snapshot, run the finite privacy preflight:

```sh
python3 -B scripts/check_public_snapshot.py --repository /path/to/new-snapshot
```

It reads the Git index and rejects private paths, selected credential patterns
and inherited multi-commit history. It is intended for preparing a new
history-free snapshot, not as a requirement that normal ongoing development
retain only one commit. Scan final bytes separately with a general-purpose
secret scanner, and keep an exact allowlist with its rights review.
