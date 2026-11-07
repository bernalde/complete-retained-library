# Thesis proof sources

This package has a Lake project at its root. Use the pinned Lean 4.35.0
installation and dependency revisions, then run these commands from this directory:

```sh
lean --version
lake exe cache get
lake build
lake build ConeMigration MigrationListChain MkCSStatement MkCSSolution
```

The first build selects the same 591 default targets as the original project.
The second adds the four remaining safe modules. The original 596 libraries now
use `lean-modern/` as their source directory. Their source bytes, library names,
roots and dependency revisions are unchanged. Module imports retain their usual
names, for example `import Chapter09Nonlinear`.

`MkCSChallenge` contains an intentional proof placeholder. It is excluded from
the default targets and every safe module's import closure. It is not part of the
proved library. Module and target counts include models, definitions, examples,
controls and adapters; they are not theorem counts.

This local root-layout candidate has not been released or submitted to
Reservoir. The existing proof-source archive is already public, but public
source availability does not establish Reservoir indexing or acceptance.
[Distribution metadata](distribution.json) records the engineering check status
and the separate publication and review gates.

## Existing proof evidence and the companion

A fresh isolated build on 4 November 2026 compiled all 595 safe baseline modules
under a 12 GiB memory limit with swap disabled. It used new project outputs,
pinned dependency checkouts and official upstream cache artifacts. That build
ran modules one at a time in dependency order, followed by the default build and
the four additional safe targets. The ordinary commands above do not impose an
operating-system memory limit. The published
[historical build record](https://bernalde.github.io/thesis_ai_remake/downloads/proof-source-build.json)
identifies its inputs and resource settings.

The Chapter 9 manuscript-route companion has a separate recorded build,
theorem-type check, dependency traversal, axiom report and independent
source-first review. It was not included in the historical 595-module build.
Its proof, checker, documentation and build record are preserved byte for byte.
See its [source mapping and scope](companions/ch09-source-procedure/README.md).
The new root layout also provides an optional target:

```sh
lake build SourceProcedure
lake env lean companions/ch09-source-procedure/CheckSourceProcedure.lean
```

The companion target is not a default target. The original nested Lake project
and the companion's original build instructions remain available unchanged.
This preparation checks the new configuration and file identities. It does not
claim a fresh full-library build, another companion proof check or a new axiom
census. Existing mathematical qualifications retain their recorded scope.

## Source identity and packaging checks

With Python 3.11 or later, run these checks in a clean source snapshot before
fetching dependencies or building:

```sh
python3 -B scripts/verify_snapshot.py
python3 -B scripts/verify_root_layout.py
python3 -B -m unittest discover -s tests -v
```

The original snapshot verifier remains unchanged. It strictly checks the full
file allowlist, all 599 original compiler inputs, local imports and challenge
isolation. The additional root-layout checker verifies the exact configuration
derivation, copied pins, unchanged companion and original files, and the clean
file and directory allowlist. It rejects extra sources, caches and symlinks.
An ordinary Git checkout is also supported: only its real root `.git` directory
is excluded from the payload walk, and the original verifier still checks the
index and staged file bytes. Nested `.git` paths and a root `.git` symlink or
worktree pointer file are rejected. Test fixtures copy the explicit payload
allowlist, so they do not inherit a checkout's index or history.
The test suite includes disposable Git-index checks; those tests do not modify
the source repository. These packaging checks do not compile the proof library.
Use a separate working copy for builds. The strict source snapshot checks reject
local `.lake` directories and other build products rather than ignoring them.

The [snapshot manifest](snapshot-manifest.json) binds every payload file except
itself. A final release record or commit must bind the manifest separately.
[Baseline archive provenance](baseline-archive.json) records the hashes of all
620 original regular archive members, including the original documentation and
manifest. [Compiler input identities](lean-inputs.json) retain the exact 599
baseline compiler inputs. Only the root README, rights explanation and snapshot
manifest differ among the original archive members.

The private audit repository and its history are excluded. This package contains
no research receipts, conversations, correspondence, credentials, publisher
papers, thesis source archives or build caches. The new payload requires an
independent engineering review, a final freeze and separate publication
approval. Its metadata records `public_release_authorized` as false.

## Thesis context and licences

These Lean formalizations accompany David E. Bernal Neira's thesis, *Modern
Computational Approaches to Nonlinear Discrete Optimization and Applications in
Process Systems Engineering*. Read the thesis, highlighted corrections and
result map in the [published reader](https://bernalde.github.io/thesis_ai_remake/).
[Proof scope](docs/proof-scope.md) explains the retained mathematical evidence.

Project-owned proof code, tools and accompanying software documentation use
[Apache-2.0](LICENSE). [RIGHTS.md](RIGHTS.md), [NOTICE.md](NOTICE.md) and
[THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md) describe the scope and retained
upstream terms. See [SECURITY.md](SECURITY.md) for reporting a security concern.
