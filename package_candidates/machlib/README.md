# MachLib

MachLib is a pre-alpha umbrella package for a small public toolchain around
zero-Mathlib evidence boundaries, EML record validation, claim-boundary
scanning, and private review packet workflows.

This PyPI package is intentionally minimal. It is not a dump of the full
MachLib repository, corpus, local review reports, Command Center feed drafts,
or private review branch artifacts. It provides a lightweight command-line
surface that describes the public package boundary and points users to the
related packages:

- `zero-mathlib-checker`
- `claim-boundary`
- `eml-records`
- `review-branch-packet`

Mathlib is valuable. MachLib is for projects that intentionally choose a
zero-Mathlib evidence boundary.

## Boundaries

MachLib is not a theorem prover, not a replacement for Mathlib, not a public
proof system, and not an open-problem solver. It is not safety certification,
not production controller evidence, not a Command Center deploy tool, and not
a Hugging Face, PETAL, or CapCard certification tool.

The package does not upload, publish, push, deploy, call remote APIs, mutate
project files, or run broad repository scans by default.

## Install

```bash
python -m pip install machlib
```

## CLI

```bash
machlib info --json
machlib boundaries
machlib toolchain
```

`machlib info` prints package metadata and the pre-alpha purpose. `machlib
boundaries` prints the public no-go boundaries. `machlib toolchain` lists the
related packages that make up the public toolchain.

## Limitations

This package is a pre-alpha umbrella and compatibility surface. It does not
include the full MachLib corpus, the larger research repository, generated
reports, local publish-readiness files, or Command Center assets. Public API
shape and dependency policy may change before a stable release.
