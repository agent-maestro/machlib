# tools/status

CI-emits `status.json` to the `status-data` branch of this repo on every
master push. The renderer at
[monogate-net/evidence-status/](https://github.com/agent-maestro/monogate-net/tree/master/evidence-status)
fetches it client-side and displays the data's own SHA + timestamp.

## Why the JSON is published to an orphan branch

The user's specification (2026-06-14) was: the data surface must be one
**only the Actions runner writes**. Committing `status.json` to `master`
would let a human with push access hand-edit and commit it — relocating
the hand-refresh problem rather than removing it. The orphan
`status-data` branch is force-pushed by the workflow at
[`.github/workflows/status.yml`](../../.github/workflows/status.yml) and
the `github-actions[bot]` is its only routine author.

A renderer that wants integrity instead of pure write-prevention can
recompute every figure at the SHA recorded in the payload — the
`reproduce.command_lines` field documents the exact pipeline.

## What the JSON carries

Key fields the renderer should rely on:

- `machlib_sha`, `generated_at_utc` — the data's own provenance.
  Renderers MUST display these, never their own page-load time.
- `content_hash_sha256` — SHA-256 of the JSON with this field set to
  null. Anyone with the same checkouts can recompute and compare
  byte-for-byte.
- `sorries.total`, `sorries.delta_vs_previous` — per-cycle change vs
  the prior status.json (read from the `status-data` branch). Method
  is `net_only` for v1; a per-theorem set-diff (closed vs added) is a
  follow-up.
- `sorries.history_recent` — short timestamped series (capped at 30
  entries) so the page can plot direction rather than a snapshot.
- `verify_audit` — the cross-referenced Forge `@verify` ledger.
  Splits `proven` into:
  - `proven_from_mathlib` (structurally 0 for MachLib by design — zero
    mathlib dependency; the field exists so the renderer never
    misreports a single "proven" total),
  - `proven_mod_machlib_axioms` (Forge-emitted Discovered/ stub
    already carries a concrete proof, conditional on the documented
    `MachLib.Real.*` axiomatized base).
- `axiomatized_base` — which axioms the headline theorems rest on.

## Counting method (canonical)

The sorry counter in `generate_status.py` matches
`monogate-research/tools/graph/builder_v2.py` byte-for-byte:

- Strip Lean block comments (`/- ... -/`, `/-! ... -/`).
- Strip Lean line comments (`--`) per line.
- Count `\bsorry\b` matches.
- File scope: `core` = the 8 hand-written
  `foundations/MachLib/<Name>.lean` files at top level; `discovered` =
  every other `.lean` under `foundations/MachLib/` excluding
  `Test.lean` and `.lake/`.

A raw `grep -o sorry` against the same tree returns ~48 more
occurrences because it counts `sorry` mentioned inside docstrings and
comments. The two methods are NOT comparable; mixing them produced an
incorrect dashboard refresh on 2026-06-14 (corrected 2026-06-15 via
this CI pipeline).

## forge_verify_audit.py

This file is duplicated from
`monogate-research/tools/forge_verify_audit/forge_verify_audit.py`
because monogate-research is a private repo and machlib's CI cannot
clone it with the default `GITHUB_TOKEN`. If you edit it here, sync
the change to monogate-research, or vice-versa.

## Reproduce locally

```bash
cd machlib
SHA=$(git rev-parse HEAD)
cd foundations && lake build && lake env lean AxiomAudit.lean > /tmp/axiom_audit.txt && cd ..
python tools/status/forge_verify_audit.py \
    --forge-root        ../forge \
    --eml-stdlib-root   ../eml-stdlib \
    --discovered-root   foundations/MachLib/Discovered \
    --applications-root foundations/MachLib/Applications \
    --out-json          /tmp/verify_audit.json \
    --out-md            /tmp/verify_audit.md
python tools/status/generate_status.py \
    --machlib-root        . \
    --machlib-sha         "$SHA" \
    --axiom-audit         /tmp/axiom_audit.txt \
    --verify-audit-json   /tmp/verify_audit.json \
    --build-exit-code     0 \
    --out                 /tmp/status.json
```

Compare `content_hash_sha256` from your `/tmp/status.json` against the
published one; a mismatch means either the toolchain drifted or the
published data was tampered with.

## What does NOT live here

- The build-time badge — `.github/workflows/build-time.yml` still
  commits `build-time.json` to master. That predates this design and
  ships a separate concern (cold-build wall-time, not verification
  status). If we want to subsume it, the right shape is moving the
  build-time figure into `status.json` and retiring `build-time.json`.
