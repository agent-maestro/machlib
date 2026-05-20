# MachLib Legacy EML Quarantine Manifest — 2026-05-20

## Purpose

The transitional legacy EML packet under `foundations/legacy_eml/` was quarantined because it contained Mathlib-dependent Lean source. MachLib's public default tree is being aligned to a zero-Mathlib dependency identity.

This manifest preserves the local audit trail without keeping Mathlib-dependent Lean files in the public default tree. It makes no public theorem/proof/open-problem claims.

## Summary

- Removed/quarantined Lean file count: 17
- Source path: `foundations/legacy_eml/`
- Local backup path: `/tmp/machlib_legacy_eml_mathlib_quarantine_2026_05_20/legacy_eml`
- Backup manifest: `/tmp/machlib_legacy_eml_mathlib_quarantine_2026_05_20/legacy_eml_manifest_2026_05_20.txt`
- Backup is local/out-of-repo and not pushed.

## Quarantine Statement

The files listed below contained transitional Mathlib-dependent Lean code or supporting legacy context. They are not part of the MachLib zero-Mathlib public default tree after this quarantine. The in-repo replacement is a non-code README that points back to this manifest.

## File List And Hashes

| Path | SHA256 |
|---|---|
| `foundations/legacy_eml/AddLowerBound.lean` | `4ea0326c379a000b2c7ea619e5c8a8bd3e73339f473187d0bb5db27836886ead` |
| `foundations/legacy_eml/ChainOrderAdditivity.lean` | `812f6a2885c6ae155e9b946f64368b7f3c2837aa9937492961af23017efa8b65` |
| `foundations/legacy_eml/DivLowerBound.lean` | `c2e18d5e160ec2a2e968f539e45b968b2f4394dbdc0cf5031b56d161525558e5` |
| `foundations/legacy_eml/DivLowerBound3.lean` | `e4fac67db1594c83b80857699fcdb0506f285c52b21392cd7a4f3eb607e14980` |
| `foundations/legacy_eml/EMLDepth.lean` | `ec6870ce2084b100f311d8d55d6fb0d10962417e078a7d8b20dbe629ce6f615b` |
| `foundations/legacy_eml/EMLDuality.lean` | `1879398723774d5d0aab025fcc911f2c13d6fa15df1123853356c123ef2fcf88` |
| `foundations/legacy_eml/Float64.lean` | `571d167cc0323ce0689cc0a959b73f43ff8b4d7593193c2c10b85ab6b24be2a1` |
| `foundations/legacy_eml/Gamma.lean` | `c468e3d123720e3eb68bd84ad48f3e98654dc4bec6baa3d0c907b976444b6d7f` |
| `foundations/legacy_eml/HyperbolicPreservation.lean` | `b7ba8c62a4db9dc9e5d036da3a2ce96193d0d6a61fb552d85ff4600c9f442bf7` |
| `foundations/legacy_eml/InfiniteZerosBarrier.lean` | `dd6f7dde6158f0dddbd837293518550940526bea8e7ed66e0042a90c4db04bb0` |
| `foundations/legacy_eml/ModelAudit.lean` | `01a8a5085fc92ec8d0122c443c76ca624de636e468708a69880ca4cc32493e6d` |
| `foundations/legacy_eml/MulLowerBound.lean` | `92ff09fdaebde7fc547124aff1efba279fa2e48894aadfc9018592a38dd8b73e` |
| `foundations/legacy_eml/PORT_PLAN.md` | `e185a798d2c697fe40bbaa2d91f97d84bc6dba5548297f43adac6abfcb1ca40e` |
| `foundations/legacy_eml/README.md` | `a26b9cc5f9e40df648cf066626c27afb8dce699108838f07ac763c4b1ffcea3b` |
| `foundations/legacy_eml/Runtime.lean` | `92591412c9a36393418e598aa8542a81acaf7e39fdea0a8a827f17e50e1ee5e0` |
| `foundations/legacy_eml/SubLowerBound.lean` | `40a3df097914d4f3c28ac3d96f3be477ff1ed722816dbf185f84faf2fbd4ebd7` |
| `foundations/legacy_eml/Tactics.lean` | `ee7f76023c21fee47d6d5d6c88e17528ff772fa6cef0c02ac7c85910d85fff77` |
| `foundations/legacy_eml/Universality.lean` | `21236d9b533d73a0ae23a42afe3e129461f3284f67f5c889bad0c2064da3a07c` |
| `foundations/legacy_eml/UpperBounds.lean` | `7e3c830f91ee5e6e3fd5f0c7787185442f0da0f3e0905823c5e7f16e7634fe3a` |
| `foundations/legacy_eml/_LegacyAggregator.lean.txt` | `5b29fa5f2580003ae07b021cc468660d309a89ffb5c05397cd8aa2a492440bd2` |
