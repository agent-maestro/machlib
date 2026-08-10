# CLAUDE.md — MachLib

**What this is.** A Mathlib-free Lean 4 corpus that proves things about EML kernels — the little
functional language Forge compiles to hardware — so that claims about compiled silicon rest on
machine-checked theorems rather than on prose.

## Architecture

Everything of substance is under **`foundations/`** (the repo root is docs, evidence, and site
material). `foundations/MachLib/` holds **922 `.lean` files** (614 top-level + 308 in subdirectories) /
**~187 k lines** / **5 851 theorems**, re-exported through the aggregator
**`foundations/MachLib.lean`** (512 imports) — a module not reachable from there is **invisible to
`lake build` and to every gate**, which is the single most common way to ship dead work.
**`MachLib/Discovered/` (294 files) is deliberately outside the aggregator**: each file is
self-contained and they cannot be imported together; it is the Forge `@verify(lean)` corpus and has
its own harness, `scripts/closerate.sh`. The numeric
substrate is **`MachLib.Real`**, an *axiomatised* real field (274 `axiom` declarations, every one
disclosed in **`foundations/axiom_ledger.json`**): there is no Mathlib, no `Complex`, and
`Real.log` is **totalised** — `log y = 0` for `y ≤ 0`, which is load-bearing in EML proofs and a
frequent source of surprise. Custom tactics **`mach_ring`** and **`mach_mpoly`** replace `ring`/
`linarith`.

## Where the content comes from

Self-contained. EML semantics live in `MachLib/SinNotInEML.lean` (the `EMLTree` type and `eval`);
the forward-error certifier is documented in `foundations/docs/forward_error_certifier.md`; the
authoritative claim inventory is **`foundations/docs/what_is_proven.md`**.

## How to run the gates

**All five run from `foundations/`, not the repo root** (this is what CI does):

```bash
cd foundations
lake build                                     # 619 jobs, ~3 s warm
bash scripts/check_aggregator.sh               # every module reachable
bash scripts/check_consistency_model.sh        # flagship closure has an external ℤ-model
lake env lean AxiomLedger.lean                 # "242 axioms pinned; 57 headline footprints ⊆ trusted"
python3 tools/claim_audit/claim_audit.py       # "all 41 claims resolve against #print axioms"
```

`lake env lean tools/sorry_audit.lean` is useful (`1 sorryAx`, allowlisted) but is **not** a CI gate.
The gate set is exactly the five above (`.github/workflows/build-time.yml`).

## Gotchas

- **`lake` from `foundations/`.** From the repo root it silently resolves the wrong toolchain (v4.14).
- **Stale `.olean`s.** `lake env lean Foo.lean` typechecks against *old* dependencies; run
  `lake build MachLib.Foo` first or `#print axioms` will report unknown constants.
- **A new module must be REACHABLE from `MachLib.lean`** or it is never built and never gated.
  Being imported by a sibling is **not** enough — an island of mutually-importing modules is
  unreachable. `check_aggregator.sh` does a real transitive closure (**616 of 922 reachable**).
- **`open Real` shadows `max`** — write `Nat.max`, and feed `omega` the `Nat.le_max_*` lemmas.
- **`set`, `linarith`, `ring` do not exist here.** Use `mach_ring` / `mach_mpoly`.
- **Keep coefficients symbolic.** `mach_mpoly` times out on `16·P²` and proves `(c·c)·(a·a)` instantly.
- **Deep `rfl` needs `set_option maxRecDepth`** (29 M-node terms check fine at 40 000 000).
- **Axiom-absence claims must be read off `#print axioms`, never a name-grep** — `exp_gt_one_plus_self`
  and `exp_tangent_line_strict` are the same content under two names.
- **`open MachLib.Real` + `open …AerospaceActuatorGuardBandRate (le_min …)` collide.** Both export a
  `le_min`; a bare `apply le_min` is then ambiguous. Qualify it. (This broke 5 `Applications/`
  modules for an unknown length of time — they were in an unreachable island, so no gate saw it.)
- **These order lemmas do NOT exist here**: `lt_or_ge`, `lt_trans`, `lt_irrefl`,
  `mul_lt_mul_of_pos_left`, `le_or_lt`, `add_lt_add_right`. The local idioms are
  `rcases lt_total`, `lt_of_lt_of_le … (le_of_lt …)`, `(ne_of_lt h) rfl`, `mul_lt_mul_pos_left`,
  `add_le_add_wit`, `add_lt_add_left`.
- **A new module needs `open Real`** inside `namespace MachLib`, or `exp`/`log` are unknown.
- **Casing on a tree then applying a lemma with an implicit tree argument leaves a metavariable** —
  pass `(A := EMLTree.const c)` explicitly, or the shape-specific proof term fails to typecheck.
- **Forward references bite**: a theorem is only usable *below* its declaration in the same file.
- **`min` and `abs` do not exist.** Use `two_bound_witness` (`a·b·exp(−a−b)` is positive and strictly
  below both `a` and `b`) rather than hand-rolling a fourth bespoke two-constraint expression.

## Status

Lean `v4.32.2`, `master`. All five gates green (619 build jobs). `sorryAx`: 1, allowlisted.
**242 axioms pinned — unchanged across the whole 2026-08 EML arc.**

Recent arc: **EML characterised** as exactly the `exp`/`log` closure of `ℝ`; then
**`s(1/x) ∈ {7,9,11}` proved** (two `eml` gates can never compute a reciprocal), `d(1/x)` frozen at
`{3,4}`, and a depth- and size-indexed **growth envelope** built. Start here:
`monogate-research/exploration/inv_x_termination_route_2026_08_06/EML_STATUS.md`, and
`FRONTIER_BRIEF_3.md` for the open questions.
