# CLAUDE.md — MachLib

**What this is.** A Mathlib-free Lean 4 corpus that proves things about EML kernels — the little
functional language Forge compiles to hardware — so that claims about compiled silicon rest on
machine-checked theorems rather than on prose.

## Architecture

Everything of substance is under **`foundations/`** (the repo root is docs, evidence, and site
material). `foundations/MachLib/` holds **612 modules / ~158 k lines / 5 569 theorems**, all
re-exported through the aggregator **`foundations/MachLib.lean`** — a module not imported there is
**invisible to the gates**, which is the single most common way to ship dead work. The numeric
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
lake build                                     # 605 jobs, ~3 s warm
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
- **A new module must be added to `MachLib.lean`** or it builds but is ungated.
- **`open Real` shadows `max`** — write `Nat.max`, and feed `omega` the `Nat.le_max_*` lemmas.
- **`set`, `linarith`, `ring` do not exist here.** Use `mach_ring` / `mach_mpoly`.
- **Keep coefficients symbolic.** `mach_mpoly` times out on `16·P²` and proves `(c·c)·(a·a)` instantly.
- **Deep `rfl` needs `set_option maxRecDepth`** (29 M-node terms check fine at 40 000 000).
- **Axiom-absence claims must be read off `#print axioms`, never a name-grep** — `exp_gt_one_plus_self`
  and `exp_tangent_line_strict` are the same content under two names.

## Status

Lean `v4.32.2`, `master`. All five gates green. `sorryAx`: 1, allowlisted.
Recent arc: **EML characterised** as exactly the `exp`/`log` closure of `ℝ` —
`monogate-research/exploration/inv_x_termination_route_2026_08_06/EML_STATUS.md`.
