# MachLib — for machines, by machines

[![cold build](https://img.shields.io/endpoint?url=https://raw.githubusercontent.com/agent-maestro/machlib/master/.github/build-time.json)](.github/workflows/build-time.yml)

A machine-native Lean/EML library with zero Mathlib dependency in the current
public default tree and release target. MachLib is Monogate's compact Lean
check target: a small verification layer for EML/Forge artifacts, not a Mathlib
replacement. Records may include verification metadata and
Lean-check status; verification status is recorded per release snapshot.

**Start here:** [`foundations/docs/what_is_proven.md`](foundations/docs/what_is_proven.md)
— what is proven, what it rests on, and what is open, with the exact commands to
check each claim yourself.

**The forward-error certifier:** [`foundations/docs/forward_error_certifier.md`](foundations/docs/forward_error_certifier.md)
— one fold (`gexpr_sound`) bounds the floating-point forward error of any kernel over
the operator basis `{+, ×, neg, exp, sin, cos, ÷}`, reaches across precisions
(cross-target) and over iterations (trajectory), and is bound to the real kernels Forge
compiles via `tree_hash` (418/483 of eml-stdlib measured in-basis).

## Install

Package installation status is release-specific. Until a reviewed package
release is published, use the repository and release manifests as the source of
truth.

## Try it

Dataset access is pending/private-gated until a reviewed public release is
approved. Counts and verification status are published per release snapshot.
Every release claiming zero Mathlib dependency must pass
`tools/check_zero_mathlib_dependency.py`.

## What's here

| | |
|---|---|
| `foundations/` | Lean 4 foundations; zero Mathlib dependency in the current release target |
| `corpus/` | Machine-readable records with metadata, proof traces, and per-record status |
| `gym/` | Gymnasium-compatible training environment, 54-tactic vocabulary |
| `tools/` | Generator, verifier, ranker, exporter, CLI |
| `api/` | Optional local interface surfaces, subject to separate review |
| `docs/` | Audience-organised guides + reference |

## Featured artifacts

`foundations/` has two pillars, both `sorryAx`-free and Mathlib-free. The
reader's guide to exactly what is and isn't proven — every claim paired with the
command to check it — is
[`foundations/docs/what_is_proven.md`](foundations/docs/what_is_proven.md).

**1. Verified numerics, bits to trajectory** — a floating-point/fixed-point
verification layer for Forge-emitted kernels, with an end-to-end capstone (a PID
control loop carried from its bit-level netlist to a finite closed-loop trajectory
bound) and a machine-checked **consistency proof** for its core.

**2. A constructive Khovanskii zero bound** for polynomial-in-(x, eˣ) and for
general triangular Pfaffian chains, with Forge-emitted safety-critical kernel
proofs on top. Honest about the foundation: these are proven modulo MachLib's
axiomatized analytic base (Rolle zero-counting corollary, `HasDerivAt` rules,
`exp_pos`, Real arithmetic and order); in mathlib every one of those is a theorem,
and grounding the base there is open work. The featured Khovanskii results and all
the safety-critical applications are **constructive** — they depend on **no**
"classical Khovanskii" axiom (verify with `#print axioms`); the one such axiom that
remains is confined to a legacy general-`PfaffianFunction` development that nothing
featured uses.

- `foundations/MachLib/PIDCapstone.lean` — `pid_trajectory_from_bits`: a PID
  control kernel proved from a bit-level netlist (the per-step round-off ε derived
  from the bits) all the way to a finite trajectory bound. The discrete-datapath
  claim and the analytic closed-loop claim are the *same* checked fact.
- `foundations/MachLib/CoreModel.lean` — the flagship results' axiom closure is
  proven consistent by an external ℤ-model (`intModel` depends on no MachLib
  axiom), CI-gated. The answer to "are these results vacuous?".
- `foundations/MachLib/FPModel.lean` — cross-target equivalence: two evaluations
  of the same exact value (e.g. Rust f64 vs WGSL f32) agree within their
  forward-error bounds (`cross_target`).
- `foundations/MachLib/SingleExpKhovanskii.lean` — three resolution paths
  (`expPoly_khovanskii_bound`, `expPoly_auto_bound_with_propagation_aux`,
  `expPoly_ode_no_zeros`).
- `foundations/MachLib/KhovanskiiReduction.lean` — `khovanskii_bound_full`
  for general triangular Pfaffian chains, parametric in a reduction witness.
- `foundations/MachLib/Applications/ButlerVolmerKhovanskii.lean` —
  current = 0 ↔ overpotential = 0 for the Butler-Volmer electrode-kinetics
  kernel (downstream: BMS, fuel cells, corrosion). Replaces a `sorry` in
  `MachLib/Discovered/butler_volmer.lean`.
- `foundations/MachLib/Applications/PlasmaConcentrationNonneg.lean` —
  non-negativity of the two-compartment pharmacokinetic plasma kernel
  (downstream: TCI anaesthesia, ICU monitoring; IEC 62304 Class C).
- `foundations/MachLib/Applications/DischargeVoltageSafety.lean` —
  sign preservation for the biphasic-truncated-exponential defibrillator
  discharge kernel (downstream: AED, ICD; IEC 62304 Class C).
- `foundations/MachLib/Applications/SpringCriticallyDamped.lean` —
  Khovanskii-localised positivity of the critically-damped harmonic spring
  (downstream: game animation, character controllers, UI motion).
- `foundations/AxiomAudit.lean` — reproducible `#print axioms` over the
  headline theorems. Run via `lake env lean AxiomAudit.lean`.
- `foundations/KhovanskiiExamples.lean` — three worked applications.

See [CHANGELOG.md](CHANGELOG.md) for the per-release entry.

## Why MachLib (not Mathlib)

Mathlib is the cathedral, by humans, for humans.
MachLib is the training gym, for machines, by machines.
You don't train for a marathon inside a cathedral.

See [PHILOSOPHY.md](PHILOSOPHY.md) for the full case.

## Status

Seed/transitional phase. Counts are published per release snapshot. The
zero-Mathlib release gate now passes for both the current public default tree
and release target. Historical legacy EML source was quarantined into a local
out-of-repo backup and represented in-tree by a non-code note.

## License

[CC BY 4.0](LICENSE) — open, citable, usable by anyone.
