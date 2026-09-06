# MachLib

A Mathlib-free Lean 4 library that proves things about **EML kernels** — the small
`exp`/`log` expression language that [Forge](https://github.com/agent-maestro/forge) compiles
to C, GPU code and RTL — so that claims about compiled numerics rest on machine-checked theorems.
It is a compact verification layer with its own axiomatised reals, not a Mathlib replacement
and not a general analysis library.

**Start here:** [`foundations/docs/what_is_proven.md`](foundations/docs/what_is_proven.md) — what
is proven, what it rests on, and what is open, each claim paired with the command that checks it.

**Coming from mathematics rather than from compilers?**
[`foundations/docs/eml_depth_problems.md`](foundations/docs/eml_depth_problems.md) states the
object and the four open questions from scratch in twenty minutes, with no dependency on anything
else here.

## What is here

| | |
|---|---|
| [`foundations/MachLib/`](foundations/MachLib) | the corpus, aggregated by `foundations/MachLib.lean` |
| [`foundations/docs/`](foundations/docs) | the claim inventory, the certifier and safety front doors, method notes |
| [`foundations/tools/check_all.sh`](foundations/tools/check_all.sh) | every gate and audit in one runner; `rc = 0` iff all green |
| [`foundations/AXIOM_MANIFEST.md`](foundations/AXIOM_MANIFEST.md) | generated: every trusted axiom and the Mathlib witness that models it |
| [`reproduction/`](reproduction) | the range-bearing EKF evidence package an outside reproducer can walk, with a weekly CI walk |
| [`corpus/eml/`](corpus/eml) | one-page result cards for headline theorems |
| [`site/`](site) | machlib.org, a static export |
| [`tools/status/`](tools/status) | the status pipeline that publishes `status.json` to the `status-data` branch |
| [`EmlGermApproachResearch.md`](EmlGermApproachResearch.md) | the live research note on the one conjecture the depth ladder still rests on |

The May 2026 product and marketplace drafts that used to live at the root (readiness manifests,
capability-card drafts, a training gym, evidence reels, reports) were retired on 2026-09-05. They
are reachable in full at the tag `attic/product-wave-2026-05`; nothing in the live tree depends on
them. `toolchain-bump` is a permanent record branch of the v4.14.0 → v4.32.2 migration, cited by
the frozen tag `toolchain-bump/v4.32.2-record`; it is not a feature branch awaiting merge.

## Two lanes

**1. Verified numerics, from bits toward trajectories.** A floating-point and fixed-point
verification layer for the kernels Forge emits: forward and backward error, condition numbers,
interval and affine arithmetic, a bit-level fixed-point datapath, and closed-loop safety.

- `fxaffine_traj_tracks_exact` (`FixedPointRealBridge`) — the bit-level datapath of the affine
  plant kernel tracks the exact real trajectory within `ulp · geom c n`, with the per-step error
  *derived* from the bits.
- `sfxloop_tracks_exact` (`SignedFixedPoint`) — the same, **in closed loop with a proportional
  controller**, within `4 ulp · geom (A−KP) n`. The signed layer it needs represents a value as a
  difference of two unsigned vectors, which is what makes an error signal `R − X` and negative
  feedback expressible at all; the unsigned datapath can represent neither. Ships with specimens
  discharging its hypotheses.
- `two_state_tracks_exact`, `weighted_max_cannot_contract_integrator` (`TwoStateTracking`) — the
  vector-state tracking bound a PID loop needs, and the proof that the obvious measure cannot
  supply it: a weighted maximum of the components can never contract a loop containing an
  integrator, for any gains, because taking moduli discards the sign that makes the feedback
  negative. The measure that does work is built from linear functionals instead.
- `spiloop_tracks_exact` (`SignedPILoop`) — the same join **with an integrator**: the signed
  bit-level PI loop tracks the exact real PI trajectory within `4 ulp · geom L n` plus transient.
  General rather than a specimen, because a PI loop's integrator row forces its eigenvectors and
  the resulting eigen equations are ring identities; ships with a deadbeat-design specimen.
- `two_state_tracks_exact_quad`, `n2_young` (`QuadTracking`) — the same for **complex** closed-loop
  eigenvalues, where no real eigenvector exists. It avoids the usual quadratic Lyapunov norm, whose
  triangle inequality would need Cauchy–Schwarz and square roots this corpus does not have, by
  working with the squared measure: a rotation-scaling multiplies it by exactly `σ²+ω²` (a ring
  identity), and the cross term splits by a sum of squares.
- **Still not proved:** the derivative term (a PID loop has three states; both measures here are
  two-state), and a bit-level instantiation of the complex case. `pid_trajectory_from_bits` is
  unchanged and still quantifies its per-step error universally — do not cite it as an end-to-end
  result.
- `cross_target` (`FPModel`) — two evaluations of one exact value at different precisions agree
  within their forward-error bounds.
- `kalman_update_1d_fwd_error` (`KalmanUpdateFixedPoint`) — a proven Q16.16 forward-error bound
  for the scalar Kalman update that was run on an Arty A7 and is the datapath of chip 2.
- `first_order_clamp_envelope`, `nonlinear_drift_clamp_safe` (`ClosedLoopSafety`) — a saturating
  guard keeps the plant state inside a safe envelope for all time, under bounded disturbance.
- `intModel` (`CoreModel`) — the flagship closure's axioms have an external ℤ-model, so those
  results are not vacuous; a gate fails if the model ever becomes circular.

The forward-error certifier that Forge binds to real kernels by `tree_hash` is documented in
[`foundations/docs/forward_error_certifier.md`](foundations/docs/forward_error_certifier.md).

**2. The EML language itself.** What finite `exp`/`log` depth can and cannot express, and how
tame the expressible functions are. Everything below is `sorryAx`-free and uses no classical
Khovanskii axiom; verify with `#print axioms`.

- `chain2_khovanskii_bound_unconditional`, `chain2_khovanskii_bound_explicit` — a Khovanskii zero
  bound for depth-2 double-exponential chains `(x, eˣ, e^{eˣ})`, with the reducibility witness
  *constructed*, so the bound is free of the classical-Khovanskii axiom, and an explicit numeric
  form usable as a tool (`khovBound`).
- `inv_x_mem_EML`, `invX4_depth_optimal` — the reciprocal is an EML tree on `x > 0`, and depth 4
  is optimal, certified by a lower-bound theorem rather than a search.
- `x_plus_neg_c_depth_exact_four` — translation by a constant costs depth exactly 4.
- `logQueryLowerBound_holds`, `sign_query_cost_bounds_tight` — the query-complexity lane:
  `log` is not a rational germ on any interval, and `1 ≤ q_F(sign) ≤ 12`.
- `depth_le_three_gap_below_refuted`, `depth3ApproachBelow_holds` — the depth-3 constant-gap
  statement is false, and its decaying-floor replacement is proved: a depth-≤3 tree that dips below
  a constant does so by at least `exp (−C − exp (exp x))`.

The general-depth Khovanskii bound is still **cited**, not proved: `zero_count_bound_classical`
stands as a named mathematical assumption, confined to a legacy development that no featured
result uses. The depth ladder above depth 3 rests on one open conjecture; read
[`EmlGermApproachResearch.md`](EmlGermApproachResearch.md) before touching it.

## What it rests on

MachLib is Mathlib-free by construction, so nothing inside it can show its axioms are
satisfiable. That check lives in the sibling project
[`monogate-lean`](https://github.com/agent-maestro/monogate-lean), which imports both Mathlib and
MachLib and, for every trusted axiom, verifies that a Mathlib term inhabits the axiom's interpreted
type. The honest headline is **zero unmodeled axioms**, never "zero axioms":

| class | count | meaning |
|---|---|---|
| witnessed | 112 | a Mathlib term inhabits the interpreted type, kernel-checked |
| mapped | 12 | carrier or function symbol, interpreted rather than asserted |
| standard | 3 | `propext`, `Classical.choice`, `Quot.sound` |
| float-bridge | 22 | IEEE-754 facts with no model in ℝ, validated by measurement |

The 22 float-bridge axioms are a different kind of trust and are not averaged in; a hardware
certificate rests on exactly those, and a reader of one should read that block of the manifest
first. Gate 13 fails if the witness project stops running, because it did once, silently, for
33 days.

## How to check it

Everything runs from `foundations/`:

```bash
cd foundations
lake build                 # about a minute warm
tools/check_all.sh         # every gate and audit; prints every verdict; rc = 0 iff all green
```

The gates, in the order the runner prints them: build, aggregator reachability, the ℤ-model
consistency check, the axiom ledger, the obligations ledger, the Forge `@verify` corpus compiles,
Forge certificates, the soundness witness, MachSig signatures, the claim audit, the witness and
hypothesis and absence audits, and the sorry audit — most with their own self-tests, each of which
must be shown able to fail before its pass is read. `scripts/closerate.sh` is a measurement, not a
gate: the Forge `@verify(lean)` corpus auto-closes **79.9 %** of its obligations
(573 of 717, measured 2026-09-05 under Lean v4.32.2).

## Numbers, measured

Every count below is the output of a command, not a memory, and `tools/prose_counts_check.py`
fails if the text drifts from the corpus. Measured 2026-09-05:

| figure | value | source |
|---|---|---|
| theorems outside `Discovered/` | 7 610 | `find MachLib -name '*.lean' -not -path '*/Discovered/*' -exec grep -hcE '^ *theorem ' {} + \| paste -sd+ \| bc` |
| theorems in the Forge `@verify` corpus | 720 | the same command over `Discovered/` |
| `.lean` files under `MachLib/` | 1 095 | `find MachLib -name '*.lean' \| wc -l` |
| axioms pinned by the ledger | 243 | `lake env lean AxiomLedger.lean` |
| trusted axioms, all modeled | 149 | `AXIOM_MANIFEST.md` |
| obligations ledger | 23 rows, 7 open rows, 4 distinct open obligations | `tools/check_obligations.sh` |
| modules reachable from the aggregator | 791 of 1 095 | `scripts/check_aggregator.sh` |

## What this does not claim

- No claim about physical silicon beyond what the reproduction package and the bench evidence in
  `monogate-research` show; a theorem about a datapath is a theorem about the datapath.
- No compiler-correctness claim for Forge: the certifier binds a proof to a kernel by hash, it
  does not verify code generation.
- The analytic base is axiomatised, not constructed; every axiom is listed and modeled, none is
  proved here.
- The research lane is the work of one author, kernel-checked and not yet externally reviewed.
- Counts are snapshots; re-run the command before quoting one.

## Status

Active, single-author, roughly twenty commits a day since April 2026. The verified-numerics lane
has one external reproduction on record (`reproduction/rb_ekf`, two of five on the first attempt,
which is why the package exists). The obligations ledger has four distinct open obligations; the
prose about them is a copy and the ledger is the source. See [`CLAUDE.md`](CLAUDE.md) for the
working notes a new session needs and [`CHANGELOG.md`](CHANGELOG.md) for the running narrative.

## License

[CC BY 4.0](LICENSE).
