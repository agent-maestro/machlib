# Proof Decomposition Before Automation

*2026-06-26. A methodology note, distilled from MachLib's closure record.*

MachLib is a zero-Mathlib Lean 4 foundation: its automation is deliberately
weak (no `linarith`/`nlinarith`/`polyrith`, a small `mach_ring`, a handful of
positivity closers). That constraint forced a discovery that turns out to be
the most reusable thing in the project:

> **Most obligations labelled "blocked on `nlinarith`" are not blocked on
> `nlinarith`. They close with an existing lemma once you pick the right
> algebraic decomposition.** The lever is almost never a heavier tactic; it is
> a better decomposition, normal form, or *object*.

A planned Fourier–Motzkin / stronger-nonlinear engine was repeatedly scoped and
repeatedly not needed. The same pattern recurred across unrelated lanes —
engine kernels, the cross-target FP layer, and the Khovanskii frontier — which
is why it is worth writing down as a checklist rather than a war story.

## The recurring shapes

Each row is a real closure. The point is that the *fix* is structural, and the
"automation" that finally discharges it is trivial once the structure is right.

| Obligation shape | Wrong instinct | What actually closed it |
| --- | --- | --- |
| Multivariate polynomial identity (8-var quaternion four-square) | "stronger ring/nlinarith" | **Normalize first** — reify once into a nested-Horner normal form, normalize once, compare once (`mach_mpoly`, `mach_mpoly_sound`). Recursion atom-by-atom did *not* finish in 50 min; the normal form closes in seconds. |
| `0 ≤ x² + y² + z²`, attenuation, energies | "positivity engine" | **Expose nonnegativity** — it's a sum of nonneg terms; the relative-error bound then needs no cancellation reasoning (`length_sq*_fwd_error`). |
| `0 < 1 + a² − 2ab`, `a∈(−1,1)`, `b∈[−1,1]` (Mie/HG denominator) | "Cauchy–Schwarz / nlinarith" | **Isolate the sign** — split on the sign of `a`, write the quadratic as a strictly-positive square plus a nonneg term (`quad_denom_pos`). |
| convex interpolant under a common bound | "nlinarith" | **Expose convexity** — the SOS split `M − lerp = (M−b)(1−β) + (M−a)β` (`lerp_le_of_le`). |
| `|v| ≤ √y` from `v² ≤ y` (normalize-by-`x/√(x²+ε)`) | "analysis" | **Lift to the squared object** (`abs_le_sqrt`); the bound is algebraic there. |
| ray/AABB/plane "well-defined" disjunctions; floor parity | "nlinarith over the reals" | **Separate discrete from continuous** — `by_cases` on the branch condition; each arm is trivial. |
| `N`-term rounded sum forward-error | "prove each arity (dot2, dot3, dot4, …) separately" | **Extract the step, then iterate it** — one `cond_combine` building block composes over an arbitrary summation tree; the general theorem (`RSum_bound`) is induction over a list, one `cond_combine` per element. |
| EML→Lean obligation that drifts from the shipped expression | "trust the annotation / a verifier" | **Introduce auxiliary state, not a stronger checker** — pin the obligation to the expression's `tree_hash` and add the missing `ensures` contract; the proof becomes definitional. |

## The checklist

When a goal "needs nlinarith," try these *first*, in roughly this order:

1. **Normalize first.** Put the expression in a canonical form (a real normal
   form, not just AC + distribution) and compare. Most polynomial identities
   die here.
2. **Expose the sign / nonnegativity.** Is it a sum of squares? A product of
   known-sign factors? Make that visible.
3. **Expose convexity.** Convex combinations under a common bound have a
   standard SOS split; write it.
4. **Isolate signs by case.** `by_cases`/`lt_total` on the one quantity whose
   sign is unknown; each arm is usually algebraic.
5. **Separate discrete from continuous.** Branch conditions, floor/parity, and
   "well-defined" disjunctions are case splits, not real-arithmetic goals.
6. **Lift to the correct object.** Square roots → the squared quantity;
   coefficients → the right measure; a sum → its building-block step. The hard
   part is often choosing *what you induct/measure on*.
7. **Introduce auxiliary state, not a stronger tactic.** A true hypothesis the
   prover needs (`0 ≤ 1`, a domain bound, an `ensures` contract) beats reaching
   for a heavier engine — and it makes the obligation *honest* about its
   preconditions.

## The negative space (where this is NOT the answer)

The doctrine has a sharp boundary, and naming it is part of the discipline:

- **Wrong-object, not under-decomposition.** Chain-2 Khovanskii does not close
  by decomposing harder — it is blocked because the *measure is wrong*: a
  coefficient-local (`mP2PFL` y→0) lex measure erases the `y₀`-degree
  information the drop needs (counterexample `p = y₀·y₁`). The fix is a
  chain-aware measure (`ChainExp2SDR`), i.e. principle (6) — *lift to the
  correct object* — not more case-splitting. Decomposition into the wrong
  pieces is just noise.
- **Genuine analysis.** Monotonicity (`rate increasing in temperature`),
  convergence, preservation — these are real theorems no decomposition shortcuts.
  In the cross-target close-rate, the residual tail after decomposition is
  exactly this: real analysis, not missing tactics.
- **Cancellation.** A relative bound is *false* for a mixed-sign sum near
  cancellation; no decomposition rescues it. The honest move is to change the
  *statement* (an absolute bound against the conditioning quantity `Σ|tᵢ|`), not
  the proof — see `dot2_fwd_error`'s conditioned form.

The leading-order rule of thumb that held across the corpus: **decomposition was
the cheap ~80%; the tail is real analysis or a genuinely new object.** Reaching
for a heavier nonlinear engine optimized the wrong 20%.

## Pointers

- Normal form: `MachLib.MPolyRing` (`mach_mpoly`, `mach_mpoly_sound`).
- Decomposition lemmas: `MachLib.Decompose` (`abs_le_sqrt`, `mul_mem_symm_band`,
  `lerp_le_of_le`, `quad_denom_pos`) + the engine closure record
  (`monogate-engine` `proofs/Proofs/README.md`, 91/91).
- Building-block composition: `MachLib.FPModel` (`cond_combine`, `RSum_bound`);
  write-up `docs/cross_target_equivalence_2026_06_26.md`.
- The wrong-object negative example: `MachLib.ChainExp2SDR`.
