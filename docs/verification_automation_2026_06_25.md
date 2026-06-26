# Automated proof closure from a math DSL — ring-v3, the decompose-first doctrine, and a 63% zero-Mathlib close-rate

*2026-06-25*

This is a status note on how far obligation-level proof **automation** has come in
MachLib — the zero-Mathlib Lean 4 foundations that back Monogate Forge's
`@verify(lean)` annotations. Three threads landed together: a multivariate
polynomial normal form (ring-v3), a small reusable "decomposition" toolkit, and —
most importantly — an honest, reproducible number for *how much closes by itself*.

The throughline: **prefer a checkable number with the method published over a vague
"Lean-verified" badge.** Everything below is reproducible against the open repo.

## 1. ring-v3 — a multivariate normal form that actually scales

Forge emits polynomial identities all the time (vector/quaternion/matrix algebra,
norm-preservation, cross-product identities). MachLib's `mach_ring` does AC +
distribution but cannot *collect* like monomials after expansion, so it stalls on
anything past the simplest identities. A first multivariate tactic closed these by
re-running the univariate engine atom-by-atom — correct, but exponential in the
variable count: the 6-variable Lagrange identity took ~70 s, and the **8-variable
Euler four-square identity** (quaternion-norm multiplicativity) did **not finish in
50 minutes**, twice (memory flat the whole time — a pure CPU grind, not divergence).

ring-v3 (`MachLib.MPolyRing`, `mach_mpoly`) replaces the recursion with a genuine
normal form: reify the whole expression *once* into a nested Horner polynomial
(`MPoly 0 = Real`, `MPoly (n+1) = List (MPoly n)`), normalise *once* (the recursive
`addM`/`mulM` collect like monomials structurally in a single pass), and compare
*once* via a recursive equality-up-to-trailing-zeros. Cost is polynomial in the
monomial count, not exponential in the variable count.

Result: the four-square identity that didn't finish in 50 minutes now closes in
**seconds** — and `#print axioms` shows only the `Real` ring axioms, no `sorryAx`.
A design note worth recording: the operations are deliberately *non-mutual*
(structural on the depth `n`, with list work in standalone helpers). Mutual `def`s
do not reduce under `simp`, which silently dead-ends the normalise-by-`simp` step;
keeping them non-mutual is what makes the whole thing go.

## 2. The decompose-first doctrine

Closing a large obligation set surfaced a lesson that is mostly the *opposite* of
the intuition: **most obligations labelled "blocked on nlinarith" are not blocked on
nlinarith.** They close with an existing lemma once you pick the right algebraic
decomposition. A planned Fourier-Motzkin engine was never needed for the set we
closed.

The recurring patterns are now named, reusable lemmas in `MachLib.Decompose`:

- `abs_le_sqrt` — `v² ≤ y ⇒ |v| ≤ √y` (every "normalise by `x/√(x²+ε)`" shape).
- `mul_mem_symm_band` — `|w| ≤ 1, 0 ≤ L ⇒ L·w ∈ [−L, L]`.
- `lerp_le_of_le` — a convex interpolant stays under any common upper bound, via the
  SOS split `M − lerp = (M−b)(1−β) + (M−a)β`.
- `quad_denom_pos` — `0 < 1 + a² − 2ab` for `a ∈ (−1,1)`, `b ∈ [−1,1]`
  (the Mie / Henyey-Greenstein / rotation denominator). No Cauchy-Schwarz: split on
  the sign of `a` and write the quadratic as a strictly-positive square plus a
  nonneg term.

On top sits `mach_decompose`, a tactic that tries each lemma against the goal and is
**safe by construction**: every arm is `apply`/`exact` + `assumption`, which *fails
cleanly* when the goal doesn't match or the hypotheses aren't present. It never
leaves a goal and never emits `sorry`/`sorryAx` — which is precisely why
silent-`sorry` tactics like `mach_ring` are kept *out* of any emitter cascade.

## 3. The number: 54% auto-close, zero-Mathlib, reproducible

The honest measurement was the missing piece. Every substantive obligation Forge
emits carries a `first | mach_positivity | rfl | sorry` cascade — so the literal
text `sorry` appears in *every* one as a fallback. Grepping for `sorry` is therefore
**not** the close-rate. The real rate is which cascades actually fall through, which
you can only learn by compiling.

`foundations/scripts/closerate.sh` does exactly that: it compiles each emitted
obligation independently (recursively, including the `carriers/`, `photonics/` and
`maglev/` sub-corpora — they're self-contained, so co-importing collides on shared
constants) and counts the `declaration uses 'sorry'` warnings.

> **364 / 582 = 62.5%** of the emitted Lean 4 obligations close *automatically*
> against zero-Mathlib foundations — no human-written proof — in a few seconds.

The 364 closures are genuine: the cascade uses only `mach_positivity` and `rfl`,
neither of which can silent-`sorry`. The remaining ~37% emit and stay
regression-gated against a baseline; they are not claimed as proven. This is a raw,
uncurated figure over all 251 emitted obligation files — re-run the harness on a
fresh clone and you get the same number.

## 4. Honest scope — what does *not* close

Of the obligations that still need a human (or a future tactic): a large share are
genuine analysis — **monotonicity** (`rate increasing in temperature`),
preservation, convergence — which no amount of decomposition touches. The bounded
ones that remain mostly need a *smarter positivity tactic* (one that exploits the
input-domain hypotheses compositionally), not more decomposition lemmas. That — plus
the close-rate harness as the measuring stick — is the next lever. Decomposition was
the cheap 80%; the tail is real analysis.

## Reproduce it

```bash
git clone https://github.com/agent-maestro/machlib
cd machlib/foundations
lake build MachLib.MPolyRing          # ring-v3 + the four-square regression theorem
lake build MachLib.Decompose          # the doctrine lemmas + mach_decompose
bash scripts/closerate.sh             # the 54% number, from scratch
```

No Mathlib, direct or transitive — that gate is enforced per release.
