import MachLib.UniformConvergence

/-!
# The Weierstrass sum is continuous — wiring the M-test to `Real.cos`

`UniformConvergence.lean` built the abstract Weierstrass M-test
(`continuousSum_of_uniform_dominated`) but stayed general — no `Real.cos`, no concrete
parameters. This file supplies the missing pieces for the actual `a=½,b=3` heat-mollified
Weierstrass series (the `k=0` case, i.e. the mollified sum itself, not a formal derivative):

  `W_t(x) = Σ (1/2)ⁿ · cos(3ⁿπx) · exp(−9ⁿπ²t/2)`

is a genuine `Real → Real` function for every `t > 0`, and it is **continuous everywhere**. This
is the first time this codebase's Weierstrass work has touched `Real.cos` directly, and the first
concrete (non-abstract) payoff of the M-test.

## The three pieces `continuousSum_of_uniform_dominated` needs

  - **The majorant is already proven.** `weierstrassAmplitude t n := (1/2)ⁿ·exp(−9ⁿπ²t/2)` is
    exactly `weierstrass_term_hasBoundedPartialSums t ht 0` (Summability.lean) up to the trivial
    `npow 0 pi = 1` / `npow (n*0) 3 = 1` factors that appear at `k=0` — no new summability work,
    just a `funext` + those two simplifications to transfer `HasBoundedPartialSums`.
  - **Domination** (`|term n x| ≤ A n`): `|C·cos(θ)| = |C|·|cos θ| ≤ |C|·1 = C` (`C` already
    nonneg) via `abs_mul` + `abs_cos_le_one`.
  - **The derivative** (`HasDerivAt`): none of the three pieces needed (scalar-times-`cos`-of-a-
    scaled-argument derivative) existed in MachLib as a named lemma — every other file that
    touches `HasDerivAt_cos` composes it ad hoc, inline, per call site. Built the general small
    reusable chain here instead: `HasDerivAt_scaled_id` (derivative of `K·y` is `K`) →
    `HasDerivAt_scaled_cos` (chain rule) → `HasDerivAt_const_mul_cos` (product rule with a
    constant amplitude). `-C·sin(Kx)·K` — the familiar `A·ω·sin` amplitude-times-frequency
    envelope from any physics derivation of a damped cosine's derivative, arrived at the same
    way here from three raw closure axioms.

## What this still does NOT do

Continuity, not `C^∞`. Term-by-term differentiation — connecting this `k=0` sum's actual
derivative to the `k=1` term sequence (`weierstrass_term_hasBoundedPartialSums t ht 1`, already
proven summable) — is a separate theorem: uniform convergence of the DERIVATIVE series doesn't by
itself hand you "the limit is differentiable and its derivative is that series' sum" for free;
that implication is its own piece of analysis, not attempted here.

`sorryAx`-free, Mathlib-free, no new axioms beyond what MachLib already has.
-/

namespace MachLib
namespace Real

/-! ## §1 — Three small derivative-closure lemmas MachLib didn't have named -/

/-- Derivative of `y ↦ K·y` is the constant `K`. -/
theorem HasDerivAt_scaled_id (K x : Real) : HasDerivAt (fun y => K * y) K x := by
  have h := HasDerivAt_mul (fun _ => K) (fun y => y) 0 1 x (HasDerivAt_const K x) (HasDerivAt_id x)
  rwa [show (0 : Real) * x + K * 1 = K from by mach_ring] at h

/-- Chain rule: derivative of `y ↦ cos(K·y)` is `-sin(K·x)·K`. -/
theorem HasDerivAt_scaled_cos (K x : Real) :
    HasDerivAt (fun y => Real.cos (K * y)) (-Real.sin (K * x) * K) x :=
  HasDerivAt_comp Real.cos (fun y => K * y) K (-Real.sin (K * x)) x
    (HasDerivAt_scaled_id K x) (HasDerivAt_cos (K * x))

/-- Product rule with a constant amplitude: derivative of `y ↦ C·cos(K·y)` is `C·(-sin(K·x)·K)`. -/
theorem HasDerivAt_const_mul_cos (C K x : Real) :
    HasDerivAt (fun y => C * Real.cos (K * y)) (C * (-Real.sin (K * x) * K)) x := by
  have h := HasDerivAt_mul (fun _ => C) (fun y => Real.cos (K * y)) 0 (-Real.sin (K * x) * K) x
    (HasDerivAt_const C x) (HasDerivAt_scaled_cos K x)
  rwa [show (0 : Real) * Real.cos (K * x) + C * (-Real.sin (K * x) * K) = C * (-Real.sin (K * x) * K)
        from by mach_ring] at h

/-! ## §2 — The concrete Weierstrass amplitude, frequency, and term (`a=½, b=3`, `k=0`) -/

private theorem wsc_h11pos : (0 : Real) < 1 + 1 := add_pos one_pos one_pos

/-- `(1/2)ⁿ · exp(−9ⁿπ²t/2)` — the `k=0` majorant, heat damping folded in. Matches
`weierstrass_term_hasBoundedPartialSums`'s function exactly at `k=0` (up to trivial `npow 0 _=1`
factors), so its summability is inherited, not reproven. -/
noncomputable def weierstrassAmplitude (t : Real) (n : Nat) : Real :=
  npow n (1 / (1 + 1)) * Real.exp (-(pi * pi * t / (1 + 1) * npow n (npow 2 (1 + 1 + 1))))

/-- `3ⁿπ` — the angular frequency of the `n`-th Weierstrass cosine. -/
noncomputable def weierstrassFreq (n : Nat) : Real := npow n (1 + 1 + 1) * pi

/-- The actual `n`-th term of the heat-mollified Weierstrass sum: `(1/2)ⁿ·cos(3ⁿπx)·exp(−9ⁿπ²t/2)`. -/
noncomputable def weierstrassTerm (t : Real) (n : Nat) (x : Real) : Real :=
  weierstrassAmplitude t n * Real.cos (weierstrassFreq n * x)

theorem weierstrassAmplitude_nonneg (t : Real) (n : Nat) : 0 ≤ weierstrassAmplitude t n := by
  unfold weierstrassAmplitude
  exact mul_nonneg (npow_nonneg (le_of_lt (div_pos_of_pos_pos one_pos wsc_h11pos)) n) (le_of_lt (exp_pos _))

/-- The majorant is exactly `weierstrass_term_hasBoundedPartialSums` at `k=0`, modulo the two
trivial factors (`npow 0 pi = 1`, `npow (n*0) 3 = 1`) that appear when a general-`k` statement is
instantiated at `k=0`. -/
theorem weierstrassAmplitude_hasBoundedPartialSums (t : Real) (ht : 0 < t) :
    HasBoundedPartialSums (weierstrassAmplitude t) := by
  have h := weierstrass_term_hasBoundedPartialSums t ht 0
  have heq : (fun n => npow 0 pi * npow n (1 / (1 + 1)) * npow (n * 0) (1 + 1 + 1)
        * Real.exp (-(pi * pi * t / (1 + 1) * npow n (npow 2 (1 + 1 + 1)))))
      = weierstrassAmplitude t := by
    funext n
    show npow 0 pi * npow n (1 / (1 + 1)) * npow (n * 0) (1 + 1 + 1)
        * Real.exp (-(pi * pi * t / (1 + 1) * npow n (npow 2 (1 + 1 + 1))))
      = weierstrassAmplitude t n
    unfold weierstrassAmplitude
    rw [show npow 0 pi = 1 from rfl, show n * 0 = 0 from Nat.mul_zero n,
        show npow 0 (1 + 1 + 1 : Real) = 1 from rfl]
    mach_ring
  rwa [heq] at h

theorem weierstrassTerm_dom (t : Real) (n : Nat) (x : Real) :
    abs (weierstrassTerm t n x) ≤ weierstrassAmplitude t n := by
  unfold weierstrassTerm
  rw [abs_mul, abs_of_nonneg (weierstrassAmplitude_nonneg t n)]
  calc weierstrassAmplitude t n * abs (Real.cos (weierstrassFreq n * x))
      ≤ weierstrassAmplitude t n * 1 :=
        mul_le_mul_of_nonneg_left (abs_cos_le_one _) (weierstrassAmplitude_nonneg t n)
    _ = weierstrassAmplitude t n := by mach_ring

theorem weierstrassTerm_hasDerivAt (t : Real) (n : Nat) (x : Real) :
    HasDerivAt (weierstrassTerm t n)
      (weierstrassAmplitude t n * (-Real.sin (weierstrassFreq n * x) * weierstrassFreq n)) x :=
  HasDerivAt_const_mul_cos (weierstrassAmplitude t n) (weierstrassFreq n) x

/-! ## §3 — The payoff -/

/-- **The heat-mollified Weierstrass sum is a genuine continuous function, for every `t>0`.**
`Σ (1/2)ⁿ·cos(3ⁿπx)·exp(−9ⁿπ²t/2)` converges uniformly in `x` to some `W`, and `W` is continuous
everywhere. First result in this arc that actually touches `Real.cos`. -/
theorem weierstrass_sum_continuous (t : Real) (ht : 0 < t) :
    ∃ W : Real → Real,
      (∀ ε : Real, 0 < ε → ∃ N, ∀ n, N ≤ n → ∀ x,
        abs (W x - partialSum (fun i => weierstrassTerm t i x) n) < ε)
      ∧ ∀ x0, ContinuousAt W x0 :=
  continuousSum_of_uniform_dominated (weierstrassAmplitude_nonneg t)
    (weierstrassAmplitude_hasBoundedPartialSums t ht) (weierstrassTerm_dom t) (weierstrassTerm_hasDerivAt t)

end Real
end MachLib
