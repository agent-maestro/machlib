import MachLib.Decimal
import MachLib.Linarith
import MachLib.SelfMapConjugacy
import MachLib.Trig

/-!
# `mach_sign` — automated sign/positivity for Forge `> 0` obligations

The largest blocked-`@verify` subclass is `f(vars) > 0` (≈178 of the `Discovered/` sorries): a
product / sum / `exp` of manifestly-positive subterms (positive inputs by hypothesis, `exp` always
positive, positive constants). `mach_positivity` already closes squares / decimals / fog bands but has
no `mul_pos` / `add_pos` / `exp_pos` recursion, and the goals carry the decimal zero `0.0`
(`realOfScientific 0 true 1`) rather than `0`, so a `mul_pos`-produced `0 < _` doesn't match `_ > 0.0`.

`mach_sign` bridges both: normalise the decimal zero to `0` (only the zeros, so `mach_positivity`'s
`OfScientific` arms still fire on nonzero literals), then recurse through `mul_pos` / `add_pos` /
`div_pos` / `exp_pos` / `exp10_pos` (and their `≤` mirrors), delegating leaves to `mach_positivity`.
Every leaf is a real positivity fact — it cannot manufacture a false sign (`x > 0`, `x·x > 0`,
`a − b > 0` are all correctly *refused*).

**Measured (2026-06-30), per-obligation** (the rigorous metric: swap each `sorry` for
`(first | mach_sign | sorry)` so the file always compiles, then `#print axioms` per theorem — a
theorem with no `sorryAx` is a *real* close): of the `Discovered/` positivity/ordering obligations,
the tactics close **116 / 165 (70%)**. (A per-FILE check reads 58/97 ≈ 60%, but that under-counts —
a multi-obligation file stays red if any one obligation fails.) Coverage spans: positivity
(`mul_pos`/`add_pos`/`div_pos`/`exp_pos`), the sigmoid-GELU/zero-floor/`1−p`/`realPow` arms, the
ordering layer (`mach_le` + `min_nonneg` + `sub_nonneg_of_le` for structural `a − b ≥ 0` via monotone
differences), and — using the emitted refinement hypotheses — **bound transitivity** (`0 ≤ x` from
`c ≤ x` + `0 ≤ c`) and **square monotonicity** (`|a| ≤ |b| ⇒ a² ≤ b²`), which together close e.g.
`defibrillator.phase1_energy = HALF·C·(v0²−v1²) ≥ 0` from `C ≥ C_MIN` and `|v1| ≤ |v0|`.

Honest ceiling: the remaining ~30% are out of any general tactic's reach — a **domain** inequality
(`a − b ≥ 0` where `b ≤ a` is Black-Scholes-price / energy-balance specific, not structural), or a
conditional/min loss needing case analysis. Those need a real nlinarith + a domain-lemma library, not
more arms.
-/

namespace MachLib.Real

/-- `exp10 x > 0` (base-10 exponential is always positive) — `exp10 x = exp(x·log 10) > 0`. -/
theorem exp10_pos (x : Real) : 0 < exp10 x := by rw [exp10_def]; exact exp_pos _

/-- `|x|·|x| = x·x` — bridges a square to its absolute value (`x·x ≥ 0`). -/
theorem abs_mul_self (x : Real) : abs x * abs x = x * x := by
  rw [← abs_mul, abs_of_nonneg (mul_self_nonneg x)]

/-- **Square monotonicity: `|a| ≤ |b| ⇒ a·a ≤ b·b`.** The `v1² ≤ v0²`-from-`|v1| ≤ |v0|` step in
energy/quadratic kernels (defibrillator). Built from the monotone-multiply lemmas, no new axiom. -/
theorem mul_self_le_mul_self_of_abs_le {a b : Real} (h : abs a ≤ abs b) : a * a ≤ b * b := by
  rw [← abs_mul_self a, ← abs_mul_self b]
  exact le_trans (mul_le_mul_of_nonneg_right h (abs_nonneg a))
                 (mul_le_mul_of_nonneg_left h (abs_nonneg b))

/-- `0 < 1 + tanh x` — the sigmoid/GELU positivity (`HALF·(1 + tanh …)` shape). From `−1 < tanh x`. -/
theorem one_add_tanh_pos (x : Real) : 0 < 1 + tanh x := by
  have h := sub_pos_of_lt (neg_one_lt_tanh x)
  have e : tanh x - (-1) = 1 + tanh x := by mach_ring
  rwa [e] at h

/-- The decimal zero `0.0…0` *is* `0` — cleared via `realOfScientific_clears` (`0·10ᵉ = 0`). -/
theorem rOS_zero (e : Nat) : realOfScientific 0 true e = 0 := by
  have hc : natCast (10 ^ e) ≠ 0 := ne_of_gt (natCast_pos (Nat.pos_pow_of_pos e (by decide)))
  refine mul_right_cancel' hc ?_
  rw [realOfScientific_clears 0 e, natCast_zero, zero_mul]

/-- Simp form: rewrite only zero-mantissa literals (`0.0`) to `0`, leaving nonzero decimals as
`OfScientific` so `mach_positivity`'s decimal arms keep matching. -/
@[simp] theorem ofSci_zero (e : Nat) : (OfScientific.ofScientific 0 true e : Real) = 0 := rOS_zero e

/-- The ordering companion: prove `b ≤ a` goals by monotonicity (`exp_monotone`, `neg_le_neg`,
`add_le_add_left`, `mul_le_mul_of_nonneg_left`) and the `min`/`max` bounds, delegating `0 ≤ _`
side-conditions to `mach_sign_core`. Mutually recursive with it. This is what lets `sub_nonneg_of_le`
turn an `a − b ≥ 0` goal into a tractable `b ≤ a` — e.g. an exp-difference `exp(−h₀) − exp(−h₁) ≥ 0`
from `h₀ ≤ h₁`. -/
syntax "mach_le" : tactic

/-- Recursive positivity core: `exp_pos`, `mul_pos`, `add_pos`, `min_nonneg`, the tanh/max/pow arms,
and `sub_nonneg_of_le` (→ `mach_le`), delegating leaves to the existing `mach_positivity`. -/
syntax "mach_sign_core" : tactic
macro_rules
  | `(tactic| mach_sign_core) => `(tactic|
      first
      | assumption
      | exact exp_pos _
      | exact exp_nonneg _
      | exact exp10_pos _
      | exact one_add_tanh_pos _
      | exact le_of_lt (one_add_tanh_pos _)
      | exact le_max_right _ _
      | exact le_max_left _ _
      | mach_positivity
      | (apply mul_pos <;> mach_sign_core)
      | (apply add_pos <;> mach_sign_core)
      | (apply div_pos_of_pos_pos <;> mach_sign_core)
      | (apply sub_pos_of_lt <;> mach_sign_core)
      | (apply mul_nonneg <;> mach_sign_core)
      | (apply add_nonneg <;> mach_sign_core)
      | (apply div_nonneg <;> mach_sign_core)
      | (apply realPow_nonneg <;> mach_sign_core)
      | (apply min_nonneg <;> mach_sign_core)
      -- bound transitivity: `0 ≤ x` from a refinement hyp `c ≤ x` (e.g. `capacitance ≥ C_MIN`)
      -- + `0 ≤ c`. The `by assumption` resolves the hyp (instantiating the midpoint) first.
      | (refine le_trans ?_ (by assumption) <;> mach_sign_core)
      | (apply sub_nonneg_of_le <;> mach_le))

macro_rules
  | `(tactic| mach_le) => `(tactic|
      first
      | assumption
      | exact le_refl _
      | exact le_max_right _ _
      | exact le_max_left _ _
      | exact min_le_right _ _
      | exact min_le_left _ _
      | (apply exp_monotone <;> mach_le)
      | (apply neg_le_neg <;> mach_le)
      | (apply add_le_add_left <;> mach_le)
      | (apply mul_self_le_mul_self_of_abs_le <;> mach_le)
      | (apply mul_le_mul_of_nonneg_left <;> (first | mach_le | mach_sign_core)))

/-- **`mach_sign`** — close a Forge `f(vars) > 0` / `0 < f(vars)` obligation. Normalise the decimal
zero, then run the positivity recursion. -/
macro "mach_sign" : tactic => `(tactic|
  ((try simp only [ofSci_zero] at *) <;> mach_sign_core))

/-! ### Regression suite -/
namespace SignTests
example (p : Real) (h : p > (0.0 : Real)) : p * (exp p) > (0.0 : Real) := by mach_sign
example (a b : Real) (ha : a > (0.0 : Real)) (hb : b > (0.0 : Real)) : a * b > (0.0 : Real) := by mach_sign
example (x : Real) : (exp x) > (0.0 : Real) := by mach_sign
example (a b : Real) (ha : a > (0.0 : Real)) (hb : b > (0.0 : Real)) :
    a + (b * (exp a)) > (0.0 : Real) := by mach_sign
-- new arms: sigmoid/GELU, zero-floor max, 1−p denominators, real powers
example (x : Real) : (0.5 : Real) * (1 + tanh x) > (0 : Real) := by mach_sign
example (e : Real) : max e (0 : Real) ≥ (0 : Real) := by mach_sign
example (c e : Real) (hc : c > (0:Real)) : c * (max e (0:Real)) ≥ (0 : Real) := by mach_sign
example (p : Real) (h : p < (1:Real)) : (1 : Real) - p > (0 : Real) := by mach_sign
example (b y : Real) (hb : b ≥ (0:Real)) : b ^ y ≥ (0 : Real) := by mach_sign
-- ordering layer: saturating min/max ≥ 0, exp-difference monotonicity, ≤-recursion
example (e hi : Real) (h : (0:Real) ≤ hi) : (0:Real) ≤ min (max e 0) hi := by mach_sign
example (a b : Real) (h : a ≤ b) : (0:Real) ≤ exp (-a) - exp (-b) := by mach_sign
example (x y : Real) (h : x ≤ y) : exp x ≤ exp y := by mach_le
example (c x y : Real) (hc : (0:Real) ≤ c) (h : x ≤ y) : c * x ≤ c * y := by mach_le
-- using refinement hyps: bound transitivity + square monotonicity (the defibrillator chain)
example (x : Real) (h : (0.5:Real) ≤ x) : (0:Real) ≤ x := by mach_sign
example (a b : Real) (h : abs a ≤ abs b) : a * a ≤ b * b := by mach_le
example (c v0 v1 : Real) (hc : (0.5:Real) ≤ c) (hv : abs v1 ≤ abs v0) :
    c * (v0 * v0 - v1 * v1) ≥ (0:Real) := by mach_sign
end SignTests

end MachLib.Real
