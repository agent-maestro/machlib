import MachLib.Decimal
import MachLib.Linarith
import MachLib.SelfMapConjugacy

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

**Measured (2026-06-30):** of the 102 `Discovered/` positivity obligations (`f(vars) > 0` / `≥ 0`)
that were left `sorry`, `mach_sign` closes **61 (60%)** — the first real close-rate lift on the wild
`@verify` corpus. The remaining 40% are out of scope by construction: a non-manifest sign
(`a − b ≥ 0`, needs `a ≥ b`), a conditional/min loss (needs case analysis), or an operand whose sign
the hypotheses don't pin down. Those want an ordering/`linarith` layer, not more positivity arms.
-/

namespace MachLib.Real

/-- `exp10 x > 0` (base-10 exponential is always positive) — `exp10 x = exp(x·log 10) > 0`. -/
theorem exp10_pos (x : Real) : 0 < exp10 x := by rw [exp10_def]; exact exp_pos _

/-- The decimal zero `0.0…0` *is* `0` — cleared via `realOfScientific_clears` (`0·10ᵉ = 0`). -/
theorem rOS_zero (e : Nat) : realOfScientific 0 true e = 0 := by
  have hc : natCast (10 ^ e) ≠ 0 := ne_of_gt (natCast_pos (Nat.pos_pow_of_pos e (by decide)))
  refine mul_right_cancel' hc ?_
  rw [realOfScientific_clears 0 e, natCast_zero, zero_mul]

/-- Simp form: rewrite only zero-mantissa literals (`0.0`) to `0`, leaving nonzero decimals as
`OfScientific` so `mach_positivity`'s decimal arms keep matching. -/
@[simp] theorem ofSci_zero (e : Nat) : (OfScientific.ofScientific 0 true e : Real) = 0 := rOS_zero e

/-- Recursive positivity core: `exp_pos`, `mul_pos`, `add_pos`, delegating leaves to the existing
`mach_positivity` (squares, decimals, domain hypotheses). -/
syntax "mach_sign_core" : tactic
macro_rules
  | `(tactic| mach_sign_core) => `(tactic|
      first
      | assumption
      | exact exp_pos _
      | exact exp_nonneg _
      | exact exp10_pos _
      | mach_positivity
      | (apply mul_pos <;> mach_sign_core)
      | (apply add_pos <;> mach_sign_core)
      | (apply div_pos_of_pos_pos <;> mach_sign_core)
      | (apply mul_nonneg <;> mach_sign_core)
      | (apply add_nonneg <;> mach_sign_core)
      | (apply div_nonneg <;> mach_sign_core))

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
end SignTests

end MachLib.Real
