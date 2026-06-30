import MachLib.FieldLemmas
import MachLib.AffineContraction
import MachLib.Asymptotics

/-!
# Decimal-literal arithmetic — making `1 − 0.99 = 0.01` provable

Forge emits decimal constants (`0.99`, `0.01`, `0.001`, …) that desugar to the opaque carrier
`realOfScientific m true e` (= `m · 10⁻ᵉ`). `MachLib.Basic` left it opaque except three ad-hoc
bridges (`1.0`, `2.0`, `3.0`), so decimal arithmetic — `1 − 0.99 = 0.01`, the per-kernel safety
envelope numbers, the 18 unclosed `@verify` "nlinarith-decimal" obligations — was unprovable.

This file adds the one missing foundation: the **defining property** of a decimal literal, stated
*division-free* (cleared of its denominator), `realOfScientific m true e · 10ᵉ = m`. From it, any
decimal identity reduces by **clearing denominators** to an integer identity `mach_mpoly` closes:
to prove `lhs = rhs`, multiply by `10ᵉ` (cancellable since it's `≠ 0`), rewrite each decimal·10ᵉ to
its mantissa, and finish with `natCast` arithmetic.
-/

namespace MachLib.Real

/-- **The defining property of a decimal literal (the missing foundation).** `realOfScientific m
true e` denotes `m·10⁻ᵉ`; cleared of its denominator, `(m·10⁻ᵉ)·10ᵉ = m`. Division-free, the standard
`OfScientific` meaning, and it subsumes the ad-hoc `realOfScientific_{one,two,three}_dot_zero`. -/
axiom realOfScientific_clears (m e : Nat) :
    realOfScientific m true e * natCast (10 ^ e) = natCast m

/-- `natCast` is additive (induction on `natCast_succ`). -/
theorem natCast_add (a b : Nat) : natCast (a + b) = natCast a + natCast b := by
  induction b with
  | zero => rw [Nat.add_zero, natCast_zero, add_zero]
  | succ n ih => rw [Nat.add_succ, natCast_succ, natCast_succ, ih, add_assoc]

/-- `0 ≤ natCast n`. -/
theorem natCast_nonneg (n : Nat) : 0 ≤ natCast n := by
  induction n with
  | zero => rw [natCast_zero]; exact le_refl _
  | succ k ih => rw [natCast_succ]; exact le_trans ih (le_add_of_nonneg_right (le_of_lt zero_lt_one_ax))

/-- `0 < natCast (n+1)` — so `10ᵉ` can be cancelled. -/
theorem natCast_succ_pos (n : Nat) : 0 < natCast (n + 1) := by
  rw [natCast_succ]
  have h : (0 : Real) + 1 ≤ natCast n + 1 := add_le_add_both (natCast_nonneg n) (le_refl 1)
  rw [add_comm (0 : Real) 1, add_zero] at h
  exact lt_of_lt_of_le zero_lt_one_ax h

/-- `0 < n ⇒ 0 < natCast n`. -/
theorem natCast_pos {n : Nat} (h : 0 < n) : 0 < natCast n := by
  cases n with
  | zero => exact (Nat.lt_irrefl 0 h).elim
  | succ k => exact natCast_succ_pos k

/-- `(a + b) − b = a` — clean-named so `mach_mpoly` parses the atoms (it rejects the dirty
`natCast (n − m)` atom). -/
theorem add_sub_cancel_right (a b : Real) : (a + b) - b = a := by mach_mpoly [a, b]

/-- Right cancellation (the library ships only `mul_left_cancel`; derive the mirror via `mul_comm`).
Needed to cancel the cleared denominator on the right. -/
theorem mul_right_cancel' {a b c : Real} (hc : c ≠ 0) (h : a * c = b * c) : a = b := by
  refine mul_left_cancel hc ?_
  rw [mul_comm c a, mul_comm c b]; exact h

/-- `natCast` of a Nat subtraction, for `m ≤ n`. -/
theorem natCast_sub {m n : Nat} (h : m ≤ n) : natCast (n - m) = natCast n - natCast m := by
  have hn : natCast n = natCast (n - m) + natCast m := by rw [← natCast_add, Nat.sub_add_cancel h]
  rw [hn, add_sub_cancel_right]

/-- `x·y + x = x·(y+1)` — clean-named helper for the `natCast_mul` induction step. -/
theorem mul_succ_eq (x y : Real) : x * y + x = x * (y + 1) := by mach_mpoly [x, y]

/-- `natCast` is multiplicative (induction on `natCast_succ`, mirroring `natCast_add`). -/
theorem natCast_mul (a b : Nat) : natCast (a * b) = natCast a * natCast b := by
  induction b with
  | zero => rw [Nat.mul_zero, natCast_zero, mul_zero]
  | succ k ih => rw [Nat.mul_succ, natCast_add, ih, natCast_succ, mul_succ_eq]

/-- `a·b·(c·d) = (a·c)·(b·d)` — clean-named AC regrouping for `decimal_mul`. -/
theorem mul4_rearrange (a b c d : Real) : a * b * (c * d) = (a * c) * (b * d) := by
  mach_mpoly [a, b, c, d]

/-- Distribute over `1 − x` without a `mul_sub` lemma (`mach_mpoly` does the ring identity). -/
theorem mul_one_sub (c x : Real) : c * (1 - x) = c - c * x := by mach_mpoly [c, x]

/-- **The general decimal-subtraction fact: `1 − (m·10⁻ᵉ) = (10ᵉ − m)·10⁻ᵉ`** for `m ≤ 10ᵉ`.
Machine-checked by clearing the denominator `10ᵉ`: cancel by it (`≠ 0`), rewrite each decimal·10ᵉ to
its mantissa via `realOfScientific_clears`, and close `10ᵉ − m = (10ᵉ − m)` with `natCast` arithmetic.
Every concrete decimal pole→offset (`1−0.99=0.01`, `1−0.996=0.004`, …) is now a one-line corollary. -/
theorem one_sub_decimal (m e : Nat) (h : m ≤ 10 ^ e) :
    (1 : Real) - realOfScientific m true e = realOfScientific (10 ^ e - m) true e := by
  have hc : natCast (10 ^ e) ≠ 0 := ne_of_gt (natCast_pos (Nat.pos_pow_of_pos e (by decide)))
  refine mul_left_cancel hc ?_
  rw [mul_one_sub,
      mul_comm (natCast (10 ^ e)) (realOfScientific m true e), realOfScientific_clears m e,
      mul_comm (natCast (10 ^ e)) (realOfScientific (10 ^ e - m) true e),
      realOfScientific_clears (10 ^ e - m) e, natCast_sub h]

/-- `1 − 0.99 = 0.01` (the PID kernel's pole→offset) — a one-line corollary. -/
theorem one_sub_point99 : (1 : Real) - 0.99 = 0.01 := one_sub_decimal 99 2 (by decide)

/-- `1 − 0.996 = 0.004` (the motor kernel's pole, a different mantissa/exponent) — same one-liner. -/
theorem one_sub_point996 : (1 : Real) - 0.996 = 0.004 := one_sub_decimal 996 3 (by decide)

/-- **Decimal multiplication: `(m₁·10⁻ᵉ¹)(m₂·10⁻ᵉ²) = (m₁m₂)·10⁻⁽ᵉ¹⁺ᵉ²⁾`.** The second evaluator
pillar (after subtraction): clear by `10^(e₁+e₂) = 10^e₁·10^e₂`, regroup `d₁d₂·(c₁c₂) = (d₁c₁)(d₂c₂)`,
discharge each factor by `realOfScientific_clears`, and finish in `natCast` integer arithmetic. -/
theorem decimal_mul (m₁ e₁ m₂ e₂ : Nat) :
    realOfScientific m₁ true e₁ * realOfScientific m₂ true e₂
      = realOfScientific (m₁ * m₂) true (e₁ + e₂) := by
  have hC : natCast (10 ^ (e₁ + e₂)) ≠ 0 :=
    ne_of_gt (natCast_pos (Nat.pos_pow_of_pos (e₁ + e₂) (by decide)))
  refine mul_right_cancel' hC ?_
  rw [realOfScientific_clears (m₁ * m₂) (e₁ + e₂), natCast_mul m₁ m₂,
      Nat.pow_add, natCast_mul (10 ^ e₁) (10 ^ e₂), mul4_rearrange,
      realOfScientific_clears m₁ e₁, realOfScientific_clears m₂ e₂]

/-- **Decimal renormalization (trailing zero): `(m·10)·10⁻⁽ᵉ⁺¹⁾ = m·10⁻ᵉ`.** Lets a product land in
its canonical mantissa/exponent (`80·10⁻⁴ = 8·10⁻³`). Same clear-and-cancel recipe. -/
theorem decimal_normalize (m e : Nat) :
    realOfScientific (m * 10) true (e + 1) = realOfScientific m true e := by
  have hc : natCast (10 ^ (e + 1)) ≠ 0 :=
    ne_of_gt (natCast_pos (Nat.pos_pow_of_pos (e + 1) (by decide)))
  refine mul_right_cancel' hc ?_
  rw [realOfScientific_clears (m * 10) (e + 1), natCast_mul m 10,
      Nat.pow_succ, natCast_mul (10 ^ e) 10, ← mul_assoc, realOfScientific_clears m e]

/-- **The PID kernel's safety-envelope relation, machine-checked.** `first_order_clamp_envelope` takes
`(1−a)·X = U+W`; for the silicon/RC-validated PID (`a=0.99, X=1, U=0.01, W=0`) that is `(1−0.99)·1 =
0.01+0`. Previously this decimal fact was asserted in Python; now it is a theorem. -/
theorem pid_envelope_relation : ((1 : Real) - 0.99) * 1 = 0.01 + 0 := by
  rw [one_sub_point99]; mach_ring

/-- **The motor kernel's safety-envelope relation, machine-checked** (the `2.0` number). The PI motor
(`K=2`) has pole `a=0.996`, so `first_order_clamp_envelope`'s `(1−a)·X = U+W` is `(1−0.996)·2.0 =
0.008`. This needs the *multiplication* pillar: `0.004·2.0 = 80·10⁻⁴`, renormalized to `0.008`. -/
theorem motor_envelope_relation : ((1 : Real) - 0.996) * 2.0 = 0.008 := by
  rw [one_sub_point996]
  show realOfScientific 4 true 3 * realOfScientific 20 true 1 = realOfScientific 8 true 3
  rw [decimal_mul 4 3 20 1]
  exact decimal_normalize 8 3

/-- **Consistency check: the new general axiom reproduces the ad-hoc `realOfScientific_one_dot_zero`**
(`1.0 = 1`). So `realOfScientific_clears` *subsumes* the three hand-written decimal bridges in
`Basic.lean` rather than merely sitting beside them — evidence it is the right single foundation. -/
theorem one_dot_zero_from_clears : realOfScientific 10 true 1 = 1 := by
  have h := realOfScientific_clears 10 1
  have hc : natCast (10 ^ 1) ≠ 0 := ne_of_gt (natCast_pos (Nat.pos_pow_of_pos 1 (by decide)))
  refine mul_right_cancel' hc ?_
  rw [one_mul_thm]; exact h

end MachLib.Real
