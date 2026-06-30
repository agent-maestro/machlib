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

/-- **Common-denominator scaling: `(m·10⁻ᵉ)·10ᴱ = m·10ᴱ⁻ᵉ`** for `e ≤ E.** The engine primitive for
clearing a *multi-exponent* decimal goal: pick `E = max` exponent, scale by `10ᴱ` (cancellable), and
every decimal in the goal turns into the integer `m·10ᴱ⁻ᵉ` — so a mixed identity like `0.99 + 0.001 =
0.991` reduces to one integer equation. Proven by writing `E = e + (E−e)` and the same clear recipe. -/
theorem decimal_scaled (m e E : Nat) (h : e ≤ E) :
    realOfScientific m true e * natCast (10 ^ E) = natCast (m * 10 ^ (E - e)) := by
  obtain ⟨d, rfl⟩ := Nat.le.dest h
  rw [Nat.add_sub_cancel_left, Nat.pow_add, natCast_mul (10 ^ e) (10 ^ d), ← mul_assoc,
      realOfScientific_clears m e, ← natCast_mul]

/-! ### The `mach_decimal` tactic — automated decimal-literal arithmetic

`mach_norm_num` (MachLib.Linarith) already closes decimal **order** goals between literals
(`2.0 ≤ 3.0`) via cross-multiplication. `mach_decimal` completes the family: it discharges decimal
**arithmetic** goals (`1 − 0.99 = 0.01`, `0.004·2.0 = 0.008`, `1.0 + 2.0 = 3.0`) and the safety-envelope
relations, by `simp`-normalising the `+ − ×` decimal operations into a single scientific literal on
each side, then closing by cross-multiplication (`decide` on the resulting integer identity).

Scope (honest): the terminating-decimal `+ − ×` fragment with literal operands, plus order. It does
**not** do division (no field inverse in the Mathlib-free automation) and does **not** reason over free
variables — the dominant blockers in the wild `@verify` corpus are exactly those two, which need a
separate decimal-division evaluator and a linarith-over-variables layer. -/

/-- Definitional bridge: a `0.99`-style literal *is* `realOfScientific` (the `OfScientific` instance).
Lets `simp` see the decimal lemmas, whose LHSs are stated in `realOfScientific` form. -/
theorem ofSci_eq (m e : Nat) :
    (OfScientific.ofScientific m true e : Real) = realOfScientific m true e := rfl

/-- **Cross-multiplication equality** (the `=` analog of `realOfScientific_le_of_nat`): two decimals
are equal iff their mantissas agree after clearing to a common denominator. The integer premise is
`decide`-able, so it closes a normalised `rOS a true b = rOS c true d` without canonicalising. -/
theorem realOfScientific_eq_of_nat {m₁ e₁ m₂ e₂ : Nat} (h : m₁ * 10 ^ e₂ = m₂ * 10 ^ e₁) :
    realOfScientific m₁ true e₁ = realOfScientific m₂ true e₂ := by
  have hc : natCast (10 ^ (e₁ + e₂)) ≠ 0 :=
    ne_of_gt (natCast_pos (Nat.pos_pow_of_pos (e₁ + e₂) (by decide)))
  refine mul_right_cancel' hc ?_
  rw [decimal_scaled m₁ e₁ (e₁ + e₂) (Nat.le_add_right e₁ e₂),
      decimal_scaled m₂ e₂ (e₁ + e₂) (Nat.le_add_left e₂ e₁),
      Nat.add_sub_cancel_left, Nat.add_sub_cancel, h]

/-- **Same-exponent decimal addition: `m₁·10⁻ᵉ + m₂·10⁻ᵉ = (m₁+m₂)·10⁻ᵉ`.** Covers same-scale constant
sums (`1.0 + 2.0 = 3.0`, the `K + 2.0` shape). Different-exponent sums are handled by the final
cross-multiplication, once each side is a single literal. -/
theorem decimal_add_same (m₁ m₂ e : Nat) :
    realOfScientific m₁ true e + realOfScientific m₂ true e = realOfScientific (m₁ + m₂) true e := by
  have hc : natCast (10 ^ e) ≠ 0 := ne_of_gt (natCast_pos (Nat.pos_pow_of_pos e (by decide)))
  refine mul_right_cancel' hc ?_
  rw [mul_distrib_right, realOfScientific_clears m₁ e, realOfScientific_clears m₂ e,
      realOfScientific_clears (m₁ + m₂) e, ← natCast_add]

/-- **`mach_decimal`** — close a decimal-literal arithmetic goal. Normalise the `+ − ×` operations to a
single scientific literal per side (`simp` with the decimal lemmas + `decide`-discharged side
conditions), then close by cross-multiplication (`=`, `≤`, `<`) or `rfl`. Sound: every arm reduces to a
`decide`-checked integer fact over the true mantissas, so it cannot prove a false decimal relation. -/
macro "mach_decimal" : tactic => `(tactic|
  (try simp (config := { decide := true }) only
     [ofSci_eq, mul_one_ax, one_mul_thm, add_zero, zero_add,
      one_sub_decimal, decimal_add_same, decimal_mul, decimal_normalize]) <;>
  (first
   | rfl
   | (apply realOfScientific_eq_of_nat <;> decide)
   | (apply realOfScientific_le_of_nat <;> decide)
   | (apply realOfScientific_lt_of_nat <;> decide)
   | (apply le_of_lt <;> apply realOfScientific_lt_of_nat <;> decide)
   | (apply realOfScientific_pos <;> decide)))

/-- **The PID kernel's safety-envelope relation, machine-checked.** `first_order_clamp_envelope` takes
`(1−a)·X = U+W`; for the silicon/RC-validated PID (`a=0.99, X=1, U=0.01, W=0`) that is `(1−0.99)·1 =
0.01+0`. Previously this decimal fact was asserted in Python; now it is a theorem. -/
theorem pid_envelope_relation : ((1 : Real) - 0.99) * 1 = 0.01 + 0 := by mach_decimal

/-- **The motor kernel's safety-envelope relation, machine-checked** (the `2.0` number). The PI motor
(`K=2`) has pole `a=0.996`, so `first_order_clamp_envelope`'s `(1−a)·X = U+W` is `(1−0.996)·2.0 =
0.008`. This needs the *multiplication* pillar: `0.004·2.0 = 80·10⁻⁴`, renormalized to `0.008`. -/
theorem motor_envelope_relation : ((1 : Real) - 0.996) * 2.0 = 0.008 := by mach_decimal

/-- **Consistency check: the new general axiom reproduces the ad-hoc `realOfScientific_one_dot_zero`**
(`1.0 = 1`). So `realOfScientific_clears` *subsumes* the three hand-written decimal bridges in
`Basic.lean` rather than merely sitting beside them — evidence it is the right single foundation. -/
theorem one_dot_zero_from_clears : realOfScientific 10 true 1 = 1 := by
  have h := realOfScientific_clears 10 1
  have hc : natCast (10 ^ 1) ≠ 0 := ne_of_gt (natCast_pos (Nat.pos_pow_of_pos 1 (by decide)))
  refine mul_right_cancel' hc ?_
  rw [one_mul_thm]; exact h

/-! ### `mach_decimal` regression suite (doubles as the tactic's spec). -/
namespace DecimalTests

example : (1 : Real) - 0.99 = 0.01 := by mach_decimal           -- subtraction (PID pole)
example : (1 : Real) - 0.996 = 0.004 := by mach_decimal         -- subtraction (motor pole)
example : (0.004 : Real) * 2.0 = 0.008 := by mach_decimal       -- mul + trailing-zero renorm
example : (0.5 : Real) * 0.5 = 0.25 := by mach_decimal          -- mul
example : (1.0 : Real) + 2.0 = 3.0 := by mach_decimal           -- same-exponent add (K + 2.0 shape)
example : (0.1 : Real) + 0.2 = 0.3 := by mach_decimal           -- same-exponent add
example : (2.0 : Real) ≤ 3.0 := by mach_decimal                 -- order ≤
example : (0.5 : Real) < 1.0 := by mach_decimal                 -- order <
example : (0 : Real) < 0.5 := by mach_decimal                   -- positivity
example : (0.50 : Real) = 0.5 := by mach_decimal                -- cross-exponent equal forms
example : ((1 : Real) - 0.99) * 1 = 0.01 + 0 := by mach_decimal -- PID envelope, end-to-end
example : ((1 : Real) - 0.996) * 2.0 = 0.008 := by mach_decimal -- motor envelope, end-to-end

end DecimalTests

end MachLib.Real
