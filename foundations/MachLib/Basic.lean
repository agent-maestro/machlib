/-
MachLib.Basic — axiomatic real numbers, zero Mathlib dependency.

The type `Real` is opaque, equipped with the standard arithmetic
operations, an order relation, and the analytic axioms exp / log /
trig will need (Archimedean, supremum on bounded predicates).

Construction from rationals via Cauchy sequences is omitted by
design: it adds ~3,000 lines for no MachLib benefit. Every axiom
below is consistent with classical ZFC.
-/

namespace MachLib

axiom Real : Type

namespace Real

/-! ### Underlying values + typeclass instances -/

axiom addR : Real → Real → Real
axiom subR : Real → Real → Real
axiom mulR : Real → Real → Real
axiom divR : Real → Real → Real
axiom negR : Real → Real
axiom oneR : Real
axiom zeroR : Real
axiom ltR : Real → Real → Prop
axiom leR : Real → Real → Prop

@[instance] noncomputable def instAdd  : Add Real := ⟨addR⟩
@[instance] noncomputable def instSub  : Sub Real := ⟨subR⟩
@[instance] noncomputable def instMul  : Mul Real := ⟨mulR⟩
@[instance] noncomputable def instDiv  : Div Real := ⟨divR⟩
@[instance] noncomputable def instNeg  : Neg Real := ⟨negR⟩
@[instance] noncomputable def instLT   : LT Real := ⟨ltR⟩
@[instance] noncomputable def instLE   : LE Real := ⟨leR⟩
@[instance] noncomputable def instOfNatZero : OfNat Real (nat_lit 0) := ⟨zeroR⟩
@[instance] noncomputable def instOfNatOne  : OfNat Real (nat_lit 1) := ⟨oneR⟩
@[instance] noncomputable def instInhabited : Inhabited Real := ⟨zeroR⟩

/--
Scientific-notation literal carrier. Forge-emitted Lean files
contain decimal constants like `(0.0 : Real)`, `(0.001 : Real)`,
`(2.99792458e8 : Real)`. Lean's elaborator desugars each one to
`OfScientific.ofScientific mantissa expSign decExp`; without this
instance the elaborator reports `failed to synthesize OfScientific
Real` and refuses to type-check the file.

The carrier `realOfScientific` is opaque — `MachLib.Basic` does
not commit to a concrete real-number representation, so we treat
the decimal-to-Real conversion the same way we treat `exp`, `log`,
and friends: as an axiom that downstream files may further
constrain. The instance is `noncomputable` to match the rest of
the field.
-/
axiom realOfScientific
    (mantissa : Nat) (exponentSign : Bool) (decimalExponent : Nat) : Real

@[instance] noncomputable def instOfScientific : OfScientific Real :=
  ⟨realOfScientific⟩

/--
Real-to-real power. Forge kernels emit `(base ^ exp)` for
non-integer exponents (e.g. `(1 + (alpha * psi) ^ n_shape)` in
the van Genuchten retention curve). Lean's default `^` resolves
to integer powers via `Monoid.npow`; for `Real ^ Real` we must
provide an explicit `HPow` instance.

We do NOT axiomatise the analytic identity `realPow x y = exp(y * log x)`
here — that's a CHOICE the downstream theorem can pin down with
its own axioms when needed. The carrier is opaque so MachLib
stays agnostic about whether the kernel target is real-analytic
or a piecewise extension.
-/
axiom realPow : Real → Real → Real

@[instance] noncomputable def instHPow : HPow Real Real Real :=
  ⟨realPow⟩

axiom realPow_zero (x : Real) : realPow x 0 = 1
axiom realPow_one  (x : Real) : realPow x 1 = x
axiom realPow_pos  {x y : Real} : 0 < x → 0 < realPow x y

@[instance] noncomputable def instDecLT (a b : Real) : Decidable (a < b) :=
  Classical.propDecidable _
@[instance] noncomputable def instDecLE (a b : Real) : Decidable (a ≤ b) :=
  Classical.propDecidable _

/-! ### Field axioms -/

axiom add_comm    (a b   : Real) : a + b = b + a
axiom add_assoc   (a b c : Real) : (a + b) + c = a + (b + c)
axiom add_zero    (a     : Real) : a + 0 = a
axiom add_neg     (a     : Real) : a + (-a) = 0
axiom sub_def     (a b   : Real) : a - b = a + (-b)

axiom mul_comm    (a b   : Real) : a * b = b * a
axiom mul_assoc   (a b c : Real) : (a * b) * c = a * (b * c)
axiom mul_one_ax  (a     : Real) : a * 1 = a
axiom mul_distrib (a b c : Real) : a * (b + c) = a * b + a * c

axiom zero_ne_one_ax : (0 : Real) ≠ 1
axiom div_def        (a b : Real) : b ≠ 0 → a / b = a * (1 / b)
axiom mul_inv        (a   : Real) : a ≠ 0 → a * (1 / a) = 1

/-! ### Order axioms -/

axiom lt_irrefl_ax (a   : Real) : ¬ a < a
axiom lt_trans_ax  {a b c : Real} : a < b → b < c → a < c
axiom lt_total     (a b : Real) : a < b ∨ a = b ∨ b < a
axiom le_iff_lt_or_eq (a b : Real) : a ≤ b ↔ a < b ∨ a = b

axiom add_lt_add_left  {a b : Real} (h : a < b) (c : Real) : c + a < c + b
axiom mul_pos          {a b : Real} : 0 < a → 0 < b → 0 < a * b
axiom zero_lt_one_ax   : (0 : Real) < 1

/-! ### Archimedean + completeness -/

axiom natCast : Nat → Real

axiom natCast_zero : natCast 0 = 0
axiom natCast_succ (n : Nat) : natCast (n + 1) = natCast n + 1

axiom archimedean (x : Real) : ∃ n : Nat, x < natCast n

def BoundedAbove (p : Real → Prop) : Prop :=
  ∃ M : Real, ∀ x : Real, p x → x ≤ M

axiom sup_exists
    (p : Real → Prop) (h_nonempty : ∃ x, p x) (h_bound : BoundedAbove p) :
    ∃ s : Real,
      (∀ x, p x → x ≤ s) ∧
      (∀ s', (∀ x, p x → x ≤ s') → s ≤ s')

/-! ## Derived definitions -/

noncomputable def abs (x : Real) : Real := if 0 ≤ x then x else -x
noncomputable def min (a b : Real) : Real := if a ≤ b then a else b
noncomputable def max (a b : Real) : Real := if a ≤ b then b else a

/-- Two-argument Heaviside step. `step a b = 1` when `a ≥ b`,
otherwise `0`. The 2-arg form matches the `step(sample, threshold)`
convention Forge kernels emit (e.g. shadow PCF, neural threshold
activations) and avoids carrying around a separate
`heaviside`/`step1` distinction. -/
noncomputable def step (a b : Real) : Real := if b ≤ a then 1 else 0

/-! ## Basic derived lemmas -/

theorem zero_add (a : Real) : 0 + a = a := by
  rw [add_comm]; exact add_zero a

theorem neg_add_self (a : Real) : -a + a = 0 := by
  rw [add_comm]; exact add_neg a

theorem one_mul_thm (a : Real) : 1 * a = a := by
  rw [mul_comm]; exact mul_one_ax a

theorem mul_zero (a : Real) : a * 0 = 0 := by
  have h : a * 0 = a * 0 + a * 0 := by
    have step : a * (0 + 0) = a * 0 + a * 0 := mul_distrib a 0 0
    rw [add_zero] at step
    exact step
  have h2 : a * 0 + (-(a * 0)) = (a * 0 + a * 0) + (-(a * 0)) := by
    rw [← h]
  rw [add_neg, add_assoc, add_neg, add_zero] at h2
  exact h2.symm

theorem zero_mul (a : Real) : 0 * a = 0 := by
  rw [mul_comm]; exact mul_zero a

theorem ne_of_lt {a b : Real} (h : a < b) : a ≠ b := by
  intro heq; rw [heq] at h; exact lt_irrefl_ax b h

theorem ne_of_gt {a b : Real} (h : b < a) : a ≠ b := by
  intro heq; rw [heq] at h; exact lt_irrefl_ax b h

theorem one_pos : (0 : Real) < 1 := zero_lt_one_ax

theorem one_ne_zero : (1 : Real) ≠ 0 := fun h => zero_ne_one_ax h.symm

theorem abs_zero : abs (0 : Real) = 0 := by
  unfold abs
  have h : (0 : Real) ≤ 0 := (le_iff_lt_or_eq 0 0).mpr (Or.inr rfl)
  simp [h]

theorem abs_one : abs (1 : Real) = 1 := by
  unfold abs
  have h : (0 : Real) ≤ 1 := (le_iff_lt_or_eq 0 1).mpr (Or.inl zero_lt_one_ax)
  simp [h]

theorem min_self (a : Real) : min a a = a := by
  unfold min
  have h : a ≤ a := (le_iff_lt_or_eq a a).mpr (Or.inr rfl)
  simp [h]

theorem max_self (a : Real) : max a a = a := by
  unfold max
  have h : a ≤ a := (le_iff_lt_or_eq a a).mpr (Or.inr rfl)
  simp [h]

end Real

end MachLib
