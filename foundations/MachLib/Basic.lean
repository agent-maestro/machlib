/-
MachLib.Basic — axiomatic real numbers, zero Mathlib dependency.

The type `R` is opaque, equipped with the standard arithmetic
operations, an order relation, and the analytic axioms exp / log /
trig will need (Archimedean, supremum on bounded predicates).

Construction from rationals via Cauchy sequences is omitted by
design: it adds ~3,000 lines for no MachLib benefit. Every axiom
below is consistent with classical ZFC.
-/

namespace MachLib

axiom R : Type

namespace R

/-! ### Underlying values + typeclass instances -/

axiom addR : R → R → R
axiom subR : R → R → R
axiom mulR : R → R → R
axiom divR : R → R → R
axiom negR : R → R
axiom oneR : R
axiom zeroR : R
axiom ltR : R → R → Prop
axiom leR : R → R → Prop

@[instance] noncomputable def instAdd  : Add R := ⟨addR⟩
@[instance] noncomputable def instSub  : Sub R := ⟨subR⟩
@[instance] noncomputable def instMul  : Mul R := ⟨mulR⟩
@[instance] noncomputable def instDiv  : Div R := ⟨divR⟩
@[instance] noncomputable def instNeg  : Neg R := ⟨negR⟩
@[instance] noncomputable def instLT   : LT R := ⟨ltR⟩
@[instance] noncomputable def instLE   : LE R := ⟨leR⟩
@[instance] noncomputable def instOfNatZero : OfNat R (nat_lit 0) := ⟨zeroR⟩
@[instance] noncomputable def instOfNatOne  : OfNat R (nat_lit 1) := ⟨oneR⟩
@[instance] noncomputable def instInhabited : Inhabited R := ⟨zeroR⟩

@[instance] noncomputable def instDecLT (a b : R) : Decidable (a < b) :=
  Classical.propDecidable _
@[instance] noncomputable def instDecLE (a b : R) : Decidable (a ≤ b) :=
  Classical.propDecidable _

/-! ### Field axioms -/

axiom add_comm    (a b   : R) : a + b = b + a
axiom add_assoc   (a b c : R) : (a + b) + c = a + (b + c)
axiom add_zero    (a     : R) : a + 0 = a
axiom add_neg     (a     : R) : a + (-a) = 0
axiom sub_def     (a b   : R) : a - b = a + (-b)

axiom mul_comm    (a b   : R) : a * b = b * a
axiom mul_assoc   (a b c : R) : (a * b) * c = a * (b * c)
axiom mul_one_ax  (a     : R) : a * 1 = a
axiom mul_distrib (a b c : R) : a * (b + c) = a * b + a * c

axiom zero_ne_one_ax : (0 : R) ≠ 1
axiom div_def        (a b : R) : b ≠ 0 → a / b = a * (1 / b)
axiom mul_inv        (a   : R) : a ≠ 0 → a * (1 / a) = 1

/-! ### Order axioms -/

axiom lt_irrefl_ax (a   : R) : ¬ a < a
axiom lt_trans_ax  {a b c : R} : a < b → b < c → a < c
axiom lt_total     (a b : R) : a < b ∨ a = b ∨ b < a
axiom le_iff_lt_or_eq (a b : R) : a ≤ b ↔ a < b ∨ a = b

axiom add_lt_add_left  {a b : R} (h : a < b) (c : R) : c + a < c + b
axiom mul_pos          {a b : R} : 0 < a → 0 < b → 0 < a * b
axiom zero_lt_one_ax   : (0 : R) < 1

/-! ### Archimedean + completeness -/

axiom natCast : Nat → R

axiom natCast_zero : natCast 0 = 0
axiom natCast_succ (n : Nat) : natCast (n + 1) = natCast n + 1

axiom archimedean (x : R) : ∃ n : Nat, x < natCast n

def BoundedAbove (p : R → Prop) : Prop :=
  ∃ M : R, ∀ x : R, p x → x ≤ M

axiom sup_exists
    (p : R → Prop) (h_nonempty : ∃ x, p x) (h_bound : BoundedAbove p) :
    ∃ s : R,
      (∀ x, p x → x ≤ s) ∧
      (∀ s', (∀ x, p x → x ≤ s') → s ≤ s')

/-! ## Derived definitions -/

noncomputable def abs (x : R) : R := if 0 ≤ x then x else -x
noncomputable def min (a b : R) : R := if a ≤ b then a else b
noncomputable def max (a b : R) : R := if a ≤ b then b else a

/-! ## Basic derived lemmas -/

theorem zero_add (a : R) : 0 + a = a := by
  rw [add_comm]; exact add_zero a

theorem neg_add_self (a : R) : -a + a = 0 := by
  rw [add_comm]; exact add_neg a

theorem one_mul_thm (a : R) : 1 * a = a := by
  rw [mul_comm]; exact mul_one_ax a

theorem mul_zero (a : R) : a * 0 = 0 := by
  have h : a * 0 = a * 0 + a * 0 := by
    have step : a * (0 + 0) = a * 0 + a * 0 := mul_distrib a 0 0
    rw [add_zero] at step
    exact step
  have h2 : a * 0 + (-(a * 0)) = (a * 0 + a * 0) + (-(a * 0)) := by
    rw [← h]
  rw [add_neg, add_assoc, add_neg, add_zero] at h2
  exact h2.symm

theorem zero_mul (a : R) : 0 * a = 0 := by
  rw [mul_comm]; exact mul_zero a

theorem ne_of_lt {a b : R} (h : a < b) : a ≠ b := by
  intro heq; rw [heq] at h; exact lt_irrefl_ax b h

theorem ne_of_gt {a b : R} (h : b < a) : a ≠ b := by
  intro heq; rw [heq] at h; exact lt_irrefl_ax b h

theorem one_pos : (0 : R) < 1 := zero_lt_one_ax

theorem one_ne_zero : (1 : R) ≠ 0 := fun h => zero_ne_one_ax h.symm

theorem abs_zero : abs (0 : R) = 0 := by
  unfold abs
  have h : (0 : R) ≤ 0 := (le_iff_lt_or_eq 0 0).mpr (Or.inr rfl)
  simp [h]

theorem abs_one : abs (1 : R) = 1 := by
  unfold abs
  have h : (0 : R) ≤ 1 := (le_iff_lt_or_eq 0 1).mpr (Or.inl zero_lt_one_ax)
  simp [h]

theorem min_self (a : R) : min a a = a := by
  unfold min
  have h : a ≤ a := (le_iff_lt_or_eq a a).mpr (Or.inr rfl)
  simp [h]

theorem max_self (a : R) : max a a = a := by
  unfold max
  have h : a ≤ a := (le_iff_lt_or_eq a a).mpr (Or.inr rfl)
  simp [h]

end R

end MachLib
