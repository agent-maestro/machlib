import MachLib.SinNotInEML
import MachLib.EMLAsymptoticClass
import MachLib.EMLAsymptoticBound
import MachLib.Forge

/-!
# The witness-finding residual's `T1` cannot have depth ≤ 1

Part of the 2026-07-19 continuation of `EML_WITNESS_FINDING_DECISION_2026_07_15.md`'s
Option D. The residual sub-case needs `T1` BOUNDED (above) and NON-CONSTANT. This file
shows: if `T1 = eml A B` with `A` and `B` both leaves (`const`/`var`, i.e. `T1` has depth
exactly 1), `T1` is either globally CONSTANT or UNBOUNDED ABOVE — never both bounded and
non-constant. So the residual's smallest possible `T1` has depth ≥ 2, not depth 1. Proven
from existing MachLib lemmas only — no new axioms.
-/

namespace MachLib
namespace Real

/-- `f` is unbounded above: for every `N`, some point exceeds it. -/
def UnboundedAbove (f : Real → Real) : Prop := ∀ N : Real, ∃ x, N < f x

/-! ### Small arithmetic helpers (no `linarith` here — MachLib is Mathlib-free) -/

theorem lt_sub_of_add_lt {N c E : Real} (h : N + c < E) : N < E - c := by
  have h2 := add_lt_add_left h (-c)
  have e1 : -c + (N + c) = N := by mach_ring
  have e2 : -c + E = E - c := by mach_ring
  rw [e1, e2] at h2
  exact h2

theorem lt_succ_self (N : Real) : N < N + 1 := by
  have h := add_lt_add_left zero_lt_one_ax N
  have e : N + 0 = N := by mach_ring
  rw [e] at h
  exact h

/-- `a<b → c<d → a+c<b+d`. A generic fact that already exists as
`MachLib.MultiVarMod.TwoExp.add_lt_add`, but re-derived locally (from `add_lt_add_left` +
`mach_ring` + `lt_trans_ax`, already in scope) rather than pulling in that unrelated
namespace for one trivial lemma. -/
theorem add_lt_add {a b c d : Real} (h1 : a < b) (h2 : c < d) : a + c < b + d := by
  have hstep1 := add_lt_add_left h2 a
  have hstep2 := add_lt_add_left h1 d
  have e1 : d + a = a + d := by mach_ring
  have e2 : d + b = b + d := by mach_ring
  rw [e1, e2] at hstep2
  exact lt_trans_ax hstep1 hstep2

/-- For every `N`, some `x ≥ 1` exceeds it. Avoids `if`-terms entirely by case-splitting
on `lt_total` directly, matching this codebase's own idiom (several files each locally
re-derive a `le_total`-style split rather than share one canonical version). -/
theorem exists_ge_one_gt (N : Real) : ∃ x : Real, 1 ≤ x ∧ N < x := by
  rcases lt_total N 0 with hN | hN | hN
  · exact ⟨1, le_refl 1, lt_trans_ax hN zero_lt_one_ax⟩
  · exact ⟨1, le_refl 1, hN ▸ zero_lt_one_ax⟩
  · have h1 := add_lt_add_left hN 1
    have e1 : (1 : Real) + 0 = 1 := by mach_ring
    have e2 : (1 : Real) + N = N + 1 := by mach_ring
    rw [e1, e2] at h1
    exact ⟨N + 1, le_of_lt h1, lt_succ_self N⟩

/-- Case 4: `A = var`, `B = var`. `eml var var` is unbounded above. -/
theorem depth1_var_var_unbounded :
    UnboundedAbove (EMLTree.eval (EMLTree.eml .var .var)) := by
  intro N
  obtain ⟨x, hx1, hNx⟩ := exists_ge_one_gt N
  refine ⟨x, ?_⟩
  show N < Real.exp x - Real.log x
  have hloglt : Real.log x ≤ x := MachLib.EMLTree.log_le_id_at_one x hx1
  have hexp : (1 + 1) * x < Real.exp x := exp_gt_two_x_at_one x hx1
  have hxx_eq : x + x = (1 + 1) * x := by mach_ring
  have hxx_lt_exp : x + x < Real.exp x := by rw [hxx_eq]; exact hexp
  have hchain : N + Real.log x < Real.exp x := by
    rcases (le_iff_lt_or_eq _ _).mp hloglt with h | h
    · exact lt_trans_ax (add_lt_add hNx h) hxx_lt_exp
    · rw [h]
      have h1 := add_lt_add_left hNx x
      have h2 : x + N = N + x := by mach_ring
      rw [h2] at h1
      exact lt_trans_ax h1 hxx_lt_exp
  exact lt_sub_of_add_lt hchain

/-! ### The four leaf/leaf cases -/

/-- Case 1: both leaves constant. `eml (const a) (const b)` is globally constant. -/
theorem depth1_const_const_is_const (a b : Real) :
    ∀ x, (EMLTree.eml (.const a) (.const b)).eval x = Real.exp a - Real.log b := by
  intro x
  rfl

/-- Case 2: `A = var`, `B = const b`. `eml var (const b)` is unbounded above. -/
theorem depth1_var_const_unbounded (b : Real) :
    UnboundedAbove (EMLTree.eval (EMLTree.eml .var (.const b))) := by
  intro N
  refine ⟨N + Real.log b, ?_⟩
  show N < Real.exp (N + Real.log b) - Real.log b
  exact lt_sub_of_add_lt (exp_grows_strictly_thm (N + Real.log b))

/-- Case 3: `A = const a`, `B = var`. `eml (const a) var` is unbounded above. -/
theorem depth1_const_var_unbounded (a : Real) :
    UnboundedAbove (EMLTree.eval (EMLTree.eml (.const a) .var)) := by
  intro N
  refine ⟨Real.exp (Real.exp a - N - 1), ?_⟩
  show N < Real.exp a - Real.log (Real.exp (Real.exp a - N - 1))
  rw [log_exp]
  have e : Real.exp a - (Real.exp a - N - 1) = N + 1 := by mach_ring
  rw [e]
  exact lt_succ_self N

/-- **Combined**: any depth-1 `eml`-tree (both children leaves) is either globally
constant or unbounded above — never both bounded and non-constant. So the witness-finding
residual's `T1` (which must be both bounded and non-constant) cannot have depth 1; its
smallest possible depth is 2. -/
theorem depth1_eml_const_or_unbounded (A B : EMLTree)
    (hA : A.depth = 0) (hB : B.depth = 0) :
    (∃ c, ∀ x, (EMLTree.eml A B).eval x = c) ∨ UnboundedAbove (EMLTree.eml A B).eval := by
  match A, hA with
  | .const a, _ =>
    match B, hB with
    | .const b, _ => exact Or.inl ⟨Real.exp a - Real.log b, depth1_const_const_is_const a b⟩
    | .var, _ => exact Or.inr (depth1_const_var_unbounded a)
    | .eml _ _, hB' => simp [EMLTree.depth] at hB'
  | .var, _ =>
    match B, hB with
    | .const b, _ => exact Or.inr (depth1_var_const_unbounded b)
    | .var, _ => exact Or.inr depth1_var_var_unbounded
    | .eml _ _, hB' => simp [EMLTree.depth] at hB'
  | .eml _ _, hA' => simp [EMLTree.depth] at hA'

end Real
end MachLib
