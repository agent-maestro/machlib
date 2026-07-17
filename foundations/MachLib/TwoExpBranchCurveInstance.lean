import MachLib.BivariateDeriv
import MachLib.TwoExpCurveCount
import MachLib.Log
import MachLib.Linarith

/-!
# The branch curve `eˣ+eʸ=c`, via the interval-localized IFT axiom (Gate 2d, §9.1 closed)

`multivariate-khovanskii-chainN-scoping.md §9.1` found that `eˣ+eʸ=c` — the most natural "two independent
exponentials" curve — has no GLOBAL solution branch (`yc(x) = log(c−eˣ)` is only real for `x < log c`), so
the existing `hasDerivAt_implicit` (needing `∀s:Real, f s (yc s) = 0`) can never be discharged for it. This
was left as a genuine, deliberate gap — closing it needs a new axiom, not another instance from existing
pieces, and every step in this arc up to here had added zero new axioms.

`BivariateDeriv.lean` now has `hasDerivAt_implicit_local` — the standard IMPLICIT FUNCTION THEOREM is
inherently local (the derivative at `x` depends only on `f`'s behavior near `x`); the new axiom asks for
the curve identity on an open interval `(p,q) ∋ x` instead of globally. Strictly weaker than the existing
axiom (a global witness restricts to a local one on any `(p,q)`), added alongside it rather than replacing
it. This file is the first user: builds `yc(x) = log(c−eˣ)` on `(−∞, log c)`, and — reusing
`hasDerivAt2_exp_sum` (already in `BivariateDeriv.lean`, built as a "framework validation" example that had
never been paired with a genuine curve) — closes a real curve-intersection count via
`khovanskii_rolle_count_curve_local`.
-/

namespace MachLib
namespace MultiVarMod
namespace TwoExp

open MachLib.Real

/-! ## Part 0: `khovanskii_rolle_count_curve`, interval-localized -/

/-- **`khovanskii_rolle_count_curve`, interval-localized.** Same shape, built from
`curve_tangent_and_chain_local` instead — the curve identity `hid` only needs to hold on `(p,q)`, as long as
the counting interval `(a,b)` sits inside it (`hpa : p ≤ a`, `hbq : b ≤ q`). -/
theorem khovanskii_rolle_count_curve_local
    (f g : Real → Real → Real) (fx fy gx gy yc : Real → Real) (a b p q : Real)
    (hab : a < b) (hpa : p ≤ a) (hbq : b ≤ q)
    (hf2 : ∀ z : Real, a < z → z < b → HasDerivAt2 f (fx z) (fy z) z (yc z))
    (hg2 : ∀ z : Real, a < z → z < b → HasDerivAt2 g (gx z) (gy z) z (yc z))
    (hfy : ∀ z : Real, a < z → z < b → fy z ≠ 0)
    (hid : ∀ s : Real, p < s → s < q → f s (yc s) = 0)
    (N : Nat)
    (hJ_bound : ∀ zeros_J : List Real, zeros_J.Nodup →
        (∀ z ∈ zeros_J, a < z ∧ z < b ∧ fx z * gy z - fy z * gx z = 0) →
        zeros_J.length ≤ N) :
    ∀ zeros_g : List Real, zeros_g.Nodup →
      (∀ z ∈ zeros_g, a < z ∧ z < b ∧ g z (yc z) = 0) →
      zeros_g.length ≤ N + 1 := by
  apply khovanskii_rolle_count
    (fun s => g s (yc s)) (fun z => -fx z / fy z) fx fy gx gy a b hab
  · intro z hza hzb
    obtain ⟨_, _, hchain⟩ := curve_tangent_and_chain_local f g (fx z) (fy z) (gx z) (gy z) yc z p q
      (lt_of_le_of_lt hpa hza) (lt_of_lt_of_le hzb hbq)
      (hf2 z hza hzb) (hg2 z hza hzb) (hfy z hza hzb) hid
    rw [show gx z + gy z * (-fx z / fy z) = gx z * 1 + gy z * (-fx z / fy z) from by rw [mul_one_ax]]
    exact hchain
  · intro z hza hzb
    exact (curve_tangent_and_chain_local f g (fx z) (fy z) (gx z) (gy z) yc z p q
      (lt_of_le_of_lt hpa hza) (lt_of_lt_of_le hzb hbq)
      (hf2 z hza hzb) (hg2 z hza hzb) (hfy z hza hzb) hid).2.1
  · exact hJ_bound

/-! ## Part 1: the branch curve `yc(x) = log(c−eˣ)`, real only for `x < log c` -/

noncomputable def branchYc (c x : Real) : Real := log (c - exp x)

theorem branch_pos (c x : Real) (hxc : x < log c) (hc : 0 < c) : 0 < c - exp x := by
  have h1 : exp x < exp (log c) := exp_lt hxc
  have h2 : exp (log c) = c := exp_log hc
  have h3 : exp x < c := by rw [← h2]; exact h1
  exact sub_pos_of_lt h3

theorem branch_exp_yc (c x : Real) (hxc : x < log c) (hc : 0 < c) :
    exp (branchYc c x) = c - exp x :=
  exp_log (branch_pos c x hxc hc)

theorem branch_curve_id (c : Real) (hc : 0 < c) (s : Real) (hs : s < log c) :
    exp s + exp (branchYc c s) - c = 0 := by
  rw [branch_exp_yc c s hs hc]; mach_ring

/-! ## Part 2: `f(a,b) = eᵃ+eᵇ−c` (reusing `hasDerivAt2_exp_sum`) and `g(a,b) = eᵃ−eᵇ` -/

noncomputable def branchG : Real → Real → Real := fun a b => exp a - exp b

theorem hasDerivAt2_branchG (x y : Real) : HasDerivAt2 branchG (exp x) (-exp y) x y := by
  have hExpA : HasDerivAt2 (fun a _ => exp a) (exp x * 1) (exp x * 0) x y :=
    HasDerivAt2_scomp exp (exp x) (fun a _ => a) 1 0 x y (HasDerivAt_exp x) (HasDerivAt2_projX x y)
  have hExpB : HasDerivAt2 (fun _ b => exp b) (exp y * 0) (exp y * 1) x y :=
    HasDerivAt2_scomp exp (exp y) (fun _ b => b) 0 1 x y (HasDerivAt_exp y) (HasDerivAt2_projY x y)
  have hSub := HasDerivAt2_sub (fun a _ => exp a) (fun _ b => exp b) _ _ _ _ x y hExpA hExpB
  have e1 : exp x * 1 - exp y * 0 = exp x := by mach_ring
  have e2 : exp x * 0 - exp y * 1 = -exp y := by mach_ring
  rw [e1, e2] at hSub
  exact hSub

/-! ## Part 3: the Jacobian never vanishes on the branch domain -/

theorem branchG_f_sum (d x y : Real) : HasDerivAt2 (fun a b => exp a + exp b - d) (exp x) (exp y) x y :=
  hasDerivAt2_exp_sum d x y

/-- **The Jacobian `fx·gy − fy·gx = -2eᶻ(c−eᶻ)` is strictly negative — never zero — on the whole branch
domain `z < log c`.** Hand-derived and checked against SymPy before Lean. -/
theorem branch_jacobian_neg (c z : Real) (hzc : z < log c) (hc : 0 < c) :
    exp z * (-(c - exp z)) - (c - exp z) * exp z < 0 := by
  have h1 : 0 < exp z := exp_pos z
  have h2 : 0 < c - exp z := branch_pos c z hzc hc
  have heq : exp z * (-(c - exp z)) - (c - exp z) * exp z = -(exp z * (c - exp z) + (c - exp z) * exp z) := by
    mach_ring
  rw [heq]
  have hp : 0 < exp z * (c - exp z) + (c - exp z) * exp z := by
    have := add_pos (mul_pos h1 h2) (mul_pos h2 h1)
    exact this
  exact neg_neg_of_pos hp

/-! ## Part 4: the capstone — at most one intersection of `{eˣ+eʸ=c}` and `{eˣ=eʸ}` on the branch -/

/-- **The branch curve `eˣ+eʸ=c` closes**: `{f=0}` (this curve) and `{g=0}` (`eˣ=eʸ`, i.e. `x=y`) meet at
most once on any interval `(a,b) ⊆ (−∞, log c)`. Genuinely achieved (`x = log(c/2)` is the unique solution)
— the general bound is not vacuous here, it is TIGHT. This is the first result in the whole
multivariate-Khovanskii arc built on a curve with no global solution branch. -/
theorem branch_intersection_le_one (c a b : Real) (hc : 0 < c) (hab : a < b) (hbc : b < log c) :
    ∀ zeros_g : List Real, zeros_g.Nodup →
      (∀ z ∈ zeros_g, a < z ∧ z < b ∧ branchG z (branchYc c z) = 0) →
      zeros_g.length ≤ 1 := by
  have hf2 : ∀ z : Real, a < z → z < b →
      HasDerivAt2 (fun a b => exp a + exp b - c) (exp z) (c - exp z) z (branchYc c z) := by
    intro z _ hzb
    rw [← branch_exp_yc c z (lt_trans_ax hzb hbc) hc]
    exact branchG_f_sum c z (branchYc c z)
  have hg2 : ∀ z : Real, a < z → z < b →
      HasDerivAt2 branchG (exp z) (-(c - exp z)) z (branchYc c z) := by
    intro z _ hzb
    rw [← branch_exp_yc c z (lt_trans_ax hzb hbc) hc]
    exact hasDerivAt2_branchG z (branchYc c z)
  have hfyne : ∀ z : Real, a < z → z < b → (c - exp z) ≠ 0 := by
    intro z _ hzb
    exact ne_of_gt (branch_pos c z (lt_trans_ax hzb hbc) hc)
  have hid : ∀ s : Real, a - 1 < s → s < log c → exp s + exp (branchYc c s) - c = 0 := by
    intro s _ hslc
    exact branch_curve_id c hc s hslc
  have hJb : ∀ zeros_J : List Real, zeros_J.Nodup →
      (∀ z ∈ zeros_J, a < z ∧ z < b ∧
        exp z * (-(c - exp z)) - (c - exp z) * exp z = 0) →
      zeros_J.length ≤ 0 := by
    intro zeros_J hnd hz
    rcases zeros_J with _ | ⟨z0, rest⟩
    · exact Nat.le_refl 0
    · exfalso
      obtain ⟨_, hz0b, hJ0⟩ := hz z0 (List.mem_cons_self z0 rest)
      have hlt := branch_jacobian_neg c z0 (lt_trans_ax hz0b hbc) hc
      rw [hJ0] at hlt
      exact lt_irrefl_ax 0 hlt
  have hres := khovanskii_rolle_count_curve_local
    (fun a b => exp a + exp b - c) branchG (fun z => exp z) (fun z => c - exp z)
    (fun z => exp z) (fun z => -(c - exp z)) (branchYc c) a b (a - 1) (log c) hab
    (sub_le_self (le_of_lt zero_lt_one_ax)) (le_of_lt hbc) hf2 hg2 hfyne hid 0 hJb
  intro zeros_g hnd hz
  simpa using hres zeros_g hnd hz

end TwoExp
end MultiVarMod
end MachLib
