import MachLib.EMLPfaffianValidOnCrossingObstruction
import MachLib.WitnessResidualNonMonotonic
import MachLib.WitnessResidualSimpleRightChildren

/-! # Completing the positive-crossing instance: a genuine, fully-verified open-class member the
`EMLPfaffianValidOn` route provably cannot reach

`EMLPfaffianValidOnCrossingObstruction.lean` proved `EMLPfaffianValidOn
(expWrappedNonMonotonicWitnessC concreteC) 0 b` is FALSE for `b` past the crossing point — a
negative, structural result about the closure route, deliberately NOT accompanied by a
verification that `expWrappedNonMonotonicWitnessC concreteC` actually belongs to the residual's
open classification (bounded both directions, non-constant, non-`RightChildrenSimplePositive`,
non-monotonic). That verification — checked only numerically last round — is completed here, by
mirroring `WitnessResidualNonMonotonic.lean` / `WitnessResidualExpWrappedNonMonotonic.lean`'s
exact technique with the crossing constant `1+1` replaced by `concreteC := exp(exp 1)`.

**The one genuinely new piece.** Every step transfers directly EXCEPT the boundedness proof's
`two_mul_eq_add_self` trick, which was specific to the crossing constant literally being `1+1`
(`exp(exp x) = (1+1)·exp(D)` collapsing to `exp(D)+exp(D)`). For general `concreteC` this doesn't
apply — the fix: `concreteC > 1+1` (proven cheaply via `exp_gt_one_plus_self` applied twice, at
`x=1` and `x=exp 1`) gives `1 < concreteC - 1`, hence (via `mul_lt_mul_of_pos_right`)
`exp(D) < (concreteC-1)·exp(D)`, which plays the exact same role the doubling trick did — the
rest of the boundedness chain is untouched.

**The result.** `expWrappedNonMonotonicWitnessC concreteC` is a fully verified, concrete member
of the open classification (`concreteC_expwrapped_exists`) for which
`EMLPfaffianValidOnCrossingObstruction.lean`'s `concreteC_validon_false` ALSO holds — the first
tree in this whole arc confirmed to be BOTH a genuine open-class member AND resistant to the one
closure technique that worked for the negative-crossing case. This does NOT prove the tree is a
real counterexample to the axiom (other techniques — domain-splitting around the crossing,
mirroring the arc's much earlier `EMLZeroCrossingDomainSplit.lean` work, or a genuinely new
branch-switching chain construction — remain unexplored) — it sharpens the target for whoever
attempts them next from "a numerically-plausible instance" to "a formally-verified one". -/

namespace MachLib
namespace Real

open EMLTree

theorem concreteC_log_eq : Real.log concreteC = Real.exp 1 := by
  show Real.log (Real.exp (Real.exp 1)) = Real.exp 1
  exact log_exp _

theorem concreteC_log_pos : 0 < Real.log concreteC := by
  rw [concreteC_log_eq]; exact Real.exp_pos _

theorem concreteC_pos : 0 < concreteC := Real.exp_pos _

/-- `concreteC > 1+1` — the fact that replaces `two_mul_eq_add_self` in the boundedness proof.
Chain: `1+1 < exp 1` (`exp_gt_one_plus_self`), `exp 1 < 1 + exp 1 < exp(exp 1) = concreteC`
(`exp_gt_one_plus_self` again, at `x = exp 1`). -/
theorem concreteC_gt_two : (1 + 1 : Real) < concreteC := by
  show (1 + 1 : Real) < Real.exp (Real.exp 1)
  have h1 : (1 + 1 : Real) < Real.exp 1 := exp_gt_one_plus_self 1 zero_lt_one_ax
  have h2 : 1 + Real.exp 1 < Real.exp (Real.exp 1) :=
    exp_gt_one_plus_self (Real.exp 1) (Real.exp_pos 1)
  have h3 : Real.exp 1 < 1 + Real.exp 1 := by
    have h := add_lt_add_left zero_lt_one_ax (Real.exp 1)
    have e : Real.exp 1 + 0 = Real.exp 1 := add_zero _
    rw [e] at h
    rwa [add_comm (Real.exp 1) 1] at h
  exact lt_trans_ax h1 (lt_trans_ax h3 h2)

theorem nonMonotonicWitnessC_eval_clamped {x : Real} (hx : x ≤ Real.log (Real.log concreteC)) :
    (nonMonotonicWitnessC concreteC).eval x = 0 := by
  have hlog2pos := concreteC_log_pos
  have hDnonpos : Real.exp x - Real.log concreteC ≤ 0 := by
    rcases (le_iff_lt_or_eq x (Real.log (Real.log concreteC))).mp hx with h | h
    · have hexp : Real.exp x < Real.exp (Real.log (Real.log concreteC)) := Real.exp_lt h
      have hexp0 : Real.exp (Real.log (Real.log concreteC)) = Real.log concreteC :=
        Real.exp_log hlog2pos
      rw [hexp0] at hexp
      have e := sub_lt_sub_right_of_lt (r := Real.log concreteC) hexp
      have e2 : Real.log concreteC - Real.log concreteC = 0 := by mach_ring
      rw [e2] at e
      exact le_of_lt e
    · rw [h]
      have hexp0 : Real.exp (Real.log (Real.log concreteC)) = Real.log concreteC :=
        Real.exp_log hlog2pos
      have e : Real.exp (Real.log (Real.log concreteC)) - Real.log concreteC = 0 := by
        rw [hexp0]; mach_ring
      exact le_of_eq e
  show Real.exp x -
      Real.log (Real.exp ((EMLTree.eml EMLTree.var (EMLTree.const 1)).eval x)
        - Real.log ((EMLTree.eml EMLTree.var (EMLTree.const concreteC)).eval x)) = 0
  have hC : (EMLTree.eml EMLTree.var (EMLTree.const 1)).eval x = Real.exp x - Real.log 1 := rfl
  have hD : (EMLTree.eml EMLTree.var (EMLTree.const concreteC)).eval x
      = Real.exp x - Real.log concreteC := rfl
  rw [hC, hD, log_one]
  have e1 : Real.exp x - 0 = Real.exp x := sub_zero _
  rw [e1, Real.log_nonpos hDnonpos, sub_zero, log_exp]
  mach_ring

theorem nonMonotonicWitnessC_eval_real {x : Real} (hx : Real.log (Real.log concreteC) < x) :
    (nonMonotonicWitnessC concreteC).eval x
      = Real.exp x
        - Real.log (Real.exp (Real.exp x) - Real.log (Real.exp x - Real.log concreteC)) := by
  show Real.exp x -
      Real.log (Real.exp ((EMLTree.eml EMLTree.var (EMLTree.const 1)).eval x)
        - Real.log ((EMLTree.eml EMLTree.var (EMLTree.const concreteC)).eval x)) = _
  have hC : (EMLTree.eml EMLTree.var (EMLTree.const 1)).eval x = Real.exp x - Real.log 1 := rfl
  have hD : (EMLTree.eml EMLTree.var (EMLTree.const concreteC)).eval x
      = Real.exp x - Real.log concreteC := rfl
  rw [hC, hD, log_one]
  have e1 : Real.exp x - 0 = Real.exp x := sub_zero _
  rw [e1]

theorem nonMonotonicWitnessC_Dpos {x : Real} (hx : Real.log (Real.log concreteC) < x) :
    0 < Real.exp x - Real.log concreteC := by
  have hlog2pos := concreteC_log_pos
  have hexp0 : Real.exp (Real.log (Real.log concreteC)) = Real.log concreteC :=
    Real.exp_log hlog2pos
  have hexp : Real.exp (Real.log (Real.log concreteC)) < Real.exp x := Real.exp_lt hx
  rw [hexp0] at hexp
  have e := sub_lt_sub_right_of_lt (r := Real.log concreteC) hexp
  have e2 : Real.log concreteC - Real.log concreteC = 0 := by mach_ring
  rwa [e2] at e

theorem nonMonotonicWitnessC_Bpos {x : Real} (hx : Real.log (Real.log concreteC) < x) :
    0 < Real.exp (Real.exp x) - Real.log (Real.exp x - Real.log concreteC) := by
  have hDpos := nonMonotonicWitnessC_Dpos hx
  have hlog2pos := concreteC_log_pos
  have hDltExp : Real.exp x - Real.log concreteC < Real.exp x := by
    have h := add_lt_add_left (neg_neg_of_pos hlog2pos) (Real.exp x)
    have e1 : Real.exp x + -Real.log concreteC = Real.exp x - Real.log concreteC := by mach_ring
    have e2 : Real.exp x + 0 = Real.exp x := add_zero _
    rwa [e1, e2] at h
  have hlogD : Real.log (Real.exp x - Real.log concreteC) < x := by
    have h := log_lt_log hDpos hDltExp
    rwa [log_exp] at h
  have hx_lt_expx : x < Real.exp x := exp_grows_strictly_thm x
  have hexpx_lt_expexpx : Real.exp x < Real.exp (Real.exp x) := exp_grows_strictly_thm (Real.exp x)
  have hchain : Real.log (Real.exp x - Real.log concreteC) < Real.exp (Real.exp x) :=
    lt_trans_ax hlogD (lt_trans_ax hx_lt_expx hexpx_lt_expexpx)
  have e := sub_lt_sub_right_of_lt (r := Real.log (Real.exp x - Real.log concreteC)) hchain
  have e2 : Real.log (Real.exp x - Real.log concreteC) - Real.log (Real.exp x - Real.log concreteC)
      = 0 := by mach_ring
  rwa [e2] at e

theorem nonMonotonicWitnessC_pos_of_gt_one {x : Real} (hx : Real.log (Real.log concreteC) < x)
    (hv : 1 < Real.exp x - Real.log concreteC) :
    0 < (nonMonotonicWitnessC concreteC).eval x := by
  rw [nonMonotonicWitnessC_eval_real hx]
  have hBpos := nonMonotonicWitnessC_Bpos hx
  have hvpos : 0 < Real.log (Real.exp x - Real.log concreteC) := log_pos_of_gt_one hv
  have hBlt : Real.exp (Real.exp x) - Real.log (Real.exp x - Real.log concreteC)
      < Real.exp (Real.exp x) := by
    have h := add_lt_add_left (neg_neg_of_pos hvpos) (Real.exp (Real.exp x))
    have e1 : Real.exp (Real.exp x) + -Real.log (Real.exp x - Real.log concreteC)
        = Real.exp (Real.exp x) - Real.log (Real.exp x - Real.log concreteC) := by mach_ring
    have e2 : Real.exp (Real.exp x) + 0 = Real.exp (Real.exp x) := add_zero _
    rwa [e1, e2] at h
  have hlogB := log_lt_log hBpos hBlt
  rw [log_exp] at hlogB
  have e := sub_lt_sub_right_of_lt (r := Real.log (Real.exp (Real.exp x)
    - Real.log (Real.exp x - Real.log concreteC))) hlogB
  have e2 : Real.log (Real.exp (Real.exp x) - Real.log (Real.exp x - Real.log concreteC))
      - Real.log (Real.exp (Real.exp x) - Real.log (Real.exp x - Real.log concreteC)) = 0 := by
    mach_ring
  rwa [e2] at e

theorem nonMonotonicWitnessC_neg_of_lt_one {x : Real} (hx : Real.log (Real.log concreteC) < x)
    (hv0 : 0 < Real.exp x - Real.log concreteC) (hv1 : Real.exp x - Real.log concreteC < 1) :
    (nonMonotonicWitnessC concreteC).eval x < 0 := by
  rw [nonMonotonicWitnessC_eval_real hx]
  have hBpos := nonMonotonicWitnessC_Bpos hx
  have hvneg : Real.log (Real.exp x - Real.log concreteC) < 0 := log_neg_of_lt_one hv0 hv1
  have hBgt : Real.exp (Real.exp x)
      < Real.exp (Real.exp x) - Real.log (Real.exp x - Real.log concreteC) := by
    have h := sub_lt_sub_left_local (Real.exp (Real.exp x)) hvneg
    have e : Real.exp (Real.exp x) - 0 = Real.exp (Real.exp x) := sub_zero _
    rwa [e] at h
  have hlogB := log_lt_log (Real.exp_pos _) hBgt
  rw [log_exp] at hlogB
  have e := sub_lt_sub_right_of_lt (r := Real.log (Real.exp (Real.exp x)
    - Real.log (Real.exp x - Real.log concreteC))) hlogB
  have e2 : Real.log (Real.exp (Real.exp x) - Real.log (Real.exp x - Real.log concreteC))
      - Real.log (Real.exp (Real.exp x) - Real.log (Real.exp x - Real.log concreteC)) = 0 := by
    mach_ring
  rwa [e2] at e

/-- **Uniform upper bound**, the one genuinely new piece: mirrors
`nonMonotonicWitness_upper_bound` exactly, except the doubling trick (`two_mul_eq_add_self`,
specific to the crossing constant being LITERALLY `1+1`) is replaced by `concreteC_gt_two` +
`mul_lt_mul_of_pos_right` to get `exp(D) < (concreteC-1)·exp(D)` — the rest of the chain is
untouched. -/
theorem nonMonotonicWitnessC_upper_bound {x : Real} (hx : Real.log (Real.log concreteC) < x) :
    (nonMonotonicWitnessC concreteC).eval x < Real.log concreteC := by
  rw [nonMonotonicWitnessC_eval_real hx]
  have hDpos := nonMonotonicWitnessC_Dpos hx
  have hA : Real.log (Real.exp x - Real.log concreteC) < Real.exp x - Real.log concreteC :=
    log_lt_self_of_pos _ hDpos
  have hB : Real.exp (Real.exp x) - (Real.exp x - Real.log concreteC)
      < Real.exp (Real.exp x) - Real.log (Real.exp x - Real.log concreteC) :=
    sub_lt_sub_left_local _ hA
  have hC1 : Real.log concreteC + (Real.exp x - Real.log concreteC) = Real.exp x :=
    add_sub_cancel_left_local2 (Real.exp x) (Real.log concreteC)
  have hC2 : Real.exp (Real.exp x)
      = Real.exp (Real.log concreteC) * Real.exp (Real.exp x - Real.log concreteC) := by
    have step := exp_add (Real.log concreteC) (Real.exp x - Real.log concreteC)
    rwa [hC1] at step
  have hC3 : Real.exp (Real.log concreteC) = concreteC := Real.exp_log (Real.exp_pos _)
  rw [hC3] at hC2
  have hcm1gt1 : (1 : Real) < concreteC - 1 := by
    have h := sub_lt_sub_right_of_lt (r := (1 : Real)) concreteC_gt_two
    have e : (1 : Real) + 1 - 1 = 1 := by mach_ring
    rwa [e] at h
  have hEDpos : (0 : Real) < Real.exp (Real.exp x - Real.log concreteC) := Real.exp_pos _
  have hstep3 : Real.exp (Real.exp x - Real.log concreteC)
      < (concreteC - 1) * Real.exp (Real.exp x - Real.log concreteC) := by
    have h := mul_lt_mul_of_pos_right hcm1gt1 hEDpos
    rwa [one_mul_thm] at h
  have hE : Real.exp x - Real.log concreteC < Real.exp (Real.exp x - Real.log concreteC) :=
    exp_grows_strictly_thm (Real.exp x - Real.log concreteC)
  have hDlt : Real.exp x - Real.log concreteC
      < (concreteC - 1) * Real.exp (Real.exp x - Real.log concreteC) :=
    lt_trans_ax hE hstep3
  have hsum := add_lt_add_left hDlt (Real.exp (Real.exp x - Real.log concreteC))
  have ealg1 : Real.exp (Real.exp x - Real.log concreteC)
      + (concreteC - 1) * Real.exp (Real.exp x - Real.log concreteC)
      = concreteC * Real.exp (Real.exp x - Real.log concreteC) := by
    have h1 : (concreteC - 1) * Real.exp (Real.exp x - Real.log concreteC)
        = concreteC * Real.exp (Real.exp x - Real.log concreteC)
          - Real.exp (Real.exp x - Real.log concreteC) := by mach_ring
    rw [h1]
    exact add_sub_cancel_left_local2 _ _
  rw [ealg1] at hsum
  have hG : Real.exp (Real.exp x - Real.log concreteC)
      < Real.exp (Real.exp x) - (Real.exp x - Real.log concreteC) := by
    rw [hC2]
    have h := sub_lt_sub_right_of_lt (r := Real.exp x - Real.log concreteC) hsum
    have e1 : Real.exp (Real.exp x - Real.log concreteC)
        + (Real.exp x - Real.log concreteC) - (Real.exp x - Real.log concreteC)
        = Real.exp (Real.exp x - Real.log concreteC) := by mach_ring
    rwa [e1] at h
  have hH : Real.exp (Real.exp x - Real.log concreteC)
      < Real.exp (Real.exp x) - Real.log (Real.exp x - Real.log concreteC) :=
    lt_trans_ax hG hB
  have hI : Real.exp x - Real.log concreteC
      < Real.log (Real.exp (Real.exp x) - Real.log (Real.exp x - Real.log concreteC)) := by
    have h := log_lt_log (Real.exp_pos (Real.exp x - Real.log concreteC)) hH
    rwa [log_exp] at h
  have hJ : Real.exp x
        - Real.log (Real.exp (Real.exp x) - Real.log (Real.exp x - Real.log concreteC))
      < Real.exp x - (Real.exp x - Real.log concreteC) :=
    sub_lt_sub_left_local _ hI
  have hK : Real.exp x - (Real.exp x - Real.log concreteC) = Real.log concreteC :=
    sub_self_sub_local (Real.exp x) (Real.log concreteC)
  rwa [hK] at hJ

noncomputable def nonMonotonicWitnessC_xb : Real :=
  Real.log (Real.log concreteC + 1 / (1 + 1))

noncomputable def nonMonotonicWitnessC_xc : Real := Real.log (Real.log concreteC + (1 + 1))

theorem nonMonotonicWitnessC_xb_exp :
    Real.exp nonMonotonicWitnessC_xb = Real.log concreteC + 1 / (1 + 1) := by
  have hlog2pos := concreteC_log_pos
  apply Real.exp_log
  have h := add_lt_add_left nonMonotonicWitness_half_pos (Real.log concreteC)
  have e1 : Real.log concreteC + 0 = Real.log concreteC := add_zero _
  exact lt_trans_ax hlog2pos (by rwa [e1] at h)

theorem nonMonotonicWitnessC_xc_exp :
    Real.exp nonMonotonicWitnessC_xc = Real.log concreteC + (1 + 1) := by
  have hlog2pos := concreteC_log_pos
  apply Real.exp_log
  have h := add_lt_add_left zero_lt_one_add_one (Real.log concreteC)
  have e1 : Real.log concreteC + 0 = Real.log concreteC := add_zero _
  exact lt_trans_ax hlog2pos (by rwa [e1] at h)

theorem nonMonotonicWitnessC_x0_lt_xb :
    Real.log (Real.log concreteC) < nonMonotonicWitnessC_xb := by
  have hlog2pos := concreteC_log_pos
  have hd : Real.log concreteC < Real.log concreteC + 1 / (1 + 1) := by
    have h := add_lt_add_left nonMonotonicWitness_half_pos (Real.log concreteC)
    have e1 : Real.log concreteC + 0 = Real.log concreteC := add_zero _
    rwa [e1] at h
  exact log_lt_log hlog2pos hd

theorem nonMonotonicWitnessC_xb_lt_xc : nonMonotonicWitnessC_xb < nonMonotonicWitnessC_xc := by
  have hlog2pos := concreteC_log_pos
  have hbpos : 0 < Real.log concreteC + 1 / (1 + 1) := by
    have h := add_lt_add_left nonMonotonicWitness_half_pos (Real.log concreteC)
    have e1 : Real.log concreteC + 0 = Real.log concreteC := add_zero _
    exact lt_trans_ax hlog2pos (by rwa [e1] at h)
  have hd : Real.log concreteC + 1 / (1 + 1) < Real.log concreteC + (1 + 1) := by
    have hhalf_lt_two : (1 : Real) / (1 + 1) < 1 + 1 :=
      lt_trans_ax nonMonotonicWitness_half_lt_one one_lt_one_add_one
    exact add_lt_add_left hhalf_lt_two (Real.log concreteC)
  exact log_lt_log hbpos hd

theorem nonMonotonicWitnessC_D_xb :
    Real.exp nonMonotonicWitnessC_xb - Real.log concreteC = 1 / (1 + 1) := by
  rw [nonMonotonicWitnessC_xb_exp]
  exact add_sub_cancel_left_local _ _

theorem nonMonotonicWitnessC_D_xc :
    Real.exp nonMonotonicWitnessC_xc - Real.log concreteC = 1 + 1 := by
  rw [nonMonotonicWitnessC_xc_exp]
  exact add_sub_cancel_left_local _ _

theorem nonMonotonicWitnessC_not_monotone :
    ¬ (∀ x y : Real, x < y →
        (nonMonotonicWitnessC concreteC).eval x ≤ (nonMonotonicWitnessC concreteC).eval y) ∧
    ¬ (∀ x y : Real, x < y →
        (nonMonotonicWitnessC concreteC).eval y ≤ (nonMonotonicWitnessC concreteC).eval x) := by
  have hTa : (nonMonotonicWitnessC concreteC).eval (Real.log (Real.log concreteC)) = 0 :=
    nonMonotonicWitnessC_eval_clamped (le_refl _)
  have hTb : (nonMonotonicWitnessC concreteC).eval nonMonotonicWitnessC_xb < 0 :=
    nonMonotonicWitnessC_neg_of_lt_one nonMonotonicWitnessC_x0_lt_xb
      (by rw [nonMonotonicWitnessC_D_xb]; exact nonMonotonicWitness_half_pos)
      (by rw [nonMonotonicWitnessC_D_xb]; exact nonMonotonicWitness_half_lt_one)
  have hxc_gt_x0 : Real.log (Real.log concreteC) < nonMonotonicWitnessC_xc :=
    lt_trans_ax nonMonotonicWitnessC_x0_lt_xb nonMonotonicWitnessC_xb_lt_xc
  have hTc : 0 < (nonMonotonicWitnessC concreteC).eval nonMonotonicWitnessC_xc :=
    nonMonotonicWitnessC_pos_of_gt_one hxc_gt_x0
      (by rw [nonMonotonicWitnessC_D_xc]; exact one_lt_one_add_one)
  constructor
  · intro hmono
    have h := hmono (Real.log (Real.log concreteC)) nonMonotonicWitnessC_xb
      nonMonotonicWitnessC_x0_lt_xb
    rw [hTa] at h
    exact lt_irrefl_ax _ (lt_of_lt_of_le hTb h)
  · intro hanti
    have h := hanti nonMonotonicWitnessC_xb nonMonotonicWitnessC_xc nonMonotonicWitnessC_xb_lt_xc
    exact lt_irrefl_ax _ (lt_trans_ax hTc (lt_of_le_of_lt h hTb))

/-! ## The `exp`-wrapped tree's properties -/

theorem expWrappedNonMonotonicWitnessC_eval (x : Real) :
    (expWrappedNonMonotonicWitnessC concreteC).eval x
      = Real.exp ((nonMonotonicWitnessC concreteC).eval x) := by
  show Real.exp ((nonMonotonicWitnessC concreteC).eval x) - Real.log 1
      = Real.exp ((nonMonotonicWitnessC concreteC).eval x)
  rw [log_one, sub_zero]

theorem expWrappedNonMonotonicWitnessC_pos (x : Real) :
    0 < (expWrappedNonMonotonicWitnessC concreteC).eval x := by
  rw [expWrappedNonMonotonicWitnessC_eval]
  exact Real.exp_pos _

theorem expWrappedNonMonotonicWitnessC_upper_bound {x : Real}
    (hx : Real.log (Real.log concreteC) < x) :
    (expWrappedNonMonotonicWitnessC concreteC).eval x < concreteC := by
  rw [expWrappedNonMonotonicWitnessC_eval]
  have h := nonMonotonicWitnessC_upper_bound hx
  have h2 := Real.exp_lt h
  rwa [Real.exp_log concreteC_pos] at h2

theorem expWrappedNonMonotonicWitnessC_upper_bound_all (x : Real) :
    (expWrappedNonMonotonicWitnessC concreteC).eval x < concreteC := by
  rcases lt_total (Real.log (Real.log concreteC)) x with h | h | h
  · exact expWrappedNonMonotonicWitnessC_upper_bound h
  · rw [expWrappedNonMonotonicWitnessC_eval, nonMonotonicWitnessC_eval_clamped (le_of_eq h.symm),
      Real.exp_zero]
    exact lt_trans_ax one_lt_one_add_one concreteC_gt_two
  · rw [expWrappedNonMonotonicWitnessC_eval, nonMonotonicWitnessC_eval_clamped (le_of_lt h),
      Real.exp_zero]
    exact lt_trans_ax one_lt_one_add_one concreteC_gt_two

theorem expWrappedNonMonotonicWitnessC_not_RightChildrenSimplePositive :
    ¬ RightChildrenSimplePositive (expWrappedNonMonotonicWitnessC concreteC) := by
  intro hsimple
  have h1 := hsimple.1
  have h2 : nonMonotonicWitnessC concreteC = EMLTree.eml EMLTree.var
      (EMLTree.eml (EMLTree.eml EMLTree.var (EMLTree.const 1))
        (EMLTree.eml EMLTree.var (EMLTree.const concreteC))) := rfl
  rw [h2] at h1
  have h3 := h1.2
  rcases h3 with h | ⟨c, hc, _⟩
  · exact EMLTree.noConfusion h
  · exact EMLTree.noConfusion hc

theorem expWrappedNonMonotonicWitnessC_not_constant :
    ∃ x y, (expWrappedNonMonotonicWitnessC concreteC).eval x
      ≠ (expWrappedNonMonotonicWitnessC concreteC).eval y := by
  refine ⟨Real.log (Real.log concreteC), nonMonotonicWitnessC_xb, ?_⟩
  rw [expWrappedNonMonotonicWitnessC_eval, expWrappedNonMonotonicWitnessC_eval]
  intro heq
  have hTa : (nonMonotonicWitnessC concreteC).eval (Real.log (Real.log concreteC)) = 0 :=
    nonMonotonicWitnessC_eval_clamped (le_refl _)
  have hTb : (nonMonotonicWitnessC concreteC).eval nonMonotonicWitnessC_xb < 0 :=
    nonMonotonicWitnessC_neg_of_lt_one nonMonotonicWitnessC_x0_lt_xb
      (by rw [nonMonotonicWitnessC_D_xb]; exact nonMonotonicWitness_half_pos)
      (by rw [nonMonotonicWitnessC_D_xb]; exact nonMonotonicWitness_half_lt_one)
  have hlt : (nonMonotonicWitnessC concreteC).eval nonMonotonicWitnessC_xb
      < (nonMonotonicWitnessC concreteC).eval (Real.log (Real.log concreteC)) := by
    rw [hTa]; exact hTb
  have hexplt := Real.exp_lt hlt
  rw [heq] at hexplt
  exact lt_irrefl_ax _ hexplt

theorem expWrappedNonMonotonicWitnessC_not_monotone :
    ¬ (∀ x y : Real, x < y → (expWrappedNonMonotonicWitnessC concreteC).eval x
        ≤ (expWrappedNonMonotonicWitnessC concreteC).eval y) ∧
    ¬ (∀ x y : Real, x < y → (expWrappedNonMonotonicWitnessC concreteC).eval y
        ≤ (expWrappedNonMonotonicWitnessC concreteC).eval x) := by
  have hTa : (nonMonotonicWitnessC concreteC).eval (Real.log (Real.log concreteC)) = 0 :=
    nonMonotonicWitnessC_eval_clamped (le_refl _)
  have hTb : (nonMonotonicWitnessC concreteC).eval nonMonotonicWitnessC_xb < 0 :=
    nonMonotonicWitnessC_neg_of_lt_one nonMonotonicWitnessC_x0_lt_xb
      (by rw [nonMonotonicWitnessC_D_xb]; exact nonMonotonicWitness_half_pos)
      (by rw [nonMonotonicWitnessC_D_xb]; exact nonMonotonicWitness_half_lt_one)
  have hxc_gt_x0 : Real.log (Real.log concreteC) < nonMonotonicWitnessC_xc :=
    lt_trans_ax nonMonotonicWitnessC_x0_lt_xb nonMonotonicWitnessC_xb_lt_xc
  have hTc : 0 < (nonMonotonicWitnessC concreteC).eval nonMonotonicWitnessC_xc :=
    nonMonotonicWitnessC_pos_of_gt_one hxc_gt_x0
      (by rw [nonMonotonicWitnessC_D_xc]; exact one_lt_one_add_one)
  have hUa : (expWrappedNonMonotonicWitnessC concreteC).eval (Real.log (Real.log concreteC))
      = Real.exp 0 := by rw [expWrappedNonMonotonicWitnessC_eval, hTa]
  have hUb_lt_Ua : (expWrappedNonMonotonicWitnessC concreteC).eval nonMonotonicWitnessC_xb
      < (expWrappedNonMonotonicWitnessC concreteC).eval (Real.log (Real.log concreteC)) := by
    rw [expWrappedNonMonotonicWitnessC_eval, hUa]
    exact Real.exp_lt hTb
  have hUb_lt_Uc : (expWrappedNonMonotonicWitnessC concreteC).eval nonMonotonicWitnessC_xb
      < (expWrappedNonMonotonicWitnessC concreteC).eval nonMonotonicWitnessC_xc := by
    rw [expWrappedNonMonotonicWitnessC_eval, expWrappedNonMonotonicWitnessC_eval]
    exact Real.exp_lt (lt_trans_ax hTb hTc)
  constructor
  · intro hmono
    have h := hmono (Real.log (Real.log concreteC)) nonMonotonicWitnessC_xb
      nonMonotonicWitnessC_x0_lt_xb
    exact lt_irrefl_ax _ (lt_of_lt_of_le hUb_lt_Ua h)
  · intro hanti
    have h := hanti nonMonotonicWitnessC_xb nonMonotonicWitnessC_xc nonMonotonicWitnessC_xb_lt_xc
    exact lt_irrefl_ax _ (lt_of_lt_of_le hUb_lt_Uc h)

/-- **The packaged result.** `expWrappedNonMonotonicWitnessC concreteC` is bounded in BOTH
directions (`0 < eval < concreteC`, everywhere), non-constant, non-
`RightChildrenSimplePositive`, and non-monotonic — a genuine, fully-verified member of the
residual's open classification, for which `EMLPfaffianValidOnCrossingObstruction.lean`'s
`concreteC_validon_false` ALSO holds: the first tree in this whole arc confirmed to be BOTH a
member of the open class AND resistant to the closure technique that worked for the
negative-crossing case. -/
theorem concreteC_expwrapped_exists :
    (∀ x, 0 < (expWrappedNonMonotonicWitnessC concreteC).eval x) ∧
    (∀ x, (expWrappedNonMonotonicWitnessC concreteC).eval x < concreteC) ∧
    (∃ x y, (expWrappedNonMonotonicWitnessC concreteC).eval x
      ≠ (expWrappedNonMonotonicWitnessC concreteC).eval y) ∧
    ¬ RightChildrenSimplePositive (expWrappedNonMonotonicWitnessC concreteC) ∧
    ¬ (∀ x y : Real, x < y → (expWrappedNonMonotonicWitnessC concreteC).eval x
        ≤ (expWrappedNonMonotonicWitnessC concreteC).eval y) ∧
    ¬ (∀ x y : Real, x < y → (expWrappedNonMonotonicWitnessC concreteC).eval y
        ≤ (expWrappedNonMonotonicWitnessC concreteC).eval x) :=
  ⟨expWrappedNonMonotonicWitnessC_pos, expWrappedNonMonotonicWitnessC_upper_bound_all,
   expWrappedNonMonotonicWitnessC_not_constant,
   expWrappedNonMonotonicWitnessC_not_RightChildrenSimplePositive,
   expWrappedNonMonotonicWitnessC_not_monotone.1, expWrappedNonMonotonicWitnessC_not_monotone.2⟩

/-- **The single combined statement.** `expWrappedNonMonotonicWitnessC concreteC` is
simultaneously a genuine member of the residual's open classification AND provably resistant to
the `EMLPfaffianValidOn`-based closure route (`EMLPfaffianValidOnCrossingObstruction.lean`'s
`concreteC_validon_false`) — the first tree in this whole multi-week arc confirmed to be BOTH,
rather than one or the other. -/
theorem concreteC_open_class_member_and_validon_resistant :
    ((∀ x, 0 < (expWrappedNonMonotonicWitnessC concreteC).eval x) ∧
     (∀ x, (expWrappedNonMonotonicWitnessC concreteC).eval x < concreteC) ∧
     (∃ x y, (expWrappedNonMonotonicWitnessC concreteC).eval x
       ≠ (expWrappedNonMonotonicWitnessC concreteC).eval y) ∧
     ¬ RightChildrenSimplePositive (expWrappedNonMonotonicWitnessC concreteC) ∧
     ¬ (∀ x y : Real, x < y → (expWrappedNonMonotonicWitnessC concreteC).eval x
         ≤ (expWrappedNonMonotonicWitnessC concreteC).eval y) ∧
     ¬ (∀ x y : Real, x < y → (expWrappedNonMonotonicWitnessC concreteC).eval y
         ≤ (expWrappedNonMonotonicWitnessC concreteC).eval x)) ∧
    ¬ EMLPfaffianValidOn (expWrappedNonMonotonicWitnessC concreteC) 0 (1 + 1) :=
  ⟨concreteC_expwrapped_exists, concreteC_validon_false⟩

end Real
end MachLib
