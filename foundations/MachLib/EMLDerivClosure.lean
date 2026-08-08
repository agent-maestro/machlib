import MachLib.EMLRingClosure
import MachLib.Differentiation

/-!
# EML is closed under differentiation

`EMLDifferentiationClosureFailure` proved its witness `exp x − 1/x` outside `EML₁` and left the
general claim open, reduced to a sub-lemma that ran through `1/x ∉ EML`.
`EMLDifferentiationClosureRefuted` killed the reduction; `EMLRingClosure` removed the sign
obstruction. **Division is now free too** — `invPos t := exp (−log t)` is `1/t` wherever `t > 0`,
built from the unconditional `negGen` and `expOf`. So `d/dx[exp a − log b] = a'·exp a − b'/b` is
expressible, and the derivative of every EML tree is an EML tree.

**`LogPos` is required and is stated, not hidden.** `MachLib.Real.log` is totalised, so where a
`log`-argument is non-positive that branch is locally constant and the classical derivative is
genuinely different.

**This is a closure claim, not a cost claim.** `eml_xx_deriv_not_in_eml_1` stays true —
differentiation does not preserve depth — and the two are consistent.
-/

namespace MachLib

open Real

/-- **Reciprocal**, wherever `t` is positive: `exp (−log t) = 1/t`. -/
noncomputable def invPos (t : EMLTree) : EMLTree := expOf (negGen (logTree t))

theorem invPos_eval {t : EMLTree} {x : Real} (ht : 0 < t.eval x) :
    (invPos t).eval x = 1 / t.eval x := by
  rw [invPos, expOf_eval, negGen_eval, logTree_eval, exp_neg_inv, exp_log ht]

/-- Every `log`-argument in `t` is positive at `x`. -/
def LogPos : EMLTree → Real → Prop
  | .const _, _ => True
  | .var, _ => True
  | .eml t1 t2, x => LogPos t1 x ∧ LogPos t2 x ∧ 0 < t2.eval x

/-- The **syntactic derivative**: `d/dx[exp a − log b] = a'·exp a − b'/b`. -/
noncomputable def derivTree : EMLTree → EMLTree
  | .const _ => .const 0
  | .var => .const 1
  | .eml a b => subGen (mulGen (derivTree a) (expOf a))
                       (mulGen (derivTree b) (invPos b))

/-- **The derivative of every EML tree is an EML tree.** -/
theorem derivTree_hasDerivAt : ∀ (t : EMLTree) (x : Real), LogPos t x →
    HasDerivAt (fun y => t.eval y) ((derivTree t).eval x) x := by
  intro t
  induction t with
  | const c =>
      intro x _
      have h : (derivTree (EMLTree.const c)).eval x = 0 := rfl
      rw [h]
      exact HasDerivAt_of_eq (fun _ => c) _ 0 x (fun _ => rfl) (HasDerivAt_const c x)
  | var =>
      intro x _
      have h : (derivTree EMLTree.var).eval x = 1 := rfl
      rw [h]
      exact HasDerivAt_of_eq (fun y => y) _ 1 x (fun _ => rfl) (HasDerivAt_id x)
  | eml t1 t2 ih1 ih2 =>
      intro x hx
      obtain ⟨h1, h2, hpos⟩ := hx
      have D1 := ih1 x h1
      have D2 := ih2 x h2
      have He : HasDerivAt (fun y => Real.exp (t1.eval y))
          (Real.exp (t1.eval x) * (derivTree t1).eval x) x :=
        HasDerivAt_comp Real.exp (fun y => t1.eval y) _ _ x D1 (HasDerivAt_exp (t1.eval x))
      have Hl : HasDerivAt (fun y => Real.log (t2.eval y))
          (1 / t2.eval x * (derivTree t2).eval x) x :=
        HasDerivAt_comp Real.log (fun y => t2.eval y) _ _ x D2
          (HasDerivAt_log_pos (t2.eval x) hpos)
      have Hs := HasDerivAt_sub _ _ _ _ x He Hl
      have hval : (derivTree (EMLTree.eml t1 t2)).eval x
          = Real.exp (t1.eval x) * (derivTree t1).eval x
            - 1 / t2.eval x * (derivTree t2).eval x := by
        show (subGen (mulGen (derivTree t1) (expOf t1))
              (mulGen (derivTree t2) (invPos t2))).eval x = _
        rw [subGen_eval, mulGen_eval, mulGen_eval, expOf_eval, invPos_eval hpos]
        mach_mpoly [(derivTree t1).eval x, (derivTree t2).eval x,
                    Real.exp (t1.eval x), 1 / t2.eval x]
      rw [hval]
      exact HasDerivAt_of_eq _ _ _ x (fun _ => rfl) Hs

/-- **EML is closed under differentiation.** -/
theorem eml_closed_under_deriv (t : EMLTree) :
    ∃ s : EMLTree, ∀ x : Real, LogPos t x →
      HasDerivAt (fun y => t.eval y) (s.eval x) x :=
  ⟨derivTree t, fun x hx => derivTree_hasDerivAt t x hx⟩

end MachLib
