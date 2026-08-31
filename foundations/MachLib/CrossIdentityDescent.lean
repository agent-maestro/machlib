/-
# The cross identity survives cancelling a common factor

`exists_coprime_representative` supplies `no_rational_logarithm`'s `hlow` — but only for a *reduced*
pair, and `hident` is stated in terms of the original `N` and `D`. This module transports it.

The transport is **not** a divisibility argument. `peq_cross_common_factor` (`CrossIdentities`) says
the Wronskian-shaped numerator is homogeneous of degree two, `W(gN, gD) = g^2 * W(N, D)`, because the
two `g * g' * N * D` terms cancel identically — no derivative of `g` survives, and no hypothesis on
`g` beyond being non-zero is needed. `peq_cancel_left` then removes the `g^2` from both sides.

Every ingredient predates this module; the assembly is seven `PEq.trans` steps.
-/
import MachLib.CrossIdentities
import MachLib.RelCoeffsEqCase
import MachLib.RelCoeffsLand

namespace MachLib

/-- A square of a non-zero polynomial is non-zero. -/
theorem pnorm_pmul_self_ne {g : List Real} (hg : pnorm g ≠ []) : pnorm (pmul g g) ≠ [] := by
  intro h
  refine hg ?_
  have h0 : PEq (pmul g g) [] := by show pnorm (pmul g g) = pnorm []; rw [h]; rfl
  exact pmul_nil_cancel' hg h0

/-- **The cross identity descends to a reduced pair.** -/
theorem cross_identity_descends {g N D R S : List Real} (hg : pnorm g ≠ [])
    (h : PEq (pmul (psub (pmul (pderiv (pmul g N)) (pmul g D))
                         (pmul (pmul g N) (pderiv (pmul g D)))) R)
             (pmul S (pmul (pmul g D) (pmul g D)))) :
    PEq (pmul (psub (pmul (pderiv N) D) (pmul N (pderiv D))) R) (pmul S (pmul D D)) := by
  refine peq_cancel_left (pnorm_pmul_self_ne hg) ?_
  refine PEq.trans (PEq.symm (peq_pmul_assoc (pmul g g) _ R)) ?_
  refine PEq.trans (peq_pmul (PEq.symm (peq_cross_common_factor g N D)) (PEq.refl R)) ?_
  refine PEq.trans h ?_
  refine PEq.trans (peq_pmul (PEq.refl S) (peq_pmul_regroup g D g D)) ?_
  refine PEq.trans (PEq.symm (peq_pmul_assoc S (pmul g g) (pmul D D))) ?_
  refine PEq.trans (peq_pmul (peq_pmul_comm S (pmul g g)) (PEq.refl (pmul D D))) ?_
  exact peq_pmul_assoc (pmul g g) S (pmul D D)

/-! ## Both sides, not one

`lowest_terms_with_ord` reduces `P/Q` as well, so the identity has to survive a cancellation on that
side too. There the factor lands in two different places — `R = P·Q` picks up `h^2` by regrouping,
and `S = W(P,Q)` picks up `h^2` by homogeneity — and it is the *same* `h^2`, so one cancellation
clears both. Same three ingredients, mirrored.
-/

/-- `(c)·(X·Y) ≈ X·((c)·Y)` — the regrouping both transports need. -/
theorem peq_pmul_pull (c X Y : List Real) :
    PEq (pmul c (pmul X Y)) (pmul X (pmul c Y)) := by
  refine PEq.trans (PEq.symm (peq_pmul_assoc c X Y)) ?_
  refine PEq.trans (peq_pmul (peq_pmul_comm c X) (PEq.refl Y)) ?_
  exact peq_pmul_assoc X c Y

/-- **The mirror transport, on the `P/Q` side.** -/
theorem cross_identity_descends_right {h N D P Q : List Real} (hh : pnorm h ≠ [])
    (hid : PEq (pmul (psub (pmul (pderiv N) D) (pmul N (pderiv D)))
                     (pmul (pmul h P) (pmul h Q)))
               (pmul (psub (pmul (pderiv (pmul h P)) (pmul h Q))
                           (pmul (pmul h P) (pderiv (pmul h Q)))) (pmul D D))) :
    PEq (pmul (psub (pmul (pderiv N) D) (pmul N (pderiv D))) (pmul P Q))
        (pmul (psub (pmul (pderiv P) Q) (pmul P (pderiv Q))) (pmul D D)) := by
  refine peq_cancel_left (pnorm_pmul_self_ne hh) ?_
  refine PEq.trans (peq_pmul_pull (pmul h h) _ (pmul P Q)) ?_
  refine PEq.trans (peq_pmul (PEq.refl _) (PEq.symm (peq_pmul_regroup h P h Q))) ?_
  refine PEq.trans hid ?_
  refine PEq.trans (peq_pmul (peq_cross_common_factor h P Q) (PEq.refl (pmul D D))) ?_
  exact peq_pmul_assoc (pmul h h) _ (pmul D D)

end MachLib
