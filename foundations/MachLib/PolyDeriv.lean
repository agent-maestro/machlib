import MachLib.PolyOrd
import MachLib.PevDeriv

/-!
# The derivative as a coefficient operation, and where characteristic zero enters

`pderiv` is a pure list operation and its laws are field-axiom-only. What is **not** field-axiom-only
is the one fact the pole-order count needs about it, and this file exists partly to say so.

## Correcting the previous commit

`PolyOrd` recorded that `pev_pderiv_cons` is field-only — nine `MachLib.Real` axioms, no `ltR`, no
`HasDerivAt` — and concluded that the pole-order count "can be stated and proved inside
`algebraFootprint`". **That conclusion was wrong.** It is true of the derivative *operation* and
false of the *count*, which needs `q ∤ q'`, hence `q' ≠ 0`, hence **characteristic zero**.

Characteristic zero is not available here, and not by omission:

* `algebraFootprint` is the theory of fields, and `𝔽₂` is a model of it;
* over `𝔽₂`, `q = X² + 1 = (X+1)²` is a square with `q' = 2X = 0`, so `q ∣ q'`;
* so `q ∤ q'` is **false in a model of the allowed axioms**, hence unprovable from them.

Measured confirmation of where the strength lives: `MachLib.Real.natCast_ne_zero` carries
`ltR`, `leR`, `lt_irrefl_ax`, `lt_trans_ax`, `add_lt_add_left`, `le_iff_lt_or_eq` and
`zero_lt_one_ax` — in this corpus characteristic zero comes from the **order** axioms.

This is the same shape as the `𝔽₂` argument in `PolyMulDegree`, and it is the second time the
finite-model observation has decided a design question. It does not invalidate the spine: the count
carries `q ∤ q'` as a **named hypothesis**, everything algebraic stays inside invariant (7), and
discharging that hypothesis for `MachLib.Real` is a separate, honest step that leaves the allow-list.

## What *is* free

Half of `q ∤ q'` costs nothing: `pderiv_length` shows the derivative never lengthens a coefficient
list, which is the degree half of `deg q' < deg q`. Only the **nonvanishing** half needs the field to
have characteristic zero.
-/

namespace MachLib

open Real

attribute [local instance] Classical.propDecidable

/-! ## The derivative is additive and commutes with scaling — exactly -/

theorem pderiv_padd : ∀ X Y : List Real,
    pderiv (padd X Y) = padd (pderiv X) (pderiv Y) := by
  intro X
  induction X with
  | nil => intro Y; rfl
  | cons c cs ih =>
      intro Y
      cases Y with
      | nil =>
          show pderiv (c :: cs) = padd (pderiv (c :: cs)) []
          rw [padd_nil_right]
      | cons d ds =>
          show padd (padd cs ds) ((0 : Real) :: pderiv (padd cs ds))
              = padd (padd cs ((0 : Real) :: pderiv cs)) (padd ds ((0 : Real) :: pderiv ds))
          rw [ih ds, ← padd_zero_cons (pderiv cs) (pderiv ds), padd_middle_four]

theorem pderiv_pscale : ∀ (a : Real) (X : List Real),
    pderiv (pscale a X) = pscale a (pderiv X) := by
  intro a X
  induction X with
  | nil => rfl
  | cons c cs ih =>
      have ha0 : a * 0 = 0 := by mach_ring
      show padd (pscale a cs) ((0 : Real) :: pderiv (pscale a cs))
          = pscale a (padd cs ((0 : Real) :: pderiv cs))
      rw [pscale_padd, ih]
      show padd (pscale a cs) ((0 : Real) :: pscale a (pderiv cs))
          = padd (pscale a cs) ((a * 0) :: pscale a (pderiv cs))
      rw [ha0]

/-! ## The derivative never lengthens a list

The degree half of `deg q' < deg q`, and it is free. The *nonvanishing* half is what needs
characteristic zero — see the module docstring. -/

theorem pderiv_length : ∀ L : List Real, (pderiv L).length = L.length := by
  intro L
  induction L with
  | nil => rfl
  | cons c cs ih =>
      show (padd cs ((0 : Real) :: pderiv cs)).length = cs.length + 1
      rw [padd_length_le]
      · show (pderiv cs).length + 1 = cs.length + 1
        rw [ih]
      · show cs.length ≤ (pderiv cs).length + 1
        rw [ih]; omega

/-! ## The product rule -/

/-- **`(A·B)' ≈ A'·B + A·B'`.** Up to `pnorm`, because `pmul (0 :: W) B` sheds a trailing zero. -/
theorem peq_pderiv_pmul : ∀ A B : List Real,
    PEq (pderiv (pmul A B)) (padd (pmul (pderiv A) B) (pmul A (pderiv B))) := by
  intro A
  induction A with
  | nil => intro B; show pnorm [] = pnorm (padd (pmul [] B) []); rfl
  | cons a as ih =>
      intro B
      -- LHS: (a·B + x·(as·B))' = a·B' + (as·B + x·(as·B)')
      have hL : pderiv (pmul (a :: as) B)
          = padd (pscale a (pderiv B))
              (padd (pmul as B) ((0 : Real) :: pderiv (pmul as B))) := by
        show pderiv (padd (pscale a B) ((0 : Real) :: pmul as B)) = _
        rw [pderiv_padd, pderiv_pscale]
        rfl
      -- RHS: (as + x·as')·B + (a + x·as)·B'
      have hR : PEq (padd (pmul (pderiv (a :: as)) B) (pmul (a :: as) (pderiv B)))
          (padd (padd (pmul as B) ((0 : Real) :: pmul (pderiv as) B))
                (padd (pscale a (pderiv B)) ((0 : Real) :: pmul as (pderiv B)))) := by
        refine peq_padd ?_ (PEq.refl _)
        show PEq (pmul (padd as ((0 : Real) :: pderiv as)) B) _
        rw [pmul_padd_left]
        exact peq_padd (PEq.refl _) (pnorm_pmul_cons_zero (pderiv as) B)
      rw [hL]
      refine PEq.trans ?_ hR.symm
      -- both sides are the same four summands; rearrange
      refine PEq.trans (peq_padd (PEq.refl (pscale a (pderiv B)))
        (peq_padd (PEq.refl (pmul as B))
          (PEq.trans (peq_cons 0 (ih B))
            (PEq.refl _)))) ?_
      show PEq (padd (pscale a (pderiv B))
                 (padd (pmul as B)
                   ((0 : Real) :: padd (pmul (pderiv as) B) (pmul as (pderiv B)))))
             (padd (padd (pmul as B) ((0 : Real) :: pmul (pderiv as) B))
                   (padd (pscale a (pderiv B)) ((0 : Real) :: pmul as (pderiv B))))
      show pnorm _ = pnorm _
      rw [← padd_zero_cons (pmul (pderiv as) B) (pmul as (pderiv B)),
          padd_middle_four (pmul as B) ((0 : Real) :: pmul (pderiv as) B)
            (pscale a (pderiv B)) ((0 : Real) :: pmul as (pderiv B)),
          padd_comm (pmul as B) (pscale a (pderiv B)),
          padd_assoc]

end MachLib
