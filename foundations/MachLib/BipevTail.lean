import MachLib.BipevMinimal
import MachLib.FPModel

/-!
# Differentiating a relation that holds on a tail

The first mismatch the assembly surfaces, and it is a real one.

Brick four's `dbipevExp_eq_zero_of_relation_off_finite` transfers the derivative when the relation
holds **off a finite set** — the shape the `C₀` work needed, where exceptional sets are finite. The
differential route's relations hold **on a tail**, and the complement of a tail is not finite, so
that lemma does not apply. The neighbourhood the transfer needs is there either way; only the way of
producing it differs.

For a tail the witness is explicit and better than the finite-set one: at any `x > X`, the radius
`x − X` works, because `|y − x| < x − X` forces `y > X`. No avoidance argument, no `Classical.em` —
`abs_lt_split` and one subtraction.

## Why this was not visible earlier

Brick four was written before the route was known, against the exceptional-set shape that the
surrounding `C₀` machinery used. It is not wrong; it is answering a neighbouring question. This is
the kind of gap that only appears when a piece is *applied*, which is why the assembly was worth
starting rather than deferring.

## The remaining gap, named

The eliminated relation has its top coefficient eventually zero, hence agrees with its truncation.
Minimality then forces the truncation's top coefficient to be eventually zero too, and so on down —
so **every** coefficient of the eliminated relation is eventually zero. That descent is not built
here. It is an induction on the list from the right, and it is what turns "the eliminated relation
is not proper" into the single coefficient identity `cleared_relation_impossible` consumes.
-/

namespace MachLib

open Real

/-! ## A tail is a neighbourhood of each of its interior points -/

/-- **Agreement on a tail transfers a derivative**, at any point strictly inside it. The radius is
`x − X`, which is the whole content. -/
theorem hasDerivAt_of_agrees_on_tail {f g : Real → Real} {X a x : Real} (hx : X < x)
    (hag : ∀ y : Real, X < y → f y = g y) (hf : HasDerivAt f a x) : HasDerivAt g a x := by
  refine HasDerivAt_congr f g a x ⟨x - X, sub_pos_of_lt hx, fun y hy => hag y ?_⟩ hf
  -- `−(y − x) ≤ |y − x| < x − X`, and adding `y − x + X` to both sides gives `X < y`
  have hlow : -(y - x) < x - X := lt_of_le_of_lt (neg_le_abs (y - x)) hy
  -- `add_lt_add_right` does not exist here; `add_lt_add_left` is the local idiom
  have h2 := add_lt_add_left hlow (y - x + X)
  have e1 : (y - x + X) + -(y - x) = X := by mach_mpoly [x, y, X]
  have e2 : (y - x + X) + (x - X) = y := by mach_mpoly [x, y, X]
  rw [e1, e2] at h2
  exact h2

/-! ## The tail version of brick four -/

/-- **A relation vanishing on a tail has a vanishing derivative there.** The shape the differential
route needs; `dbipevExp_eq_zero_of_relation_off_finite` is the finite-exceptional-set sibling. -/
theorem dbipevExp_eq_zero_of_relation_on_tail {Ls : List (List Real)} {S : Real → Real}
    {S' x X : Real} (hS : HasDerivAt S S' x) (hx : X < x)
    (hrel : ∀ y : Real, X < y → bipev Ls y (exp (S y)) = 0) :
    dbipevExp Ls S S' x = 0 := by
  have hzero : HasDerivAt (fun t => bipev Ls t (exp (S t))) 0 x :=
    hasDerivAt_of_agrees_on_tail (f := fun _ => (0 : Real)) hx
      (fun y hy => (hrel y hy).symm) (HasDerivAt_const 0 x)
  exact HasDerivAt_unique (fun t => bipev Ls t (exp (S t)))
    (dbipevExp Ls S S' x) 0 x (hasDerivAt_bipev_exp Ls S S' x hS) hzero

/-- **The cleared differentiated relation vanishes on the tail too** — brick four's tail version
composed with the denominator clearing, which is the form the elimination consumes. -/
theorem bipev_dcoeffs_eq_zero_on_tail {Ls : List (List Real)} {QQ D : List Real}
    {S : Real → Real} {S' x X : Real} (hS : HasDerivAt S S' x) (hx : X < x)
    (hQ : S' * pev QQ x = pev D x)
    (hrel : ∀ y : Real, X < y → bipev Ls y (exp (S y)) = 0) :
    bipev (dcoeffs QQ D 0 Ls) x (exp (S x)) = 0 := by
  rw [← bipev_cleared_deriv_zero Ls QQ D S S' x hQ,
      dbipevExp_eq_zero_of_relation_on_tail hS hx hrel]
  mach_ring

end MachLib
