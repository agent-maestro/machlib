import MachLib.ExpCompDeriv
import MachLib.EMLZeroQueryNormalForm

/-!
# Brick three: the germ has a derivative, off its exceptional set

`ExpCompDeriv` named this gap rather than stepping over it. `RatGerm` gives `f = pev P / pev Q` **off
a finite exceptional set**, `HasDerivAt` is pointwise, and `HasDerivAt_congr` transfers a derivative
only across a **neighbourhood**. The missing step is getting from *"agrees off a finite set"* to
*"agrees near `x`"*.

It is exactly as small as predicted: **a finite list of reals does not cover a neighbourhood of a
point outside it.** Same shape as `list_two_sided_bound` — no finite list exhausts a region — and the
same construction principle. Each `e ∈ E` sits a positive distance from `x`; `two_bound_witness`
shrinks two positive distances to one that beats both, and the induction does the rest.

With that, the germ inherits its representative's derivative, and the differential route has a
derivative for the object it actually cares about rather than for a stand-in.
-/

namespace MachLib

open Real

private theorem abs_pos_of_ne' {a : Real} (h : a ≠ 0) : 0 < abs a := abs_pos_of_ne h

private theorem sub_ne_zero' {a b : Real} (h : a ≠ b) : a - b ≠ 0 :=
  QuadraticRoots.sub_ne_zero_of_ne h

/-- **A finite list does not cover a neighbourhood of a point outside it.** -/
theorem finite_list_avoidable : ∀ (E : List Real) (x : Real), x ∉ E →
    ∃ δ : Real, 0 < δ ∧ ∀ y : Real, abs (y - x) < δ → y ∉ E := by
  intro E
  induction E with
  | nil => intro x _; exact ⟨1, zero_lt_one_ax, fun _ _ hy => by cases hy⟩
  | cons e es ih =>
      intro x hx
      have hxe : x ≠ e := fun h => hx (by rw [h]; exact List.mem_cons_self)
      have hxes : x ∉ es := fun h => hx (List.mem_cons_of_mem e h)
      obtain ⟨δ', hδ', hav⟩ := ih x hxes
      have hd : (0 : Real) < abs (e - x) := abs_pos_of_ne' (sub_ne_zero' (fun h => hxe h.symm))
      obtain ⟨w, hw, hwd, hwe⟩ := two_bound_witness' hδ' hd
      refine ⟨w, hw, fun y hy hmem => ?_⟩
      -- establish both facts BEFORE casing, so neither branch needs `abs_sub_comm`
      have hne : y ≠ e := by
        intro h
        rw [h] at hy
        exact lt_irrefl_ax (abs (e - x)) (lt_trans_ax hy hwe)
      have hnes : y ∉ es := hav y (lt_trans_ax hy hwd)
      cases hmem with
      | head => exact hne rfl
      | tail _ hmem' => exact hnes hmem'

/-- **Agreement off a finite set transfers a derivative.** The bridge `HasDerivAt_congr` needed: a
neighbourhood, produced from finiteness rather than assumed. -/
theorem hasDerivAt_of_agrees_off_finite {f g : Real → Real} {E : List Real} {a x : Real}
    (hx : x ∉ E) (hag : ∀ y : Real, y ∉ E → f y = g y) (hf : HasDerivAt f a x) :
    HasDerivAt g a x := by
  obtain ⟨δ, hδ, hav⟩ := finite_list_avoidable E x hx
  exact HasDerivAt_congr f g a x ⟨δ, hδ, fun y hy => hag y (hav y hy)⟩ hf

/-- **A zero-query function is differentiable off a finite set**, with its derivative given by
`pderiv` on the normal form's numerator and denominator.

This is what `ExpCompDeriv` could only state about a stand-in. The exceptional set is the normal
form's own, extended by nothing: `zero_query_finite_exception_normal_form` already guarantees the
denominator is nonzero there, which is exactly the hypothesis the quotient rule wants. -/
theorem hasDerivAt_zero_query (T : FTerm) (h : fOcc T = 0) :
    ∃ (E P Q : List Real), ∀ x : Real, x ∉ E →
      pev Q x ≠ 0 ∧ HasDerivAt (FTerm.eval T)
        (pev (pderiv P) x * (1 / pev Q x)
          + pev P x * (-(pev (pderiv Q) x) / (pev Q x * pev Q x))) x := by
  obtain ⟨E, P, Q, hE⟩ := zero_query_finite_exception_normal_form T h
  refine ⟨E, P, Q, fun x hx => ⟨(hE x hx).1, ?_⟩⟩
  refine hasDerivAt_of_agrees_off_finite (f := fun y => pev P y * (1 / pev Q y)) hx
    (fun y hy => ?_) (hasDerivAt_ratFn P Q x (hE x hx).1)
  -- off `E` the product form and the quotient form agree, and the quotient form is `T`
  rw [(hE y hy).2, div_def (pev P y) (pev Q y) (hE y hy).1]

/-- **And so does `exp` of it** — `y' = S'·y` now applies to a genuine zero-query argument rather
than to an explicit stand-in. The last brick before differentiating a relation. -/
theorem hasDerivAt_exp_zero_query (T : FTerm) (h : fOcc T = 0) :
    ∃ (E P Q : List Real), ∀ x : Real, x ∉ E →
      pev Q x ≠ 0 ∧ HasDerivAt (fun y => exp (FTerm.eval T y))
        ((pev (pderiv P) x * (1 / pev Q x)
          + pev P x * (-(pev (pderiv Q) x) / (pev Q x * pev Q x)))
          * exp (FTerm.eval T x)) x := by
  obtain ⟨E, P, Q, hE⟩ := hasDerivAt_zero_query T h
  exact ⟨E, P, Q, fun x hx => ⟨(hE x hx).1, hasDerivAt_exp_comp_swap (hE x hx).2⟩⟩

end MachLib
