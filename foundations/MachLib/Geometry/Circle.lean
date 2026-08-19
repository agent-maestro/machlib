import MachLib.SignTactic

/-!
# Circles and tangency, algebraically

The geometric objects Apollonius' problem is stated over, and the one design decision that
everything downstream rests on: **tangency is an algebraic predicate, never a `sqrt` equation.**

`MachLib.Real.sqrt` is *totalised* — `sqrt_neg_zero : x < 0 → sqrt x = 0` — exactly as `Real.log`
is. A tangency predicate written as `sqrt (distSq …) = r + s` would therefore be satisfiable by
accident wherever the totalisation fires, and a "solution" manufactured that way would be
indistinguishable from a real one. Defining tangency as `distSq = (r+s)^2` removes the hazard
structurally rather than by hypothesis: `sqrt` never appears in `TangentExt` or `TangentInt`, so
`sqrt_neg_zero` cannot appear in their axiom footprint.

The geometric reading is then a **theorem** (`tangentExt_iff`, `tangentInt_iff`) rather than a
definition — that is where `sqrt` is allowed, and where it is safe, because those lemmas carry the
nonnegativity side conditions explicitly.
-/

namespace MachLib
namespace Geometry

open Real

structure Circle where
  x : Real
  y : Real
  r : Real
  hr : 0 < r

noncomputable def centerDistSq (C D : Circle) : Real :=
  (C.x - D.x) * (C.x - D.x) + (C.y - D.y) * (C.y - D.y)

theorem centerDistSq_nonneg (C D : Circle) : 0 ≤ centerDistSq C D := by
  have h1 : 0 ≤ (C.x - D.x) * (C.x - D.x) := mul_self_nonneg _
  have h2 : 0 ≤ (C.y - D.y) * (C.y - D.y) := mul_self_nonneg _
  exact add_nonneg h1 h2

/-- Squaring is injective on the nonnegatives. -/
theorem sq_inj_nonneg {a b : Real} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a * a = b * b) : a = b := by
  rcases lt_total a b with hlt | heq | hgt
  · exfalso
    have hbpos : (0 : Real) < b := lt_of_le_of_lt ha hlt
    have h1 : a * a ≤ a * b := mul_le_mul_of_nonneg_left (le_of_lt hlt) ha
    have h2 : a * b < b * b := mul_lt_mul_of_pos_right hlt hbpos
    exact lt_irrefl_ax _ (h ▸ lt_of_le_of_lt h1 h2)
  · exact heq
  · exfalso
    have hapos : (0 : Real) < a := lt_of_le_of_lt hb hgt
    have h1 : b * b ≤ b * a := mul_le_mul_of_nonneg_left (le_of_lt hgt) hb
    have h2 : b * a < a * a := mul_lt_mul_of_pos_right hgt hapos
    exact lt_irrefl_ax _ (h ▸ lt_of_le_of_lt h1 h2)

noncomputable def centerDist (C D : Circle) : Real := sqrt (centerDistSq C D)

theorem centerDist_nonneg (C D : Circle) : 0 ≤ centerDist C D := sqrt_nonneg _

theorem centerDist_sq (C D : Circle) :
    centerDist C D * centerDist C D = centerDistSq C D :=
  sqrt_sq_nonneg _ (centerDistSq_nonneg C D)

/-- **The sqrt-free form loses nothing.** For any nonnegative target `t`, the algebraic equation
`centerDistSq = t*t` and the geometric equation `centerDist = t` are the same statement. This is
what licenses stating every tangency condition without `sqrt` ever entering a predicate. -/
theorem centerDist_eq_iff_sq (C D : Circle) {t : Real} (ht : 0 ≤ t) :
    centerDist C D = t ↔ centerDistSq C D = t * t := by
  constructor
  · intro h; rw [← centerDist_sq, h]
  · intro h
    refine sq_inj_nonneg (centerDist_nonneg C D) ht ?_
    rw [centerDist_sq]; exact h

/-- External tangency, algebraically. -/
def TangentExt (C D : Circle) : Prop :=
  centerDistSq C D = (C.r + D.r) * (C.r + D.r)

/-- Internal tangency, algebraically. -/
def TangentInt (C D : Circle) : Prop :=
  centerDistSq C D = (C.r - D.r) * (C.r - D.r)

/-- **External tangency means what it should**: centres exactly a sum-of-radii apart. -/
theorem tangentExt_iff (C D : Circle) :
    TangentExt C D ↔ centerDist C D = C.r + D.r :=
  (centerDist_eq_iff_sq C D (le_of_lt (add_pos C.hr D.hr))).symm

/-- **Internal tangency means what it should**: centres exactly a difference-of-radii apart.
`abs` appears in the GEOMETRIC side only; the algebraic side stays sign-free, which is the
point -- `(r-s)*(r-s)` already absorbs both containment orientations. -/
theorem tangentInt_iff (C D : Circle) :
    TangentInt C D ↔ centerDist C D = abs (C.r - D.r) := by
  rw [centerDist_eq_iff_sq C D (abs_nonneg _), abs_mul_self]
  exact Iff.rfl

end Geometry
end MachLib
