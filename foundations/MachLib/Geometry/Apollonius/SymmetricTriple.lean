import MachLib.Geometry.Apollonius.Mode
import MachLib.QuadraticRoots

/-!
# One mode class, all the way through

The vertical slice: **linear elimination → one quadratic → candidate → positive radius → three
checked tangencies**, for a single antipodal class, before any of it is generalised.

The family is the symmetric triple

    A = (0, 0, ρ)    B = (d, 0, ρ)    C = (0, d, ρ)

with `d, ρ > 0`, and the class is `(outer, inner, inner)`. That class is chosen deliberately over
`(outer, outer, outer)`: there the two difference equations lose their `r` terms and the centre is
*constant*, so the slice would never exercise a centre that moves with the radius. Here it does —
`2d·x = d² + 4rρ` genuinely couples them.

**Everything is symbolic.** No numeral above `1` appears, which is not stylistic: `MachLib.Real`
has `OfNat` instances only for `0` and `1`, so `2` does not elaborate at all, and the corpus already
warns that `mach_mpoly` "times out on `16·P²` and proves `(c·c)·(a·a)` instantly". Keeping `d` and
`ρ` as atoms is what makes these identities close in one call each. A numeric instance is an
instantiation of this file, not a rewrite of it.

**No division anywhere.** The elimination multiplies through by `4d²` rather than solving for `x`,
and `QuadraticRoots.mul_left_cancel` undoes the scaling. `sqrt` does not appear either: the
candidate is characterised by *satisfying the quadratic*, never by a closed radical form, which is
exactly the freedom the certification layer wants — a candidate carries a root certificate, not an
expression.
-/

namespace MachLib
namespace Geometry
namespace Apollonius
namespace SymmetricTriple

open Real

variable (d ρ : Real)

/-- `A = (0, 0, ρ)`. -/
noncomputable def cA (hρ : 0 < ρ) : Circle := ⟨0, 0, ρ, hρ⟩
/-- `B = (d, 0, ρ)`. -/
noncomputable def cB (hρ : 0 < ρ) : Circle := ⟨d, 0, ρ, hρ⟩
/-- `C = (0, d, ρ)`. -/
noncomputable def cC (hρ : 0 < ρ) : Circle := ⟨0, d, ρ, hρ⟩

/-- The class under study: external to `A`, internal to `B` and `C`. -/
def classOII : Mode := ⟨Sign.outer, Sign.inner, Sign.inner⟩

/-- **The class quadratic**, `(d² + 4rρ)² − 2d²(r+ρ)²`, written out.

Its leading coefficient is `16ρ² − 2d²`, which vanishes exactly when `d² = 8ρ²` — a degeneration
this file does *not* assume away, because the elimination below never divides by it. -/
noncomputable def Q (r : Real) : Real :=
  (d * d + (1 + 1 + 1 + 1) * r * ρ) * (d * d + (1 + 1 + 1 + 1) * r * ρ)
    - (1 + 1) * (d * d) * ((r + ρ) * (r + ρ))

/-- The locus the two difference equations cut out: `2d·x = d² + 4rρ`, and the same for `y`. -/
def OnLocus (x y r : Real) : Prop :=
  (1 + 1) * d * x = d * d + (1 + 1 + 1 + 1) * r * ρ
  ∧ (1 + 1) * d * y = d * d + (1 + 1 + 1 + 1) * r * ρ

/-- **The elimination.** For this class the three-equation system is *equivalent* to a line
together with one quadratic in the radius. Both directions matter: forward is what completeness
will consume, backward is what makes a candidate checkable. -/
theorem solvesMode_iff (hd : 0 < d) (hρ : 0 < ρ) (x y r : Real) :
    SolvesMode (cA ρ hρ) (cB d ρ hρ) (cC d ρ hρ) classOII x y r
      ↔ (OnLocus d ρ x y r ∧ Q d ρ r = 0) := by
  have hd0 : d ≠ 0 := ne_of_gt hd
  -- the three raw equations, with the mode's signs already evaluated
  have unfoldA : tangentEq (cA ρ hρ).x (cA ρ hρ).y (cA ρ hρ).r classOII.sA x y r
      ↔ (x - 0) * (x - 0) + (y - 0) * (y - 0) = (r + 1 * ρ) * (r + 1 * ρ) := Iff.rfl
  have unfoldB : tangentEq (cB d ρ hρ).x (cB d ρ hρ).y (cB d ρ hρ).r classOII.sB x y r
      ↔ (x - d) * (x - d) + (y - 0) * (y - 0) = (r + -1 * ρ) * (r + -1 * ρ) := Iff.rfl
  have unfoldC : tangentEq (cC d ρ hρ).x (cC d ρ hρ).y (cC d ρ hρ).r classOII.sC x y r
      ↔ (x - 0) * (x - 0) + (y - d) * (y - d) = (r + -1 * ρ) * (r + -1 * ρ) := Iff.rfl
  constructor
  · rintro ⟨hA, hB, hC⟩
    rw [unfoldA] at hA; rw [unfoldB] at hB; rw [unfoldC] at hC
    -- A − B pins x, A − C pins y
    have hx : (1 + 1) * d * x = d * d + (1 + 1 + 1 + 1) * r * ρ := by
      have e : (1 + 1) * d * x - (d * d + (1 + 1 + 1 + 1) * r * ρ)
          = ((x - 0) * (x - 0) + (y - 0) * (y - 0) - (r + 1 * ρ) * (r + 1 * ρ))
            - ((x - d) * (x - d) + (y - 0) * (y - 0) - (r + -1 * ρ) * (r + -1 * ρ)) := by
        mach_mpoly [x, y, d, r, ρ]
      have z : ((x - 0) * (x - 0) + (y - 0) * (y - 0) - (r + 1 * ρ) * (r + 1 * ρ))
            - ((x - d) * (x - d) + (y - 0) * (y - 0) - (r + -1 * ρ) * (r + -1 * ρ)) = 0 := by
        rw [hA, hB]; mach_mpoly [r, ρ]
      rw [z] at e
      exact QuadraticRoots.eq_of_sub_eq_zero e
    have hy : (1 + 1) * d * y = d * d + (1 + 1 + 1 + 1) * r * ρ := by
      have e : (1 + 1) * d * y - (d * d + (1 + 1 + 1 + 1) * r * ρ)
          = ((x - 0) * (x - 0) + (y - 0) * (y - 0) - (r + 1 * ρ) * (r + 1 * ρ))
            - ((x - 0) * (x - 0) + (y - d) * (y - d) - (r + -1 * ρ) * (r + -1 * ρ)) := by
        mach_mpoly [x, y, d, r, ρ]
      have z : ((x - 0) * (x - 0) + (y - 0) * (y - 0) - (r + 1 * ρ) * (r + 1 * ρ))
            - ((x - 0) * (x - 0) + (y - d) * (y - d) - (r + -1 * ρ) * (r + -1 * ρ)) = 0 := by
        rw [hA, hC]; mach_mpoly [r, ρ]
      rw [z] at e
      exact QuadraticRoots.eq_of_sub_eq_zero e
    refine ⟨⟨hx, hy⟩, ?_⟩
    -- scale `eqA` by `4d²` and substitute the locus
    have hscale : ((1 + 1) * d * x) * ((1 + 1) * d * x) + ((1 + 1) * d * y) * ((1 + 1) * d * y)
        = ((1 + 1) * d) * ((1 + 1) * d) * ((r + 1 * ρ) * (r + 1 * ρ)) := by
      have e : ((1 + 1) * d * x) * ((1 + 1) * d * x) + ((1 + 1) * d * y) * ((1 + 1) * d * y)
          = ((1 + 1) * d) * ((1 + 1) * d)
              * ((x - 0) * (x - 0) + (y - 0) * (y - 0)) := by mach_mpoly [x, y, d]
      rw [e, hA]
    rw [hx, hy] at hscale
    -- `2·Q = 0`, then cancel the 2
    have htwo : (0 : Real) < 1 + 1 := add_pos zero_lt_one_ax zero_lt_one_ax
    refine QuadraticRoots.mul_left_cancel (ne_of_gt htwo) ?_
    have e : (1 + 1) * Q d ρ r
        = (d * d + (1 + 1 + 1 + 1) * r * ρ) * (d * d + (1 + 1 + 1 + 1) * r * ρ)
          + (d * d + (1 + 1 + 1 + 1) * r * ρ) * (d * d + (1 + 1 + 1 + 1) * r * ρ)
          - ((1 + 1) * d) * ((1 + 1) * d) * ((r + 1 * ρ) * (r + 1 * ρ)) := by
      unfold Q; mach_mpoly [d, r, ρ]
    rw [e, ← hscale]
    have z : (0 : Real) = (1 + 1) * 0 := by mach_ring
    rw [← z]; mach_mpoly [d, r, ρ]
  · rintro ⟨⟨hx, hy⟩, hq⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [unfoldA]
      -- cancel the 4d² the scaling introduced
      have h4 : (0 : Real) < ((1 + 1) * d) * ((1 + 1) * d) :=
        mul_pos (mul_pos (add_pos zero_lt_one_ax zero_lt_one_ax) hd)
                (mul_pos (add_pos zero_lt_one_ax zero_lt_one_ax) hd)
      refine QuadraticRoots.mul_left_cancel (ne_of_gt h4) ?_
      have lhs : ((1 + 1) * d) * ((1 + 1) * d) * ((x - 0) * (x - 0) + (y - 0) * (y - 0))
          = ((1 + 1) * d * x) * ((1 + 1) * d * x) + ((1 + 1) * d * y) * ((1 + 1) * d * y) := by
        mach_mpoly [x, y, d]
      rw [lhs, hx, hy]
      have e : (d * d + (1 + 1 + 1 + 1) * r * ρ) * (d * d + (1 + 1 + 1 + 1) * r * ρ)
            + (d * d + (1 + 1 + 1 + 1) * r * ρ) * (d * d + (1 + 1 + 1 + 1) * r * ρ)
          = ((1 + 1) * d) * ((1 + 1) * d) * ((r + 1 * ρ) * (r + 1 * ρ)) + (1 + 1) * Q d ρ r := by
        unfold Q; mach_mpoly [d, r, ρ]
      rw [e, hq]
      mach_mpoly [d, r, ρ]
    · rw [unfoldB]
      have h4 : (0 : Real) < ((1 + 1) * d) * ((1 + 1) * d) :=
        mul_pos (mul_pos (add_pos zero_lt_one_ax zero_lt_one_ax) hd)
                (mul_pos (add_pos zero_lt_one_ax zero_lt_one_ax) hd)
      refine QuadraticRoots.mul_left_cancel (ne_of_gt h4) ?_
      have lhs : ((1 + 1) * d) * ((1 + 1) * d) * ((x - d) * (x - d) + (y - 0) * (y - 0))
          = (((1 + 1) * d * x) - (1 + 1) * d * d) * (((1 + 1) * d * x) - (1 + 1) * d * d)
            + ((1 + 1) * d * y) * ((1 + 1) * d * y) := by
        mach_mpoly [x, y, d]
      rw [lhs, hx, hy]
      have e : ((d * d + (1 + 1 + 1 + 1) * r * ρ) - (1 + 1) * d * d)
              * ((d * d + (1 + 1 + 1 + 1) * r * ρ) - (1 + 1) * d * d)
            + (d * d + (1 + 1 + 1 + 1) * r * ρ) * (d * d + (1 + 1 + 1 + 1) * r * ρ)
          = ((1 + 1) * d) * ((1 + 1) * d) * ((r + -1 * ρ) * (r + -1 * ρ)) + (1 + 1) * Q d ρ r := by
        unfold Q; mach_mpoly [d, r, ρ]
      rw [e, hq]
      mach_mpoly [d, r, ρ]
    · rw [unfoldC]
      have h4 : (0 : Real) < ((1 + 1) * d) * ((1 + 1) * d) :=
        mul_pos (mul_pos (add_pos zero_lt_one_ax zero_lt_one_ax) hd)
                (mul_pos (add_pos zero_lt_one_ax zero_lt_one_ax) hd)
      refine QuadraticRoots.mul_left_cancel (ne_of_gt h4) ?_
      have lhs : ((1 + 1) * d) * ((1 + 1) * d) * ((x - 0) * (x - 0) + (y - d) * (y - d))
          = ((1 + 1) * d * x) * ((1 + 1) * d * x)
            + (((1 + 1) * d * y) - (1 + 1) * d * d) * (((1 + 1) * d * y) - (1 + 1) * d * d) := by
        mach_mpoly [x, y, d]
      rw [lhs, hx, hy]
      have e : (d * d + (1 + 1 + 1 + 1) * r * ρ) * (d * d + (1 + 1 + 1 + 1) * r * ρ)
            + ((d * d + (1 + 1 + 1 + 1) * r * ρ) - (1 + 1) * d * d)
              * ((d * d + (1 + 1 + 1 + 1) * r * ρ) - (1 + 1) * d * d)
          = ((1 + 1) * d) * ((1 + 1) * d) * ((r + -1 * ρ) * (r + -1 * ρ)) + (1 + 1) * Q d ρ r := by
        unfold Q; mach_mpoly [d, r, ρ]
      rw [e, hq]
      mach_mpoly [d, r, ρ]


/-! ## The quadratic in coefficient form, and the root bound instantiated -/

/-- `Q` written as `a·r² + b·r + c`. The leading coefficient `16ρ² − 2d²` is displayed rather than
hidden, because whether it vanishes is a real branch — `d² = 8ρ²` degenerates the class to a linear
equation with one root, and nothing above assumed it away. -/
theorem Q_expand (r : Real) :
    Q d ρ r
      = ((1 + 1) * ((1 + 1) * ((1 + 1) * ((1 + 1) * (ρ * ρ)))) - (1 + 1) * (d * d)) * r * r
        + ((1 + 1) * ((1 + 1) * (d * d * ρ))) * r
        + (d * d * (d * d) - (1 + 1) * (d * d * (ρ * ρ))) := by
  unfold Q; mach_mpoly [d, r, ρ]

/-- **At most two radii in this class** — `QuadraticRoots.quadratic_no_three_distinct_roots`
instantiated. This is where the degree-2 bound earns its place: without it the class could a priori
contribute unboundedly many candidate radii and completeness would have nothing to close against. -/
theorem at_most_two_radii
    (hlead : ((1 + 1) * ((1 + 1) * ((1 + 1) * ((1 + 1) * (ρ * ρ)))) - (1 + 1) * (d * d)) ≠ 0)
    (r s t : Real) (hr : Q d ρ r = 0) (hs : Q d ρ s = 0) (ht : Q d ρ t = 0) :
    r = s ∨ r = t ∨ s = t := by
  rw [Q_expand] at hr hs ht
  exact QuadraticRoots.quadratic_no_three_distinct_roots hlead hr hs ht

/-! ## The bridge: from an algebraic certificate to a geometric circle -/

/-- **The vertical slice, closed.**

A positive `r` on the locus satisfying the class quadratic *is* a genuine `Circle` externally
tangent to `A` and internally tangent to `B` and `C` — in `Circle.lean`'s geometric predicates, not
merely in the algebraic enumeration equation. Nothing here computes a radical: the candidate is
identified by the certificate `Q d ρ r = 0`, which is exactly the freedom the certification layer
needs to accept a root it cannot write in closed form. -/
theorem certified_tangencies (hd : 0 < d) (hρ : 0 < ρ) (x y r : Real) (hr : 0 < r)
    (hloc : OnLocus d ρ x y r) (hq : Q d ρ r = 0) :
    TangentExt ⟨x, y, r, hr⟩ (cA ρ hρ)
    ∧ TangentInt ⟨x, y, r, hr⟩ (cB d ρ hρ)
    ∧ TangentInt ⟨x, y, r, hr⟩ (cC d ρ hρ) := by
  obtain ⟨hA, hB, hC⟩ := (solvesMode_iff d ρ hd hρ x y r).mpr ⟨hloc, hq⟩
  refine ⟨?_, ?_, ?_⟩
  · show (x - 0) * (x - 0) + (y - 0) * (y - 0) = (r + ρ) * (r + ρ)
    have e : (r + 1 * ρ) * (r + 1 * ρ) = (r + ρ) * (r + ρ) := by mach_mpoly [r, ρ]
    rw [← e]; exact hA
  · show (x - d) * (x - d) + (y - 0) * (y - 0) = (r - ρ) * (r - ρ)
    have e : (r + -1 * ρ) * (r + -1 * ρ) = (r - ρ) * (r - ρ) := by mach_mpoly [r, ρ]
    rw [← e]; exact hB
  · show (x - 0) * (x - 0) + (y - d) * (y - d) = (r - ρ) * (r - ρ)
    have e : (r + -1 * ρ) * (r + -1 * ρ) = (r - ρ) * (r - ρ) := by mach_mpoly [r, ρ]
    rw [← e]; exact hC

/-- **The antipodal partner, decoded.** A *negative* root of the same quadratic is the other
solution of the class: it satisfies the system at signed radius `r`, hence the antipodal mode
`(inner, outer, outer)` at signed radius `-r`, whose geometric radius `-r` is positive. Two roots,
one quadratic, two circles, opposite orientations — the antipodal law doing its work concretely. -/
theorem negative_root_is_antipodal (hd : 0 < d) (hρ : 0 < ρ) (x y r : Real)
    (hloc : OnLocus d ρ x y r) (hq : Q d ρ r = 0) (hneg : r < 0) :
    0 < -r ∧ SolvesMode (cA ρ hρ) (cB d ρ hρ) (cC d ρ hρ) classOII.anti x y (-r) := by
  have hpos : (0 : Real) < -r := by
    have v := add_lt_add_left hneg (-r)
    have l : -r + r = 0 := by mach_ring
    have rr : -r + (0 : Real) = -r := by mach_ring
    rw [l, rr] at v; exact v
  exact ⟨hpos, (solvesMode_antipodal _ _ _ _ _ _ _).mp
    ((solvesMode_iff d ρ hd hρ x y r).mpr ⟨hloc, hq⟩)⟩

end SymmetricTriple
end Apollonius
end Geometry
end MachLib
