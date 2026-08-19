import MachLib.Geometry.Apollonius.Mode
import MachLib.QuadraticRoots
import MachLib.Geometry.Apollonius.Elimination

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



/-! ## Every mode at once

`solvesMode_iff` above did one class by hand. With the general linearisation available the same
result holds for **all eight modes simultaneously**, with the mode's signs carried symbolically —
so the remaining three classes need no separate treatment. The locus and the quadratic depend on the
mode only through `σ_A − σ_B` and `σ_A − σ_C`, each of which is `0` or `±2`. -/

@[simp] theorem cA_x : (cA ρ hρ).x = 0 := rfl
@[simp] theorem cA_y : (cA ρ hρ).y = 0 := rfl
@[simp] theorem cA_r : (cA ρ hρ).r = ρ := rfl
@[simp] theorem cB_x : (cB d ρ hρ).x = d := rfl
@[simp] theorem cB_y : (cB d ρ hρ).y = 0 := rfl
@[simp] theorem cB_r : (cB d ρ hρ).r = ρ := rfl
@[simp] theorem cC_x : (cC d ρ hρ).x = 0 := rfl
@[simp] theorem cC_y : (cC d ρ hρ).y = d := rfl
@[simp] theorem cC_r : (cC d ρ hρ).r = ρ := rfl

/-- The locus, for an arbitrary mode. -/
def OnLocusM (m : Mode) (x y r : Real) : Prop :=
  (1 + 1) * d * x = d * d + (1 + 1) * ρ * (m.sA.val - m.sB.val) * r
  ∧ (1 + 1) * d * y = d * d + (1 + 1) * ρ * (m.sA.val - m.sC.val) * r

/-- The class quadratic, for an arbitrary mode.

Its leading coefficient is `16ρ²·(…) − 4d²`, and evaluating the signs gives three distinct cases
over the four canonical classes: `−4d²` for `(o,o,o)`, which never vanishes; `16ρ² − 4d²` for
`(o,o,i)` and `(o,i,o)`, vanishing exactly at `d = 2ρ` — the mutually externally tangent inputs; and
`32ρ² − 4d²` for `(o,i,i)`, vanishing at `d² = 8ρ²`. The constant term `2d²(d² − 2ρ²)` is the same
for every mode. -/
noncomputable def QM (m : Mode) (r : Real) : Real :=
  (d * d + (1 + 1) * ρ * (m.sA.val - m.sB.val) * r)
    * (d * d + (1 + 1) * ρ * (m.sA.val - m.sB.val) * r)
  + (d * d + (1 + 1) * ρ * (m.sA.val - m.sC.val) * r)
    * (d * d + (1 + 1) * ρ * (m.sA.val - m.sC.val) * r)
  - (1 + 1) * (1 + 1) * (d * d) * (r * r + (1 + 1) * (m.sA.val * ρ) * r + ρ * ρ)

/-- **The elimination, for every mode of the family.** -/
theorem solvesModeM_iff (hd : 0 < d) (hρ : 0 < ρ) (m : Mode) (x y r : Real) :
    SolvesMode (cA ρ hρ) (cB d ρ hρ) (cC d ρ hρ) m x y r
      ↔ (OnLocusM d ρ m x y r ∧ QM d ρ m r = 0) := by
  have hd0 : d ≠ 0 := ne_of_gt hd
  have h4 : (0 : Real) < ((1 + 1) * d) * ((1 + 1) * d) :=
    mul_pos (mul_pos (add_pos zero_lt_one_ax zero_lt_one_ax) hd)
            (mul_pos (add_pos zero_lt_one_ax zero_lt_one_ax) hd)
  rw [solvesMode_iff_linear]
  simp only [cA_x, cA_y, cA_r, cB_x, cB_y, cB_r, cC_x, cC_y, cC_r]
  rw [tangentEq_expanded]
  constructor
  · rintro ⟨hA, hB, hC⟩
    have hx : (1 + 1) * d * x = d * d + (1 + 1) * ρ * (m.sA.val - m.sB.val) * r := by
      refine QuadraticRoots.eq_of_sub_eq_zero ?_
      have e : (1 + 1) * d * x - (d * d + (1 + 1) * ρ * (m.sA.val - m.sB.val) * r)
          = ((1 + 1) * (d - 0) * x + (1 + 1) * ((0 : Real) - 0) * y
              + (1 + 1) * (m.sB.val * ρ - m.sA.val * ρ) * r)
            - ((d * d + (0 : Real) * 0 - ρ * ρ) - ((0 : Real) * 0 + (0 : Real) * 0 - ρ * ρ)) := by
        mach_mpoly [d, ρ, x, y, r, m.sA.val, m.sB.val] <;> mach_ring
      rw [e, hB]; mach_mpoly [d, ρ] <;> mach_ring
    have hy : (1 + 1) * d * y = d * d + (1 + 1) * ρ * (m.sA.val - m.sC.val) * r := by
      refine QuadraticRoots.eq_of_sub_eq_zero ?_
      have e : (1 + 1) * d * y - (d * d + (1 + 1) * ρ * (m.sA.val - m.sC.val) * r)
          = ((1 + 1) * ((0 : Real) - 0) * x + (1 + 1) * (d - 0) * y
              + (1 + 1) * (m.sC.val * ρ - m.sA.val * ρ) * r)
            - ((d * d + (0 : Real) * 0 - ρ * ρ) - ((0 : Real) * 0 + (0 : Real) * 0 - ρ * ρ)) := by
        mach_mpoly [d, ρ, x, y, r, m.sA.val, m.sC.val] <;> mach_ring
      rw [e, hC]; mach_mpoly [d, ρ] <;> mach_ring
    refine ⟨⟨hx, hy⟩, ?_⟩
    have hscale : ((1 + 1) * d * x) * ((1 + 1) * d * x) + ((1 + 1) * d * y) * ((1 + 1) * d * y)
        = ((1 + 1) * d) * ((1 + 1) * d)
            * (r * r + (1 + 1) * (m.sA.val * ρ) * r + ρ * ρ) := by
      have e : ((1 + 1) * d * x) * ((1 + 1) * d * x) + ((1 + 1) * d * y) * ((1 + 1) * d * y)
          = ((1 + 1) * d) * ((1 + 1) * d)
              * ((x - 0) * (x - 0) + (y - 0) * (y - 0)) := by mach_mpoly [x, y, d]
      rw [e, hA]
    rw [hx, hy] at hscale
    have hgoal : QM d ρ m r
        = ((d * d + (1 + 1) * ρ * (m.sA.val - m.sB.val) * r)
             * (d * d + (1 + 1) * ρ * (m.sA.val - m.sB.val) * r)
           + (d * d + (1 + 1) * ρ * (m.sA.val - m.sC.val) * r)
             * (d * d + (1 + 1) * ρ * (m.sA.val - m.sC.val) * r))
          - ((1 + 1) * d) * ((1 + 1) * d) * (r * r + (1 + 1) * (m.sA.val * ρ) * r + ρ * ρ) := by
      unfold QM; mach_mpoly [d, ρ, r, m.sA.val, m.sB.val, m.sC.val] <;> mach_ring
    rw [hgoal, hscale]
    mach_mpoly [d, ρ, r, m.sA.val] <;> mach_ring
  · rintro ⟨⟨hx, hy⟩, hq⟩
    refine ⟨?_, ?_, ?_⟩
    · refine QuadraticRoots.mul_left_cancel (ne_of_gt h4) ?_
      have lhs : ((1 + 1) * d) * ((1 + 1) * d) * ((x - 0) * (x - 0) + (y - 0) * (y - 0))
          = ((1 + 1) * d * x) * ((1 + 1) * d * x) + ((1 + 1) * d * y) * ((1 + 1) * d * y) := by
        mach_mpoly [x, y, d]
      rw [lhs, hx, hy]
      have e : (d * d + (1 + 1) * ρ * (m.sA.val - m.sB.val) * r)
            * (d * d + (1 + 1) * ρ * (m.sA.val - m.sB.val) * r)
          + (d * d + (1 + 1) * ρ * (m.sA.val - m.sC.val) * r)
            * (d * d + (1 + 1) * ρ * (m.sA.val - m.sC.val) * r)
          = ((1 + 1) * d) * ((1 + 1) * d) * (r * r + (1 + 1) * (m.sA.val * ρ) * r + ρ * ρ)
            + QM d ρ m r := by
        unfold QM; mach_mpoly [d, ρ, r, m.sA.val, m.sB.val, m.sC.val] <;> mach_ring
      rw [e, hq]; mach_mpoly [d, ρ, r, m.sA.val] <;> mach_ring
    · refine QuadraticRoots.eq_of_sub_eq_zero ?_
      have e : ((1 + 1) * (d - 0) * x + (1 + 1) * ((0 : Real) - 0) * y
              + (1 + 1) * (m.sB.val * ρ - m.sA.val * ρ) * r)
            - ((d * d + (0 : Real) * 0 - ρ * ρ) - ((0 : Real) * 0 + (0 : Real) * 0 - ρ * ρ))
          = ((1 + 1) * d * x) - (d * d + (1 + 1) * ρ * (m.sA.val - m.sB.val) * r) := by
        mach_mpoly [d, ρ, x, y, r, m.sA.val, m.sB.val] <;> mach_ring
      rw [e, hx]; mach_mpoly [d, ρ, r, m.sA.val, m.sB.val] <;> mach_ring
    · refine QuadraticRoots.eq_of_sub_eq_zero ?_
      have e : ((1 + 1) * ((0 : Real) - 0) * x + (1 + 1) * (d - 0) * y
              + (1 + 1) * (m.sC.val * ρ - m.sA.val * ρ) * r)
            - (((0 : Real) * 0 + d * d - ρ * ρ) - ((0 : Real) * 0 + (0 : Real) * 0 - ρ * ρ))
          = ((1 + 1) * d * y) - (d * d + (1 + 1) * ρ * (m.sA.val - m.sC.val) * r) := by
        mach_mpoly [d, ρ, x, y, r, m.sA.val, m.sC.val] <;> mach_ring
      rw [e, hy]; mach_mpoly [d, ρ, r, m.sA.val, m.sC.val] <;> mach_ring


/-! ## The count bound: at most two solutions per mode -/

/-- The leading coefficient of `QM`, as a function of the mode. -/
noncomputable def QMlead (m : Mode) : Real :=
  (1 + 1) * ((1 + 1) * ((1 + 1) * ((1 + 1) * (ρ * ρ))))
    - (1 + 1) * (1 + 1) * ((1 + 1) * (ρ * ρ)) * (m.sA.val * m.sB.val + m.sA.val * m.sC.val)
    - (1 + 1) * (1 + 1) * (d * d)

/-- **`QM` in coefficient form.**

Proved by exhausting the eight sign assignments rather than by carrying `σ² = 1` through a symbolic
normalisation. `Sign` is a two-element type, so the case split is finite and each branch becomes a
polynomial identity with literal `±1` coefficients — which `mach_mpoly` handles, whereas threading
the square relation through an opaque atom does not. Deciding a finite thing by deciding it. -/
theorem QM_expand (m : Mode) (r : Real) :
    QM d ρ m r = QMlead d ρ m * r * r
      + (-((1 + 1) * (1 + 1) * (d * d * ρ) * (m.sB.val + m.sC.val))) * r
      + ((1 + 1) * (d * d * (d * d)) - (1 + 1) * (1 + 1) * (d * d * (ρ * ρ))) := by
  cases m with
  | mk a b c =>
    cases a <;> cases b <;> cases c <;>
      (unfold QM QMlead Sign.val; mach_mpoly [d, ρ, r] <;> mach_ring)

/-- **At most two radii per mode**, whenever the leading coefficient survives. -/
theorem at_most_two_radii_M (m : Mode) (hlead : QMlead d ρ m ≠ 0) (r s t : Real)
    (hr : QM d ρ m r = 0) (hs : QM d ρ m s = 0) (ht : QM d ρ m t = 0) :
    r = s ∨ r = t ∨ s = t := by
  rw [QM_expand] at hr hs ht
  exact QuadraticRoots.quadratic_no_three_distinct_roots hlead hr hs ht

/-- **The family's centres are never collinear.** Their determinant is `d²`, and `d > 0`, so the
general-position hypothesis that `Elimination` derived is automatic here — the family satisfies it by
construction rather than by assumption. -/
theorem centresDet_eq (hρ : 0 < ρ) :
    centresDet (cA ρ hρ) (cB d ρ hρ) (cC d ρ hρ) = d * d := by
  unfold centresDet
  simp only [cA_x, cA_y, cB_x, cB_y, cC_x, cC_y]
  mach_mpoly [d] <;> mach_ring

theorem not_collinear (hd : 0 < d) (hρ : 0 < ρ) :
    ¬ CentresCollinear (cA ρ hρ) (cB d ρ hρ) (cC d ρ hρ) := by
  unfold CentresCollinear
  rw [centresDet_eq d ρ hρ]
  exact ne_of_gt (mul_pos hd hd)

/-- **At most two solutions per mode.**

Three solutions of one mode contain a repeat — as *circles*, not merely as radii. The two halves
compose exactly as intended: `at_most_two_radii_M` collapses two of the radii, and `centre_unique`
(which is where non-collinearity does its work) upgrades equal radii to equal centres.

With the antipodal law this is the eight: four classes, at most two signed roots each, each nonzero
root decoding to one circle. What is *not* proved here is that the bound is attained — that needs
the discriminant to be positive and the roots nonzero, which is a separate question and the honest
place for the remaining general-position conditions to be forced. -/
theorem at_most_two_solutions_per_mode (hd : 0 < d) (hρ : 0 < ρ) (m : Mode)
    (hlead : QMlead d ρ m ≠ 0)
    (x₁ y₁ r₁ x₂ y₂ r₂ x₃ y₃ r₃ : Real)
    (h₁ : SolvesMode (cA ρ hρ) (cB d ρ hρ) (cC d ρ hρ) m x₁ y₁ r₁)
    (h₂ : SolvesMode (cA ρ hρ) (cB d ρ hρ) (cC d ρ hρ) m x₂ y₂ r₂)
    (h₃ : SolvesMode (cA ρ hρ) (cB d ρ hρ) (cC d ρ hρ) m x₃ y₃ r₃) :
    (x₁ = x₂ ∧ y₁ = y₂ ∧ r₁ = r₂)
    ∨ (x₁ = x₃ ∧ y₁ = y₃ ∧ r₁ = r₃)
    ∨ (x₂ = x₃ ∧ y₂ = y₃ ∧ r₂ = r₃) := by
  have q₁ := ((solvesModeM_iff d ρ hd hρ m x₁ y₁ r₁).mp h₁).2
  have q₂ := ((solvesModeM_iff d ρ hd hρ m x₂ y₂ r₂).mp h₂).2
  have q₃ := ((solvesModeM_iff d ρ hd hρ m x₃ y₃ r₃).mp h₃).2
  have hnc := not_collinear d ρ hd hρ
  rcases at_most_two_radii_M d ρ m hlead r₁ r₂ r₃ q₁ q₂ q₃ with h | h | h
  · subst h
    obtain ⟨hx, hy⟩ := centre_unique _ _ _ m hnc x₁ y₁ x₂ y₂ r₁ h₁ h₂
    exact Or.inl ⟨hx, hy, rfl⟩
  · subst h
    obtain ⟨hx, hy⟩ := centre_unique _ _ _ m hnc x₁ y₁ x₃ y₃ r₁ h₁ h₃
    exact Or.inr (Or.inl ⟨hx, hy, rfl⟩)
  · subst h
    obtain ⟨hx, hy⟩ := centre_unique _ _ _ m hnc x₂ y₂ x₃ y₃ r₂ h₂ h₃
    exact Or.inr (Or.inr ⟨hx, hy, rfl⟩)


/-- The `(outer,outer,outer)` class's leading coefficient is exactly `−4d²`. -/
theorem QMlead_ooo_eq :
    QMlead d ρ ⟨Sign.outer, Sign.outer, Sign.outer⟩ = -((1 + 1) * (1 + 1) * (d * d)) := by
  unfold QMlead Sign.val; mach_mpoly [d, ρ] <;> mach_ring

/-- **The bound is not vacuous.** For `(outer,outer,outer)` the leading coefficient never vanishes,
whatever the configuration — so `at_most_two_solutions_per_mode` applies to that class with no side
condition at all. The other three classes are the ones carrying a genuine degeneracy. -/
theorem QMlead_ooo_ne (hd : 0 < d) :
    QMlead d ρ ⟨Sign.outer, Sign.outer, Sign.outer⟩ ≠ 0 := by
  rw [QMlead_ooo_eq]
  have hpos : (0 : Real) < (1 + 1) * (1 + 1) * (d * d) :=
    mul_pos (mul_pos (add_pos zero_lt_one_ax zero_lt_one_ax)
                     (add_pos zero_lt_one_ax zero_lt_one_ax)) (mul_pos hd hd)
  intro hz
  refine (ne_of_gt hpos) ?_
  have e : (1 + 1) * (1 + 1) * (d * d) = -(-((1 + 1) * (1 + 1) * (d * d))) := by mach_ring
  rw [e, hz]; mach_ring


/-! ## Why "pairwise separated" is NOT general position

A natural guess for this family's general-position condition is that the input circles are mutually
external, `d > 2ρ`. It is **false**, and the counterexample is not exotic: at `d² = 8ρ²`
(`d ≈ 2.83ρ`, comfortably separated) the `(outer,inner,inner)` class's leading coefficient vanishes,
its equation drops to degree one, and the class contributes **one** solution instead of two. The
configuration has seven tangent circles, not eight.

The theorems below are the structural cause. They are stated rather than the count, because the count
for a specific configuration is a numeric claim this file cannot yet make (see the numeral note), but
the degeneration is symbolic and provable. -/

/-- The `(o,i,i)` leading coefficient is `32ρ² − 4d²`. -/
theorem QMlead_oii_eq :
    QMlead d ρ ⟨Sign.outer, Sign.inner, Sign.inner⟩
      = (1 + 1) * ((1 + 1) * ((1 + 1) * ((1 + 1) * ((1 + 1) * (ρ * ρ)))))
        - (1 + 1) * (1 + 1) * (d * d) := by
  unfold QMlead Sign.val; mach_mpoly [d, ρ] <;> mach_ring

/-- The `(o,i,i)` middle coefficient is `8d²ρ`, which is **positive** — so when the leading
coefficient vanishes the equation is genuinely linear, not degenerate to a constant. -/
theorem QMmid_oii_pos (hd : 0 < d) (hρ : 0 < ρ) :
    (0 : Real) < -((1 + 1) * (1 + 1) * (d * d * ρ)
      * ((⟨Sign.outer, Sign.inner, Sign.inner⟩ : Mode).sB.val
         + (⟨Sign.outer, Sign.inner, Sign.inner⟩ : Mode).sC.val)) := by
  have e : -((1 + 1) * (1 + 1) * (d * d * ρ)
      * ((⟨Sign.outer, Sign.inner, Sign.inner⟩ : Mode).sB.val
         + (⟨Sign.outer, Sign.inner, Sign.inner⟩ : Mode).sC.val))
      = (1 + 1) * ((1 + 1) * ((1 + 1) * (d * (d * ρ)))) := by
    show -((1 + 1) * (1 + 1) * (d * d * ρ) * ((-1 : Real) + -1))
        = (1 + 1) * ((1 + 1) * ((1 + 1) * (d * (d * ρ))))
    mach_mpoly [d, ρ] <;> mach_ring
  rw [e]
  exact mul_pos (add_pos zero_lt_one_ax zero_lt_one_ax)
    (mul_pos (add_pos zero_lt_one_ax zero_lt_one_ax)
      (mul_pos (add_pos zero_lt_one_ax zero_lt_one_ax) (mul_pos hd (mul_pos hd hρ))))

/-- **At `d² = 8ρ²` the `(o,i,i)` class has at most ONE radius.**

The leading coefficient vanishes, the middle coefficient does not, and a linear equation with
nonzero slope has a unique root. So that class contributes at most one circle and the total for the
configuration is at most seven — while the circles remain pairwise separated.

This is why `ApolloniusGeneralPosition` is still not defined. The obvious geometric predicate
("mutually external") is provably insufficient, and had it been written down early it would have
carried a false theorem. The condition this family actually needs is `d > 2ρ` **and** `d² ≠ 8ρ²`,
and the second conjunct has no evident geometric reading — which is precisely the kind of thing a
derivation finds and a guess does not. -/
theorem oii_at_most_one_radius (hd : 0 < d) (hρ : 0 < ρ)
    (hdeg : QMlead d ρ ⟨Sign.outer, Sign.inner, Sign.inner⟩ = 0) (r s : Real)
    (hr : QM d ρ ⟨Sign.outer, Sign.inner, Sign.inner⟩ r = 0)
    (hs : QM d ρ ⟨Sign.outer, Sign.inner, Sign.inner⟩ s = 0) :
    r = s := by
  rw [QM_expand, hdeg] at hr hs
  have hzr : ∀ z : Real,
      (0 : Real) * z * z
        + (-((1 + 1) * (1 + 1) * (d * d * ρ)
            * ((⟨Sign.outer, Sign.inner, Sign.inner⟩ : Mode).sB.val
               + (⟨Sign.outer, Sign.inner, Sign.inner⟩ : Mode).sC.val))) * z
        + ((1 + 1) * (d * d * (d * d)) - (1 + 1) * (1 + 1) * (d * d * (ρ * ρ)))
      = (-((1 + 1) * (1 + 1) * (d * d * ρ)
            * ((⟨Sign.outer, Sign.inner, Sign.inner⟩ : Mode).sB.val
               + (⟨Sign.outer, Sign.inner, Sign.inner⟩ : Mode).sC.val))) * z
        + ((1 + 1) * (d * d * (d * d)) - (1 + 1) * (1 + 1) * (d * d * (ρ * ρ))) := by
    intro z
    show (0 : Real) * z * z + _ + _ = _
    mach_mpoly [z, d, ρ] <;> mach_ring
  rw [hzr] at hr hs
  exact QuadraticRoots.linear_root_unique (ne_of_gt (QMmid_oii_pos d ρ hd hρ)) hr hs

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


/-! ## The roots, symbolically — and why `√2` is the only irrationality

The class discriminant is `8d²(d−2ρ)²(d+2ρ)²`: a perfect square times `8`. So its square root is
`2√2·d·(d²−4ρ²)` and **the only irrationality any solution of this family carries is `√2`** — for
every `d` and every `ρ`, not just for convenient ones. That is what makes an exact candidate
representable at all here: `ℚ(√2)` suffices, no general algebraic number field is needed.

The factorisation also *displays* the degeneracy rather than hiding it. The obstruction below
vanishes identically when `d = 2ρ`, which is exactly the configuration where the input circles are
mutually externally tangent (`dist(A,B) = 2ρ = ρ + ρ`) — the discriminant is zero, the two roots
collide, and the class contributes one circle instead of two. -/

/-- The leading coefficient of the class quadratic, `16ρ² − 2d²`. -/
noncomputable def lead : Real :=
  (1 + 1) * ((1 + 1) * ((1 + 1) * ((1 + 1) * (ρ * ρ)))) - (1 + 1) * (d * d)

/-- **The root identity, unconditional.**

For `r` scaled by the leading coefficient to the quadratic-formula numerator, the class quadratic
evaluates to `d²(d−2ρ)²(d+2ρ)²·(s² − 2)`. No hypothesis on `s` is needed: the statement holds for
*any* `s`, and it says precisely that the sole obstruction to `r` being a root is `s² ≠ 2`.

Stated this way rather than as "`Q r = 0` given `s = √2`" because the factored right-hand side is
the informative object — it exhibits the discriminant's square part, names the degenerate locus
`d = 2ρ`, and isolates the irrationality into a single factor. -/
theorem lead_mul_Q (r s : Real)
    (hr : lead d ρ * r
        = d * (-((1 + 1) * (d * ρ)) + s * (d * d - (1 + 1 + 1 + 1) * (ρ * ρ)))) :
    lead d ρ * Q d ρ r
      = (d * d) * (((d - (1 + 1) * ρ) * (d - (1 + 1) * ρ))
          * ((d + (1 + 1) * ρ) * (d + (1 + 1) * ρ))) * (s * s - (1 + 1)) := by
  have key : lead d ρ * Q d ρ r
      = (lead d ρ * r) * (lead d ρ * r)
        + ((1 + 1) * ((1 + 1) * (d * d * ρ))) * (lead d ρ * r)
        + lead d ρ * (d * d * (d * d) - (1 + 1) * (d * d * (ρ * ρ))) := by
    rw [Q_expand]; unfold lead; mach_mpoly [d, ρ, r]
  rw [key, hr]
  unfold lead
  -- `mach_mpoly` normalises to a residue of `0 = -0` sign goals; `mach_ring` closes those.
  mach_mpoly [d, ρ, s] <;> mach_ring

/-- **A certified root.** With `s·s = 2` the obstruction vanishes, so `r` really is a root of the
class quadratic — and `mul_left_cancel` discharges the scaling. Both roots are covered by the one
theorem: `s` ranges over *both* square roots of `2`, and negating `s` gives the other root. -/
theorem Q_eq_zero_of_root (hlead : lead d ρ ≠ 0) (r s : Real) (hs : s * s = 1 + 1)
    (hr : lead d ρ * r
        = d * (-((1 + 1) * (d * ρ)) + s * (d * d - (1 + 1 + 1 + 1) * (ρ * ρ)))) :
    Q d ρ r = 0 := by
  refine QuadraticRoots.mul_left_cancel hlead ?_
  rw [lead_mul_Q d ρ r s hr, hs]
  have z : (d * d) * (((d - (1 + 1) * ρ) * (d - (1 + 1) * ρ))
      * ((d + (1 + 1) * ρ) * (d + (1 + 1) * ρ))) * ((1 + 1) - (1 + 1)) = 0 := by
    mach_mpoly [d, ρ]
  rw [z]
  have z2 : lead d ρ * (0 : Real) = 0 := by unfold lead; mach_mpoly [d, ρ]
  rw [z2]

/-- **`√2` really is available**, so the hypothesis of `Q_eq_zero_of_root` is inhabited rather than
vacuous. This is the one place `sqrt` is used, and it is used *safely*: `sqrt_sq_nonneg` fires on a
manifestly nonnegative argument, so the totalisation branch `sqrt_neg_zero` is unreachable. -/
theorem sqrt_two_sq : sqrt (1 + 1) * sqrt (1 + 1) = 1 + 1 :=
  sqrt_sq_nonneg _ (le_of_lt (add_pos zero_lt_one_ax zero_lt_one_ax))

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
