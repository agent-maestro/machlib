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



/-! ## General position for THIS family, minimised

Deliberately **not** called `ApolloniusGeneralPosition`. The predicate below mentions only `d` and
`ρ`, which describe the equal-radius right-isosceles family and nothing else; for arbitrary triples
the condition must involve the per-class linear determinant, leading coefficient, discriminant and
zero-root exclusion separately. Naming a family condition globally is how a family theorem later
reads as a universal one.

**Minimised, not assembled.** The first draft had four conjuncts. Three of them turned out to be
consequences:

* every discriminant is positive — `32d⁶`, `32d²(d²−4ρ²)(d²−2ρ²)`, `32d²(d²−4ρ²)²` are all `> 0`
  once `d > 2ρ`, since then `d² > 4ρ² > 2ρ²`;
* the constant term `2d²(d² − 2ρ²)` is nonzero for the same reason, so **`0` is never a root** and
  the `r ≠ 0` that `mode_unique` needs is *derived* rather than hypothesised;
* two of the three leading coefficients, `−4d²` and `16ρ² − 4d²`, are nonzero under `d > 2ρ`.

Only the third leading coefficient, `32ρ² − 4d²`, needs its own conjunct — and that is the
non-geometric one, `d² ≠ 8ρ²`, whose necessity `oii_at_most_one_radius` establishes. -/

/-- General position for the symmetric equal-radius family. Three conjuncts, each load-bearing. -/
def SymmetricGeneralPosition : Prop :=
  0 < ρ ∧ (1 + 1) * ρ < d ∧ d * d ≠ (1 + 1) * ((1 + 1) * ((1 + 1) * (ρ * ρ)))

/-- Separation gives `4ρ² < d²`. -/
theorem four_rho_sq_lt (hρ : 0 < ρ) (hsep : (1 + 1) * ρ < d) :
    ((1 + 1) * ρ) * ((1 + 1) * ρ) < d * d := by
  have h2ρ : (0 : Real) < (1 + 1) * ρ := mul_pos (add_pos zero_lt_one_ax zero_lt_one_ax) hρ
  have hdpos : (0 : Real) < d := lt_trans_ax h2ρ hsep
  have s1 : ((1 + 1) * ρ) * ((1 + 1) * ρ) < d * ((1 + 1) * ρ) :=
    mul_lt_mul_of_pos_right hsep h2ρ
  have s2 : ((1 + 1) * ρ) * d < d * d := mul_lt_mul_of_pos_right hsep hdpos
  have e : d * ((1 + 1) * ρ) = ((1 + 1) * ρ) * d := by mach_ring
  rw [e] at s1
  exact lt_trans_ax s1 s2

/-- **The constant term is nonzero**, hence `0` is not a root of any class. Derived from separation,
not assumed. -/
theorem const_ne_zero (hρ : 0 < ρ) (hsep : (1 + 1) * ρ < d) :
    ((1 + 1) * (d * d * (d * d)) - (1 + 1) * (1 + 1) * (d * d * (ρ * ρ))) ≠ 0 := by
  have h4 := four_rho_sq_lt d ρ hρ hsep
  have hdpos : (0 : Real) < d :=
    lt_trans_ax (mul_pos (add_pos zero_lt_one_ax zero_lt_one_ax) hρ) hsep
  -- `2d²(d² − 2ρ²) > 0`
  have h2 : (1 + 1) * (ρ * ρ) < d * d := by
    refine lt_trans_ax ?_ h4
    have e : ((1 + 1) * ρ) * ((1 + 1) * ρ) = (1 + 1) * ((1 + 1) * (ρ * ρ)) := by mach_ring
    rw [e]
    have hp : (0 : Real) < (1 + 1) * (ρ * ρ) :=
      mul_pos (add_pos zero_lt_one_ax zero_lt_one_ax) (mul_pos hρ hρ)
    have v := add_lt_add_left hp ((1 + 1) * (ρ * ρ))
    have l : (1 + 1) * (ρ * ρ) + 0 = (1 + 1) * (ρ * ρ) := by mach_ring
    have rr : (1 + 1) * (ρ * ρ) + (1 + 1) * (ρ * ρ) = (1 + 1) * ((1 + 1) * (ρ * ρ)) := by mach_ring
    rw [l, rr] at v
    exact v
  have hpos : (0 : Real)
      < (1 + 1) * (d * d * (d * d)) - (1 + 1) * (1 + 1) * (d * d * (ρ * ρ)) := by
    have hgap : (0 : Real) < d * d - (1 + 1) * (ρ * ρ) := by
      have v := add_lt_add_left h2 (-((1 + 1) * (ρ * ρ)))
      have l : -((1 + 1) * (ρ * ρ)) + (1 + 1) * (ρ * ρ) = 0 := by mach_ring
      have rr : -((1 + 1) * (ρ * ρ)) + d * d = d * d - (1 + 1) * (ρ * ρ) := by mach_ring
      rw [l, rr] at v; exact v
    have hprod : (0 : Real) < ((1 + 1) * (d * d)) * (d * d - (1 + 1) * (ρ * ρ)) :=
      mul_pos (mul_pos (add_pos zero_lt_one_ax zero_lt_one_ax) (mul_pos hdpos hdpos)) hgap
    have e : ((1 + 1) * (d * d)) * (d * d - (1 + 1) * (ρ * ρ))
        = (1 + 1) * (d * d * (d * d)) - (1 + 1) * (1 + 1) * (d * d * (ρ * ρ)) := by
      mach_mpoly [d, ρ] <;> mach_ring
    rw [e] at hprod; exact hprod
  exact ne_of_gt hpos

/-- **No class has `0` as a root.** Exactly what `mode_unique` needs, and it comes free. -/
theorem root_ne_zero (hρ : 0 < ρ) (hsep : (1 + 1) * ρ < d) (m : Mode) {r : Real}
    (hr : QM d ρ m r = 0) : r ≠ 0 := by
  intro hz
  subst hz
  rw [QM_expand] at hr
  refine const_ne_zero d ρ hρ hsep ?_
  have e : ((1 + 1) * (d * d * (d * d)) - (1 + 1) * (1 + 1) * (d * d * (ρ * ρ)))
      = QMlead d ρ m * 0 * 0
        + (-((1 + 1) * (1 + 1) * (d * d * ρ) * (m.sB.val + m.sC.val))) * 0
        + ((1 + 1) * (d * d * (d * d)) - (1 + 1) * (1 + 1) * (d * d * (ρ * ρ))) := by
    mach_mpoly [d, ρ, QMlead d ρ m, m.sB.val, m.sC.val] <;> mach_ring
  rw [e]; exact hr


/-- **Under general position no class degenerates.**

All eight modes at once. `QMlead` is *antipode-invariant* — it depends on the signs only through the
products `σ_Aσ_B` and `σ_Aσ_C` — so the eight modes carry only **three** distinct leading
coefficients, one per antipodal class shape. Each is excluded by a different conjunct of
`SymmetricGeneralPosition`, so all three conjuncts are load-bearing and none is redundant. -/
theorem QMlead_ne_zero (gp : SymmetricGeneralPosition d ρ) (m : Mode) : QMlead d ρ m ≠ 0 := by
  obtain ⟨hρ, hsep, hne8⟩ := gp
  have two_pos : (0 : Real) < 1 + 1 := add_pos zero_lt_one_ax zero_lt_one_ax
  have hdpos : (0 : Real) < d := lt_trans_ax (mul_pos two_pos hρ) hsep
  have h4 := four_rho_sq_lt d ρ hρ hsep
  have hgap : (0 : Real) < d * d - ((1 + 1) * ρ) * ((1 + 1) * ρ) := by
    have v := add_lt_add_left h4 (-(((1 + 1) * ρ) * ((1 + 1) * ρ)))
    have l : -(((1 + 1) * ρ) * ((1 + 1) * ρ)) + ((1 + 1) * ρ) * ((1 + 1) * ρ) = 0 := by mach_ring
    have rr : -(((1 + 1) * ρ) * ((1 + 1) * ρ)) + d * d
        = d * d - ((1 + 1) * ρ) * ((1 + 1) * ρ) := by mach_ring
    rw [l, rr] at v; exact v
  have key : ∀ v : Real, v ≠ 0 → ∀ w : Real, w = v → w ≠ 0 := fun _ hv _ hw => by rw [hw]; exact hv
  -- (1) `−4d²` : nonzero because `d > 0`
  have hA : -((1 + 1) * (1 + 1) * (d * d)) ≠ 0 := by
    have hpos : (0 : Real) < (1 + 1) * (1 + 1) * (d * d) :=
      mul_pos (mul_pos two_pos two_pos) (mul_pos hdpos hdpos)
    intro hz
    refine (ne_of_gt hpos) ?_
    have e : (1 + 1) * (1 + 1) * (d * d) = -(-((1 + 1) * (1 + 1) * (d * d))) := by mach_ring
    rw [e, hz]; mach_ring
  -- (2) `16ρ² − 4d²` : nonzero because `4ρ² < d²`
  have hB : (1 + 1) * ((1 + 1) * ((1 + 1) * ((1 + 1) * (ρ * ρ))))
      - (1 + 1) * (1 + 1) * (d * d) ≠ 0 := by
    have hpos : (0 : Real) < (1 + 1) * (1 + 1) * (d * d)
        - (1 + 1) * ((1 + 1) * ((1 + 1) * ((1 + 1) * (ρ * ρ)))) := by
      have e : (1 + 1) * (1 + 1) * (d * d)
            - (1 + 1) * ((1 + 1) * ((1 + 1) * ((1 + 1) * (ρ * ρ))))
          = ((1 + 1) * (1 + 1)) * (d * d - ((1 + 1) * ρ) * ((1 + 1) * ρ)) := by
        mach_mpoly [d, ρ] <;> mach_ring
      rw [e]; exact mul_pos (mul_pos two_pos two_pos) hgap
    intro hz
    refine (ne_of_gt hpos) ?_
    have e2 : (1 + 1) * (1 + 1) * (d * d)
          - (1 + 1) * ((1 + 1) * ((1 + 1) * ((1 + 1) * (ρ * ρ))))
        = -((1 + 1) * ((1 + 1) * ((1 + 1) * ((1 + 1) * (ρ * ρ))))
            - (1 + 1) * (1 + 1) * (d * d)) := by mach_mpoly [d, ρ] <;> mach_ring
    rw [e2, hz]; mach_ring
  -- (3) `32ρ² − 4d²` : nonzero only because `d² ≠ 8ρ²`, the non-geometric conjunct
  have hC : (1 + 1) * ((1 + 1) * ((1 + 1) * ((1 + 1) * ((1 + 1) * (ρ * ρ)))))
      - (1 + 1) * (1 + 1) * (d * d) ≠ 0 := by
    intro hz
    refine hne8 ?_
    have e : ((1 + 1) * (1 + 1))
          * ((1 + 1) * ((1 + 1) * ((1 + 1) * (ρ * ρ))) - d * d)
        = (1 + 1) * ((1 + 1) * ((1 + 1) * ((1 + 1) * ((1 + 1) * (ρ * ρ)))))
          - (1 + 1) * (1 + 1) * (d * d) := by mach_mpoly [d, ρ] <;> mach_ring
    rw [← e] at hz
    exact (QuadraticRoots.eq_of_sub_eq_zero
      (QuadraticRoots.right_of_mul_eq_zero (ne_of_gt (mul_pos two_pos two_pos)) hz)).symm
  cases m with
  | mk a b c =>
    cases a <;> cases b <;> cases c <;>
      first
        | (refine key _ hA _ ?_; unfold QMlead Sign.val
           (mach_mpoly [d, ρ] <;> mach_ring); done)
        | (refine key _ hB _ ?_; unfold QMlead Sign.val
           (mach_mpoly [d, ρ] <;> mach_ring); done)
        | (refine key _ hC _ ?_; unfold QMlead Sign.val
           (mach_mpoly [d, ρ] <;> mach_ring); done)


theorem gp_rho_pos (gp : SymmetricGeneralPosition d ρ) : 0 < ρ := gp.1

theorem gp_d_pos (gp : SymmetricGeneralPosition d ρ) : 0 < d :=
  lt_trans_ax (mul_pos (add_pos zero_lt_one_ax zero_lt_one_ax) gp.1) gp.2.1

/-- **Under general position: at most two solutions per mode, with no side condition left over.**
The `QMlead ≠ 0` hypothesis of `at_most_two_solutions_per_mode` is now discharged rather than
carried. -/
theorem at_most_two_of_gp (gp : SymmetricGeneralPosition d ρ) (m : Mode)
    (x₁ y₁ r₁ x₂ y₂ r₂ x₃ y₃ r₃ : Real)
    (h₁ : SolvesMode (cA ρ (gp_rho_pos d ρ gp)) (cB d ρ (gp_rho_pos d ρ gp))
            (cC d ρ (gp_rho_pos d ρ gp)) m x₁ y₁ r₁)
    (h₂ : SolvesMode (cA ρ (gp_rho_pos d ρ gp)) (cB d ρ (gp_rho_pos d ρ gp))
            (cC d ρ (gp_rho_pos d ρ gp)) m x₂ y₂ r₂)
    (h₃ : SolvesMode (cA ρ (gp_rho_pos d ρ gp)) (cB d ρ (gp_rho_pos d ρ gp))
            (cC d ρ (gp_rho_pos d ρ gp)) m x₃ y₃ r₃) :
    (x₁ = x₂ ∧ y₁ = y₂ ∧ r₁ = r₂)
    ∨ (x₁ = x₃ ∧ y₁ = y₃ ∧ r₁ = r₃)
    ∨ (x₂ = x₃ ∧ y₂ = y₃ ∧ r₂ = r₃) :=
  at_most_two_solutions_per_mode d ρ (gp_d_pos d ρ gp) (gp_rho_pos d ρ gp) m
    (QMlead_ne_zero d ρ gp m) x₁ y₁ r₁ x₂ y₂ r₂ x₃ y₃ r₃ h₁ h₂ h₃

/-- **Under general position a solution determines its mode**, unconditionally.

`mode_unique` needs `r ≠ 0`, and that is exactly what `root_ne_zero` supplies from separation — so
the obligation is discharged inside the theorem rather than pushed onto the caller. This is the
place the earlier design decision pays: because the algebraic layer admits `r = 0` as a
*representable* candidate, the hypothesis could be stated, tracked, and now retired. -/
theorem mode_unique_of_gp (gp : SymmetricGeneralPosition d ρ) (m m' : Mode) (x y r : Real)
    (h : SolvesMode (cA ρ (gp_rho_pos d ρ gp)) (cB d ρ (gp_rho_pos d ρ gp))
           (cC d ρ (gp_rho_pos d ρ gp)) m x y r)
    (h' : SolvesMode (cA ρ (gp_rho_pos d ρ gp)) (cB d ρ (gp_rho_pos d ρ gp))
            (cC d ρ (gp_rho_pos d ρ gp)) m' x y r) :
    m = m' := by
  have hρ := gp_rho_pos d ρ gp
  have hsep := gp.2.1
  have hq := ((solvesModeM_iff d ρ (gp_d_pos d ρ gp) hρ m x y r).mp h).2
  exact mode_unique _ _ _ m m' x y r (root_ne_zero d ρ hρ hsep m hq) h h'


/-! ## Attainment: every class really has two distinct roots -/

/-- The middle coefficient of `QM`. -/
noncomputable def QMmid (m : Mode) : Real :=
  -((1 + 1) * (1 + 1) * (d * d * ρ) * (m.sB.val + m.sC.val))

/-- The constant coefficient of `QM` — the same for every mode. -/
noncomputable def QMconst : Real :=
  (1 + 1) * (d * d * (d * d)) - (1 + 1) * (1 + 1) * (d * d * (ρ * ρ))

/-- The class discriminant, in exactly the shape `quadratic_root_of_disc` consumes. -/
noncomputable def QMdisc (m : Mode) : Real :=
  QMmid d ρ m * QMmid d ρ m - (1 + 1) * (1 + 1) * QMlead d ρ m * QMconst d ρ

theorem QM_expand' (m : Mode) (r : Real) :
    QM d ρ m r = QMlead d ρ m * r * r + QMmid d ρ m * r + QMconst d ρ := by
  unfold QMmid QMconst; exact QM_expand d ρ m r

/-- The constant term is strictly positive under separation. -/
theorem QMconst_pos (hρ : 0 < ρ) (hsep : (1 + 1) * ρ < d) : 0 < QMconst d ρ := by
  have two_pos : (0 : Real) < 1 + 1 := add_pos zero_lt_one_ax zero_lt_one_ax
  have hd : (0 : Real) < d := lt_trans_ax (mul_pos two_pos hρ) hsep
  have h4 := four_rho_sq_lt d ρ hρ hsep
  have step : (1 + 1) * (ρ * ρ) < ((1 + 1) * ρ) * ((1 + 1) * ρ) := by
    have hp : (0 : Real) < (1 + 1) * (ρ * ρ) := mul_pos two_pos (mul_pos hρ hρ)
    have v := add_lt_add_left hp ((1 + 1) * (ρ * ρ))
    have l : (1 + 1) * (ρ * ρ) + 0 = (1 + 1) * (ρ * ρ) := by mach_ring
    have rr : (1 + 1) * (ρ * ρ) + (1 + 1) * (ρ * ρ) = ((1 + 1) * ρ) * ((1 + 1) * ρ) := by mach_ring
    rw [l, rr] at v; exact v
  have hgap : (0 : Real) < d * d - (1 + 1) * (ρ * ρ) := by
    have h2 : (1 + 1) * (ρ * ρ) < d * d := lt_trans_ax step h4
    have v := add_lt_add_left h2 (-((1 + 1) * (ρ * ρ)))
    have l : -((1 + 1) * (ρ * ρ)) + (1 + 1) * (ρ * ρ) = 0 := by mach_ring
    have rr : -((1 + 1) * (ρ * ρ)) + d * d = d * d - (1 + 1) * (ρ * ρ) := by mach_ring
    rw [l, rr] at v; exact v
  have hprod : (0 : Real) < ((1 + 1) * (d * d)) * (d * d - (1 + 1) * (ρ * ρ)) :=
    mul_pos (mul_pos two_pos (mul_pos hd hd)) hgap
  have e : ((1 + 1) * (d * d)) * (d * d - (1 + 1) * (ρ * ρ)) = QMconst d ρ := by
    unfold QMconst; mach_mpoly [d, ρ] <;> mach_ring
  rw [e] at hprod; exact hprod

/-- **A class with a negative leading coefficient attains two roots.**

`disc = mid² + 4(−lead)·const`, a square plus a positive product, so positivity costs no expansion
at all. Under separation this covers the `(o,o,o)` shape (`lead = −4d²`) and the
`(o,o,i)`/`(o,i,o)` shape (`lead = 16ρ² − 4d² < 0` since `d² > 4ρ²`) — six of the eight modes.

The `(o,i,i)` shape is the exception and genuinely so: its leading coefficient `32ρ² − 4d²` is
negative only when `d² > 8ρ²`. In the band `4ρ² < d² < 8ρ²` the discriminant is still positive —
it equals `32d²(d² − 4ρ²)²` — but establishing that needs the degree-6 identity expanded, and
`mach_mpoly` hits the same `Lean.Meta.acLt` wall as the numeral instantiation (unchanged at 10×
heartbeats and 500× recursion depth). Recorded as the boundary it is, not hidden. -/
theorem QMdisc_pos_of_lead_neg (hρ : 0 < ρ) (hsep : (1 + 1) * ρ < d) (m : Mode)
    (hneg : QMlead d ρ m < 0) : 0 < QMdisc d ρ m :=
  QuadraticRoots.disc_pos_of_lead_neg hneg (QMconst_pos d ρ hρ hsep)

/-- **Attainment for such a class**: two distinct roots, given any square root of the discriminant. -/
theorem QM_two_distinct_roots (gp : SymmetricGeneralPosition d ρ) (m : Mode)
    (hneg : QMlead d ρ m < 0) (s : Real) (hs : s * s = QMdisc d ρ m) (hsne : s ≠ 0) :
    ∃ r₁ r₂ : Real, r₁ ≠ r₂ ∧ QM d ρ m r₁ = 0 ∧ QM d ρ m r₂ = 0 := by
  obtain ⟨r₁, r₂, hne, h₁, h₂⟩ :=
    @QuadraticRoots.two_distinct_roots (QMlead d ρ m) (QMmid d ρ m) (QMconst d ρ) s
      (QMlead_ne_zero d ρ gp m) hsne (by rw [hs]; unfold QMdisc; mach_ring)
  exact ⟨r₁, r₂, hne, by rw [QM_expand']; exact h₁, by rw [QM_expand']; exact h₂⟩


/-! ### Every class attains, all eight modes -/

/-- `QMlead` is antipode-invariant: it sees the signs only through `σ_Aσ_B` and `σ_Aσ_C`. -/
theorem QMlead_anti (m : Mode) : QMlead d ρ m.anti = QMlead d ρ m := by
  cases m with
  | mk a b c =>
    cases a <;> cases b <;> cases c <;>
      (unfold QMlead Mode.anti Sign.flip Sign.val; mach_mpoly [d, ρ] <;> mach_ring)

/-- `QMmid` **negates** under the antipode — and squares away in the discriminant. -/
theorem QMmid_anti (m : Mode) : QMmid d ρ m.anti = -(QMmid d ρ m) := by
  cases m with
  | mk a b c =>
    cases a <;> cases b <;> cases c <;>
      (unfold QMmid Mode.anti Sign.flip Sign.val; mach_mpoly [d, ρ] <;> mach_ring)

/-- **The discriminant is antipode-invariant**, so four classes carry four discriminants. Proved
component-wise rather than by re-deriving: `QMlead` is invariant, `QMmid` negates and is squared,
`QMconst` does not mention the mode at all. -/
theorem QMdisc_anti (m : Mode) : QMdisc d ρ m.anti = QMdisc d ρ m := by
  unfold QMdisc
  rw [QMlead_anti, QMmid_anti]
  have e : -(QMmid d ρ m) * -(QMmid d ρ m) = QMmid d ρ m * QMmid d ρ m := by
    mach_mpoly [QMmid d ρ m] <;> mach_ring
  rw [e]

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

/-! ### What compressing the variables established

Substituting `X = d²`, `Y = ρ²` turns the `(o,i,i)` discriminant identity from degree 6 in `d, ρ`
into **degree 3 in two abstract variables**. That was worth trying, and it changed the failure: the
`maxRecDepth` limit cleared, and only `Lean.Meta.acLt` remained — still unmoved at 5× heartbeats on
the *degree-3* form.

So the blocker is **not** polynomial degree and **not** expression presentation. It is the unary
numeral encoding: `64` written as six nested `(1 + 1)` factors generates an AC-permutation space
`acLt` cannot search, whatever the degree. `MachLib.Real` carries `OfNat` for `0` and `1` only, so
there is no other way to write a constant at this layer — which makes `natCast` the next thing to
try and makes this a *diagnosis* rather than a dead end.

The three coefficient identities below are small enough to close, and are exactly what the assembled
discriminant proof will consume once constants can be written atomically. The target is

    QMdisc (o,i,i) = 32·d²·(d² − 4ρ²)²

from which positivity follows from separation alone (`d² > 4ρ²`), with no band split and no appeal
to the sign of the leading coefficient. -/

/-- `(o,i,i)`'s middle coefficient, `8d²ρ`. -/
theorem QMmid_oii_eq :
    QMmid d ρ ⟨Sign.outer, Sign.inner, Sign.inner⟩
      = (1 + 1) * ((1 + 1) * ((1 + 1) * (d * d * ρ))) := by
  unfold QMmid Sign.val; mach_mpoly [d, ρ] <;> mach_ring

/-- `(o,i,i)`'s leading coefficient, factored as `4(8ρ² − d²)`. -/
theorem QMlead_oii_factored :
    QMlead d ρ ⟨Sign.outer, Sign.inner, Sign.inner⟩
      = (1 + 1) * ((1 + 1) * ((1 + 1) * ((1 + 1) * ((1 + 1) * (ρ * ρ))) - d * d)) := by
  rw [QMlead_oii_eq]; mach_mpoly [d, ρ] <;> mach_ring

/-- The constant term, factored as `2d²(d² − 2ρ²)`. -/
theorem QMconst_factored :
    QMconst d ρ = (1 + 1) * ((d * d) * (d * d - (1 + 1) * (ρ * ρ))) := by
  unfold QMconst; mach_mpoly [d, ρ] <;> mach_ring

/-! ### Assembling the discriminant in steps no single call can choke on

The degree-3 identity dies in `acLt` as one `mach_mpoly` call. Split into four steps — each of which
expands **at most one** product — every step closes in about a second. The trick is to keep the
binomial product atomic (`P`, `Q`, `E` below) until the last moment, so no call ever distributes two
brackets at once.

This is the "compress before normalising" move done by hand. It is what a future algebraic layer
should automate; until then it is cheap enough to do explicitly, and explicit is more auditable. -/

/-- Step 1 — the core, degree 2: `(8Y−X)(X−2Y) = 2XY − (X−4Y)²`. -/
theorem oii_core (X Y : Real) :
    ((1 + 1) * ((1 + 1) * ((1 + 1) * Y)) - X) * (X - (1 + 1) * Y)
      = (1 + 1) * (X * Y)
        - (X - (1 + 1) * ((1 + 1) * Y)) * (X - (1 + 1) * ((1 + 1) * Y)) := by
  mach_mpoly [X, Y] <;> mach_ring

/-- Step 2 — monomial regrouping: `4·(4P)·(2XQ) = 32X(PQ)`. -/
theorem oii_regroup (X P Q : Real) :
    (1 + 1) * (1 + 1) * ((1 + 1) * ((1 + 1) * P)) * ((1 + 1) * (X * Q))
      = (1 + 1) * ((1 + 1) * ((1 + 1) * ((1 + 1) * ((1 + 1) * (X * (P * Q)))))) := by
  mach_mpoly [X, P, Q] <;> mach_ring

/-- Step 3 — the middle coefficient squared: `(8Zρ)² = 64Z²ρ²`. -/
theorem oii_midsq (Z w : Real) :
    ((1 + 1) * ((1 + 1) * ((1 + 1) * (Z * w)))) * ((1 + 1) * ((1 + 1) * ((1 + 1) * (Z * w))))
      = (1 + 1) * ((1 + 1) * ((1 + 1) * ((1 + 1) * ((1 + 1) * ((1 + 1) * (Z * Z * (w * w))))))) := by
  mach_mpoly [Z, w] <;> mach_ring

/-- Step 4 — the one distribution: `64X²Y − 32X(2XY − E) = 32XE`. -/
theorem oii_final (X Y E : Real) :
    (1 + 1) * ((1 + 1) * ((1 + 1) * ((1 + 1) * ((1 + 1) * ((1 + 1) * (X * X * Y))))))
      - (1 + 1) * ((1 + 1) * ((1 + 1) * ((1 + 1) * ((1 + 1) * (X * ((1 + 1) * (X * Y) - E))))))
    = (1 + 1) * ((1 + 1) * ((1 + 1) * ((1 + 1) * ((1 + 1) * (X * E))))) := by
  mach_mpoly [X, Y, E] <;> mach_ring

/-- **`(o,i,i)`'s discriminant is `32d²(d² − 4ρ²)²`.** -/
theorem QMdisc_oii_eq :
    QMdisc d ρ ⟨Sign.outer, Sign.inner, Sign.inner⟩
      = (1 + 1) * ((1 + 1) * ((1 + 1) * ((1 + 1) * ((1 + 1)
          * ((d * d) * ((d * d - (1 + 1) * ((1 + 1) * (ρ * ρ)))
                        * (d * d - (1 + 1) * ((1 + 1) * (ρ * ρ))))))))) := by
  unfold QMdisc
  rw [QMmid_oii_eq, QMlead_oii_factored, QMconst_factored,
      oii_midsq (d * d) ρ,
      oii_regroup (d * d) ((1 + 1) * ((1 + 1) * ((1 + 1) * (ρ * ρ))) - d * d)
        (d * d - (1 + 1) * (ρ * ρ)),
      oii_core (d * d) (ρ * ρ)]
  exact oii_final (d * d) (ρ * ρ)
    ((d * d - (1 + 1) * ((1 + 1) * (ρ * ρ))) * (d * d - (1 + 1) * ((1 + 1) * (ρ * ρ))))

/-- **`(o,i,i)`'s discriminant is positive from SEPARATION ALONE.**

No band split, no appeal to the sign of the leading coefficient. `d > 2ρ` gives `d² − 4ρ² > 0`, its
square is positive, and `32d²` is positive — so the class attains two distinct roots throughout
`d > 2ρ`, including the band `4ρ² < d² < 8ρ²` where the cheap `lead < 0` argument does not apply.

This is the better structural statement: discriminant positivity and leading-coefficient
non-vanishing are **independent** properties with different exceptional loci — `d² = 4ρ²` for the
first, `d² = 8ρ²` for the second — which is exactly why the seven-circle configuration is a
degree-drop rather than a repeated root. -/
theorem QMdisc_oii_pos (hρ : 0 < ρ) (hsep : (1 + 1) * ρ < d) :
    0 < QMdisc d ρ ⟨Sign.outer, Sign.inner, Sign.inner⟩ := by
  have two_pos : (0 : Real) < 1 + 1 := add_pos zero_lt_one_ax zero_lt_one_ax
  have hd : (0 : Real) < d := lt_trans_ax (mul_pos two_pos hρ) hsep
  have h4 := four_rho_sq_lt d ρ hρ hsep
  have hgap : (0 : Real) < d * d - (1 + 1) * ((1 + 1) * (ρ * ρ)) := by
    have e : ((1 + 1) * ρ) * ((1 + 1) * ρ) = (1 + 1) * ((1 + 1) * (ρ * ρ)) := by mach_ring
    rw [e] at h4
    have v := add_lt_add_left h4 (-((1 + 1) * ((1 + 1) * (ρ * ρ))))
    have l : -((1 + 1) * ((1 + 1) * (ρ * ρ))) + (1 + 1) * ((1 + 1) * (ρ * ρ)) = 0 := by mach_ring
    have rr : -((1 + 1) * ((1 + 1) * (ρ * ρ))) + d * d
        = d * d - (1 + 1) * ((1 + 1) * (ρ * ρ)) := by mach_ring
    rw [l, rr] at v; exact v
  rw [QMdisc_oii_eq]
  exact mul_pos two_pos (mul_pos two_pos (mul_pos two_pos (mul_pos two_pos
    (mul_pos two_pos (mul_pos (mul_pos hd hd) (mul_pos hgap hgap))))))

/-- **Every mode's discriminant is positive under general position.**

Six of the eight go through `disc_pos_of_lead_neg` (their leading coefficient is negative under
separation); the `(o,i,i)` class goes through its factored discriminant, and its antipode `(i,o,o)`
through `QMdisc_anti`. Note the two routes are genuinely different arguments, not two spellings of
one — which is the honest shape, since the `(o,i,i)` class is the one whose leading coefficient can
vanish while its discriminant does not. -/
theorem QMdisc_pos_all (gp : SymmetricGeneralPosition d ρ) (m : Mode) : 0 < QMdisc d ρ m := by
  have hρ := gp_rho_pos d ρ gp
  have hsep := gp.2.1
  have hd := gp_d_pos d ρ gp
  have two_pos : (0 : Real) < 1 + 1 := add_pos zero_lt_one_ax zero_lt_one_ax
  have h4 := four_rho_sq_lt d ρ hρ hsep
  -- the two negative leading-coefficient values
  have negA : -((1 + 1) * (1 + 1) * (d * d)) < 0 := by
    have hp : (0 : Real) < (1 + 1) * (1 + 1) * (d * d) :=
      mul_pos (mul_pos two_pos two_pos) (mul_pos hd hd)
    have v := add_lt_add_left hp (-((1 + 1) * (1 + 1) * (d * d)))
    have l : -((1 + 1) * (1 + 1) * (d * d)) + 0 = -((1 + 1) * (1 + 1) * (d * d)) := by mach_ring
    have rr : -((1 + 1) * (1 + 1) * (d * d)) + (1 + 1) * (1 + 1) * (d * d) = 0 := by mach_ring
    rw [l, rr] at v; exact v
  have negB : (1 + 1) * ((1 + 1) * ((1 + 1) * ((1 + 1) * (ρ * ρ))))
      - (1 + 1) * (1 + 1) * (d * d) < 0 := by
    have e : ((1 + 1) * ρ) * ((1 + 1) * ρ) = (1 + 1) * ((1 + 1) * (ρ * ρ)) := by mach_ring
    rw [e] at h4
    have hp : (0 : Real) < (1 + 1) * (1 + 1) * (d * d)
        - (1 + 1) * ((1 + 1) * ((1 + 1) * ((1 + 1) * (ρ * ρ)))) := by
      have e2 : (1 + 1) * (1 + 1) * (d * d)
            - (1 + 1) * ((1 + 1) * ((1 + 1) * ((1 + 1) * (ρ * ρ))))
          = ((1 + 1) * (1 + 1)) * (d * d - (1 + 1) * ((1 + 1) * (ρ * ρ))) := by
        mach_mpoly [d, ρ] <;> mach_ring
      rw [e2]
      refine mul_pos (mul_pos two_pos two_pos) ?_
      have v := add_lt_add_left h4 (-((1 + 1) * ((1 + 1) * (ρ * ρ))))
      have l : -((1 + 1) * ((1 + 1) * (ρ * ρ))) + (1 + 1) * ((1 + 1) * (ρ * ρ)) = 0 := by mach_ring
      have rr : -((1 + 1) * ((1 + 1) * (ρ * ρ))) + d * d
          = d * d - (1 + 1) * ((1 + 1) * (ρ * ρ)) := by mach_ring
      rw [l, rr] at v; exact v
    have v := add_lt_add_left hp ((1 + 1) * ((1 + 1) * ((1 + 1) * ((1 + 1) * (ρ * ρ))))
      - (1 + 1) * (1 + 1) * (d * d))
    have l : (1 + 1) * ((1 + 1) * ((1 + 1) * ((1 + 1) * (ρ * ρ))))
          - (1 + 1) * (1 + 1) * (d * d) + 0
        = (1 + 1) * ((1 + 1) * ((1 + 1) * ((1 + 1) * (ρ * ρ))))
          - (1 + 1) * (1 + 1) * (d * d) := by mach_ring
    have rr : (1 + 1) * ((1 + 1) * ((1 + 1) * ((1 + 1) * (ρ * ρ))))
          - (1 + 1) * (1 + 1) * (d * d)
          + ((1 + 1) * (1 + 1) * (d * d)
             - (1 + 1) * ((1 + 1) * ((1 + 1) * ((1 + 1) * (ρ * ρ))))) = 0 := by
      mach_mpoly [d, ρ] <;> mach_ring
    rw [l, rr] at v; exact v
  have keyneg : ∀ v : Real, v < 0 → ∀ w : Real, w = v → w < 0 := fun _ hv _ hw => by
    rw [hw]; exact hv
  -- explicit per-case dispatch: `first` cannot backtrack out of a failing nested `by`,
  -- so each of the eight modes names its own route.
  have viaA : ∀ m' : Mode, QMlead d ρ m' = -((1 + 1) * (1 + 1) * (d * d)) → 0 < QMdisc d ρ m' :=
    fun m' h => QMdisc_pos_of_lead_neg d ρ hρ hsep m' (keyneg _ negA _ h)
  have viaB : ∀ m' : Mode,
      QMlead d ρ m' = (1 + 1) * ((1 + 1) * ((1 + 1) * ((1 + 1) * (ρ * ρ))))
                      - (1 + 1) * (1 + 1) * (d * d) → 0 < QMdisc d ρ m' :=
    fun m' h => QMdisc_pos_of_lead_neg d ρ hρ hsep m' (keyneg _ negB _ h)
  have anti : QMdisc d ρ ⟨Sign.inner, Sign.outer, Sign.outer⟩
      = QMdisc d ρ ⟨Sign.outer, Sign.inner, Sign.inner⟩ :=
    QMdisc_anti d ρ ⟨Sign.outer, Sign.inner, Sign.inner⟩
  cases m with
  | mk a b c =>
    cases a <;> cases b <;> cases c
    · exact viaA _ (by unfold QMlead Sign.val; mach_mpoly [d, ρ] <;> mach_ring)
    · exact viaB _ (by unfold QMlead Sign.val; mach_mpoly [d, ρ] <;> mach_ring)
    · exact viaB _ (by unfold QMlead Sign.val; mach_mpoly [d, ρ] <;> mach_ring)
    · exact QMdisc_oii_pos d ρ hρ hsep
    · rw [anti]; exact QMdisc_oii_pos d ρ hρ hsep
    · exact viaB _ (by unfold QMlead Sign.val; mach_mpoly [d, ρ] <;> mach_ring)
    · exact viaB _ (by unfold QMlead Sign.val; mach_mpoly [d, ρ] <;> mach_ring)
    · exact viaA _ (by unfold QMlead Sign.val; mach_mpoly [d, ρ] <;> mach_ring)


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


/-- **Attainment, for every mode.** Under general position each mode's quadratic has two distinct
real roots — the discriminant is positive, so `√disc` is a nonzero square root of it, and
`two_distinct_roots` constructs both branches.

This is where `sqrt` finally enters the development, and it enters at the *candidate* boundary
exactly as intended: the totalisation branch is unreachable because `QMdisc_pos_all` supplies strict
positivity, so `sqrt_sq_nonneg` fires on a manifestly nonnegative argument.

With the antipodal law this is the eight: four classes, two distinct roots each, each nonzero root
(`root_ne_zero`) decoding to one circle in one of the class's two modes, and `mode_unique` making
those circles distinct. -/
theorem QM_two_roots_of_gp (gp : SymmetricGeneralPosition d ρ) (m : Mode) :
    ∃ r₁ r₂ : Real, r₁ ≠ r₂ ∧ QM d ρ m r₁ = 0 ∧ QM d ρ m r₂ = 0 := by
  have hpos := QMdisc_pos_all d ρ gp m
  have hs : sqrt (QMdisc d ρ m) * sqrt (QMdisc d ρ m) = QMdisc d ρ m :=
    sqrt_sq_nonneg _ (le_of_lt hpos)
  have hsne : sqrt (QMdisc d ρ m) ≠ 0 := by
    intro hz
    rw [hz] at hs
    have z : (0 : Real) * 0 = 0 := by mach_ring
    rw [z] at hs
    exact (ne_of_gt hpos) hs.symm
  obtain ⟨r₁, r₂, hne, h₁, h₂⟩ :=
    @QuadraticRoots.two_distinct_roots (QMlead d ρ m) (QMmid d ρ m) (QMconst d ρ)
      (sqrt (QMdisc d ρ m)) (QMlead_ne_zero d ρ gp m) hsne
      (by rw [hs]; unfold QMdisc; mach_ring)
  exact ⟨r₁, r₂, hne, by rw [QM_expand']; exact h₁, by rw [QM_expand']; exact h₂⟩

/-- **Both roots are nonzero and carry distinct modes.** The decode obligations, discharged. -/
theorem QM_roots_decode (gp : SymmetricGeneralPosition d ρ) (m : Mode) :
    ∃ r₁ r₂ : Real, r₁ ≠ r₂ ∧ r₁ ≠ 0 ∧ r₂ ≠ 0
      ∧ QM d ρ m r₁ = 0 ∧ QM d ρ m r₂ = 0 := by
  obtain ⟨r₁, r₂, hne, h₁, h₂⟩ := QM_two_roots_of_gp d ρ gp m
  exact ⟨r₁, r₂, hne,
    root_ne_zero d ρ (gp_rho_pos d ρ gp) gp.2.1 m h₁,
    root_ne_zero d ρ (gp_rho_pos d ρ gp) gp.2.1 m h₂, h₁, h₂⟩

end SymmetricTriple
end Apollonius
end Geometry
end MachLib
