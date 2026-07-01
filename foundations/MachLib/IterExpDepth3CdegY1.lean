import MachLib.ChainExp2CdegInv
import MachLib.ChainExp2YPIT

/-!
# `cdegY1` arc, brick 1 — the nested canonical-zero test and its eval-invariance

The depth-3 termination needs a FULLY eval-invariant depth-2 measure (the depth-2 `chain2MeasureCanon`
has a *syntactic* `degreeY₁` first component — not eval-invariant). That measure's first component must
be a canonical `y₁`-degree `cdegY1`, whose canon-zero test on `y₁`-coefficients (polys in `x, y₀`) is
NESTED one level deeper than the depth-2 `coeffCanonZeroB` (which only tests the `x`-part at `y=0`):

  `coeffCanonZeroB1 c` = "every `y₀`-coefficient of `c` is `x`-canonically-zero"
                       = "`c` vanishes on the chain `(x, eˣ)` for all `x`".

This brick builds that test and proves it eval-invariant (via the `y`-PIT at index `⟨0⟩` + the depth-2
`coeffCanonZeroB` eval-invariance). It mirrors `ChainExp2CdegInv.coeffCanonZeroB_eq_of_eval_eq` one level
up. `ChainExp2*` untouched (Path B); no `sorry`.
-/

namespace MachLib.IterExpDepth3CdegY1

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.MultiPolyMod.MultiPoly
open MachLib.PolynomialCanonical
open MachLib.PfaffianChainMod.PfaffianFn
open MachLib.MultiPolyReconstruct
open MachLib.ChainExp2CanonMeasure
open MachLib.ChainExp2CdegInv
open MachLib.ChainExp2YPIT

/-- The `y=0` env with `y₀` set to `y0` (slot 0), everything else 0. -/
private noncomputable def env0 (y0 : Real) : Fin 2 → Real :=
  fun i => if i = (⟨0, by omega⟩ : Fin 2) then y0 else 0

/-- **Nested canon-zero test.** `c` is canonically zero as an `x, y₀`-poly iff all its `y₀`-coefficients
are `x`-canonically-zero (`coeffCanonZeroB`). -/
noncomputable def coeffCanonZeroB1 (c : MultiPoly 2) : Bool :=
  (yCoeffsAt (⟨0, by omega⟩ : Fin 2) c).all coeffCanonZeroB

/-- **Characterization.** `coeffCanonZeroB1 c = true` iff `c` vanishes at `(x, y₀, 0)` for all `x, y₀`
(i.e. `c`'s `y₁ = 0` slice is the zero `x, y₀`-poly). -/
theorem coeffCanonZeroB1_true_iff (c : MultiPoly 2) :
    coeffCanonZeroB1 c = true ↔ ∀ (x y0 : Real), MultiPoly.eval c x (env0 y0) = 0 := by
  unfold coeffCanonZeroB1
  rw [List.all_eq_true]
  constructor
  · -- all y₀-coeffs canon-zero ⇒ c vanishes at (x, y₀, 0).
    intro hall x y0
    have hmap : (yCoeffsAt (⟨0, by omega⟩ : Fin 2) c).map (fun c' => MultiPoly.eval c' x (env0 y0))
              = (yCoeffsAt (⟨0, by omega⟩ : Fin 2) c).map (fun _ => (0 : Real)) := by
      apply List.map_congr_left
      intro e he
      have hcz : coeffCanonZeroB e = true := hall e he
      have hz0 : ∀ w : Real, MultiPoly.eval e w (fun _ => 0) = 0 := by
        have := (canonZero_iff_eval_zero_at_0 e).mp
        unfold coeffCanonZeroB at hcz
        exact this (of_decide_eq_true hcz)
      -- e is y₀-free, so eval e at env0 = eval e at 0-env.
      have hyfree : MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) e = 0 :=
        yCoeffsAt_entries_degreeY_zero (⟨0, by omega⟩ : Fin 2) c e he
      have hoff : ∀ j : Fin 2, j ≠ (⟨0, by omega⟩ : Fin 2) → env0 y0 j = (fun _ => (0 : Real)) j := by
        intro j hj; show (if j = (⟨0, by omega⟩ : Fin 2) then y0 else 0) = 0; rw [if_neg hj]
      rw [eval_eq_of_env_agree_off (⟨0, by omega⟩ : Fin 2) e x (env0 y0) (fun _ => 0) hoff hyfree, hz0]
    have hz : ∀ (L : List (MultiPoly 2)) (w : Real),
        evalCoeffs (List.map (fun _ => (0 : Real)) L) w = 0 := by
      intro L w
      induction L with
      | nil => rw [List.map_nil, evalCoeffs_nil]
      | cons a as ih =>
        rw [List.map_cons, evalCoeffs_cons, ih, MachLib.Real.mul_zero, MachLib.Real.add_zero]
    have hbridge := listEvalN_eq_evalCoeffs_map (⟨0, by omega⟩ : Fin 2)
      (yCoeffsAt (⟨0, by omega⟩ : Fin 2) c) x (env0 y0)
    rw [eval_yCoeffsAt (⟨0, by omega⟩ : Fin 2) c x (env0 y0)] at hbridge
    rw [hbridge, hmap, hz]
  · -- c vanishes at (x, y₀, 0) ⇒ all y₀-coeffs canon-zero.
    intro hvanish e he
    have hyfree : MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) e = 0 :=
      yCoeffsAt_entries_degreeY_zero (⟨0, by omega⟩ : Fin 2) c e he
    -- coeffCanonZeroB e ⟺ ∀x, eval e x 0-env = 0.
    have hgoal : ∀ x : Real, MultiPoly.eval e x (fun _ => 0) = 0 := by
      intro x
      have hall : ∀ y : Real,
          evalCoeffs ((yCoeffsAt (⟨0, by omega⟩ : Fin 2) c).map
            (fun c' => MultiPoly.eval c' x (fun _ => 0))) y = 0 := by
        intro y
        have hmapy : (yCoeffsAt (⟨0, by omega⟩ : Fin 2) c).map
              (fun c' => MultiPoly.eval c' x (env0 y))
            = (yCoeffsAt (⟨0, by omega⟩ : Fin 2) c).map (fun c' => MultiPoly.eval c' x (fun _ => 0)) := by
          apply List.map_congr_left
          intro e' he'
          have hyf' : MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) e' = 0 :=
            yCoeffsAt_entries_degreeY_zero (⟨0, by omega⟩ : Fin 2) c e' he'
          have hoff : ∀ j : Fin 2, j ≠ (⟨0, by omega⟩ : Fin 2) → env0 y j = (fun _ => (0 : Real)) j := by
            intro j hj; show (if j = (⟨0, by omega⟩ : Fin 2) then y else 0) = 0; rw [if_neg hj]
          exact eval_eq_of_env_agree_off (⟨0, by omega⟩ : Fin 2) e' x (env0 y) (fun _ => 0) hoff hyf'
        have hbridge := listEvalN_eq_evalCoeffs_map (⟨0, by omega⟩ : Fin 2)
          (yCoeffsAt (⟨0, by omega⟩ : Fin 2) c) x (env0 y)
        rw [eval_yCoeffsAt (⟨0, by omega⟩ : Fin 2) c x (env0 y), hvanish x y] at hbridge
        rw [← hmapy]; exact hbridge.symm
      exact evalCoeffs_zero_iff_all_zero _ hall (MultiPoly.eval e x (fun _ => 0))
        (List.mem_map_of_mem _ he)
    unfold coeffCanonZeroB
    exact decide_eq_true ((canonZero_iff_eval_zero_at_0 e).mpr hgoal)

/-- **The nested canon-zero test is eval-invariant.** -/
theorem coeffCanonZeroB1_eq_of_eval_eq (c1 c2 : MultiPoly 2)
    (h : ∀ (x : Real) (env : Fin 2 → Real), MultiPoly.eval c1 x env = MultiPoly.eval c2 x env) :
    coeffCanonZeroB1 c1 = coeffCanonZeroB1 c2 := by
  have hiff : coeffCanonZeroB1 c1 = true ↔ coeffCanonZeroB1 c2 = true := by
    rw [coeffCanonZeroB1_true_iff, coeffCanonZeroB1_true_iff]
    constructor
    · intro h1 x y0; rw [← h x (env0 y0)]; exact h1 x y0
    · intro h2 x y0; rw [h x (env0 y0)]; exact h2 x y0
  cases hb1 : coeffCanonZeroB1 c1 <;> cases hb2 : coeffCanonZeroB1 c2 <;> simp_all

end MachLib.IterExpDepth3CdegY1
