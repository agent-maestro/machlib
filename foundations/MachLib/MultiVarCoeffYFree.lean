import MachLib.MultiVarCoeffY

/-!
# `coeffsY` produces y-free coefficients (Gate 2d, resultant Rung, brick 3b completion)

`coeffsY p` writes `p` as `Σ cᵢ(x)·yⁱ`; the coefficients `cᵢ` must be **y-free** (`degVar 1 = 0`, i.e.
genuine polynomials in `x`) for the resultant machinery to treat them as `ℝ[x]` elements. This file
proves that (`coeffsY_yfree`) — discharging the `hps_yfree` hypothesis of `resLin`/`xbound_lin` for any
actual `p`. The coefficient arithmetic (`addCoeffs`, `negCoeffs`, `mulCoeffs`) each preserve
`y`-freeness, and the base coefficients (`const c`, `var 0`, and the `[const 0, const 1]` of `var 1`) are
`y`-free. Pure structural induction, Mathlib-free.
-/

namespace MachLib
namespace MultiVarMod

open MachLib.MultiVarMod.MultiVar

theorem addCoeffs_yfree {i : Fin 2} : ∀ as bs : List (MultiVar 2),
    (∀ c ∈ as, MultiVar.degVar i c = 0) → (∀ c ∈ bs, MultiVar.degVar i c = 0) →
    ∀ c ∈ addCoeffs as bs, MultiVar.degVar i c = 0
  | [], bs, _, hbs => fun c hc => hbs c hc
  | a :: as, [], has, _ => fun c hc => has c hc
  | a :: as, b :: bs, has, hbs => by
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc'
      · show Nat.max (MultiVar.degVar i a) (MultiVar.degVar i b) = 0
        rw [has a (List.mem_cons_self _ _), hbs b (List.mem_cons_self _ _)]; decide
      · exact addCoeffs_yfree as bs (fun c hc => has c (List.mem_cons_of_mem _ hc))
          (fun c hc => hbs c (List.mem_cons_of_mem _ hc)) c hc'

theorem negCoeffs_yfree {i : Fin 2} (bs : List (MultiVar 2))
    (hbs : ∀ c ∈ bs, MultiVar.degVar i c = 0) :
    ∀ c ∈ negCoeffs bs, MultiVar.degVar i c = 0 := by
  intro c hc
  simp only [negCoeffs, List.mem_map] at hc
  obtain ⟨b, hb, rfl⟩ := hc
  show Nat.max (MultiVar.degVar i (MultiVar.const 0)) (MultiVar.degVar i b) = 0
  rw [show MultiVar.degVar i (MultiVar.const 0) = 0 from rfl, hbs b hb]; decide

theorem mulCoeffs_yfree {i : Fin 2} : ∀ as bs : List (MultiVar 2),
    (∀ c ∈ as, MultiVar.degVar i c = 0) → (∀ c ∈ bs, MultiVar.degVar i c = 0) →
    ∀ c ∈ mulCoeffs as bs, MultiVar.degVar i c = 0
  | [], _, _, _ => by intro c hc; simp [mulCoeffs] at hc
  | a :: as, bs, has, hbs => by
      have ha : MultiVar.degVar i a = 0 := has a (List.mem_cons_self _ _)
      refine addCoeffs_yfree (bs.map (fun b => MultiVar.mul a b))
        (MultiVar.const 0 :: mulCoeffs as bs) ?_ ?_
      · intro c hc
        simp only [List.mem_map] at hc
        obtain ⟨b, hb, rfl⟩ := hc
        show MultiVar.degVar i a + MultiVar.degVar i b = 0
        rw [ha, hbs b hb]
      · intro c hc
        rcases List.mem_cons.mp hc with rfl | hc'
        · rfl
        · exact mulCoeffs_yfree as bs (fun c hc => has c (List.mem_cons_of_mem _ hc)) hbs c hc'

/-- **`coeffsY` produces y-free coefficients** — every coefficient of `p` as a polynomial in `y` is a
polynomial in `x` alone. Discharges `xbound_lin`'s `hps_yfree` for an actual `p`. -/
theorem coeffsY_yfree : ∀ p : MultiVar 2, ∀ c ∈ coeffsY p, MultiVar.degVar (1 : Fin 2) c = 0
  | .const _ => by
      intro c hc
      simp only [coeffsY, List.mem_singleton] at hc
      subst hc; rfl
  | .var j => by
      intro c hc
      by_cases h : j = 0
      · rw [coeffsY, if_pos h] at hc
        simp only [List.mem_singleton] at hc
        subst hc
        show (if (0 : Fin 2) = (1 : Fin 2) then 1 else 0) = 0
        decide
      · rw [coeffsY, if_neg h] at hc
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl <;> rfl
  | .add p q => by
      intro c hc
      exact addCoeffs_yfree (coeffsY p) (coeffsY q) (coeffsY_yfree p) (coeffsY_yfree q) c hc
  | .sub p q => by
      intro c hc
      exact addCoeffs_yfree (coeffsY p) (negCoeffs (coeffsY q)) (coeffsY_yfree p)
        (negCoeffs_yfree (coeffsY q) (coeffsY_yfree q)) c hc
  | .mul p q => by
      intro c hc
      exact mulCoeffs_yfree (coeffsY p) (coeffsY q) (coeffsY_yfree p) (coeffsY_yfree q) c hc

end MultiVarMod
end MachLib
