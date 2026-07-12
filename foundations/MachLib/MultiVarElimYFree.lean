import MachLib.MultiVarElimCoeff

/-!
# `coeffsElim` produces `i`-free coefficients (Gate 2d, M.0-d)

k-generic analogue of `MultiVarCoeffYFree`: the coefficients of `coeffsElim i p` are `i`-free
(`degVar i = 0` — genuine polynomials in the *other* `k−1` variables), so the eliminated remainder is a
polynomial in those variables. The coefficient arithmetic preserves `i`-freeness; the base coefficients
(`const c`, `var j` for `j ≠ i`, and the `[const 0, const 1]` of `var i`) are `i`-free. Mirror of the
`MultiVar 2` proofs with `2 ↦ k`, `1 ↦ i`.
-/

namespace MachLib
namespace MultiVarMod
namespace ElimK

open MachLib.MultiVarMod.MultiVar

theorem addC_ifree {k : Nat} {i : Fin k} : ∀ as bs : List (MultiVar k),
    (∀ c ∈ as, MultiVar.degVar i c = 0) → (∀ c ∈ bs, MultiVar.degVar i c = 0) →
    ∀ c ∈ addC as bs, MultiVar.degVar i c = 0
  | [], bs, _, hbs => fun c hc => hbs c hc
  | a :: as, [], has, _ => fun c hc => has c hc
  | a :: as, b :: bs, has, hbs => by
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc'
      · show Nat.max (MultiVar.degVar i a) (MultiVar.degVar i b) = 0
        rw [has a (List.mem_cons_self _ _), hbs b (List.mem_cons_self _ _)]; decide
      · exact addC_ifree as bs (fun c hc => has c (List.mem_cons_of_mem _ hc))
          (fun c hc => hbs c (List.mem_cons_of_mem _ hc)) c hc'

theorem negC_ifree {k : Nat} {i : Fin k} (bs : List (MultiVar k))
    (hbs : ∀ c ∈ bs, MultiVar.degVar i c = 0) :
    ∀ c ∈ negC bs, MultiVar.degVar i c = 0 := by
  intro c hc
  simp only [negC, List.mem_map] at hc
  obtain ⟨b, hb, rfl⟩ := hc
  show Nat.max (MultiVar.degVar i (MultiVar.const 0)) (MultiVar.degVar i b) = 0
  rw [show MultiVar.degVar i (MultiVar.const 0) = 0 from rfl, hbs b hb]; decide

theorem subC_ifree {k : Nat} {i : Fin k} (as bs : List (MultiVar k))
    (has : ∀ c ∈ as, MultiVar.degVar i c = 0) (hbs : ∀ c ∈ bs, MultiVar.degVar i c = 0) :
    ∀ c ∈ subC as bs, MultiVar.degVar i c = 0 :=
  addC_ifree as (negC bs) has (negC_ifree bs hbs)

theorem mulC_ifree {k : Nat} {i : Fin k} : ∀ as bs : List (MultiVar k),
    (∀ c ∈ as, MultiVar.degVar i c = 0) → (∀ c ∈ bs, MultiVar.degVar i c = 0) →
    ∀ c ∈ mulC as bs, MultiVar.degVar i c = 0
  | [], _, _, _ => by intro c hc; simp [mulC] at hc
  | a :: as, bs, has, hbs => by
      have ha : MultiVar.degVar i a = 0 := has a (List.mem_cons_self _ _)
      refine addC_ifree (bs.map (fun b => MultiVar.mul a b))
        (MultiVar.const 0 :: mulC as bs) ?_ ?_
      · intro c hc
        simp only [List.mem_map] at hc
        obtain ⟨b, hb, rfl⟩ := hc
        show MultiVar.degVar i a + MultiVar.degVar i b = 0
        rw [ha, hbs b hb]
      · intro c hc
        rcases List.mem_cons.mp hc with rfl | hc'
        · rfl
        · exact mulC_ifree as bs (fun c hc => has c (List.mem_cons_of_mem _ hc)) hbs c hc'

/-- **`coeffsElim` produces `i`-free coefficients.** -/
theorem coeffsElim_ifree {k : Nat} (i : Fin k) :
    ∀ p : MultiVar k, ∀ c ∈ coeffsElim i p, MultiVar.degVar i c = 0
  | .const _ => by
      intro c hc
      simp only [coeffsElim, List.mem_singleton] at hc
      subst hc; rfl
  | .var j => by
      intro c hc
      by_cases h : j = i
      · rw [coeffsElim, if_pos h] at hc
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl <;> rfl
      · rw [coeffsElim, if_neg h] at hc
        simp only [List.mem_singleton] at hc
        subst hc
        show (if j = i then 1 else 0) = 0
        rw [if_neg h]
  | .add p q => by
      intro c hc
      exact addC_ifree (coeffsElim i p) (coeffsElim i q) (coeffsElim_ifree i p) (coeffsElim_ifree i q) c hc
  | .sub p q => by
      intro c hc
      exact subC_ifree (coeffsElim i p) (coeffsElim i q) (coeffsElim_ifree i p) (coeffsElim_ifree i q) c hc
  | .mul p q => by
      intro c hc
      exact mulC_ifree (coeffsElim i p) (coeffsElim i q) (coeffsElim_ifree i p) (coeffsElim_ifree i q) c hc

end ElimK
end MultiVarMod
end MachLib
