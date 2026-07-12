import MachLib.MultiVarPRS
import MachLib.MultiVarCoeffYFree

/-!
# The PRS loop preserves y-free coefficients (Gate 2d, resultant brick 3c-4c-2)

For the loop's output to be a genuine resultant (`y`-free polynomial in `x`), its coefficients must stay
`y`-free. They do: the inputs are `coeffsY` coefficients (`coeffsY_yfree`), and every reduction combines
them (`scale`/`shift`/`sub`/`dropLast`, plus the leading coefficients via `getLastD`) with operations
that preserve `y`-freeness. `prsLoop_yfree` threads this through the fuel recursion.
-/

namespace MachLib
namespace MultiVarMod

open MachLib.MultiVarMod.MultiVar

theorem scaleCoeffs_yfree {i : Fin 2} (c : MultiVar 2) (hc : MultiVar.degVar i c = 0)
    (as : List (MultiVar 2)) (has : ∀ a ∈ as, MultiVar.degVar i a = 0) :
    ∀ x ∈ scaleCoeffs c as, MultiVar.degVar i x = 0 := by
  intro x hx
  simp only [scaleCoeffs, List.mem_map] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  show MultiVar.degVar i c + MultiVar.degVar i a = 0
  rw [hc, has a ha]

theorem shiftCoeffs_yfree {i : Fin 2} (k : Nat) (as : List (MultiVar 2))
    (has : ∀ a ∈ as, MultiVar.degVar i a = 0) :
    ∀ x ∈ shiftCoeffs k as, MultiVar.degVar i x = 0 := by
  intro x hx
  simp only [shiftCoeffs, List.mem_append, List.mem_replicate] at hx
  rcases hx with ⟨_, rfl⟩ | hx
  · rfl
  · exact has x hx

theorem subCoeffs_yfree {i : Fin 2} (as bs : List (MultiVar 2))
    (has : ∀ a ∈ as, MultiVar.degVar i a = 0) (hbs : ∀ b ∈ bs, MultiVar.degVar i b = 0) :
    ∀ x ∈ subCoeffs as bs, MultiVar.degVar i x = 0 :=
  addCoeffs_yfree as (negCoeffs bs) has (negCoeffs_yfree bs hbs)

theorem getLastD_yfree {i : Fin 2} (as : List (MultiVar 2))
    (has : ∀ a ∈ as, MultiVar.degVar i a = 0) :
    MultiVar.degVar i (as.getLastD (MultiVar.const 0)) = 0 := by
  cases as with
  | nil => rfl
  | cons a as' =>
    have hmem : (a :: as').getLastD (MultiVar.const 0) ∈ (a :: as') := by
      rw [getLastD_eq_getLast (List.cons_ne_nil a as')]
      exact List.getLast_mem _
    exact has _ hmem

theorem dropLast_yfree {i : Fin 2} (l : List (MultiVar 2))
    (hl : ∀ a ∈ l, MultiVar.degVar i a = 0) :
    ∀ x ∈ l.dropLast, MultiVar.degVar i x = 0 :=
  fun x hx => hl x (List.dropLast_subset l hx)

/-- **`reduceStep` preserves y-free coefficients.** -/
theorem reduceStep_yfree {i : Fin 2} (ps qs : List (MultiVar 2))
    (hps : ∀ a ∈ ps, MultiVar.degVar i a = 0) (hqs : ∀ a ∈ qs, MultiVar.degVar i a = 0) :
    ∀ x ∈ reduceStep ps qs, MultiVar.degVar i x = 0 := by
  show ∀ x ∈ (subCoeffs (scaleCoeffs (qs.getLastD (MultiVar.const 0)) ps)
      (shiftCoeffs (ps.length - qs.length)
        (scaleCoeffs (ps.getLastD (MultiVar.const 0)) qs))).dropLast, MultiVar.degVar i x = 0
  apply dropLast_yfree
  apply subCoeffs_yfree
  · exact scaleCoeffs_yfree (qs.getLastD (MultiVar.const 0)) (getLastD_yfree qs hqs) ps hps
  · exact shiftCoeffs_yfree _ _
      (scaleCoeffs_yfree (ps.getLastD (MultiVar.const 0)) (getLastD_yfree ps hps) qs hqs)

/-- **The PRS loop preserves y-free coefficients.** -/
theorem prsLoop_yfree {i : Fin 2} :
    ∀ (fuel : Nat) (ps qs : List (MultiVar 2)),
      (∀ a ∈ ps, MultiVar.degVar i a = 0) → (∀ a ∈ qs, MultiVar.degVar i a = 0) →
      ∀ x ∈ prsLoop fuel ps qs, MultiVar.degVar i x = 0
  | 0, _, _, hps, _ => hps
  | fuel + 1, ps, qs, hps, hqs => by
      show ∀ x ∈ (if qs.length ≤ 1 then qs
          else if ps.length ≤ 1 then ps
          else if ps.length ≤ qs.length then prsLoop fuel (reduceStep qs ps) ps
          else prsLoop fuel (reduceStep ps qs) qs), MultiVar.degVar i x = 0
      split
      · exact hqs
      · split
        · exact hps
        · split
          · exact prsLoop_yfree fuel (reduceStep qs ps) ps (reduceStep_yfree qs ps hqs hps) hps
          · exact prsLoop_yfree fuel (reduceStep ps qs) qs (reduceStep_yfree ps qs hps hqs) hqs

end MultiVarMod
end MachLib
