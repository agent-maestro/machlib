import MachLib.MultiVarElimReduceVanish
import MachLib.MultiVarElimYFree

/-!
# `MultiVar k` PRS loop — vanishing, `i`-freeness, termination (Gate 2d, M.0-e)

k-generic analogue of `MultiVarPRS` + `MultiVarPRSYFree`. `prsLoopK` is the fuel-bounded Euclidean
elimination on `x_i`-coefficient lists (reduce-the-bigger, so `|ps|+|qs|` strictly drops). It preserves
vanishing at common zeros (`prsLoopK_vanish`) and `i`-freeness (`prsLoopK_ifree`), and terminates to a
length-`≤1` remainder unconditionally (`prsLoopK_terminates`). Direct mirror of the `MultiVar 2` proofs.
-/

namespace MachLib
namespace MultiVarMod
namespace ElimK

open MachLib.MultiVarMod.MultiVar

theorem getLastD_eq_getLast {k : Nat} {l : List (MultiVar k)} (h : l ≠ []) (a : MultiVar k) :
    l.getLastD a = l.getLast h := by
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_getLast l h]; rfl

/-- One PRS step, leading coefficients via `getLastD`. -/
noncomputable def reduceStepK {k : Nat} (ps qs : List (MultiVar k)) : List (MultiVar k) :=
  reduceOnceK (qs.getLastD (MultiVar.const 0)) (ps.getLastD (MultiVar.const 0)) ps qs

theorem reduceStepK_vanish {k : Nat} (i : Fin k) (env : Fin k → Real) (ps qs : List (MultiVar k))
    (hps : ps ≠ []) (hqs : qs ≠ []) (hlen : qs.length ≤ ps.length)
    (hp : evalC i ps env = 0) (hq : evalC i qs env = 0) :
    evalC i (reduceStepK ps qs) env = 0 := by
  show evalC i
    (reduceOnceK (qs.getLastD (MultiVar.const 0)) (ps.getLastD (MultiVar.const 0)) ps qs) env = 0
  rw [getLastD_eq_getLast hqs, getLastD_eq_getLast hps]
  exact reduceOnceK_vanish i env ps qs hps hqs hlen hp hq

/-- The Euclidean PRS loop: reduce the bigger polynomial, fuel-bounded. -/
noncomputable def prsLoopK {k : Nat} : Nat → List (MultiVar k) → List (MultiVar k) → List (MultiVar k)
  | 0, ps, _ => ps
  | fuel + 1, ps, qs =>
      if qs.length ≤ 1 then qs
      else if ps.length ≤ 1 then ps
      else if ps.length ≤ qs.length then prsLoopK fuel (reduceStepK qs ps) ps
      else prsLoopK fuel (reduceStepK ps qs) qs

theorem length_reduceStepK {k : Nat} (ps qs : List (MultiVar k)) (h : qs.length ≤ ps.length) :
    (reduceStepK ps qs).length = ps.length - 1 :=
  length_reduceOnceK (qs.getLastD (MultiVar.const 0)) (ps.getLastD (MultiVar.const 0)) ps qs h

/-- **The PRS loop preserves vanishing at a common zero.** -/
theorem prsLoopK_vanish {k : Nat} (i : Fin k) (env : Fin k → Real) :
    ∀ (fuel : Nat) (ps qs : List (MultiVar k)),
      evalC i ps env = 0 → evalC i qs env = 0 → evalC i (prsLoopK fuel ps qs) env = 0
  | 0, _, _, hp, _ => hp
  | fuel + 1, ps, qs, hp, hq => by
      show evalC i (if qs.length ≤ 1 then qs
          else if ps.length ≤ 1 then ps
          else if ps.length ≤ qs.length then prsLoopK fuel (reduceStepK qs ps) ps
          else prsLoopK fuel (reduceStepK ps qs) qs) env = 0
      split
      · exact hq
      · split
        · exact hp
        · split
          · rename_i hq1 hp1 hpq
            have hqs : qs ≠ [] := fun he => hq1 (by rw [he]; simp)
            have hps : ps ≠ [] := fun he => hp1 (by rw [he]; simp)
            exact prsLoopK_vanish i env fuel (reduceStepK qs ps) ps
              (reduceStepK_vanish i env qs ps hqs hps hpq hq hp) hp
          · rename_i hq1 hp1 hpq
            have hqs : qs ≠ [] := fun he => hq1 (by rw [he]; simp)
            have hps : ps ≠ [] := fun he => hp1 (by rw [he]; simp)
            exact prsLoopK_vanish i env fuel (reduceStepK ps qs) qs
              (reduceStepK_vanish i env ps qs hps hqs (Nat.le_of_lt (Nat.lt_of_not_le hpq)) hp hq) hq

/-- **The PRS loop reaches a length-`≤1` remainder with enough fuel.** -/
theorem prsLoopK_terminates {k : Nat} :
    ∀ (fuel : Nat) (ps qs : List (MultiVar k)),
      ps.length + qs.length ≤ fuel → (prsLoopK fuel ps qs).length ≤ 1
  | 0, ps, qs, h => by simp only [prsLoopK]; omega
  | fuel + 1, ps, qs, h => by
      show (if qs.length ≤ 1 then qs
          else if ps.length ≤ 1 then ps
          else if ps.length ≤ qs.length then prsLoopK fuel (reduceStepK qs ps) ps
          else prsLoopK fuel (reduceStepK ps qs) qs).length ≤ 1
      split
      · assumption
      · split
        · assumption
        · split
          · rename_i hq1 hp1 hpq
            apply prsLoopK_terminates
            rw [length_reduceStepK qs ps hpq]; omega
          · rename_i hq1 hp1 hpq
            apply prsLoopK_terminates
            rw [length_reduceStepK ps qs (Nat.le_of_lt (Nat.lt_of_not_le hpq))]; omega

/-! ## `i`-freeness preservation -/

theorem scaleC_ifree {k : Nat} {i : Fin k} (c : MultiVar k) (hc : MultiVar.degVar i c = 0)
    (as : List (MultiVar k)) (has : ∀ a ∈ as, MultiVar.degVar i a = 0) :
    ∀ x ∈ scaleC c as, MultiVar.degVar i x = 0 := by
  intro x hx
  simp only [scaleC, List.mem_map] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  show MultiVar.degVar i c + MultiVar.degVar i a = 0
  rw [hc, has a ha]

theorem shiftC_ifree {k : Nat} {i : Fin k} (n : Nat) (as : List (MultiVar k))
    (has : ∀ a ∈ as, MultiVar.degVar i a = 0) :
    ∀ x ∈ shiftC n as, MultiVar.degVar i x = 0 := by
  intro x hx
  simp only [shiftC, List.mem_append, List.mem_replicate] at hx
  rcases hx with ⟨_, rfl⟩ | hx
  · rfl
  · exact has x hx

theorem getLastD_ifree {k : Nat} {i : Fin k} (as : List (MultiVar k))
    (has : ∀ a ∈ as, MultiVar.degVar i a = 0) :
    MultiVar.degVar i (as.getLastD (MultiVar.const 0)) = 0 := by
  cases as with
  | nil => rfl
  | cons a as' =>
    have hmem : (a :: as').getLastD (MultiVar.const 0) ∈ (a :: as') := by
      rw [getLastD_eq_getLast (List.cons_ne_nil a as')]
      exact List.getLast_mem _
    exact has _ hmem

theorem dropLast_ifree {k : Nat} {i : Fin k} (l : List (MultiVar k))
    (hl : ∀ a ∈ l, MultiVar.degVar i a = 0) :
    ∀ x ∈ l.dropLast, MultiVar.degVar i x = 0 :=
  fun x hx => hl x (List.dropLast_subset l hx)

theorem reduceStepK_ifree {k : Nat} {i : Fin k} (ps qs : List (MultiVar k))
    (hps : ∀ a ∈ ps, MultiVar.degVar i a = 0) (hqs : ∀ a ∈ qs, MultiVar.degVar i a = 0) :
    ∀ x ∈ reduceStepK ps qs, MultiVar.degVar i x = 0 := by
  show ∀ x ∈ (subC (scaleC (qs.getLastD (MultiVar.const 0)) ps)
      (shiftC (ps.length - qs.length)
        (scaleC (ps.getLastD (MultiVar.const 0)) qs))).dropLast, MultiVar.degVar i x = 0
  apply dropLast_ifree
  apply subC_ifree
  · exact scaleC_ifree (qs.getLastD (MultiVar.const 0)) (getLastD_ifree qs hqs) ps hps
  · exact shiftC_ifree _ _
      (scaleC_ifree (ps.getLastD (MultiVar.const 0)) (getLastD_ifree ps hps) qs hqs)

/-- **The PRS loop preserves `i`-freeness.** -/
theorem prsLoopK_ifree {k : Nat} {i : Fin k} :
    ∀ (fuel : Nat) (ps qs : List (MultiVar k)),
      (∀ a ∈ ps, MultiVar.degVar i a = 0) → (∀ a ∈ qs, MultiVar.degVar i a = 0) →
      ∀ x ∈ prsLoopK fuel ps qs, MultiVar.degVar i x = 0
  | 0, _, _, hps, _ => hps
  | fuel + 1, ps, qs, hps, hqs => by
      show ∀ x ∈ (if qs.length ≤ 1 then qs
          else if ps.length ≤ 1 then ps
          else if ps.length ≤ qs.length then prsLoopK fuel (reduceStepK qs ps) ps
          else prsLoopK fuel (reduceStepK ps qs) qs), MultiVar.degVar i x = 0
      split
      · exact hqs
      · split
        · exact hps
        · split
          · exact prsLoopK_ifree fuel (reduceStepK qs ps) ps (reduceStepK_ifree qs ps hqs hps) hps
          · exact prsLoopK_ifree fuel (reduceStepK ps qs) qs (reduceStepK_ifree ps qs hps hqs) hqs

end ElimK
end MultiVarMod
end MachLib
