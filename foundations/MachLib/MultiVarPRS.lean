import MachLib.MultiVarReduceVanish

/-!
# The polynomial-remainder-sequence loop (Gate 2d, resultant brick 3c-4c)

`prsLoop` is the Euclidean elimination on `y`-coefficient lists: while the smaller polynomial has
`deg_y ≥ 1`, replace `(p, q)` by `(q, reduceOnce p q)` (swapping so the reducer's degree fits), driving
the pair toward a `y`-free remainder. Structural recursion on a **fuel** counter (no well-founded
machinery). This file proves the **vanishing invariant** (`prsLoop_vanish`): if `p` and `q` both vanish
at `env`, so does `prsLoop fuel p q` — every entry inherits it via `reduceOnce_vanish`. The leading
coefficients are taken with `getLastD` (default `const 0`, no nonempty proofs in the def) and bridged to
`getLast` for `reduceOnce_vanish`.
-/

namespace MachLib
namespace MultiVarMod

open MachLib.MultiVarMod.MultiVar

/-- `getLastD` equals `getLast` on a nonempty list. -/
theorem getLastD_eq_getLast {l : List (MultiVar 2)} (h : l ≠ []) (a : MultiVar 2) :
    l.getLastD a = l.getLast h := by
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_getLast l h]; rfl

/-- One PRS step on coefficient lists, leading coefficients via `getLastD`. -/
noncomputable def reduceStep (ps qs : List (MultiVar 2)) : List (MultiVar 2) :=
  reduceOnce (qs.getLastD (MultiVar.const 0)) (ps.getLastD (MultiVar.const 0)) ps qs

theorem reduceStep_vanish (env : Fin 2 → Real) (ps qs : List (MultiVar 2))
    (hps : ps ≠ []) (hqs : qs ≠ []) (hlen : qs.length ≤ ps.length)
    (hp : evalCoeffs ps env = 0) (hq : evalCoeffs qs env = 0) :
    evalCoeffs (reduceStep ps qs) env = 0 := by
  show evalCoeffs (reduceOnce (qs.getLastD (MultiVar.const 0)) (ps.getLastD (MultiVar.const 0)) ps qs) env
      = 0
  rw [getLastD_eq_getLast hqs, getLastD_eq_getLast hps]
  exact reduceOnce_vanish env ps qs hps hqs hlen hp hq

/-- The Euclidean PRS loop: eliminate `y` by repeated reduction, fuel-bounded. -/
noncomputable def prsLoop : Nat → List (MultiVar 2) → List (MultiVar 2) → List (MultiVar 2)
  | 0, ps, _ => ps
  | fuel + 1, ps, qs =>
      if qs.length ≤ 1 then qs
      else if ps.length ≤ 1 then ps
      else if ps.length ≤ qs.length then prsLoop fuel (reduceStep qs ps) ps
      else prsLoop fuel (reduceStep ps qs) qs

theorem length_reduceStep (ps qs : List (MultiVar 2)) (h : qs.length ≤ ps.length) :
    (reduceStep ps qs).length = ps.length - 1 :=
  length_reduceOnce (qs.getLastD (MultiVar.const 0)) (ps.getLastD (MultiVar.const 0)) ps qs h

/-- **The PRS loop preserves vanishing at a common zero.** If `evalCoeffs ps = evalCoeffs qs = 0`, so
does `evalCoeffs (prsLoop fuel ps qs)`. Fuel induction; the reduce arms use `reduceStep_vanish`. -/
theorem prsLoop_vanish (env : Fin 2 → Real) :
    ∀ (fuel : Nat) (ps qs : List (MultiVar 2)),
      evalCoeffs ps env = 0 → evalCoeffs qs env = 0 →
      evalCoeffs (prsLoop fuel ps qs) env = 0
  | 0, _, _, hp, _ => hp
  | fuel + 1, ps, qs, hp, hq => by
      show evalCoeffs (if qs.length ≤ 1 then qs
          else if ps.length ≤ 1 then ps
          else if ps.length ≤ qs.length then prsLoop fuel (reduceStep qs ps) ps
          else prsLoop fuel (reduceStep ps qs) qs) env = 0
      split
      · exact hq
      · split
        · exact hp
        · split
          · rename_i hq1 hp1 hpq
            have hqs : qs ≠ [] := fun he => hq1 (by rw [he]; simp)
            have hps : ps ≠ [] := fun he => hp1 (by rw [he]; simp)
            exact prsLoop_vanish env fuel (reduceStep qs ps) ps
              (reduceStep_vanish env qs ps hqs hps hpq hq hp) hp
          · rename_i hq1 hp1 hpq
            have hqs : qs ≠ [] := fun he => hq1 (by rw [he]; simp)
            have hps : ps ≠ [] := fun he => hp1 (by rw [he]; simp)
            exact prsLoop_vanish env fuel (reduceStep ps qs) qs
              (reduceStep_vanish env ps qs hps hqs (Nat.le_of_lt (Nat.lt_of_not_le hpq)) hp hq) hq

/-- **The PRS loop reaches a y-free remainder (length ≤ 1) with enough fuel.** The reduce arms shrink
`|ps| + |qs|` by one each step (`length_reduceStep`); `fuel ≥ |ps| + |qs|` suffices. This discharges the
resultant's `hterm` unconditionally. -/
theorem prsLoop_terminates :
    ∀ (fuel : Nat) (ps qs : List (MultiVar 2)),
      ps.length + qs.length ≤ fuel → (prsLoop fuel ps qs).length ≤ 1
  | 0, ps, qs, h => by simp only [prsLoop]; omega
  | fuel + 1, ps, qs, h => by
      show (if qs.length ≤ 1 then qs
          else if ps.length ≤ 1 then ps
          else if ps.length ≤ qs.length then prsLoop fuel (reduceStep qs ps) ps
          else prsLoop fuel (reduceStep ps qs) qs).length ≤ 1
      split
      · assumption
      · split
        · assumption
        · split
          · rename_i hq1 hp1 hpq
            apply prsLoop_terminates
            rw [length_reduceStep qs ps hpq]; omega
          · rename_i hq1 hp1 hpq
            apply prsLoop_terminates
            rw [length_reduceStep ps qs (Nat.le_of_lt (Nat.lt_of_not_le hpq))]; omega

end MultiVarMod
end MachLib
