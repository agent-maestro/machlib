import MachLib.MultiPoly

/-!
# Interior-variable deletion `dropAt` — foundation for mixed-chain recip clearing

The mixed-chain `exp_hard` port (`roadmap/exp-hard-mixed-measure-port.md`, Stage A) needs to
eliminate a reciprocal variable that is buried in the middle of the chain (the encoder stacks
recip → log → exp). `MultiPoly`'s existing `dropLastY` only deletes the TOP variable; this file
adds `dropAt i`, deleting the INTERIOR coordinate `i : Fin (N+1)` and reindexing the rest —
the projection analog of `dropLastY` at an arbitrary index. It is the reindexing substrate a
future interior-recip `clearAt` builds on (as `dropLastY` underlies `clearTop`).

`embedSkip i : Fin N → Fin (N+1)` is the complementary embedding that skips slot `i` (so an
`env : Fin (N+1) → Real` restricts to `fun k => env (embedSkip i k)` on the surviving slots).
`eval_dropAt` is the load-bearing correctness theorem: when `p` does not depend on `y_i`
(`degreeY i p = 0`), `dropAt i p` evaluates to `p` on the skip-restricted env. No new axioms.
-/

namespace MachLib
namespace MultiPolyMod
namespace MultiPoly

open MachLib.Real

/-- The embedding `Fin N ↪ Fin (N+1)` that skips slot `i`: slots below `i` stay, slots at/above
`i` shift up by one. Complementary to `dropAt i`. -/
def embedSkip {N : Nat} (i : Fin (N + 1)) (k : Fin N) : Fin (N + 1) :=
  if k.val < i.val then ⟨k.val, by omega⟩ else ⟨k.val + 1, by omega⟩

/-- **Delete the interior coordinate `i`.** `varY i ↦ const 0` (safe under `degreeY i p = 0`);
`varY j` for `j ≠ i` is reindexed into `Fin N` (drop by one above `i`, keep below). The interior
analog of `dropLastY`. -/
noncomputable def dropAt {N : Nat} (i : Fin (N + 1)) : MultiPoly (N + 1) → MultiPoly N
  | .const c => .const c
  | .varX => .varX
  | .varY j =>
      if hj : j.val < i.val then .varY ⟨j.val, by omega⟩
      else if hj2 : i.val < j.val then .varY ⟨j.val - 1, by omega⟩
      else .const 0
  | .add p q => .add (dropAt i p) (dropAt i q)
  | .sub p q => .sub (dropAt i p) (dropAt i q)
  | .mul p q => .mul (dropAt i p) (dropAt i q)

/-- **Eval correctness for `dropAt`.** When `degreeY i p = 0` (`p` doesn't use `y_i`), `dropAt i p`
evaluates on the skip-restricted env `fun k => env (embedSkip i k)` to the same value as `p` on
`env`. The interior analog of `eval_dropLastY`. -/
theorem eval_dropAt {N : Nat} (i : Fin (N + 1)) (p : MultiPoly (N + 1))
    (hp : degreeY i p = 0) (x : Real) (env : Fin (N + 1) → Real) :
    eval (dropAt i p) x (fun k => env (embedSkip i k)) = eval p x env := by
  induction p with
  | const c => rfl
  | varX => rfl
  | varY j =>
    show eval (dropAt i (varY j)) x (fun k => env (embedSkip i k)) = env j
    by_cases hj : j.val < i.val
    · have hlt : dropAt i (varY j) = varY ⟨j.val, by omega⟩ := by
        simp only [dropAt, hj, dif_pos]
      rw [hlt]
      show env (embedSkip i ⟨j.val, by omega⟩) = env j
      have : embedSkip i (⟨j.val, by omega⟩ : Fin N) = j := by
        show (if (⟨j.val, by omega⟩ : Fin N).val < i.val then _ else _) = j
        rw [if_pos hj]
      rw [this]
    · by_cases hj2 : i.val < j.val
      · have hgt : dropAt i (varY j) = varY ⟨j.val - 1, by omega⟩ := by
          simp only [dropAt, hj, hj2, dif_neg, dif_pos, not_false_iff]
        rw [hgt]
        show env (embedSkip i (⟨j.val - 1, by omega⟩ : Fin N)) = env j
        have : embedSkip i (⟨j.val - 1, by omega⟩ : Fin N) = j := by
          show (if (⟨j.val - 1, by omega⟩ : Fin N).val < i.val then _ else _) = j
          rw [if_neg (by omega : ¬ (j.val - 1 < i.val))]
          apply Fin.eq_of_val_eq
          show (j.val - 1) + 1 = j.val
          omega
        rw [this]
      · -- j = i: then degreeY i (varY i) = 1, contradicting hp.
        exfalso
        have hji : j = i := Fin.eq_of_val_eq (by omega)
        rw [hji] at hp
        have hone : degreeY i (varY i) = 1 := by
          show (if i = i then 1 else 0) = 1; simp
        rw [hone] at hp
        exact absurd hp (by omega)
  | add p q ihp ihq =>
    have hpq : degreeY i p = 0 ∧ degreeY i q = 0 := by
      have hmax : Nat.max (degreeY i p) (degreeY i q) = 0 := hp
      have := Nat.max_le.mp (Nat.le_of_eq hmax); refine ⟨?_, ?_⟩ <;> omega
    show eval (dropAt i p) x (fun k => env (embedSkip i k))
       + eval (dropAt i q) x (fun k => env (embedSkip i k)) = eval p x env + eval q x env
    rw [ihp hpq.1, ihq hpq.2]
  | sub p q ihp ihq =>
    have hpq : degreeY i p = 0 ∧ degreeY i q = 0 := by
      have hmax : Nat.max (degreeY i p) (degreeY i q) = 0 := hp
      have := Nat.max_le.mp (Nat.le_of_eq hmax); refine ⟨?_, ?_⟩ <;> omega
    show eval (dropAt i p) x (fun k => env (embedSkip i k))
       - eval (dropAt i q) x (fun k => env (embedSkip i k)) = eval p x env - eval q x env
    rw [ihp hpq.1, ihq hpq.2]
  | mul p q ihp ihq =>
    have hpq : degreeY i p = 0 ∧ degreeY i q = 0 := by
      have hsum : degreeY i p + degreeY i q = 0 := hp
      refine ⟨?_, ?_⟩ <;> omega
    show eval (dropAt i p) x (fun k => env (embedSkip i k))
       * eval (dropAt i q) x (fun k => env (embedSkip i k)) = eval p x env * eval q x env
    rw [ihp hpq.1, ihq hpq.2]

end MultiPoly
end MultiPolyMod
end MachLib
