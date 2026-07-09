import MachLib.IterExpDepthNCanonLcYBound
import MachLib.IterExpDepthNEstablishHnz

/-!
# Chain-N explicit bound — cross-index `degreeY` bounds for the trim & lift arms

The outer WF wrap's trim and lift arms need the inner poly's `degreeY` bounded (for `rankRec_lt`'s cap
hypothesis). `dropLeadingYAt i` and `liftInner` both reconstruct along `y_i`, so for a target index `jt ≠ i`
they do not raise `degreeY jt` — the cross-index mirror of the proven `degreeX_dropLeadingYAt_le` /
`degreeX_liftInner_le`, using the cross-index `degreeY` tower (`yCoeffsAt_entries_degreeY_le`).
-/

namespace MachLib.IterExpDepthN

open MachLib.MultiPolyMod MachLib.MultiPolyMod.MultiPoly
open MachLib.MultiPolyReconstruct
open MachLib.ChainExp2Explicit
open MachLib.ChainExp2Trim

/-- `degreeY jt ((varYⁱ)ᵏ) = 0` for `jt ≠ i` — the power of a *different* chain variable is `y_jt`-free. -/
theorem degreeY_pow_varY_ne {n : Nat} (i jt : Fin n) (hij : jt ≠ i) (k : Nat) :
    degreeY jt (pow (varY i) k) = 0 := by
  induction k with
  | zero => rfl
  | succ m ih =>
    show (if jt = i then 1 else 0) + degreeY jt (pow (varY i) m) = 0
    rw [ih, if_neg hij]

/-- **`reconstructY` never raises `degreeY jt`** past its coefficients, when `jt ≠ i` (the reconstruction
variable). Cross-index mirror of `degreeX_reconstructY_le`. -/
theorem degreeY_reconstructY_le_ne {n : Nat} (i jt : Fin n) (hij : jt ≠ i) (D : Nat) :
    ∀ (coeffs : List (MultiPoly n)) (k : Nat),
      (∀ c ∈ coeffs, degreeY jt c ≤ D) → degreeY jt (reconstructY i coeffs k) ≤ D
  | [], _, _ => by rw [reconstructY_nil]; exact Nat.zero_le _
  | c :: cs, k, h => by
      rw [reconstructY_cons]
      show Nat.max (degreeY jt (mul c (pow (varY i) k))) (degreeY jt (reconstructY i cs (k + 1))) ≤ D
      refine Nat.max_le.mpr ⟨?_, ?_⟩
      · show degreeY jt c + degreeY jt (pow (varY i) k) ≤ D
        rw [degreeY_pow_varY_ne i jt hij]
        have hc := h c (List.mem_cons_self c cs)
        omega
      · exact degreeY_reconstructY_le_ne i jt hij D cs (k + 1)
          (fun c' hc' => h c' (List.mem_cons_of_mem c hc'))

/-- **`dropLeadingYAt i` does not raise `degreeY jt`** for `jt ≠ i` — the trim arm's inner bound. -/
theorem degreeY_dropLeadingYAt_le_ne {n : Nat} (i jt : Fin n) (hij : jt ≠ i) (p : MultiPoly n) :
    degreeY jt (dropLeadingYAt i p) ≤ degreeY jt p := by
  show degreeY jt (reconstructY i (yCoeffsAt i p).dropLast 0) ≤ degreeY jt p
  exact degreeY_reconstructY_le_ne i jt hij (degreeY jt p) (yCoeffsAt i p).dropLast 0
    (fun c hc => yCoeffsAt_entries_degreeY_le jt i p c (List.dropLast_subset _ hc))

/-- **`liftInner` does not raise `degreeY jt`** past `max (degreeY jt c) (degreeY jt (liftLastY inner'))`
for `jt ≠ top` — the lift arm's inner bound. -/
theorem degreeY_liftInner_le_ne (k : Nat) (jt : Fin (k + 3))
    (hjt : jt ≠ (⟨k + 2, by omega⟩ : Fin (k + 3))) (c : MultiPoly (k + 3)) (inner' : MultiPoly (k + 2)) :
    degreeY jt (liftInner k c inner')
      ≤ Nat.max (degreeY jt c) (degreeY jt (liftLastY inner')) := by
  unfold liftInner
  apply degreeY_reconstructY_le_ne _ jt hjt
  intro c' hc'
  rw [List.mem_append] at hc'
  rcases hc' with h | h
  · exact Nat.le_trans
      (yCoeffsAt_entries_degreeY_le jt _ c c' (List.dropLast_subset _ h))
      (Nat.le_max_left _ _)
  · rw [List.mem_singleton] at h
    rw [h]
    exact Nat.le_max_right _ _

end MachLib.IterExpDepthN
