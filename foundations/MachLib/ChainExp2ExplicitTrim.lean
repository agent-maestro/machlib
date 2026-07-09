import MachLib.ChainExp2ExplicitBound
import MachLib.ChainExp2Trim

/-!
# Explicit chain-2 bound — the TRIM-side degree bound

`ChainExp2ExplicitBound.lean` proved the REDUCE-side degree-preservation facts the explicit bound
needs (`cdegY0_lcY1_reduce_le`, `degreeX_chain2Reduce_le`, `degreeY0_chain2Reduce_le`). The `rankLex A B`
linearizer (`ExplicitBoundRank.lean`) turns the nested-lex measure into a `Nat` given global bounds
`A ≥ cdegY0(lcY₁ q)` and `B ≥ (x-degree component)` over every `q` the WF recursion reaches.

The chain-2 recursion (`chain2_khovanskii_bound_unconditional`) has two descending arms:
  * **reduce** (`chain2Reduce …`) — bounds done in `ChainExp2ExplicitBound.lean`.
  * **trim** (`dropLeadingYAt ⟨1⟩ p`) — this file. `dropLeadingYAt i p = reconstructY i (yCoeffsAt i p).dropLast 0`,
    so its degrees are governed by `reconstructY` over a *sub-list* of `p`'s `y_i`-coefficients.

This file closes the trim's **B-bound** — `degreeX (dropLeadingYAt i p) ≤ degreeX p` — the trim analog of
`degreeX_chain2Reduce_le`, via a `degreeX`-non-raising tower over the `yCoeffsAt` list operations
(mirroring the existing `yCoeffsAt_entries_degreeY_zero` tower) plus `reconstructY`.

**Remaining for the full explicit chain-2 bound** (scoped):
  * Bridge: `singleExpMeasureCanon(lcY₁ q).2 ≤ degreeX q` (measure x-component ≤ poly x-degree) ⇒ global `B := degreeX p₀`.
  * A-bound trim analog (the ONE hard obligation, `ExplicitBoundRank.lean:48-52`): after reduces grow `degreeY₀`
    (`degreeY0_chain2Reduce_le`, +1/step), a `degreeY₁`-dropping trim still exposes an `lcY₁` whose `cdegY0`
    is bounded by a degree functional of the ORIGINAL `p` — the exponential-in-`degreeY₁` accounting ⇒ global `A`.
  * Thread the `(A,B)` invariant + `rankLex_succ_le` through the WF induction (replacing `∃ N`).

No new axioms — pure structural `Nat`/`degreeX` facts.
-/

namespace MachLib.ChainExp2Explicit

open MachLib.MultiPolyMod MachLib.MultiPolyMod.MultiPoly
open MachLib.MultiPolyReconstruct MachLib.ChainExp2Trim

/-! ### `reconstructY` degree core -/

/-- `degreeX ((varYⁱ)ᵏ) = 0` — the chain (`y_i`) variable is x-free, so any power of it is too. -/
theorem degreeX_pow_varY_zero {n : Nat} (i : Fin n) (k : Nat) :
    degreeX (pow (varY i) k) = 0 := by
  induction k with
  | zero => rfl
  | succ m ih =>
    show degreeX (varY i) + degreeX (pow (varY i) m) = 0
    rw [degreeX_varY, ih]

/-- **`reconstructY` never raises `degreeX` past its coefficients.** If every coefficient has
`degreeX ≤ D`, so does `reconstructY i coeffs k` — each term `c · (varYⁱ)ᵏ` has `degreeX = degreeX c`,
and `add` takes the max. -/
theorem degreeX_reconstructY_le {n : Nat} (i : Fin n) (D : Nat) :
    ∀ (coeffs : List (MultiPoly n)) (k : Nat),
      (∀ c ∈ coeffs, degreeX c ≤ D) → degreeX (reconstructY i coeffs k) ≤ D
  | [], _, _ => by rw [reconstructY_nil]; exact Nat.zero_le _
  | c :: cs, k, h => by
      rw [reconstructY_cons]
      show Nat.max (degreeX (mul c (pow (varY i) k))) (degreeX (reconstructY i cs (k + 1))) ≤ D
      refine Nat.max_le.mpr ⟨?_, ?_⟩
      · show degreeX c + degreeX (pow (varY i) k) ≤ D
        rw [degreeX_pow_varY_zero]
        have hc := h c (List.mem_cons_self c cs)
        omega
      · exact degreeX_reconstructY_le i D cs (k + 1)
          (fun c' hc' => h c' (List.mem_cons_of_mem c hc'))

/-! ### `degreeX`-non-raising tower over the `yCoeffsAt` list operations -/

/-- `listAddN` entries stay under a common `degreeX` bound `D`. -/
theorem listAddN_entries_degreeX_le {n : Nat} (l1 l2 : List (MultiPoly n)) (D : Nat)
    (h1 : ∀ c ∈ l1, degreeX c ≤ D) (h2 : ∀ c ∈ l2, degreeX c ≤ D) :
    ∀ c ∈ listAddN l1 l2, degreeX c ≤ D := by
  induction l1 generalizing l2 with
  | nil => intro c hc; rw [listAddN_nil_left] at hc; exact h2 c hc
  | cons p ps ih =>
    cases l2 with
    | nil => intro c hc; rw [listAddN_cons_nil] at hc; exact h1 c hc
    | cons q qs =>
      intro c hc; rw [listAddN_cons_cons] at hc
      cases hc with
      | head =>
        exact Nat.max_le.mpr ⟨h1 p (List.mem_cons_self _ _), h2 q (List.mem_cons_self _ _)⟩
      | tail _ hc' =>
        exact ih qs (fun c hc => h1 c (List.mem_cons_of_mem _ hc))
                 (fun c hc => h2 c (List.mem_cons_of_mem _ hc)) c hc'

/-- `listSubN` entries stay under a common `degreeX` bound `D`. -/
theorem listSubN_entries_degreeX_le {n : Nat} (l1 l2 : List (MultiPoly n)) (D : Nat)
    (h1 : ∀ c ∈ l1, degreeX c ≤ D) (h2 : ∀ c ∈ l2, degreeX c ≤ D) :
    ∀ c ∈ listSubN l1 l2, degreeX c ≤ D := by
  induction l1 generalizing l2 with
  | nil =>
    induction l2 with
    | nil => intro c hc; exact absurd hc (List.not_mem_nil _)
    | cons q qs ihq =>
      intro c hc
      change c ∈ (sub (const 0) q :: listSubN [] qs) at hc
      cases hc with
      | head =>
        exact Nat.max_le.mpr ⟨Nat.zero_le _, h2 q (List.mem_cons_self _ _)⟩
      | tail _ hc' => exact ihq (fun c hc => h2 c (List.mem_cons_of_mem _ hc)) c hc'
  | cons p ps ih =>
    cases l2 with
    | nil => intro c hc; change c ∈ (p :: ps) at hc; exact h1 c hc
    | cons q qs =>
      intro c hc; change c ∈ (sub p q :: listSubN ps qs) at hc
      cases hc with
      | head =>
        exact Nat.max_le.mpr ⟨h1 p (List.mem_cons_self _ _), h2 q (List.mem_cons_self _ _)⟩
      | tail _ hc' =>
        exact ih qs (fun c hc => h1 c (List.mem_cons_of_mem _ hc))
                 (fun c hc => h2 c (List.mem_cons_of_mem _ hc)) c hc'

/-- `listScaleN p l` entries: `degreeX ≤ Dp + D` where `Dp ≥ degreeX p` and `D` bounds `l`. -/
theorem listScaleN_entries_degreeX_le {n : Nat} (p : MultiPoly n) (Dp : Nat) (hp : degreeX p ≤ Dp)
    (l : List (MultiPoly n)) (D : Nat) (hl : ∀ c ∈ l, degreeX c ≤ D) :
    ∀ c ∈ listScaleN p l, degreeX c ≤ Dp + D := by
  induction l with
  | nil => intro c hc; rw [listScaleN_nil] at hc; exact absurd hc (List.not_mem_nil _)
  | cons q qs ih =>
    intro c hc; rw [listScaleN_cons] at hc
    cases hc with
    | head =>
      show degreeX p + degreeX q ≤ Dp + D
      exact Nat.add_le_add hp (hl q (List.mem_cons_self _ _))
    | tail _ hc' => exact ih (fun c hc => hl c (List.mem_cons_of_mem _ hc)) c hc'

/-- `listMulN l1 l2` entries: `degreeX ≤ D1 + D2`. -/
theorem listMulN_entries_degreeX_le {n : Nat} (l1 l2 : List (MultiPoly n)) (D1 D2 : Nat)
    (h1 : ∀ c ∈ l1, degreeX c ≤ D1) (h2 : ∀ c ∈ l2, degreeX c ≤ D2) :
    ∀ c ∈ listMulN l1 l2, degreeX c ≤ D1 + D2 := by
  induction l1 with
  | nil => intro c hc; rw [listMulN_nil] at hc; exact absurd hc (List.not_mem_nil _)
  | cons p ps ih =>
    intro c hc; rw [listMulN_cons] at hc
    refine listAddN_entries_degreeX_le (listScaleN p l2) (const 0 :: listMulN ps l2) (D1 + D2)
      ?_ ?_ c hc
    · exact listScaleN_entries_degreeX_le p D1 (h1 p (List.mem_cons_self _ _)) l2 D2 h2
    · intro c' hc'
      cases hc' with
      | head => exact Nat.zero_le _
      | tail _ hc'' => exact ih (fun c hc => h1 c (List.mem_cons_of_mem _ hc)) c' hc''

/-- **Every `yCoeffsAt i p` entry has `degreeX ≤ degreeX p`.** Structural induction over `p`, threading the
tower above through `listAddN`/`listSubN`/`listMulN` (mirror of `yCoeffsAt_entries_degreeY_zero`). -/
theorem yCoeffsAt_entries_degreeX_le {n : Nat} (i : Fin n) (p : MultiPoly n) :
    ∀ c ∈ yCoeffsAt i p, degreeX c ≤ degreeX p := by
  induction p with
  | const a =>
    intro c hc; change c ∈ [const a] at hc
    rw [List.mem_singleton] at hc; subst hc; exact Nat.le_refl _
  | varX =>
    intro c hc; change c ∈ [varX] at hc
    rw [List.mem_singleton] at hc; subst hc; exact Nat.le_refl _
  | varY j =>
    intro c hc
    by_cases hji : j = i
    · have he : yCoeffsAt i (varY j) = [const 0, const 1] := by
        show (if j = i then _ else _) = _; rw [if_pos hji]
      rw [he] at hc
      rcases List.mem_cons.mp hc with rfl | hc2
      · exact Nat.zero_le _
      · rw [List.mem_singleton] at hc2; subst hc2; exact Nat.zero_le _
    · have he : yCoeffsAt i (varY j) = [varY j] := by
        show (if j = i then _ else _) = _; rw [if_neg hji]
      rw [he, List.mem_singleton] at hc; subst hc; exact Nat.le_refl _
  | add p q ihp ihq =>
    intro c hc
    exact listAddN_entries_degreeX_le (yCoeffsAt i p) (yCoeffsAt i q) (Nat.max (degreeX p) (degreeX q))
      (fun c hc => Nat.le_trans (ihp c hc) (Nat.le_max_left _ _))
      (fun c hc => Nat.le_trans (ihq c hc) (Nat.le_max_right _ _)) c hc
  | sub p q ihp ihq =>
    intro c hc
    exact listSubN_entries_degreeX_le (yCoeffsAt i p) (yCoeffsAt i q) (Nat.max (degreeX p) (degreeX q))
      (fun c hc => Nat.le_trans (ihp c hc) (Nat.le_max_left _ _))
      (fun c hc => Nat.le_trans (ihq c hc) (Nat.le_max_right _ _)) c hc
  | mul p q ihp ihq =>
    intro c hc
    exact listMulN_entries_degreeX_le (yCoeffsAt i p) (yCoeffsAt i q) (degreeX p) (degreeX q)
      ihp ihq c hc

/-! ### The trim B-bound -/

/-- **`degreeX` non-increase under the trim (B-bound).** `dropLeadingYAt i p = reconstructY` over a
sub-list (`dropLast`) of `p`'s `y_i`-coefficients, each of `degreeX ≤ degreeX p`, so the reconstruction
does not exceed `degreeX p`. The trim analog of `degreeX_chain2Reduce_le`. -/
theorem degreeX_dropLeadingYAt_le {n : Nat} (i : Fin n) (p : MultiPoly n) :
    degreeX (dropLeadingYAt i p) ≤ degreeX p := by
  show degreeX (reconstructY i (yCoeffsAt i p).dropLast 0) ≤ degreeX p
  exact degreeX_reconstructY_le i (degreeX p) (yCoeffsAt i p).dropLast 0
    (fun c hc => yCoeffsAt_entries_degreeX_le i p c (List.dropLast_subset _ hc))

end MachLib.ChainExp2Explicit
