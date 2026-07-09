import MachLib.ChainExp2ExplicitTrim

/-!
# Explicit chain-2 bound — the A-bound foundation (`cdegY0(lcY₁ q) ≤ degreeY₀ q`)

The B-bound is closed (`ChainExp2ExplicitTrim.lean`: x-degree non-increasing under both recursion arms
+ the measure↔degreeX bridge). This file starts the **A-bound**: a global bound on the measure's
first inner component `cdegY0(lcY₁ q)` over the recursion.

The clean load-bearing link is `cdegY0(lcY₁ q) ≤ degreeY₀ q`, via:
  * `degreeY_leadingCoeffY_le` — `leadingCoeffY i` never raises the degree in ANY variable `y_j`
    (cross-index; a direct mirror of `MultiPoly.degreeX_leadingCoeffY_le`, valid for `j = i` too since
    then the LHS is 0). A general, reusable MultiPoly fact.
  * `cdegY0_le_degreeY0` (existing) — the canonical `y₀`-degree refines the syntactic one.

So `A`'s per-node value is bounded by `degreeY₀ q`. What remains for the FULL A-bound is the genuine
research mile: `degreeY₀ q` GROWS `+1` per reduce (`degreeY0_chain2Reduce_le`) and is non-increasing
under trim, so a global `A` is NOT a fixed functional of `p₀` — it is entangled with the reduce count
itself (the exponential-in-`degreeY₁` accounting). Closing it needs a level-indexed / recurrence
argument, not just these monotonicity facts. This file supplies the `cdegY0 → degreeY₀` reduction; the
`degreeY₀`-evolution facts (`degreeY0_chain2Reduce_le` exists; the trim `degreeY₀` non-increase mirrors
the degreeX trim tower) plus the accounting are the remainder.

No new axioms.
-/

namespace MachLib.ChainExp2Explicit

open MachLib.MultiPolyMod MachLib.MultiPolyMod.MultiPoly
open MachLib.ChainExp2CanonMeasure
open MachLib.MultiPolyReconstruct MachLib.ChainExp2Trim

/-- **`leadingCoeffY i` never raises the degree in any `y_j`** (cross-index). Direct mirror of
`degreeX_leadingCoeffY_le`; for `j = i` the leading coefficient is `y_i`-free so the LHS is 0. -/
theorem degreeY_leadingCoeffY_le {n : Nat} (i j : Fin n) :
    ∀ p : MultiPoly n, degreeY j (leadingCoeffY i p) ≤ degreeY j p
  | const _ => Nat.le_refl _
  | varX => Nat.le_refl _
  | varY k => by
      show degreeY j (if k = i then const 1 else varY k) ≤ degreeY j (varY k : MultiPoly n)
      by_cases h : k = i
      · simp [h]; exact Nat.zero_le _
      · simp [h]
  | add p q => by
      show degreeY j (if degreeY i p > degreeY i q then leadingCoeffY i p
             else if degreeY i q > degreeY i p then leadingCoeffY i q
             else add (leadingCoeffY i p) (leadingCoeffY i q))
           ≤ Nat.max (degreeY j p) (degreeY j q)
      by_cases h1 : degreeY i p > degreeY i q
      · simp [h1]; exact Nat.le_trans (degreeY_leadingCoeffY_le i j p) (Nat.le_max_left _ _)
      · simp [h1]
        by_cases h2 : degreeY i q > degreeY i p
        · simp [h2]; exact Nat.le_trans (degreeY_leadingCoeffY_le i j q) (Nat.le_max_right _ _)
        · simp [h2]
          show Nat.max (degreeY j (leadingCoeffY i p)) (degreeY j (leadingCoeffY i q))
               ≤ Nat.max (degreeY j p) (degreeY j q)
          exact Nat.max_le.mpr
            ⟨Nat.le_trans (degreeY_leadingCoeffY_le i j p) (Nat.le_max_left _ _),
             Nat.le_trans (degreeY_leadingCoeffY_le i j q) (Nat.le_max_right _ _)⟩
  | sub p q => by
      show degreeY j (if degreeY i p > degreeY i q then leadingCoeffY i p
             else if degreeY i q > degreeY i p then sub (const 0) (leadingCoeffY i q)
             else sub (leadingCoeffY i p) (leadingCoeffY i q))
           ≤ Nat.max (degreeY j p) (degreeY j q)
      by_cases h1 : degreeY i p > degreeY i q
      · simp [h1]; exact Nat.le_trans (degreeY_leadingCoeffY_le i j p) (Nat.le_max_left _ _)
      · simp [h1]
        by_cases h2 : degreeY i q > degreeY i p
        · simp [h2]
          show Nat.max (degreeY j (const 0 : MultiPoly n)) (degreeY j (leadingCoeffY i q))
               ≤ Nat.max (degreeY j p) (degreeY j q)
          exact Nat.max_le.mpr
            ⟨Nat.zero_le _, Nat.le_trans (degreeY_leadingCoeffY_le i j q) (Nat.le_max_right _ _)⟩
        · simp [h2]
          show Nat.max (degreeY j (leadingCoeffY i p)) (degreeY j (leadingCoeffY i q))
               ≤ Nat.max (degreeY j p) (degreeY j q)
          exact Nat.max_le.mpr
            ⟨Nat.le_trans (degreeY_leadingCoeffY_le i j p) (Nat.le_max_left _ _),
             Nat.le_trans (degreeY_leadingCoeffY_le i j q) (Nat.le_max_right _ _)⟩
  | mul p q => by
      show degreeY j (leadingCoeffY i p) + degreeY j (leadingCoeffY i q)
           ≤ degreeY j p + degreeY j q
      exact Nat.add_le_add (degreeY_leadingCoeffY_le i j p) (degreeY_leadingCoeffY_le i j q)

/-- **The A-component ≤ `degreeY₀` link.** `cdegY0 (lcY₁ q) ≤ degreeY₀ q`: the canonical `y₀`-degree of
the `y₁`-leading coefficient refines the syntactic `y₀`-degree (`cdegY0_le_degreeY0`), which
`leadingCoeffY ⟨1⟩` does not raise (`degreeY_leadingCoeffY_le`). So `A`'s per-node value is governed by
`degreeY₀ q`. -/
theorem cdegY0_lcY1_le_degreeY0 (q : MultiPoly 2) :
    cdegY0 (leadingCoeffY (⟨1, by omega⟩ : Fin 2) q) ≤ degreeY (⟨0, by omega⟩ : Fin 2) q :=
  Nat.le_trans (cdegY0_le_degreeY0 _)
    (degreeY_leadingCoeffY_le (⟨1, by omega⟩ : Fin 2) (⟨0, by omega⟩ : Fin 2) q)

/-! ### The trim `degreeY₀` non-increase (`degreeY₀(dropLeadingYAt ⟨1⟩ q) ≤ degreeY₀ q`)

A degreeY-⟨0⟩ mirror of the degreeX trim tower (`ChainExp2ExplicitTrim`): the trim `dropLeadingYAt ⟨1⟩`
reconstructs at index ⟨1⟩ over a sub-list of the ⟨1⟩-coefficients, and `degreeY ⟨0⟩` is 0 on powers of
`varY ⟨1⟩`, `max` on add/sub, `+` on mul — so the reconstruction does not raise `degreeY ⟨0⟩`. The
list-entry proofs are identical to the degreeX ones (both degrees have the same add/sub/mul behaviour);
only the `varY` base case differs (`degreeY ⟨0⟩ (varY ⟨0⟩) = 1`). Needed for the trim arm of the A-bound
(`invPhi_trim`'s `g' ≤ g`). -/

/-- `degreeY ⟨0⟩ ((varY ⟨1⟩)ᵏ) = 0` — the reconstruct variable `y₁` is `y₀`-free. -/
theorem degreeY0_pow_varY1_zero (k : Nat) :
    degreeY (⟨0, by omega⟩ : Fin 2) (pow (varY (⟨1, by omega⟩ : Fin 2)) k) = 0 := by
  have hne : (⟨0, by omega⟩ : Fin 2) ≠ (⟨1, by omega⟩ : Fin 2) := by
    intro h; have : (0 : Nat) = 1 := congrArg Fin.val h; omega
  induction k with
  | zero => rfl
  | succ m ih =>
    show degreeY (⟨0, by omega⟩ : Fin 2) (varY (⟨1, by omega⟩ : Fin 2))
        + degreeY (⟨0, by omega⟩ : Fin 2) (pow (varY (⟨1, by omega⟩ : Fin 2)) m) = 0
    rw [ih]
    show (if (⟨0, by omega⟩ : Fin 2) = (⟨1, by omega⟩ : Fin 2) then 1 else 0) + 0 = 0
    rw [if_neg hne]

/-- `reconstructY ⟨1⟩` never raises `degreeY ⟨0⟩` past its coefficients. -/
theorem degreeY0_reconstructY1_le (D : Nat) :
    ∀ (coeffs : List (MultiPoly 2)) (k : Nat),
      (∀ c ∈ coeffs, degreeY (⟨0, by omega⟩ : Fin 2) c ≤ D) →
      degreeY (⟨0, by omega⟩ : Fin 2) (reconstructY (⟨1, by omega⟩ : Fin 2) coeffs k) ≤ D
  | [], _, _ => by rw [reconstructY_nil]; exact Nat.zero_le _
  | c :: cs, k, h => by
      rw [reconstructY_cons]
      show Nat.max (degreeY (⟨0, by omega⟩ : Fin 2)
                      (mul c (pow (varY (⟨1, by omega⟩ : Fin 2)) k)))
                   (degreeY (⟨0, by omega⟩ : Fin 2)
                      (reconstructY (⟨1, by omega⟩ : Fin 2) cs (k + 1))) ≤ D
      refine Nat.max_le.mpr ⟨?_, ?_⟩
      · show degreeY (⟨0, by omega⟩ : Fin 2) c
            + degreeY (⟨0, by omega⟩ : Fin 2) (pow (varY (⟨1, by omega⟩ : Fin 2)) k) ≤ D
        rw [degreeY0_pow_varY1_zero]
        have hc := h c (List.mem_cons_self c cs)
        omega
      · exact degreeY0_reconstructY1_le D cs (k + 1)
          (fun c' hc' => h c' (List.mem_cons_of_mem c hc'))

theorem listAddN_entries_degreeY0_le (l1 l2 : List (MultiPoly 2)) (D : Nat)
    (h1 : ∀ c ∈ l1, degreeY (⟨0, by omega⟩ : Fin 2) c ≤ D)
    (h2 : ∀ c ∈ l2, degreeY (⟨0, by omega⟩ : Fin 2) c ≤ D) :
    ∀ c ∈ listAddN l1 l2, degreeY (⟨0, by omega⟩ : Fin 2) c ≤ D := by
  induction l1 generalizing l2 with
  | nil => intro c hc; rw [listAddN_nil_left] at hc; exact h2 c hc
  | cons p ps ih =>
    cases l2 with
    | nil => intro c hc; rw [listAddN_cons_nil] at hc; exact h1 c hc
    | cons q qs =>
      intro c hc; rw [listAddN_cons_cons] at hc
      cases hc with
      | head => exact Nat.max_le.mpr ⟨h1 p (List.mem_cons_self _ _), h2 q (List.mem_cons_self _ _)⟩
      | tail _ hc' =>
        exact ih qs (fun c hc => h1 c (List.mem_cons_of_mem _ hc))
                 (fun c hc => h2 c (List.mem_cons_of_mem _ hc)) c hc'

theorem listSubN_entries_degreeY0_le (l1 l2 : List (MultiPoly 2)) (D : Nat)
    (h1 : ∀ c ∈ l1, degreeY (⟨0, by omega⟩ : Fin 2) c ≤ D)
    (h2 : ∀ c ∈ l2, degreeY (⟨0, by omega⟩ : Fin 2) c ≤ D) :
    ∀ c ∈ listSubN l1 l2, degreeY (⟨0, by omega⟩ : Fin 2) c ≤ D := by
  induction l1 generalizing l2 with
  | nil =>
    induction l2 with
    | nil => intro c hc; exact absurd hc (List.not_mem_nil _)
    | cons q qs ihq =>
      intro c hc
      change c ∈ (sub (const 0) q :: listSubN [] qs) at hc
      cases hc with
      | head => exact Nat.max_le.mpr ⟨Nat.zero_le _, h2 q (List.mem_cons_self _ _)⟩
      | tail _ hc' => exact ihq (fun c hc => h2 c (List.mem_cons_of_mem _ hc)) c hc'
  | cons p ps ih =>
    cases l2 with
    | nil => intro c hc; change c ∈ (p :: ps) at hc; exact h1 c hc
    | cons q qs =>
      intro c hc; change c ∈ (sub p q :: listSubN ps qs) at hc
      cases hc with
      | head => exact Nat.max_le.mpr ⟨h1 p (List.mem_cons_self _ _), h2 q (List.mem_cons_self _ _)⟩
      | tail _ hc' =>
        exact ih qs (fun c hc => h1 c (List.mem_cons_of_mem _ hc))
                 (fun c hc => h2 c (List.mem_cons_of_mem _ hc)) c hc'

theorem listScaleN_entries_degreeY0_le (p : MultiPoly 2) (Dp : Nat)
    (hp : degreeY (⟨0, by omega⟩ : Fin 2) p ≤ Dp)
    (l : List (MultiPoly 2)) (D : Nat) (hl : ∀ c ∈ l, degreeY (⟨0, by omega⟩ : Fin 2) c ≤ D) :
    ∀ c ∈ listScaleN p l, degreeY (⟨0, by omega⟩ : Fin 2) c ≤ Dp + D := by
  induction l with
  | nil => intro c hc; rw [listScaleN_nil] at hc; exact absurd hc (List.not_mem_nil _)
  | cons q qs ih =>
    intro c hc; rw [listScaleN_cons] at hc
    cases hc with
    | head => exact Nat.add_le_add hp (hl q (List.mem_cons_self _ _))
    | tail _ hc' => exact ih (fun c hc => hl c (List.mem_cons_of_mem _ hc)) c hc'

theorem listMulN_entries_degreeY0_le (l1 l2 : List (MultiPoly 2)) (D1 D2 : Nat)
    (h1 : ∀ c ∈ l1, degreeY (⟨0, by omega⟩ : Fin 2) c ≤ D1)
    (h2 : ∀ c ∈ l2, degreeY (⟨0, by omega⟩ : Fin 2) c ≤ D2) :
    ∀ c ∈ listMulN l1 l2, degreeY (⟨0, by omega⟩ : Fin 2) c ≤ D1 + D2 := by
  induction l1 with
  | nil => intro c hc; rw [listMulN_nil] at hc; exact absurd hc (List.not_mem_nil _)
  | cons p ps ih =>
    intro c hc; rw [listMulN_cons] at hc
    refine listAddN_entries_degreeY0_le (listScaleN p l2) (const 0 :: listMulN ps l2) (D1 + D2)
      ?_ ?_ c hc
    · exact listScaleN_entries_degreeY0_le p D1 (h1 p (List.mem_cons_self _ _)) l2 D2 h2
    · intro c' hc'
      cases hc' with
      | head => exact Nat.zero_le _
      | tail _ hc'' => exact ih (fun c hc => h1 c (List.mem_cons_of_mem _ hc)) c' hc''

/-- Every `yCoeffsAt ⟨1⟩ p` entry has `degreeY ⟨0⟩ ≤ degreeY ⟨0⟩ p`. -/
theorem yCoeffsAt_entries_degreeY0_le (p : MultiPoly 2) :
    ∀ c ∈ yCoeffsAt (⟨1, by omega⟩ : Fin 2) p, degreeY (⟨0, by omega⟩ : Fin 2) c
      ≤ degreeY (⟨0, by omega⟩ : Fin 2) p := by
  induction p with
  | const a =>
    intro c hc; change c ∈ [const a] at hc
    rw [List.mem_singleton] at hc; subst hc; exact Nat.le_refl _
  | varX =>
    intro c hc; change c ∈ [varX] at hc
    rw [List.mem_singleton] at hc; subst hc; exact Nat.le_refl _
  | varY j =>
    intro c hc
    by_cases hji : j = (⟨1, by omega⟩ : Fin 2)
    · have he : yCoeffsAt (⟨1, by omega⟩ : Fin 2) (varY j) = [const 0, const 1] := by
        show (if j = (⟨1, by omega⟩ : Fin 2) then _ else _) = _; rw [if_pos hji]
      rw [he] at hc
      rcases List.mem_cons.mp hc with rfl | hc2
      · exact Nat.zero_le _
      · rw [List.mem_singleton] at hc2; subst hc2; exact Nat.zero_le _
    · have he : yCoeffsAt (⟨1, by omega⟩ : Fin 2) (varY j) = [varY j] := by
        show (if j = (⟨1, by omega⟩ : Fin 2) then _ else _) = _; rw [if_neg hji]
      rw [he, List.mem_singleton] at hc; subst hc; exact Nat.le_refl _
  | add p q ihp ihq =>
    intro c hc
    exact listAddN_entries_degreeY0_le (yCoeffsAt (⟨1, by omega⟩ : Fin 2) p)
      (yCoeffsAt (⟨1, by omega⟩ : Fin 2) q)
      (Nat.max (degreeY (⟨0, by omega⟩ : Fin 2) p) (degreeY (⟨0, by omega⟩ : Fin 2) q))
      (fun c hc => Nat.le_trans (ihp c hc) (Nat.le_max_left _ _))
      (fun c hc => Nat.le_trans (ihq c hc) (Nat.le_max_right _ _)) c hc
  | sub p q ihp ihq =>
    intro c hc
    exact listSubN_entries_degreeY0_le (yCoeffsAt (⟨1, by omega⟩ : Fin 2) p)
      (yCoeffsAt (⟨1, by omega⟩ : Fin 2) q)
      (Nat.max (degreeY (⟨0, by omega⟩ : Fin 2) p) (degreeY (⟨0, by omega⟩ : Fin 2) q))
      (fun c hc => Nat.le_trans (ihp c hc) (Nat.le_max_left _ _))
      (fun c hc => Nat.le_trans (ihq c hc) (Nat.le_max_right _ _)) c hc
  | mul p q ihp ihq =>
    intro c hc
    exact listMulN_entries_degreeY0_le (yCoeffsAt (⟨1, by omega⟩ : Fin 2) p)
      (yCoeffsAt (⟨1, by omega⟩ : Fin 2) q)
      (degreeY (⟨0, by omega⟩ : Fin 2) p) (degreeY (⟨0, by omega⟩ : Fin 2) q) ihp ihq c hc

/-- **The trim `degreeY₀` non-increase.** `degreeY ⟨0⟩ (dropLeadingYAt ⟨1⟩ p) ≤ degreeY ⟨0⟩ p` — the
`invPhi_trim` prerequisite (`g' ≤ g`). -/
theorem degreeY0_dropLeadingYAt1_le (p : MultiPoly 2) :
    degreeY (⟨0, by omega⟩ : Fin 2) (dropLeadingYAt (⟨1, by omega⟩ : Fin 2) p)
      ≤ degreeY (⟨0, by omega⟩ : Fin 2) p := by
  show degreeY (⟨0, by omega⟩ : Fin 2)
        (reconstructY (⟨1, by omega⟩ : Fin 2) (yCoeffsAt (⟨1, by omega⟩ : Fin 2) p).dropLast 0)
      ≤ degreeY (⟨0, by omega⟩ : Fin 2) p
  exact degreeY0_reconstructY1_le (degreeY (⟨0, by omega⟩ : Fin 2) p)
    (yCoeffsAt (⟨1, by omega⟩ : Fin 2) p).dropLast 0
    (fun c hc => yCoeffsAt_entries_degreeY0_le p c (List.dropLast_subset _ hc))

end MachLib.ChainExp2Explicit
