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

end MachLib.ChainExp2Explicit
