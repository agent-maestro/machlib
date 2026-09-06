import MachLib.SignedFixedPoint
import MachLib.TwoStateTracking

/-!
# The join, for a PI controller: a signed bit-level loop with an integrator

This is the instantiation `TwoStateTracking` was written for, and it removes the last of the four
obstacles `foundations/docs/what_is_proven.md` §2 lists between the corpus and an end-to-end
closed-loop result for a controller with state.

**What is proved.** For a proportional-integral controller with quantised gains, the signed
bit-level closed loop

```
X_{k+1} = GA ⊗ X_k ⊕ GB ⊗ I_k ⊕ GC        (two truncating multiplies)
I_{k+1} = (I_k ⊖ X_k) ⊕ GF                 (exact — no multiply on the integrator row)
```

stays within `npow n L · m₀ + 4·ulp · geom L n` of the exact real PI trajectory, where `L` bounds
the closed-loop eigenvalues and the error is measured by the eigen-coordinate seminorm of
`TwoStateTracking`. The per-step `4·ulp` is **derived** from the datapath — two signed truncating
multiplies at `2·ulp` each — and the integrator row contributes nothing, because subtraction and
addition of signed vectors are exact.

**Why this is general rather than a specimen.** The integrator row of a PI loop is always
`i' = −x + i + r`, so the closed-loop matrix is `[[A, B], [−1, 1]]` and its left eigenvectors are
forced: `(1, λ₂ − 1)` and `(1, λ₁ − 1)`. Substituting them into the four eigen equations gives
**pure ring identities in `λ₁` and `λ₂`** — they hold for arbitrary eigenvalues, with no side
condition and no decimal arithmetic anywhere. So the contraction hypothesis of
`two_state_tracks_exact` is discharged once, for every PI design whose closed-loop eigenvalues are
real, rather than at hand-picked gains.

The caller supplies only what is genuinely design-specific: that `λ₁, λ₂` are the eigenvalues of
its own *quantised* gains (`A = λ₁ + λ₂ − 1`, `B = (1−λ₁)(1−λ₂)` — the characteristic equation
written as the coefficients), and a bound `L` on their moduli.

**What is still not claimed.** The eigenvalues must be **real**: a complex pair (an under-damped
design) has no real eigenvector and this measure does not exist for it. No anti-windup, no
derivative term, and no claim about a physical plant — the subject is the datapath and the real
recurrence it implements. `pid_trajectory_from_bits` remains what it was; it is not this theorem
and its `ε` is still universally quantified.
-/

namespace MachLib

namespace SRTL

/-- **The signed PI closed loop, over bits.** The integrator row uses `ssub`/`sadd` only, so it is
exact; all the error in the loop comes from the two truncating multiplies on the state row. -/
def spiloop (GA GB GC GF X0 I0 : SVec) : Nat → SVec × SVec
  | 0 => (X0, I0)
  | k + 1 =>
      let st := spiloop GA GB GC GF X0 I0 k
      (sadd (sadd (sfxmul GA st.1) (sfxmul GB st.2)) GC, sadd (ssub st.2 st.1) GF)

end SRTL

namespace Real

open SRTL

/-- The exact real PI recurrence the datapath implements, in the coefficient form
`two_state_tracks_exact` consumes. -/
noncomputable def exactPI (A B C F x0 i0 : Real) : Nat → Real × Real
  | 0 => (x0, i0)
  | k + 1 =>
      let st := exactPI A B C F x0 i0 k
      (A * st.1 + B * st.2 + C, (-1) * st.1 + 1 * st.2 + F)

/-! ### The eigenstructure of a PI loop is forced, and free -/

/-- **The contraction hypothesis, discharged for every PI design with real eigenvalues.**

The closed-loop matrix of a PI loop is `[[A, B], [−1, 1]]`, and writing its coefficients through
the characteristic equation — `A = λ₁ + λ₂ − 1`, `B = (1−λ₁)(1−λ₂)` — makes the left eigenvectors
`(1, λ₂−1)` and `(1, λ₁−1)`. All four eigen equations are then ring identities in `λ₁, λ₂`: they
need no hypothesis at all, which is why this is a theorem about every such design rather than a
specimen at chosen gains. -/
theorem pi_eigen_contraction {lam₁ lam₂ L : Real}
    (h₁ : abs lam₁ ≤ L) (h₂ : abs lam₂ ≤ L) (u v : Real) :
    m2 1 (lam₂ - 1) 1 (lam₁ - 1)
        ((lam₁ + lam₂ - 1) * u + ((1 - lam₁) * (1 - lam₂)) * v) ((-1) * u + 1 * v)
      ≤ L * m2 1 (lam₂ - 1) 1 (lam₁ - 1) u v := by
  refine m2_contract_of_eigen (lam₁ := lam₁) (lam₂ := lam₂) ?_ ?_ ?_ ?_ h₁ h₂ u v
  · mach_mpoly [lam₁, lam₂]
  · mach_mpoly [lam₁, lam₂]
  · mach_mpoly [lam₁, lam₂]
  · mach_mpoly [lam₁, lam₂]

/-- With both functionals' first coefficient `1`, a perturbation confined to the state row is
measured at its own size — the integrator row being exact is what makes this the whole per-step
error rather than a term in it. -/
theorem m2_state_only (q s u : Real) : m2 1 q 1 s u 0 = abs u := by
  show max (abs (1 * u + q * 0)) (abs (1 * u + s * 0)) = abs u
  have e : (1 : Real) * u + q * 0 = u := by mach_mpoly [u, q]
  have e' : (1 : Real) * u + s * 0 = u := by mach_mpoly [u, s]
  rw [e, e', max_self]

/-! ### The datapath's per-step error -/

/-- The integrator row is **exact**: `sadd (ssub i x) F` denotes `−x + i + F` with no truncation,
because signed subtraction and addition are exact. -/
theorem spi_integrator_exact (X I GF : SVec) :
    sval (sadd (ssub I X) GF) = (-1) * sval X + 1 * sval I + sval GF := by
  rw [sval_sadd, sval_ssub]
  mach_mpoly [sval X, sval I, sval GF]

/-- **The state row is within `4·ulp`**: two signed truncating multiplies at `2·ulp` each, and the
two adders contribute nothing. -/
theorem spi_state_error (GA GB GC X I : SVec) :
    abs (sval (sadd (sadd (sfxmul GA X) (sfxmul GB I)) GC)
         - (sval GA * sval X + sval GB * sval I + sval GC))
      ≤ natCast 4 * ulp := by
  obtain ⟨hp1, hn1⟩ := sval_sfxmul_error GA X
  obtain ⟨hp2, hn2⟩ := sval_sfxmul_error GB I
  have hsplit : sval (sadd (sadd (sfxmul GA X) (sfxmul GB I)) GC)
        - (sval GA * sval X + sval GB * sval I + sval GC)
      = (sval (sfxmul GA X) - sval GA * sval X)
        + (sval (sfxmul GB I) - sval GB * sval I) := by
    rw [sval_sadd, sval_sadd]
    mach_mpoly [sval (sfxmul GA X), sval (sfxmul GB I), sval GC,
                sval GA * sval X, sval GB * sval I]
  have hfour : natCast 4 * ulp = natCast 2 * ulp + natCast 2 * ulp := by
    have h : natCast 4 = natCast 2 + natCast 2 := by
      have e : (4 : Nat) = 2 + 2 := by omega
      rw [e, natCast_add]
    rw [h]; mach_mpoly [natCast 2, ulp]
  rw [hsplit, hfour]
  refine abs_le_of ?_ ?_
  · exact add_le_add_both (le_of_lt hn1) (le_of_lt hn2)
  · have e : -((sval (sfxmul GA X) - sval GA * sval X)
              + (sval (sfxmul GB I) - sval GB * sval I))
        = (sval GA * sval X - sval (sfxmul GA X))
          + (sval GB * sval I - sval (sfxmul GB I)) := by
      mach_mpoly [sval (sfxmul GA X), sval GA * sval X,
                  sval (sfxmul GB I), sval GB * sval I]
    rw [e]
    exact add_le_add_both (le_of_lt hp1) (le_of_lt hp2)

/-- `x = a + (x − a)`: the residual form, factored over fresh variables.

`mach_mpoly`'s bracket list cannot parse an atom containing a projection like
`(spiloop … k).1` — the same parser limitation `CLAUDE.md` records for `obtain`-bound `Nat`s. The
established workaround is a lemma over clean variables applied by term application, which handles
arbitrary expressions because only the tactic's list macro chokes on them. -/
private theorem residual_eq (x a : Real) : x = a + (x - a) := by mach_mpoly [x, a]

/-- `y = y + 0`, for the integrator row whose residual is literally zero. -/
private theorem eq_add_zero (y : Real) : y = y + 0 := (add_zero y).symm

/-! ### The join -/

/-- **The signed bit-level PI loop tracks the exact real PI loop.**

The subject is the datapath: `spiloop` is built from `List Bool` pairs by the signed adder,
subtractor and truncating multiply. The per-step `4·ulp` is derived from those operations
(`spi_state_error`), the integrator row contributes none (`spi_integrator_exact`), and the
contraction is free for any PI design with real closed-loop eigenvalues
(`pi_eigen_contraction`).

`heig` is the one design-specific input: it says `λ₁, λ₂` are the eigenvalues of the caller's own
**quantised** gains, written as the characteristic equation's coefficient form. Nothing here
assumes the quantised gains are close to the designer's intended ones — that is a separate
question and this theorem does not answer it. -/
theorem spiloop_tracks_exact
    (GA GB GC GF X0 I0 : SVec) {lam₁ lam₂ L : Real}
    (heigA : sval GA = lam₁ + lam₂ - 1)
    (heigB : sval GB = (1 - lam₁) * (1 - lam₂))
    (h₁ : abs lam₁ ≤ L) (h₂ : abs lam₂ ≤ L) (hL : 0 ≤ L) (n : Nat) :
    m2 1 (lam₂ - 1) 1 (lam₁ - 1)
        (sval (spiloop GA GB GC GF X0 I0 n).1
          - (exactPI (sval GA) (sval GB) (sval GC) (sval GF) (sval X0) (sval I0) n).1)
        (sval (spiloop GA GB GC GF X0 I0 n).2
          - (exactPI (sval GA) (sval GB) (sval GC) (sval GF) (sval X0) (sval I0) n).2)
      ≤ npow n L * m2 1 (lam₂ - 1) 1 (lam₁ - 1)
            (sval (spiloop GA GB GC GF X0 I0 0).1
              - (exactPI (sval GA) (sval GB) (sval GC) (sval GF) (sval X0) (sval I0) 0).1)
            (sval (spiloop GA GB GC GF X0 I0 0).2
              - (exactPI (sval GA) (sval GB) (sval GC) (sval GF) (sval X0) (sval I0) 0).2)
        + natCast 4 * ulp * geom L n := by
  -- the state row's residual, named so the recurrence holds by construction
  let dx : Nat → Real := fun k =>
    sval (spiloop GA GB GC GF X0 I0 (k + 1)).1
      - (sval GA * sval (spiloop GA GB GC GF X0 I0 k).1
         + sval GB * sval (spiloop GA GB GC GF X0 I0 k).2 + sval GC)
  refine two_state_tracks_exact (A := sval GA) (B := sval GB) (C := sval GC)
    (D := -1) (E := 1) (F := sval GF) (L := L) (ε := natCast 4 * ulp)
    (p := 1) (q := lam₂ - 1) (r := 1) (s := lam₁ - 1)
    (x := fun k => sval (spiloop GA GB GC GF X0 I0 k).1)
    (i := fun k => sval (spiloop GA GB GC GF X0 I0 k).2)
    (xe := fun k => (exactPI (sval GA) (sval GB) (sval GC) (sval GF) (sval X0) (sval I0) k).1)
    (ie := fun k => (exactPI (sval GA) (sval GB) (sval GC) (sval GF) (sval X0) (sval I0) k).2)
    (dx := dx) (di := fun _ => 0)
    hL (mul_nonneg (natCast_nonneg 4) (le_of_lt ulp_pos))
    (fun k => rfl) (fun k => rfl) (fun k => residual_eq _ _) ?_ ?_ ?_ n
  · -- the integrator row is exact, so its residual is literally zero
    intro k
    show sval (sadd (ssub (spiloop GA GB GC GF X0 I0 k).2 (spiloop GA GB GC GF X0 I0 k).1) GF)
        = (-1) * sval (spiloop GA GB GC GF X0 I0 k).1
          + 1 * sval (spiloop GA GB GC GF X0 I0 k).2 + sval GF + 0
    rw [spi_integrator_exact]
    exact eq_add_zero _
  · -- the contraction, free for any PI design with real eigenvalues
    intro u v
    rw [heigA, heigB]
    exact pi_eigen_contraction h₁ h₂ u v
  · -- the per-step error: the state row within 4 ulp, the integrator row exact
    intro k
    rw [m2_state_only]
    exact spi_state_error GA GB GC (spiloop GA GB GC GF X0 I0 k).1
      (spiloop GA GB GC GF X0 I0 k).2

/-! ### A specimen — the design hypotheses are satisfiable

`spiloop_tracks_exact` is conditional on `heigA` and `heigB`, which tie the caller's quantised
gains to a pair of real eigenvalues. A pair of gains admitting no such eigenvalues would make the
theorem empty on that design, so one concrete datapath is exhibited here. This corpus has a
recorded flagship that was vacuously true for weeks while every gate passed; the rule written
afterwards is that a capstone ships with its hypotheses discharged at a point.

The specimen is the **deadbeat** design `λ₁ = λ₂ = 0`: gains `A = −1`, `B = 1`, contraction factor
`L = 0`. Both eigenvalues at the origin means the exact loop reaches its target in two steps and
the tracking bound collapses to the last step's rounding — `4·ulp`, with no accumulation at all,
since `geom 0 n = 1` for `n ≥ 1`. It is a real design and a sharp instance rather than a
convenient one. -/

/-- `2^FRAC` as a bit-vector: sixteen zeros then a one (`toNat` is little-endian). Its `qval` is
exactly `1`, which is what lets a gain of `±1` be a genuine datapath constant. -/
def oneVec : List Bool := List.replicate RTL.FRAC false ++ [true]

theorem toNat_oneVec : RTL.toNat oneVec = 2 ^ RTL.FRAC := by decide

theorem qval_oneVec : qval oneVec = 1 := by
  unfold qval
  rw [toNat_oneVec]
  exact ulp_scale

/-- Gain `A = −1`, as a signed datapath constant. -/
theorem sval_negOne : sval ([], oneVec) = -1 := by
  show qval ([] : List Bool) - qval oneVec = -1
  rw [qval_nil, qval_oneVec]
  mach_ring

/-- Gain `B = +1`. -/
theorem sval_posOne : sval (oneVec, []) = 1 := by
  show qval oneVec - qval ([] : List Bool) = 1
  rw [qval_nil, qval_oneVec]
  mach_ring

/-- **The capstone, instantiated at the deadbeat design.** Every hypothesis discharged at a
concrete datapath, so the bound is a statement about actual bit vectors. -/
theorem spiloop_tracks_exact_deadbeat (GC GF X0 I0 : SVec) (n : Nat) :
    m2 1 (0 - 1) 1 (0 - 1)
        (sval (spiloop ([], oneVec) (oneVec, []) GC GF X0 I0 n).1
          - (exactPI (sval ([], oneVec)) (sval (oneVec, [])) (sval GC) (sval GF)
              (sval X0) (sval I0) n).1)
        (sval (spiloop ([], oneVec) (oneVec, []) GC GF X0 I0 n).2
          - (exactPI (sval ([], oneVec)) (sval (oneVec, [])) (sval GC) (sval GF)
              (sval X0) (sval I0) n).2)
      ≤ npow n 0 * m2 1 (0 - 1) 1 (0 - 1)
            (sval (spiloop ([], oneVec) (oneVec, []) GC GF X0 I0 0).1
              - (exactPI (sval ([], oneVec)) (sval (oneVec, [])) (sval GC) (sval GF)
                  (sval X0) (sval I0) 0).1)
            (sval (spiloop ([], oneVec) (oneVec, []) GC GF X0 I0 0).2
              - (exactPI (sval ([], oneVec)) (sval (oneVec, [])) (sval GC) (sval GF)
                  (sval X0) (sval I0) 0).2)
        + natCast 4 * ulp * geom 0 n := by
  refine spiloop_tracks_exact _ _ GC GF X0 I0 (lam₁ := 0) (lam₂ := 0) (L := 0) ?_ ?_ ?_ ?_
    (le_refl 0) n
  · rw [sval_negOne]; mach_ring
  · rw [sval_posOne]; mach_ring
  · rw [abs_zero]; exact le_refl 0
  · rw [abs_zero]; exact le_refl 0

end Real

end MachLib
