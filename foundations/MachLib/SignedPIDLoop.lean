import MachLib.ThreeStateTracking
import MachLib.SignedPILoop
import MachLib.ThreeStateQuadTracking

/-!
# The signed bit-level PID loop tracks its exact trajectory

`ThreeStateTracking` supplies the measure and the tracking theorem for a three-state loop, and
`pid_eigen_contraction` discharges the contraction for every PID design with three real
eigenvalues. Neither is about a datapath. This file is: `spidloop` is built from `List Bool` pairs
by the signed adder, subtractor and truncating multiply, and `spidloop_tracks_exact` bounds its
distance from the exact real PID trajectory with the per-step error **derived from the bits**.

That is the same step `SignedPILoop` took for the two-state cases, and it is the step that turns a
lemma into a join.

## Two rows are free, and the second one is freer than the first

```
X' = GA ⊗ X ⊕ GB ⊗ I ⊕ GC ⊗ P ⊕ GD      three truncating multiplies
I' = (I ⊖ X) ⊕ GF                        EXACT — no multiply
P' = X                                   EXACT — not even an operation
```

The integrator row is `ssub` then `sadd`, both exact in the signed representation, so it
contributes no truncation. The delay row contributes none either, and for a stronger reason: it is
**a wire**. `P' = X` is the identity on bit vectors, so there is nothing there to round. The whole
per-step error is the state row's three multiplies at `2·ulp` each.

So the two rows that make the loop hard to *analyse* — the two structural rows that force the
eigenvectors — are exactly the two rows that are free to *compute*. That was true of the
integrator alone at 2×2 and it is more true here.

## The price the PI case did not pay

`SignedPILoop`'s per-step error passes through its measure untouched, because both PI functionals
begin with `1` (`m2_state_only` is an *equality*). The PID functionals begin with `λᵢ(λᵢ−1)`, so a
state-row perturbation is **scaled** by whatever dominates those three coefficients. The bound
below therefore carries an explicit `K` with `|λᵢ(λᵢ−1)| ≤ K`, and the per-step term is `K·6·ulp`
rather than `6·ulp`.

This is carried in the statement rather than hidden. It cannot be normalised away: scaling the
eigenvectors to make the first coefficient `1` needs division, which this corpus does not have,
and rescaling the measure instead would move the same factor to the other side of the inequality.

## What is not claimed

Three **real** eigenvalues, as in `ThreeStateTracking`. And the caveat that file records applies
here with force: `m3` is a norm only when the eigenvalues are distinct and none is `0` or `1`, so
**the deadbeat design that served as `SignedPILoop`'s specimen is vacuous for this loop** — every
functional vanishes and the bound reads `0 ≤ 0`. The specimen at the end is therefore built at a
design where the measure is a genuine norm, which is a strictly harder thing to exhibit and the
reason it is worth exhibiting.
-/

namespace MachLib

namespace SRTL

/-- **The signed PID closed loop, over bits.**

The state row is three truncating multiplies and three adders; the integrator row is `ssub` then
`sadd`, both exact; the delay row is `st.1` — a wire, with no operation to round. -/
def spidloop (GA GB GC GD GF X0 I0 P0 : SVec) : Nat → SVec × SVec × SVec
  | 0 => (X0, I0, P0)
  | k + 1 =>
      let st := spidloop GA GB GC GD GF X0 I0 P0 k
      (sadd (sadd (sadd (sfxmul GA st.1) (sfxmul GB st.2.1)) (sfxmul GC st.2.2)) GD,
       sadd (ssub st.2.1 st.1) GF,
       st.1)

end SRTL

namespace Real

open SRTL

/-- The exact real PID recurrence the datapath implements, written in the coefficient form
`three_state_tracks_exact` consumes. -/
noncomputable def exactPID (A B C D F x0 i0 p0 : Real) : Nat → Real × Real × Real
  | 0 => (x0, i0, p0)
  | k + 1 =>
      let st := exactPID A B C D F x0 i0 p0 k
      (A * st.1 + B * st.2.1 + C * st.2.2 + D,
       (-1) * st.1 + 1 * st.2.1 + 0 * st.2.2 + F,
       1 * st.1 + 0 * st.2.1 + 0 * st.2.2 + 0)

/-! ### The datapath's per-step error -/

/-- The integrator row is **exact**. -/
theorem spid_integrator_exact (X I GF : SVec) :
    sval (sadd (ssub I X) GF) = (-1) * sval X + 1 * sval I + sval GF := by
  rw [sval_sadd, sval_ssub]
  mach_mpoly [sval X, sval I, sval GF]

/-- **The state row is within `6·ulp`**: three signed truncating multiplies at `2·ulp` each, the
three adders contributing nothing. -/
theorem spid_state_error (GA GB GC GD X I P : SVec) :
    abs (sval (sadd (sadd (sadd (sfxmul GA X) (sfxmul GB I)) (sfxmul GC P)) GD)
         - (sval GA * sval X + sval GB * sval I + sval GC * sval P + sval GD))
      ≤ natCast 6 * ulp := by
  obtain ⟨hp1, hn1⟩ := sval_sfxmul_error GA X
  obtain ⟨hp2, hn2⟩ := sval_sfxmul_error GB I
  obtain ⟨hp3, hn3⟩ := sval_sfxmul_error GC P
  have hsplit : sval (sadd (sadd (sadd (sfxmul GA X) (sfxmul GB I)) (sfxmul GC P)) GD)
        - (sval GA * sval X + sval GB * sval I + sval GC * sval P + sval GD)
      = (sval (sfxmul GA X) - sval GA * sval X)
        + (sval (sfxmul GB I) - sval GB * sval I)
        + (sval (sfxmul GC P) - sval GC * sval P) := by
    rw [sval_sadd, sval_sadd, sval_sadd]
    mach_mpoly [sval (sfxmul GA X), sval (sfxmul GB I), sval (sfxmul GC P), sval GD,
                sval GA * sval X, sval GB * sval I, sval GC * sval P]
  have hsix : natCast 6 * ulp = natCast 2 * ulp + natCast 2 * ulp + natCast 2 * ulp := by
    have h : natCast 6 = natCast 2 + natCast 2 + natCast 2 := by
      have e : (6 : Nat) = 2 + 2 + 2 := by omega
      rw [e, natCast_add, natCast_add]
    rw [h]; mach_mpoly [natCast 2, ulp]
  rw [hsplit, hsix]
  refine abs_le_of ?_ ?_
  · exact add_le_add_both (add_le_add_both (le_of_lt hn1) (le_of_lt hn2)) (le_of_lt hn3)
  · have e : -((sval (sfxmul GA X) - sval GA * sval X)
              + (sval (sfxmul GB I) - sval GB * sval I)
              + (sval (sfxmul GC P) - sval GC * sval P))
        = (sval GA * sval X - sval (sfxmul GA X))
          + (sval GB * sval I - sval (sfxmul GB I))
          + (sval GC * sval P - sval (sfxmul GC P)) := by
      mach_mpoly [sval (sfxmul GA X), sval GA * sval X,
                  sval (sfxmul GB I), sval GB * sval I,
                  sval (sfxmul GC P), sval GC * sval P]
    rw [e]
    exact add_le_add_both (add_le_add_both (le_of_lt hp1) (le_of_lt hp2)) (le_of_lt hp3)

/-! ### Shape lemmas over fresh variables

`mach_mpoly`'s bracket list cannot parse an atom containing a projection like `(spidloop … k).2.1`,
so each rearrangement the capstone needs is factored here over fresh variables and applied by term
application. That is the established workaround in this corpus.

These are also written with `zero_mul`/`add_zero` rewrites rather than `mach_mpoly`, because
`CLAUDE.md` records that a literal `0 * t` makes the normaliser **grind rather than fail** — the
tell is a build that hangs, and every row below contains one. -/

/-- `x = a + (x − a)`: the residual form. -/
private theorem residual_eq3 (x a : Real) : x = a + (x - a) := by mach_mpoly [x, a]

/-- The integrator row's residual is literally zero, and its `0 * z` term must not reach the
normaliser. -/
private theorem integ_shape (p q F z : Real) : p + q + F = p + q + 0 * z + F + 0 := by
  rw [zero_mul, add_zero, add_zero]

/-- The delay row is a wire: its value is the previous state, with a zero residual. -/
private theorem delay_shape (x i z : Real) : x = 1 * x + 0 * i + 0 * z + 0 + 0 := by
  rw [zero_mul, zero_mul, one_mul_thm, add_zero, add_zero, add_zero, add_zero]

/-! ### The join -/

/-- **The signed bit-level PID loop tracks the exact real PID loop.**

Everything design-specific is in `heigA`, `heigB`, `heigC`, which say `λ₁, λ₂, λ₃` are the
eigenvalues of the caller's own **quantised** gains written through the characteristic equation,
and in `hK`, which bounds the three functionals' leading coefficients. The contraction itself is
free (`pid_eigen_contraction`), the integrator and delay rows are exact, and the per-step
`K·6·ulp` is derived from the state row's three truncating multiplies.

Nothing here claims the quantised gains are close to the designer's intended ones. That is a
separate question and this theorem does not answer it. -/
theorem spidloop_tracks_exact
    (GA GB GC GD GF X0 I0 P0 : SVec) {l₁ l₂ l₃ L K : Real}
    (heigA : sval GA = (l₁ + l₂ + l₃) - 1)
    (heigB : sval GB = (l₁*l₂ + l₁*l₃ + l₂*l₃) - (l₁ + l₂ + l₃) + 1 - l₁*l₂*l₃)
    (heigC : sval GC = -(l₁*l₂*l₃))
    (h₁ : abs l₁ ≤ L) (h₂ : abs l₂ ≤ L) (h₃ : abs l₃ ≤ L) (hL : 0 ≤ L)
    (hK₁ : abs (l₁ * (l₁ - 1)) ≤ K) (hK₂ : abs (l₂ * (l₂ - 1)) ≤ K)
    (hK₃ : abs (l₃ * (l₃ - 1)) ≤ K)
    (n : Nat) :
    m3 (l₁ * (l₁ - 1)) (l₁ * ((l₁*l₂ + l₁*l₃ + l₂*l₃) - (l₁ + l₂ + l₃) + 1 - l₁*l₂*l₃))
         ((l₁ - 1) * (-(l₁*l₂*l₃)))
       (l₂ * (l₂ - 1)) (l₂ * ((l₁*l₂ + l₁*l₃ + l₂*l₃) - (l₁ + l₂ + l₃) + 1 - l₁*l₂*l₃))
         ((l₂ - 1) * (-(l₁*l₂*l₃)))
       (l₃ * (l₃ - 1)) (l₃ * ((l₁*l₂ + l₁*l₃ + l₂*l₃) - (l₁ + l₂ + l₃) + 1 - l₁*l₂*l₃))
         ((l₃ - 1) * (-(l₁*l₂*l₃)))
        (sval (spidloop GA GB GC GD GF X0 I0 P0 n).1
          - (exactPID (sval GA) (sval GB) (sval GC) (sval GD) (sval GF)
              (sval X0) (sval I0) (sval P0) n).1)
        (sval (spidloop GA GB GC GD GF X0 I0 P0 n).2.1
          - (exactPID (sval GA) (sval GB) (sval GC) (sval GD) (sval GF)
              (sval X0) (sval I0) (sval P0) n).2.1)
        (sval (spidloop GA GB GC GD GF X0 I0 P0 n).2.2
          - (exactPID (sval GA) (sval GB) (sval GC) (sval GD) (sval GF)
              (sval X0) (sval I0) (sval P0) n).2.2)
      ≤ npow n L
          * m3 (l₁ * (l₁ - 1)) (l₁ * ((l₁*l₂ + l₁*l₃ + l₂*l₃) - (l₁ + l₂ + l₃) + 1 - l₁*l₂*l₃))
                 ((l₁ - 1) * (-(l₁*l₂*l₃)))
               (l₂ * (l₂ - 1)) (l₂ * ((l₁*l₂ + l₁*l₃ + l₂*l₃) - (l₁ + l₂ + l₃) + 1 - l₁*l₂*l₃))
                 ((l₂ - 1) * (-(l₁*l₂*l₃)))
               (l₃ * (l₃ - 1)) (l₃ * ((l₁*l₂ + l₁*l₃ + l₂*l₃) - (l₁ + l₂ + l₃) + 1 - l₁*l₂*l₃))
                 ((l₃ - 1) * (-(l₁*l₂*l₃)))
              (sval (spidloop GA GB GC GD GF X0 I0 P0 0).1
                - (exactPID (sval GA) (sval GB) (sval GC) (sval GD) (sval GF)
                    (sval X0) (sval I0) (sval P0) 0).1)
              (sval (spidloop GA GB GC GD GF X0 I0 P0 0).2.1
                - (exactPID (sval GA) (sval GB) (sval GC) (sval GD) (sval GF)
                    (sval X0) (sval I0) (sval P0) 0).2.1)
              (sval (spidloop GA GB GC GD GF X0 I0 P0 0).2.2
                - (exactPID (sval GA) (sval GB) (sval GC) (sval GD) (sval GF)
                    (sval X0) (sval I0) (sval P0) 0).2.2)
        + K * (natCast 6 * ulp) * geom L n := by
  have hKnn : (0 : Real) ≤ K := le_trans (abs_nonneg _) hK₁
  have hεnn : (0 : Real) ≤ K * (natCast 6 * ulp) :=
    mul_nonneg hKnn (mul_nonneg (natCast_nonneg 6) (le_of_lt ulp_pos))
  -- the state row's residual, named so its recurrence holds by construction
  let dx : Nat → Real := fun k =>
    sval (spidloop GA GB GC GD GF X0 I0 P0 (k + 1)).1
      - (sval GA * sval (spidloop GA GB GC GD GF X0 I0 P0 k).1
         + sval GB * sval (spidloop GA GB GC GD GF X0 I0 P0 k).2.1
         + sval GC * sval (spidloop GA GB GC GD GF X0 I0 P0 k).2.2 + sval GD)
  refine three_state_tracks_exact
    (A₁₁ := sval GA) (A₁₂ := sval GB) (A₁₃ := sval GC) (C₁ := sval GD)
    (A₂₁ := -1) (A₂₂ := 1) (A₂₃ := 0) (C₂ := sval GF)
    (A₃₁ := 1) (A₃₂ := 0) (A₃₃ := 0) (C₃ := 0)
    (L := L) (ε := K * (natCast 6 * ulp))
    (a₁ := l₁ * (l₁ - 1))
    (b₁ := l₁ * ((l₁*l₂ + l₁*l₃ + l₂*l₃) - (l₁ + l₂ + l₃) + 1 - l₁*l₂*l₃))
    (c₁ := (l₁ - 1) * (-(l₁*l₂*l₃)))
    (a₂ := l₂ * (l₂ - 1))
    (b₂ := l₂ * ((l₁*l₂ + l₁*l₃ + l₂*l₃) - (l₁ + l₂ + l₃) + 1 - l₁*l₂*l₃))
    (c₂ := (l₂ - 1) * (-(l₁*l₂*l₃)))
    (a₃ := l₃ * (l₃ - 1))
    (b₃ := l₃ * ((l₁*l₂ + l₁*l₃ + l₂*l₃) - (l₁ + l₂ + l₃) + 1 - l₁*l₂*l₃))
    (c₃ := (l₃ - 1) * (-(l₁*l₂*l₃)))
    (x := fun k => sval (spidloop GA GB GC GD GF X0 I0 P0 k).1)
    (i := fun k => sval (spidloop GA GB GC GD GF X0 I0 P0 k).2.1)
    (z := fun k => sval (spidloop GA GB GC GD GF X0 I0 P0 k).2.2)
    (xe := fun k => (exactPID (sval GA) (sval GB) (sval GC) (sval GD) (sval GF)
                      (sval X0) (sval I0) (sval P0) k).1)
    (ie := fun k => (exactPID (sval GA) (sval GB) (sval GC) (sval GD) (sval GF)
                      (sval X0) (sval I0) (sval P0) k).2.1)
    (ze := fun k => (exactPID (sval GA) (sval GB) (sval GC) (sval GD) (sval GF)
                      (sval X0) (sval I0) (sval P0) k).2.2)
    (dx := dx) (di := fun _ => 0) (dz := fun _ => 0)
    hL hεnn
    (fun k => rfl) (fun k => rfl) (fun k => rfl)
    (fun k => residual_eq3 _ _) ?_ ?_ ?_ ?_ n
  · -- the integrator row is exact, so its residual is literally zero
    intro k
    show sval (sadd (ssub (spidloop GA GB GC GD GF X0 I0 P0 k).2.1
                          (spidloop GA GB GC GD GF X0 I0 P0 k).1) GF)
        = (-1) * sval (spidloop GA GB GC GD GF X0 I0 P0 k).1
          + 1 * sval (spidloop GA GB GC GD GF X0 I0 P0 k).2.1
          + 0 * sval (spidloop GA GB GC GD GF X0 I0 P0 k).2.2 + sval GF + 0
    rw [spid_integrator_exact]
    exact integ_shape _ _ _ _
  · -- the delay row is a wire: exact, and not even an operation
    intro k
    exact delay_shape _ _ _
  · -- the contraction, free for any PID design with three real eigenvalues
    intro u v w
    rw [heigA, heigB, heigC]
    exact pid_eigen_contraction h₁ h₂ h₃ u v w
  · -- the per-step error: the state row's three multiplies, scaled by the measure's leading row
    intro k
    refine le_trans (m3_state_only_le hK₁ hK₂ hK₃ (dx k)) ?_
    exact mul_le_mul_of_nonneg_left
      (spid_state_error GA GB GC GD
        (spidloop GA GB GC GD GF X0 I0 P0 k).1
        (spidloop GA GB GC GD GF X0 I0 P0 k).2.1
        (spidloop GA GB GC GD GF X0 I0 P0 k).2.2) hKnn

/-! ### A specimen — and it may NOT be the deadbeat design

`spidloop_tracks_exact` is conditional on `heigA`, `heigB`, `heigC`, `hK₁`–`hK₃` and the three
modulus bounds. A gain triple admitting no such eigenvalues, or an eigenvalue triple degenerating
the measure, would make the theorem empty on that design. This corpus has a recorded flagship that
was vacuously true for weeks while every gate passed, so the rule is that a conditional theorem
ships with a specimen discharging **every** hypothesis.

**The two-state playbook does not transfer, and that is the point.** `SignedPILoop` discharges its
specimen at the deadbeat design `λ = 0`, which is the sharpest possible instance there. Here it is
the *worst* possible one: `ThreeStateTracking` records that `m3` is a norm only when the
eigenvalues are distinct and none is `0` or `1`, and at `λ₁ = λ₂ = λ₃ = 0` every functional
vanishes, so the conclusion reads `0 ≤ 0`. Ticking the vacuity box with a deadbeat specimen would
have produced a bound that cannot fail and therefore cannot inform.

So the design below is `λ = 1/2, −1/2, 1/4`: **distinct, none of them `0` or `1`, and all of
modulus `≤ 1/2`, so the bound genuinely contracts.** Every constant is a real Q16.16 bit vector,
and every fraction is expressed through `ulp` rather than by division — `q + q + q + q = 1` is what
makes `qval quarterVec` a quarter, and each gain identity is then a ring identity in `q` together
with `4q² = q`.
-/

/-- `2^14`, so `qval` is a quarter: fourteen zeros then a one, `toNat` being little-endian. -/
def quarterVec : List Bool := List.replicate 14 false ++ [true]

/-- `2^14 + 2^15 = 49152`, three quarters — the magnitude of gain `A`. -/
def gainAVec : List Bool := List.replicate 14 false ++ [true, true]

/-- `2^12 + 2^15 = 36864`, nine sixteenths — gain `B`. -/
def gainBVec : List Bool := List.replicate 12 false ++ [true, false, false, true]

/-- `2^12 = 4096`, one sixteenth — gain `C`. -/
def gainCVec : List Bool := List.replicate 12 false ++ [true]

private theorem toNat_quarterVec : RTL.toNat quarterVec = 2 ^ 14 := by decide
private theorem toNat_gainAVec : RTL.toNat gainAVec = 2 ^ 14 + 2 ^ 15 := by decide
private theorem toNat_gainBVec : RTL.toNat gainBVec = 2 ^ 12 + 2 ^ 15 := by decide
private theorem toNat_gainCVec : RTL.toNat gainCVec = 2 ^ 12 := by decide

/-- Two `natCast`-scaled `ulp`s add by adding their scales. -/
private theorem cast_sum (a b : Nat) :
    natCast a * ulp + natCast b * ulp = natCast (a + b) * ulp := by
  rw [natCast_add]; mach_mpoly [natCast a, natCast b, ulp]

/-- A scale that is a whole multiple of `2^FRAC` cancels `ulp` entirely. -/
private theorem scale_down {a b : Nat} (h : a = b * 2 ^ RTL.FRAC) :
    natCast a * ulp = natCast b := by
  rw [h, natCast_mul, mul_assoc, ulp_scale]
  mach_mpoly [natCast b]

private theorem eq_sub_of_add_eq' {a b c : Real} (h : a + b = c) : a = c - b := by
  rw [← h]; mach_mpoly [a, b]

theorem qval_quarterVec : qval quarterVec = natCast (2 ^ 14) * ulp := by
  unfold qval; rw [toNat_quarterVec]

/-- **`qval quarterVec` is a quarter**, said without division: four of them are one. -/
theorem quarter_four :
    qval quarterVec + qval quarterVec + qval quarterVec + qval quarterVec = 1 := by
  rw [qval_quarterVec, cast_sum, cast_sum, cast_sum]
  have e : (2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 : Nat) = 2 ^ RTL.FRAC := by decide
  rw [e, ulp_scale]

theorem quarter_sq : qval quarterVec * qval quarterVec = natCast (2 ^ 12) * ulp := by
  rw [qval_quarterVec]
  have e : natCast (2 ^ 14) * ulp * (natCast (2 ^ 14) * ulp)
      = natCast (2 ^ 14) * natCast (2 ^ 14) * ulp * ulp := by
    mach_mpoly [natCast (2 ^ 14), ulp]
  rw [e, ← natCast_mul]
  have e2 : (2 ^ 14 * 2 ^ 14 : Nat) = 2 ^ 12 * 2 ^ RTL.FRAC := by decide
  rw [scale_down e2]

theorem quarter_cube :
    qval quarterVec * qval quarterVec * qval quarterVec = natCast (2 ^ 10) * ulp := by
  rw [quarter_sq, qval_quarterVec]
  have e : natCast (2 ^ 12) * ulp * (natCast (2 ^ 14) * ulp)
      = natCast (2 ^ 12) * natCast (2 ^ 14) * ulp * ulp := by
    mach_mpoly [natCast (2 ^ 12), natCast (2 ^ 14), ulp]
  rw [e, ← natCast_mul]
  have e2 : (2 ^ 12 * 2 ^ 14 : Nat) = 2 ^ 10 * 2 ^ RTL.FRAC := by decide
  rw [scale_down e2]

/-- **`4q² = q`**, the second relation the gain identities need. Everything else about this design
is a ring identity in `q` once this and `quarter_four` are in hand. -/
theorem quarter_sq_four :
    qval quarterVec * qval quarterVec + qval quarterVec * qval quarterVec
      + qval quarterVec * qval quarterVec + qval quarterVec * qval quarterVec
    = qval quarterVec := by
  rw [quarter_sq, cast_sum, cast_sum, cast_sum, qval_quarterVec]

theorem qval_gainAVec : qval gainAVec
    = qval quarterVec + qval quarterVec + qval quarterVec := by
  rw [qval_quarterVec, cast_sum, cast_sum]
  unfold qval; rw [toNat_gainAVec]

theorem qval_gainBVec : qval gainBVec
    = qval quarterVec * qval quarterVec * qval quarterVec
      + qval quarterVec * qval quarterVec * qval quarterVec
      + qval quarterVec * qval quarterVec * qval quarterVec
      + qval quarterVec * qval quarterVec * qval quarterVec
      + qval quarterVec + qval quarterVec := by
  rw [quarter_cube, qval_quarterVec, cast_sum, cast_sum, cast_sum, cast_sum, cast_sum]
  unfold qval; rw [toNat_gainBVec]

theorem qval_gainCVec : qval gainCVec
    = qval quarterVec * qval quarterVec * qval quarterVec
      + qval quarterVec * qval quarterVec * qval quarterVec
      + qval quarterVec * qval quarterVec * qval quarterVec
      + qval quarterVec * qval quarterVec * qval quarterVec := by
  rw [quarter_cube, cast_sum, cast_sum, cast_sum]
  unfold qval; rw [toNat_gainCVec]


/-! ### The design, named -/

/-- Gain `A = −3/4`, as a signed datapath constant: a pure negative limb. -/
def gainA : SVec := (([] : List Bool), gainAVec)
/-- Gain `B = 9/16`. -/
def gainB : SVec := (gainBVec, ([] : List Bool))
/-- Gain `C = 1/16`. -/
def gainC : SVec := (gainCVec, ([] : List Bool))

/-- `λ₁ = 1/2`. -/
noncomputable def lamA : Real := qval quarterVec + qval quarterVec
/-- `λ₂ = −1/2`. -/
noncomputable def lamB : Real := -(qval quarterVec + qval quarterVec)
/-- `λ₃ = 1/4`. -/
noncomputable def lamC : Real := qval quarterVec

theorem sval_gainA : sval gainA
    = -(qval quarterVec + qval quarterVec + qval quarterVec) := by
  show qval ([] : List Bool) - qval gainAVec = _
  rw [qval_nil, qval_gainAVec]
  mach_mpoly [qval quarterVec]

theorem sval_gainC : sval gainC
    = qval quarterVec * qval quarterVec * qval quarterVec
      + qval quarterVec * qval quarterVec * qval quarterVec
      + qval quarterVec * qval quarterVec * qval quarterVec
      + qval quarterVec * qval quarterVec * qval quarterVec := by
  show qval gainCVec - qval ([] : List Bool) = _
  rw [qval_nil, qval_gainCVec]
  mach_mpoly [qval quarterVec * qval quarterVec * qval quarterVec]

/-- **Gain `B`, written so the eigen identity is pure ring.** `qval gainBVec` is `4q³ + 2q`, but
the characteristic-equation form of `B` is `4q³ + 3q − 4q²`. The two agree only because `4q² = q`,
so the subtractive form is the one to expose: with it, `heigB` needs nothing but `4q = 1` and is a
ring identity like the other two. The equation is established additively — `cast_sum` adds and does
not subtract — and rearranged afterwards. -/
theorem qval_gainBVec_add :
    qval gainBVec
      + (qval quarterVec * qval quarterVec + qval quarterVec * qval quarterVec
         + qval quarterVec * qval quarterVec + qval quarterVec * qval quarterVec)
    = qval quarterVec * qval quarterVec * qval quarterVec
      + qval quarterVec * qval quarterVec * qval quarterVec
      + qval quarterVec * qval quarterVec * qval quarterVec
      + qval quarterVec * qval quarterVec * qval quarterVec
      + (qval quarterVec + qval quarterVec + qval quarterVec) := by
  rw [qval_gainBVec, quarter_cube, quarter_sq, qval_quarterVec]
  simp only [cast_sum]

theorem sval_gainB_eq : sval gainB = qval gainBVec := by
  show qval gainBVec - qval ([] : List Bool) = qval gainBVec
  rw [qval_nil]
  mach_mpoly [qval gainBVec]

theorem sval_gainB : sval gainB
    = qval quarterVec * qval quarterVec * qval quarterVec
      + qval quarterVec * qval quarterVec * qval quarterVec
      + qval quarterVec * qval quarterVec * qval quarterVec
      + qval quarterVec * qval quarterVec * qval quarterVec
      + (qval quarterVec + qval quarterVec + qval quarterVec)
      - (qval quarterVec * qval quarterVec + qval quarterVec * qval quarterVec
         + qval quarterVec * qval quarterVec + qval quarterVec * qval quarterVec) := by
  rw [sval_gainB_eq]
  exact eq_sub_of_add_eq' qval_gainBVec_add


/-- **The capstone, at a design where the measure is a genuine norm.**

`λ = 1/2, −1/2, 1/4` — distinct, none of them `0` or `1`, every modulus at most `1/2`, so the
factor `npow n lamA` genuinely decays. Every gain is a real Q16.16 bit vector, every hypothesis of
`spidloop_tracks_exact` is discharged, and the whole design is generated by the single relation
`q + q + q + q = 1` together with `4q² = q`.

`K` is taken as `1` rather than the sharp `3/4`; it is an upper bound either way, and the looser
constant keeps the discharge readable. -/
theorem spidloop_tracks_exact_quarter (GD GF X0 I0 P0 : SVec) (n : Nat) :
    m3 (lamA * (lamA - 1)) (lamA * ((lamA*lamB + lamA*lamC + lamB*lamC) - (lamA + lamB + lamC) + 1 - lamA*lamB*lamC))
         ((lamA - 1) * (-(lamA*lamB*lamC)))
       (lamB * (lamB - 1)) (lamB * ((lamA*lamB + lamA*lamC + lamB*lamC) - (lamA + lamB + lamC) + 1 - lamA*lamB*lamC))
         ((lamB - 1) * (-(lamA*lamB*lamC)))
       (lamC * (lamC - 1)) (lamC * ((lamA*lamB + lamA*lamC + lamB*lamC) - (lamA + lamB + lamC) + 1 - lamA*lamB*lamC))
         ((lamC - 1) * (-(lamA*lamB*lamC)))
        (sval (spidloop gainA gainB gainC GD GF X0 I0 P0 n).1
          - (exactPID (sval gainA) (sval gainB) (sval gainC) (sval GD) (sval GF)
              (sval X0) (sval I0) (sval P0) n).1)
        (sval (spidloop gainA gainB gainC GD GF X0 I0 P0 n).2.1
          - (exactPID (sval gainA) (sval gainB) (sval gainC) (sval GD) (sval GF)
              (sval X0) (sval I0) (sval P0) n).2.1)
        (sval (spidloop gainA gainB gainC GD GF X0 I0 P0 n).2.2
          - (exactPID (sval gainA) (sval gainB) (sval gainC) (sval GD) (sval GF)
              (sval X0) (sval I0) (sval P0) n).2.2)
      ≤ npow n lamA
          * m3 (lamA * (lamA - 1)) (lamA * ((lamA*lamB + lamA*lamC + lamB*lamC) - (lamA + lamB + lamC) + 1 - lamA*lamB*lamC))
                 ((lamA - 1) * (-(lamA*lamB*lamC)))
               (lamB * (lamB - 1)) (lamB * ((lamA*lamB + lamA*lamC + lamB*lamC) - (lamA + lamB + lamC) + 1 - lamA*lamB*lamC))
                 ((lamB - 1) * (-(lamA*lamB*lamC)))
               (lamC * (lamC - 1)) (lamC * ((lamA*lamB + lamA*lamC + lamB*lamC) - (lamA + lamB + lamC) + 1 - lamA*lamB*lamC))
                 ((lamC - 1) * (-(lamA*lamB*lamC)))
              (sval (spidloop gainA gainB gainC GD GF X0 I0 P0 0).1
                - (exactPID (sval gainA) (sval gainB) (sval gainC) (sval GD) (sval GF)
                    (sval X0) (sval I0) (sval P0) 0).1)
              (sval (spidloop gainA gainB gainC GD GF X0 I0 P0 0).2.1
                - (exactPID (sval gainA) (sval gainB) (sval gainC) (sval GD) (sval GF)
                    (sval X0) (sval I0) (sval P0) 0).2.1)
              (sval (spidloop gainA gainB gainC GD GF X0 I0 P0 0).2.2
                - (exactPID (sval gainA) (sval gainB) (sval gainC) (sval GD) (sval GF)
                    (sval X0) (sval I0) (sval P0) 0).2.2)
        + 1 * (natCast 6 * ulp) * geom lamA n := by
  have hq0 : (0 : Real) ≤ qval quarterVec := qval_nonneg _
  have hqq : (0 : Real) ≤ qval quarterVec * qval quarterVec := mul_nonneg hq0 hq0
  have hq1 : qval quarterVec ≤ 1 := by
    rw [← quarter_four]
    exact le_trans (le_add_of_nonneg_right hq0)
      (le_trans (le_add_of_nonneg_right hq0) (le_add_of_nonneg_right hq0))
  refine spidloop_tracks_exact gainA gainB gainC GD GF X0 I0 P0
    (l₁ := lamA) (l₂ := lamB) (l₃ := lamC) (L := lamA) (K := 1)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ n
  · -- gain A against the characteristic equation
    unfold lamA lamB lamC
    rw [sval_gainA, ← quarter_four]
    mach_mpoly [qval quarterVec]
  · -- gain B: a ring identity precisely because `sval_gainB` exposes the `− 4q²`
    unfold lamA lamB lamC
    rw [sval_gainB, ← quarter_four]
    mach_mpoly [qval quarterVec]
  · -- gain C
    unfold lamA lamB lamC
    rw [sval_gainC]
    mach_mpoly [qval quarterVec]
  · unfold lamA
    rw [abs_of_nonneg (add_nonneg hq0 hq0)]
    exact le_refl _
  · unfold lamA lamB
    rw [abs_neg, abs_of_nonneg (add_nonneg hq0 hq0)]
    exact le_refl _
  · unfold lamA lamC
    rw [abs_of_nonneg hq0]
    exact le_add_of_nonneg_right hq0
  · exact add_nonneg hq0 hq0
  · -- |λ₁(λ₁−1)| = 4q² = q ≤ 1
    have e : lamA * (lamA - 1)
        = -(qval quarterVec * qval quarterVec + qval quarterVec * qval quarterVec
            + qval quarterVec * qval quarterVec + qval quarterVec * qval quarterVec) := by
      unfold lamA; rw [← quarter_four]; mach_mpoly [qval quarterVec]
    rw [e, quarter_sq_four, abs_neg, abs_of_nonneg hq0]
    exact hq1
  · -- |λ₂(λ₂−1)| = 12q² = 3q ≤ 1
    have e : lamB * (lamB - 1)
        = (qval quarterVec * qval quarterVec + qval quarterVec * qval quarterVec
           + qval quarterVec * qval quarterVec + qval quarterVec * qval quarterVec)
          + (qval quarterVec * qval quarterVec + qval quarterVec * qval quarterVec
             + qval quarterVec * qval quarterVec + qval quarterVec * qval quarterVec)
          + (qval quarterVec * qval quarterVec + qval quarterVec * qval quarterVec
             + qval quarterVec * qval quarterVec + qval quarterVec * qval quarterVec) := by
      unfold lamB; rw [← quarter_four]; mach_mpoly [qval quarterVec]
    rw [e, quarter_sq_four, abs_of_nonneg (add_nonneg (add_nonneg hq0 hq0) hq0)]
    rw [← quarter_four]
    exact le_add_of_nonneg_right hq0
  · -- |λ₃(λ₃−1)| = 3q² = q − q² ≤ q ≤ 1
    have e : lamC * (lamC - 1)
        = -(qval quarterVec * qval quarterVec + qval quarterVec * qval quarterVec
            + qval quarterVec * qval quarterVec) := by
      unfold lamC; rw [← quarter_four]; mach_mpoly [qval quarterVec]
    have h3 : qval quarterVec * qval quarterVec + qval quarterVec * qval quarterVec
              + qval quarterVec * qval quarterVec
            = qval quarterVec - qval quarterVec * qval quarterVec :=
      eq_sub_of_add_eq' quarter_sq_four
    rw [e, abs_neg, abs_of_nonneg (add_nonneg (add_nonneg hqq hqq) hqq), h3]
    exact le_trans (sub_le_self hqq) hq1

/-! ### The same datapath, for an under-damped PID design

`spidloop_tracks_exact` above needs all three closed-loop eigenvalues **real**, because `m3` is
built from three real left eigenvectors. An under-damped PID design has one real eigenvalue and a
complex pair, and two of those functionals do not exist for it. `ThreeStateQuadTracking` supplies
the squared measure for that case; what follows is the *same datapath* analysed with it, so the two
together cover every PID design whatever its damping.

Nothing about the loop changes. `spidloop` is the same definition, the integrator row is still
exact, the delay row is still a wire, and the state row still loses exactly three truncating
multiplies. Only the measure and the contraction factor differ. -/

/-- With a perturbation confined to the state row, `n3` reduces to the sum of the three leading
coefficients' squares times `u²` — an equality, and the analogue of the factor `K` that the
real-eigenvalue join carries. The integrator and delay rows being exact is again what makes this
the whole per-step term rather than one part of it. -/
theorem n3_state_only (a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ u : Real) :
    n3 a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ u 0 0
      = (a₁ * a₁ + (a₂ * a₂ + a₃ * a₃)) * (u * u) := by
  have e : ∀ a b c : Real, a * u + b * 0 + c * 0 = a * u := by
    intro a b c
    rw [mul_zero, mul_zero, add_zero, add_zero]
  show (a₁ * u + b₁ * 0 + c₁ * 0) * (a₁ * u + b₁ * 0 + c₁ * 0)
      + ((a₂ * u + b₂ * 0 + c₂ * 0) * (a₂ * u + b₂ * 0 + c₂ * 0)
         + (a₃ * u + b₃ * 0 + c₃ * 0) * (a₃ * u + b₃ * 0 + c₃ * 0)) = _
  rw [e, e, e]
  mach_mpoly [a₁, a₂, a₃, u]

/-- The state row's squared error, from its absolute one. -/
theorem spid_state_error_sq (GA GB GC GD X I P : SVec) :
    (sval (sadd (sadd (sadd (sfxmul GA X) (sfxmul GB I)) (sfxmul GC P)) GD)
      - (sval GA * sval X + sval GB * sval I + sval GC * sval P + sval GD))
    * (sval (sadd (sadd (sadd (sfxmul GA X) (sfxmul GB I)) (sfxmul GC P)) GD)
      - (sval GA * sval X + sval GB * sval I + sval GC * sval P + sval GD))
      ≤ (natCast 6 * ulp) * (natCast 6 * ulp) := by
  refine mul_self_le_mul_self_of_abs_le ?_
  have hnn : (0 : Real) ≤ natCast 6 * ulp :=
    mul_nonneg (natCast_nonneg 6) (le_of_lt ulp_pos)
  rw [abs_of_nonneg hnn]
  exact spid_state_error GA GB GC GD X I P

/-- **The join for an under-damped PID design.** The same signed bit-level loop, tracked in the
squared measure of `ThreeStateQuadTracking`, so the result covers designs with one real closed-loop
eigenvalue and a complex pair.

The contraction factor is `(1+α)·L` for any `L` dominating `r²` and `σ²+ω²`, carrying the cost of
splitting the cross term by a sum of squares instead of Cauchy–Schwarz;
`pid_complex_contraction_specimen` exhibits a genuinely complex design where that cost is not
fatal. As in every other case in this arc the nine relations are ring identities, so nothing
design-specific is needed beyond naming the eigenvalues of the caller's own quantised gains. -/
theorem spidloop_tracks_exact_complex
    (GA GB GC GD GF X0 I0 P0 : SVec) {rr sig om L α β : Real}
    (heigA : sval GA = rr + sig + sig - 1)
    (heigB : sval GB = rr * sig + rr * sig + (sig * sig + om * om) - rr - sig - sig + 1
                        - rr * (sig * sig + om * om))
    (heigC : sval GC = -(rr * (sig * sig + om * om)))
    (hr : rr * rr ≤ L) (hc : sig * sig + om * om ≤ L) (hL : 0 ≤ L)
    (hαβ : α * β = 1) (hα : 0 ≤ α) (hβ : 0 ≤ β) (n : Nat) :
    n3 (rr * (rr - 1)) (rr * sval GB) ((rr - 1) * sval GC)
       (sig * sig - om * om - sig) (sig * sval GB) ((sig - 1) * sval GC)
       (sig * om + sig * om - om) (om * sval GB) (om * sval GC)
        (sval (spidloop GA GB GC GD GF X0 I0 P0 n).1
          - (exactPID (sval GA) (sval GB) (sval GC) (sval GD) (sval GF)
              (sval X0) (sval I0) (sval P0) n).1)
        (sval (spidloop GA GB GC GD GF X0 I0 P0 n).2.1
          - (exactPID (sval GA) (sval GB) (sval GC) (sval GD) (sval GF)
              (sval X0) (sval I0) (sval P0) n).2.1)
        (sval (spidloop GA GB GC GD GF X0 I0 P0 n).2.2
          - (exactPID (sval GA) (sval GB) (sval GC) (sval GD) (sval GF)
              (sval X0) (sval I0) (sval P0) n).2.2)
      ≤ npow n ((1 + α) * L)
          * n3 (rr * (rr - 1)) (rr * sval GB) ((rr - 1) * sval GC)
               (sig * sig - om * om - sig) (sig * sval GB) ((sig - 1) * sval GC)
               (sig * om + sig * om - om) (om * sval GB) (om * sval GC)
              (sval (spidloop GA GB GC GD GF X0 I0 P0 0).1
                - (exactPID (sval GA) (sval GB) (sval GC) (sval GD) (sval GF)
                    (sval X0) (sval I0) (sval P0) 0).1)
              (sval (spidloop GA GB GC GD GF X0 I0 P0 0).2.1
                - (exactPID (sval GA) (sval GB) (sval GC) (sval GD) (sval GF)
                    (sval X0) (sval I0) (sval P0) 0).2.1)
              (sval (spidloop GA GB GC GD GF X0 I0 P0 0).2.2
                - (exactPID (sval GA) (sval GB) (sval GC) (sval GD) (sval GF)
                    (sval X0) (sval I0) (sval P0) 0).2.2)
        + (1 + β)
            * (((rr * (rr - 1)) * (rr * (rr - 1))
                + ((sig * sig - om * om - sig) * (sig * sig - om * om - sig)
                   + (sig * om + sig * om - om) * (sig * om + sig * om - om)))
               * ((natCast 6 * ulp) * (natCast 6 * ulp)))
          * geom ((1 + α) * L) n := by
  obtain ⟨f₁, f₂, f₃⟩ := pid_complex_real_direction rr sig om
  obtain ⟨p₁, p₂, p₃⟩ := pid_complex_jordan_first rr sig om
  obtain ⟨q₁, q₂, q₃⟩ := pid_complex_jordan_second rr sig om
  -- `A` occurs only in the first relation of each triple; `B` and `C` occur in all nine, since
  -- the functionals themselves are built from them. Rewriting the gains BACKWARDS turns the
  -- inlined characteristic-equation forms into the caller's actual bit vectors.
  rw [← heigA] at f₁ p₁ q₁
  rw [← heigB, ← heigC] at f₁ f₂ f₃ p₁ p₂ p₃ q₁ q₂ q₃
  have hβ1 : (0 : Real) ≤ 1 + β := le_trans (le_of_lt zero_lt_one_ax) (le_add_of_nonneg_right hβ)
  have hSnn : (0 : Real) ≤ (rr * (rr - 1)) * (rr * (rr - 1))
      + ((sig * sig - om * om - sig) * (sig * sig - om * om - sig)
         + (sig * om + sig * om - om) * (sig * om + sig * om - om)) :=
    add_nonneg (mul_self_nonneg _)
      (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _))
  refine three_state_tracks_exact_quad
    (A₁₁ := sval GA) (A₁₂ := sval GB) (A₁₃ := sval GC) (C₁ := sval GD)
    (A₂₁ := -1) (A₂₂ := 1) (A₂₃ := 0) (C₂ := sval GF)
    (A₃₁ := 1) (A₃₂ := 0) (A₃₃ := 0) (C₃ := 0)
    (rr := rr) (sig := sig) (om := om) (L := L) (α := α) (β := β)
    (ε := (1 + β)
        * (((rr * (rr - 1)) * (rr * (rr - 1))
            + ((sig * sig - om * om - sig) * (sig * sig - om * om - sig)
               + (sig * om + sig * om - om) * (sig * om + sig * om - om)))
           * ((natCast 6 * ulp) * (natCast 6 * ulp))))
    (x := fun k => sval (spidloop GA GB GC GD GF X0 I0 P0 k).1)
    (i := fun k => sval (spidloop GA GB GC GD GF X0 I0 P0 k).2.1)
    (z := fun k => sval (spidloop GA GB GC GD GF X0 I0 P0 k).2.2)
    (xe := fun k => (exactPID (sval GA) (sval GB) (sval GC) (sval GD) (sval GF)
                      (sval X0) (sval I0) (sval P0) k).1)
    (ie := fun k => (exactPID (sval GA) (sval GB) (sval GC) (sval GD) (sval GF)
                      (sval X0) (sval I0) (sval P0) k).2.1)
    (ze := fun k => (exactPID (sval GA) (sval GB) (sval GC) (sval GD) (sval GF)
                      (sval X0) (sval I0) (sval P0) k).2.2)
    (dx := fun k => sval (spidloop GA GB GC GD GF X0 I0 P0 (k + 1)).1
        - (sval GA * sval (spidloop GA GB GC GD GF X0 I0 P0 k).1
           + sval GB * sval (spidloop GA GB GC GD GF X0 I0 P0 k).2.1
           + sval GC * sval (spidloop GA GB GC GD GF X0 I0 P0 k).2.2 + sval GD))
    (di := fun _ => 0) (dz := fun _ => 0)
    hαβ hβ hα (mul_nonneg hβ1 (mul_nonneg hSnn (mul_self_nonneg _))) hL
    (fun k => rfl) (fun k => rfl) (fun k => rfl)
    (fun k => residual_eq3 _ _) ?_ ?_ f₁ f₂ f₃ p₁ p₂ p₃ q₁ q₂ q₃ hr hc ?_ n
  · intro k
    show sval (sadd (ssub (spidloop GA GB GC GD GF X0 I0 P0 k).2.1
                          (spidloop GA GB GC GD GF X0 I0 P0 k).1) GF)
        = (-1) * sval (spidloop GA GB GC GD GF X0 I0 P0 k).1
          + 1 * sval (spidloop GA GB GC GD GF X0 I0 P0 k).2.1
          + 0 * sval (spidloop GA GB GC GD GF X0 I0 P0 k).2.2 + sval GF + 0
    rw [spid_integrator_exact]
    exact integ_shape _ _ _ _
  · intro k
    exact delay_shape _ _ _
  · intro k
    rw [n3_state_only]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left
        (spid_state_error_sq GA GB GC GD
          (spidloop GA GB GC GD GF X0 I0 P0 k).1
          (spidloop GA GB GC GD GF X0 I0 P0 k).2.1
          (spidloop GA GB GC GD GF X0 I0 P0 k).2.2) hSnn) hβ1

end Real

end MachLib
