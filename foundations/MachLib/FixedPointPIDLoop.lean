import MachLib.SignedLoopEnvelope
import MachLib.Forge

/-!
# The fixed-point PID loop on the Q-grid — the last link, stated where the hardware is

`spidloopOf_tracks_exact_floor` bounds a loop whose state row lands within `3·ulp` of the exact
linear combination, and says nothing about how the truncation happens. `PIDStepIteration` shows
that iterating a compiler-emitted step reproduces `exactPID`. What was still missing is a model of
the **truncating datapath itself**: something in this corpus that actually truncates the way the
emitted Verilog does, so the envelope hypothesis can be discharged rather than assumed.

This file supplies it, and the ingredient turned out to be already here.

## `floor` was already an axiom, with exactly the two facts needed

`MachLib/Forge.lean` carries `floor : Real → Real` with `floor_le : floor x ≤ x` and
`lt_floor_add_one : x < floor x + 1`. Those bracket the fractional part in `[0, 1)`, which is the
entire content of "an arithmetic shift right discards the low bits". Scaling to the Q-grid,

```
qtrunc y = floor (y · 2^FRAC) · ulp
```

satisfies `0 ≤ y − qtrunc y ≤ ulp`: **at most one `ulp` below the exact value, never above it.**
That is the hypothesis `row_within_three_ulp` takes, and it is one-sided, which is why the emitted
datapath comes out at `3·ulp` per row rather than `sfxmul`'s `6`.

## What this model abstracts, said plainly

`qtrunc` is truncation on an *unbounded* Q-grid. It does not model **overflow**: a real 32-bit
datapath wraps, and a wrapped value is not within one `ulp` of anything. So this is a faithful
model of the arithmetic and not of the register width, and a bound proved here is conditional on
the design not overflowing.

That is exactly the abstraction Forge's own fixed-point certifier makes — its `_trunc(x, s)` is
`floor(x/s)·s`, documented as "toward −∞, the typical fixed-point datapath" — so the two projects
now model the same object. Saying so is the point: the previous model, `sfxmul`, truncated toward
**zero** and was a faithful model of a datapath nobody builds.

## Axiom cost

Three: `floor`, `floor_le`, `lt_floor_add_one`. All three are already pinned in the ledger and
carry Mathlib witnesses through `Int.floor`, so the trusted base does not grow — but the trajectory
theorems in this file have a strictly larger footprint than those in `SignedPIDLoop`, which rest on
the plain real spine alone. That is a real difference and `#print axioms` will show it.
-/

namespace MachLib

namespace Real

/-! ### Truncation onto the Q-grid -/

/-- **Truncate onto the Q-grid, toward `−∞`** — what `>>> FRAC` does to a full-width product. -/
noncomputable def qtrunc (y : Real) : Real :=
  floor (y * natCast (2 ^ RTL.FRAC)) * ulp

/-- `y` scaled up and back down is `y`. The bridge between the grid and the reals. -/
private theorem scale_roundtrip (y : Real) : y * natCast (2 ^ RTL.FRAC) * ulp = y := by
  have e : y * natCast (2 ^ RTL.FRAC) * ulp = y * (natCast (2 ^ RTL.FRAC) * ulp) := by
    mach_mpoly [y, natCast (2 ^ RTL.FRAC), ulp]
  rw [e, ulp_scale, mul_one_ax]

/-- **The truncation never overshoots.** `qtrunc y ≤ y`. -/
theorem qtrunc_nonneg_residue (y : Real) : 0 ≤ y - qtrunc y := by
  have h := floor_le (y * natCast (2 ^ RTL.FRAC))
  have hstep : floor (y * natCast (2 ^ RTL.FRAC)) * ulp
      ≤ y * natCast (2 ^ RTL.FRAC) * ulp :=
    mul_le_mul_of_nonneg_right h (le_of_lt ulp_pos)
  rw [scale_roundtrip y] at hstep
  exact sub_nonneg_of_le hstep

/-- **And it undershoots by less than one `ulp`.** Together with the previous theorem this is the
whole behaviour of an arithmetic shift, expressed where a compiler can use it. -/
theorem qtrunc_residue_le_ulp (y : Real) : y - qtrunc y ≤ ulp := by
  have h := lt_floor_add_one (y * natCast (2 ^ RTL.FRAC))
  -- `z < ⌊z⌋ + 1` gives `z − ⌊z⌋ ≤ 1`
  have hz : y * natCast (2 ^ RTL.FRAC) - floor (y * natCast (2 ^ RTL.FRAC)) ≤ 1 := by
    have e : y * natCast (2 ^ RTL.FRAC) - floor (y * natCast (2 ^ RTL.FRAC))
        ≤ floor (y * natCast (2 ^ RTL.FRAC)) + 1
          - floor (y * natCast (2 ^ RTL.FRAC)) :=
      sub_le_sub_right (le_of_lt h) _
    have e2 : floor (y * natCast (2 ^ RTL.FRAC)) + 1
        - floor (y * natCast (2 ^ RTL.FRAC)) = 1 := by
      mach_mpoly [floor (y * natCast (2 ^ RTL.FRAC))]
    rw [e2] at e
    exact e
  have hscaled : (y * natCast (2 ^ RTL.FRAC) - floor (y * natCast (2 ^ RTL.FRAC))) * ulp
      ≤ 1 * ulp := mul_le_mul_of_nonneg_right hz (le_of_lt ulp_pos)
  have edist : (y * natCast (2 ^ RTL.FRAC) - floor (y * natCast (2 ^ RTL.FRAC))) * ulp
      = y * natCast (2 ^ RTL.FRAC) * ulp - floor (y * natCast (2 ^ RTL.FRAC)) * ulp := by
    mach_mpoly [y * natCast (2 ^ RTL.FRAC), floor (y * natCast (2 ^ RTL.FRAC)), ulp]
  rw [edist, scale_roundtrip y, one_mul_thm] at hscaled
  exact hscaled

/-! ### The loop -/

/-- **The fixed-point PID loop on the Q-grid.**

Three truncating products on the state row; the integrator is a subtract and an add, exact; the
delay row is a copy. The same three-row shape as `spidloop`, with the truncation that the emitted
hardware actually performs. -/
noncomputable def fxpidloop (A B C D F x0 i0 p0 : Real) : Nat → Real × Real × Real
  | 0 => (x0, i0, p0)
  | k + 1 =>
      let st := fxpidloop A B C D F x0 i0 p0 k
      (qtrunc (A * st.1) + qtrunc (B * st.2.1) + qtrunc (C * st.2.2) + D,
       (st.2.1 - st.1) + F,
       st.1)

/-- The state row of `fxpidloop` is within `3·ulp` of the exact linear combination — the envelope
hypothesis, discharged from the two `floor` facts rather than assumed. -/
theorem fxpidloop_row_envelope (A B C D x i p : Real) :
    abs ((qtrunc (A * x) + qtrunc (B * i) + qtrunc (C * p) + D)
         - (A * x + B * i + C * p + D))
      ≤ ulp + ulp + ulp :=
  row_within_three_ulp
    (qtrunc_nonneg_residue (A * x)) (qtrunc_residue_le_ulp (A * x))
    (qtrunc_nonneg_residue (B * i)) (qtrunc_residue_le_ulp (B * i))
    (qtrunc_nonneg_residue (C * p)) (qtrunc_residue_le_ulp (C * p))

/-! ### Shape lemmas

Re-declared, as in `SignedLoopEnvelope`: the originals are `private`, which is right for a
proof-local rearrangement. `zero_mul`/`add_zero` rewrites rather than the normaliser, because both
rows carry a literal `0 * z`. -/

private theorem residual_fx (x a : Real) : x = a + (x - a) := by mach_mpoly [x, a]

private theorem integ_fx (x i F z : Real) :
    (i - x) + F = (-1) * x + 1 * i + 0 * z + F + 0 := by
  rw [zero_mul, add_zero, add_zero, one_mul_thm]
  mach_mpoly [x, i, F]

private theorem delay_fx (x i z : Real) : x = 1 * x + 0 * i + 0 * z + 0 + 0 := by
  rw [zero_mul, zero_mul, one_mul_thm, add_zero, add_zero, add_zero, add_zero]

/-! ### The join, on the Q-grid -/

/-- **The fixed-point PID loop tracks the exact real PID trajectory.**

Per-step term `K·3·ulp`, from three one-sided truncations. Every hypothesis is either the caller
naming the eigenvalues of its own quantised gains or a bound on their moduli; the truncation side
is discharged inside, from `floor`'s two bracketing axioms.

Conditional on the design not overflowing — `qtrunc` is truncation on an unbounded grid, and the
header says so. -/
theorem fxpidloop_tracks_exact
    {A B C D F : Real} {l₁ l₂ l₃ L K : Real}
    (heigA : A = (l₁ + l₂ + l₃) - 1)
    (heigB : B = (l₁*l₂ + l₁*l₃ + l₂*l₃) - (l₁ + l₂ + l₃) + 1 - l₁*l₂*l₃)
    (heigC : C = -(l₁*l₂*l₃))
    (h₁ : abs l₁ ≤ L) (h₂ : abs l₂ ≤ L) (h₃ : abs l₃ ≤ L) (hL : 0 ≤ L)
    (hK₁ : abs (l₁ * (l₁ - 1)) ≤ K) (hK₂ : abs (l₂ * (l₂ - 1)) ≤ K)
    (hK₃ : abs (l₃ * (l₃ - 1)) ≤ K)
    (x0 i0 p0 : Real) (n : Nat) :
    m3 (l₁ * (l₁ - 1)) (l₁ * ((l₁*l₂ + l₁*l₃ + l₂*l₃) - (l₁ + l₂ + l₃) + 1 - l₁*l₂*l₃))
         ((l₁ - 1) * (-(l₁*l₂*l₃)))
       (l₂ * (l₂ - 1)) (l₂ * ((l₁*l₂ + l₁*l₃ + l₂*l₃) - (l₁ + l₂ + l₃) + 1 - l₁*l₂*l₃))
         ((l₂ - 1) * (-(l₁*l₂*l₃)))
       (l₃ * (l₃ - 1)) (l₃ * ((l₁*l₂ + l₁*l₃ + l₂*l₃) - (l₁ + l₂ + l₃) + 1 - l₁*l₂*l₃))
         ((l₃ - 1) * (-(l₁*l₂*l₃)))
        ((fxpidloop A B C D F x0 i0 p0 n).1
          - (exactPID A B C D F x0 i0 p0 n).1)
        ((fxpidloop A B C D F x0 i0 p0 n).2.1
          - (exactPID A B C D F x0 i0 p0 n).2.1)
        ((fxpidloop A B C D F x0 i0 p0 n).2.2
          - (exactPID A B C D F x0 i0 p0 n).2.2)
      ≤ npow n L
          * m3 (l₁ * (l₁ - 1)) (l₁ * ((l₁*l₂ + l₁*l₃ + l₂*l₃) - (l₁ + l₂ + l₃) + 1 - l₁*l₂*l₃))
                 ((l₁ - 1) * (-(l₁*l₂*l₃)))
               (l₂ * (l₂ - 1)) (l₂ * ((l₁*l₂ + l₁*l₃ + l₂*l₃) - (l₁ + l₂ + l₃) + 1 - l₁*l₂*l₃))
                 ((l₂ - 1) * (-(l₁*l₂*l₃)))
               (l₃ * (l₃ - 1)) (l₃ * ((l₁*l₂ + l₁*l₃ + l₂*l₃) - (l₁ + l₂ + l₃) + 1 - l₁*l₂*l₃))
                 ((l₃ - 1) * (-(l₁*l₂*l₃)))
              ((fxpidloop A B C D F x0 i0 p0 0).1
                - (exactPID A B C D F x0 i0 p0 0).1)
              ((fxpidloop A B C D F x0 i0 p0 0).2.1
                - (exactPID A B C D F x0 i0 p0 0).2.1)
              ((fxpidloop A B C D F x0 i0 p0 0).2.2
                - (exactPID A B C D F x0 i0 p0 0).2.2)
        + K * (ulp + ulp + ulp) * geom L n := by
  have hKnn : (0 : Real) ≤ K := le_trans (abs_nonneg _) hK₁
  have h3nn : (0 : Real) ≤ ulp + ulp + ulp :=
    add_nonneg (add_nonneg (le_of_lt ulp_pos) (le_of_lt ulp_pos)) (le_of_lt ulp_pos)
  let dx : Nat → Real := fun k =>
    (fxpidloop A B C D F x0 i0 p0 (k + 1)).1
      - (A * (fxpidloop A B C D F x0 i0 p0 k).1
         + B * (fxpidloop A B C D F x0 i0 p0 k).2.1
         + C * (fxpidloop A B C D F x0 i0 p0 k).2.2 + D)
  refine three_state_tracks_exact
    (A₁₁ := A) (A₁₂ := B) (A₁₃ := C) (C₁ := D)
    (A₂₁ := -1) (A₂₂ := 1) (A₂₃ := 0) (C₂ := F)
    (A₃₁ := 1) (A₃₂ := 0) (A₃₃ := 0) (C₃ := 0)
    (L := L) (ε := K * (ulp + ulp + ulp))
    (a₁ := l₁ * (l₁ - 1))
    (b₁ := l₁ * ((l₁*l₂ + l₁*l₃ + l₂*l₃) - (l₁ + l₂ + l₃) + 1 - l₁*l₂*l₃))
    (c₁ := (l₁ - 1) * (-(l₁*l₂*l₃)))
    (a₂ := l₂ * (l₂ - 1))
    (b₂ := l₂ * ((l₁*l₂ + l₁*l₃ + l₂*l₃) - (l₁ + l₂ + l₃) + 1 - l₁*l₂*l₃))
    (c₂ := (l₂ - 1) * (-(l₁*l₂*l₃)))
    (a₃ := l₃ * (l₃ - 1))
    (b₃ := l₃ * ((l₁*l₂ + l₁*l₃ + l₂*l₃) - (l₁ + l₂ + l₃) + 1 - l₁*l₂*l₃))
    (c₃ := (l₃ - 1) * (-(l₁*l₂*l₃)))
    (x := fun k => (fxpidloop A B C D F x0 i0 p0 k).1)
    (i := fun k => (fxpidloop A B C D F x0 i0 p0 k).2.1)
    (z := fun k => (fxpidloop A B C D F x0 i0 p0 k).2.2)
    (xe := fun k => (exactPID A B C D F x0 i0 p0 k).1)
    (ie := fun k => (exactPID A B C D F x0 i0 p0 k).2.1)
    (ze := fun k => (exactPID A B C D F x0 i0 p0 k).2.2)
    (dx := dx) (di := fun _ => 0) (dz := fun _ => 0)
    hL (mul_nonneg hKnn h3nn)
    (fun k => rfl) (fun k => rfl) (fun k => rfl)
    (fun k => residual_fx _ _) ?_ ?_ ?_ ?_ n
  · intro k
    exact integ_fx _ _ _ _
  · intro k
    exact delay_fx _ _ _
  · intro u v w
    rw [heigA, heigB, heigC]
    exact pid_eigen_contraction h₁ h₂ h₃ u v w
  · intro k
    refine le_trans (m3_state_only_le hK₁ hK₂ hK₃ (dx k)) ?_
    exact mul_le_mul_of_nonneg_left
      (fxpidloop_row_envelope A B C D
        (fxpidloop A B C D F x0 i0 p0 k).1
        (fxpidloop A B C D F x0 i0 p0 k).2.1
        (fxpidloop A B C D F x0 i0 p0 k).2.2) hKnn

end Real

end MachLib
