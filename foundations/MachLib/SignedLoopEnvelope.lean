import MachLib.SignedPIDLoop

/-!
# The loop generalised over its state row — so the theorem is about the HARDWARE

`spidloop_tracks_exact` is a theorem about one datapath: the state row built from `sfxmul`. That
is *a* model of a fixed-point multiplier, and it is not the only one, which matters more than it
sounds.

## The discovery that forced this file

Forge's Verilog backend emits, for each gain,

```verilog
assign _w2_full = A * x;          // full-width signed product
assign _w3      = _w2_full >>> FRAC;   // arithmetic shift right
```

An arithmetic shift right is **floor** division: it truncates toward `−∞`, for negative values
too. `sfxmul` truncates a different way. It is built as a difference of *unsigned* truncated
products,

```
sfxmul a b = (fxmul a⁺ b⁺ ⊕ fxmul a⁻ b⁻,  fxmul a⁺ b⁻ ⊕ fxmul a⁻ b⁺)
```

and each `fxmul` floors a **non-negative** quotient, so the difference they denote truncates
toward **zero**. The two agree whenever the product is non-negative and differ by exactly one
`ulp` when it is not.

This was found by simulating the emitted RTL under Verilator and comparing it against both
models over forty steps of a PID loop: the floor model matched at every step, `sfxmul` diverged
at step three by one `ulp`. Forge's own fixed-point certifier uses floor and says so
(*"toward −∞, the typical fixed-point datapath"*). So `spidloop_tracks_exact` is a true theorem
about a datapath that is **not the one on the FPGA**.

## Why the conclusion survives, and what has to change for it to be claimed

Nothing in the trajectory proof uses *how* the multiply truncates. It uses one fact: the state
row lands within `6·ulp` of the exact linear combination. Floor truncation errs by less than one
`ulp` in one direction, `sfxmul` by less than two in either, and both are inside that envelope.

So the honest form of the theorem takes the envelope as a **hypothesis** and says nothing about
the multiplier at all. `spidloopOf_tracks_exact` below is that form: the integrator and delay
rows stay fixed, because their exactness is structural and is what forces the eigenvectors, and
the state row becomes an arbitrary function carrying an error bound. A different multiplier is
then a different *instance*, not a different theorem — and an instance is exactly what a compiler
backend can supply about its own emitted RTL.

`spidloop_row_envelope` records that the `sfxmul` datapath is one such instance, so the existing
join is recovered rather than replaced.

## What this does NOT do

It does not prove that Forge's shift-based multiply meets the envelope. That is a statement about
a *different* bit-level operation than the one this corpus models, and it needs its own proof or
its own measurement; asserting it here would be the exact "evidence attaches to names" error both
projects are built to avoid. What this file does is make that the only remaining step.
-/

namespace MachLib

namespace SRTL

/-- **The three-row loop with an arbitrary state row.**

The integrator row is still `ssub` then `sadd` and the delay row is still a wire: those two are
exact by construction, and their exactness is what pins the left eigenvectors. Only the state row
is abstract. -/
def spidloopOf (step : SVec → SVec → SVec → SVec) (GF X0 I0 P0 : SVec) :
    Nat → SVec × SVec × SVec
  | 0 => (X0, I0, P0)
  | k + 1 =>
      let st := spidloopOf step GF X0 I0 P0 k
      (step st.1 st.2.1 st.2.2, sadd (ssub st.2.1 st.1) GF, st.1)

end SRTL

namespace Real

open SRTL

/-! ### Shape lemmas

Re-declared rather than imported: the originals in `SignedPIDLoop` are `private`, which is the
right default for a proof-local rearrangement and means they cannot be named from here. They are
one line each, and re-deriving them is cheaper than widening another module's interface. -/

private theorem residual_env (x a : Real) : x = a + (x - a) := by mach_mpoly [x, a]

private theorem integ_env (p q F z : Real) : p + q + F = p + q + 0 * z + F + 0 := by
  rw [zero_mul, add_zero, add_zero]

private theorem delay_env (x i z : Real) : x = 1 * x + 0 * i + 0 * z + 0 + 0 := by
  rw [zero_mul, zero_mul, one_mul_thm, add_zero, add_zero, add_zero, add_zero]

/-! ### The join, over any state row inside the envelope -/

/-- **A three-row loop tracks its exact trajectory whenever its state row is within `ε`.**

`hstep` is the whole interface to the datapath: it says the computed state row lands within `ε`
of `A·x + B·i + C·p + D`, and says nothing about how. Everything else is the PID structure —
`heigA`–`heigC` name the eigenvalues of the caller's own gains, and the contraction follows from
`pid_eigen_contraction`, free as always.

The per-step term is `K·ε`, with `K` bounding the measure's three leading coefficients. That
factor is the same one `spidloop_tracks_exact` carries and for the same reason: the PID
functionals begin with `λ(λ−1)` rather than `1`, so a state-row perturbation is scaled rather
than passed through. -/
theorem spidloopOf_tracks_exact
    (step : SVec → SVec → SVec → SVec) (GF X0 I0 P0 : SVec)
    {A B C D : Real} {l₁ l₂ l₃ L K ε : Real}
    (hstep : ∀ X I P : SVec,
        abs (sval (step X I P) - (A * sval X + B * sval I + C * sval P + D)) ≤ ε)
    (heigA : A = (l₁ + l₂ + l₃) - 1)
    (heigB : B = (l₁*l₂ + l₁*l₃ + l₂*l₃) - (l₁ + l₂ + l₃) + 1 - l₁*l₂*l₃)
    (heigC : C = -(l₁*l₂*l₃))
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
        (sval (spidloopOf step GF X0 I0 P0 n).1
          - (exactPID A B C D (sval GF) (sval X0) (sval I0) (sval P0) n).1)
        (sval (spidloopOf step GF X0 I0 P0 n).2.1
          - (exactPID A B C D (sval GF) (sval X0) (sval I0) (sval P0) n).2.1)
        (sval (spidloopOf step GF X0 I0 P0 n).2.2
          - (exactPID A B C D (sval GF) (sval X0) (sval I0) (sval P0) n).2.2)
      ≤ npow n L
          * m3 (l₁ * (l₁ - 1)) (l₁ * ((l₁*l₂ + l₁*l₃ + l₂*l₃) - (l₁ + l₂ + l₃) + 1 - l₁*l₂*l₃))
                 ((l₁ - 1) * (-(l₁*l₂*l₃)))
               (l₂ * (l₂ - 1)) (l₂ * ((l₁*l₂ + l₁*l₃ + l₂*l₃) - (l₁ + l₂ + l₃) + 1 - l₁*l₂*l₃))
                 ((l₂ - 1) * (-(l₁*l₂*l₃)))
               (l₃ * (l₃ - 1)) (l₃ * ((l₁*l₂ + l₁*l₃ + l₂*l₃) - (l₁ + l₂ + l₃) + 1 - l₁*l₂*l₃))
                 ((l₃ - 1) * (-(l₁*l₂*l₃)))
              (sval (spidloopOf step GF X0 I0 P0 0).1
                - (exactPID A B C D (sval GF) (sval X0) (sval I0) (sval P0) 0).1)
              (sval (spidloopOf step GF X0 I0 P0 0).2.1
                - (exactPID A B C D (sval GF) (sval X0) (sval I0) (sval P0) 0).2.1)
              (sval (spidloopOf step GF X0 I0 P0 0).2.2
                - (exactPID A B C D (sval GF) (sval X0) (sval I0) (sval P0) 0).2.2)
        + K * ε * geom L n := by
  have hKnn : (0 : Real) ≤ K := le_trans (abs_nonneg _) hK₁
  have hεnn : (0 : Real) ≤ ε := le_trans (abs_nonneg _) (hstep X0 I0 P0)
  let dx : Nat → Real := fun k =>
    sval (spidloopOf step GF X0 I0 P0 (k + 1)).1
      - (A * sval (spidloopOf step GF X0 I0 P0 k).1
         + B * sval (spidloopOf step GF X0 I0 P0 k).2.1
         + C * sval (spidloopOf step GF X0 I0 P0 k).2.2 + D)
  refine three_state_tracks_exact
    (A₁₁ := A) (A₁₂ := B) (A₁₃ := C) (C₁ := D)
    (A₂₁ := -1) (A₂₂ := 1) (A₂₃ := 0) (C₂ := sval GF)
    (A₃₁ := 1) (A₃₂ := 0) (A₃₃ := 0) (C₃ := 0)
    (L := L) (ε := K * ε)
    (a₁ := l₁ * (l₁ - 1))
    (b₁ := l₁ * ((l₁*l₂ + l₁*l₃ + l₂*l₃) - (l₁ + l₂ + l₃) + 1 - l₁*l₂*l₃))
    (c₁ := (l₁ - 1) * (-(l₁*l₂*l₃)))
    (a₂ := l₂ * (l₂ - 1))
    (b₂ := l₂ * ((l₁*l₂ + l₁*l₃ + l₂*l₃) - (l₁ + l₂ + l₃) + 1 - l₁*l₂*l₃))
    (c₂ := (l₂ - 1) * (-(l₁*l₂*l₃)))
    (a₃ := l₃ * (l₃ - 1))
    (b₃ := l₃ * ((l₁*l₂ + l₁*l₃ + l₂*l₃) - (l₁ + l₂ + l₃) + 1 - l₁*l₂*l₃))
    (c₃ := (l₃ - 1) * (-(l₁*l₂*l₃)))
    (x := fun k => sval (spidloopOf step GF X0 I0 P0 k).1)
    (i := fun k => sval (spidloopOf step GF X0 I0 P0 k).2.1)
    (z := fun k => sval (spidloopOf step GF X0 I0 P0 k).2.2)
    (xe := fun k => (exactPID A B C D (sval GF) (sval X0) (sval I0) (sval P0) k).1)
    (ie := fun k => (exactPID A B C D (sval GF) (sval X0) (sval I0) (sval P0) k).2.1)
    (ze := fun k => (exactPID A B C D (sval GF) (sval X0) (sval I0) (sval P0) k).2.2)
    (dx := dx) (di := fun _ => 0) (dz := fun _ => 0)
    hL (mul_nonneg hKnn hεnn)
    (fun k => rfl) (fun k => rfl) (fun k => rfl)
    (fun k => residual_env _ _) ?_ ?_ ?_ ?_ n
  · intro k
    show sval (sadd (ssub (spidloopOf step GF X0 I0 P0 k).2.1
                          (spidloopOf step GF X0 I0 P0 k).1) GF)
        = (-1) * sval (spidloopOf step GF X0 I0 P0 k).1
          + 1 * sval (spidloopOf step GF X0 I0 P0 k).2.1
          + 0 * sval (spidloopOf step GF X0 I0 P0 k).2.2 + sval GF + 0
    rw [spid_integrator_exact]
    exact integ_env _ _ _ _
  · intro k
    exact delay_env _ _ _
  · intro u v w
    rw [heigA, heigB, heigC]
    exact pid_eigen_contraction h₁ h₂ h₃ u v w
  · intro k
    refine le_trans (m3_state_only_le hK₁ hK₂ hK₃ (dx k)) ?_
    exact mul_le_mul_of_nonneg_left
      (hstep (spidloopOf step GF X0 I0 P0 k).1
             (spidloopOf step GF X0 I0 P0 k).2.1
             (spidloopOf step GF X0 I0 P0 k).2.2) hKnn

/-- **The `sfxmul` datapath is one instance of the envelope**, so `spidloop_tracks_exact` is
recovered rather than replaced. A backend whose multiplier truncates the other way supplies a
different proof of this same shape and gets the same conclusion. -/
theorem spidloop_row_envelope (GA GB GC GD : SVec) (X I P : SVec) :
    abs (sval (sadd (sadd (sadd (sfxmul GA X) (sfxmul GB I)) (sfxmul GC P)) GD)
         - (sval GA * sval X + sval GB * sval I + sval GC * sval P + sval GD))
      ≤ natCast 6 * ulp :=
  spid_state_error GA GB GC GD X I P

/-- **A datapath NEAR the modelled one is inside the envelope too**, by the triangle inequality.

This is the lemma that makes a *measurement* usable. Comparing two multipliers is a local,
finite, checkable thing — Verilator against a reference, one operation at a time — whereas
comparing a whole trajectory is not. So a backend that has established "my multiplier is within
`δ` of `sfxmul`, per operation" gets the envelope at `δ + 6·ulp` and, through
`spidloopOf_tracks_exact`, a trajectory bound.

For Forge's shift-based row the measured per-multiply gap is one `ulp` and there are three
multiplies, so `δ = 3·ulp` and the envelope closes at `9·ulp`. That is looser than the `6·ulp`
the modelled datapath enjoys, and it is *sound for the hardware*, which the tighter number is
not. -/
theorem spidloop_row_envelope_of_near
    (GA GB GC GD : SVec) (step : SVec → SVec → SVec → SVec) {δ : Real}
    (hnear : ∀ X I P : SVec, abs (sval (step X I P)
        - sval (sadd (sadd (sadd (sfxmul GA X) (sfxmul GB I)) (sfxmul GC P)) GD)) ≤ δ)
    (X I P : SVec) :
    abs (sval (step X I P)
         - (sval GA * sval X + sval GB * sval I + sval GC * sval P + sval GD))
      ≤ δ + natCast 6 * ulp := by
  have e : sval (step X I P)
        - (sval GA * sval X + sval GB * sval I + sval GC * sval P + sval GD)
      = (sval (step X I P)
          - sval (sadd (sadd (sadd (sfxmul GA X) (sfxmul GB I)) (sfxmul GC P)) GD))
        + (sval (sadd (sadd (sadd (sfxmul GA X) (sfxmul GB I)) (sfxmul GC P)) GD)
           - (sval GA * sval X + sval GB * sval I + sval GC * sval P + sval GD)) := by
    mach_mpoly [sval (step X I P),
                sval (sadd (sadd (sadd (sfxmul GA X) (sfxmul GB I)) (sfxmul GC P)) GD),
                sval GA * sval X, sval GB * sval I, sval GC * sval P, sval GD]
  rw [e]
  exact le_trans (abs_add _ _)
    (add_le_add_both (hnear X I P) (spid_state_error GA GB GC GD X I P))

/-! ### The datapath Forge actually emits, from the defining property of `>>>`

`spidloop_row_envelope_of_near` gets the hardware inside the envelope by comparing it to `sfxmul`,
which costs `δ + 6·ulp`. There is a better route, and it is better in three ways at once: it is
tighter, it needs no reference model, and its hypothesis is the *definition* of an arithmetic
shift rather than a measurement against something else.

An arithmetic shift right by `FRAC` on the Q-grid discards the low `FRAC` bits. So the computed
product is **at most one `ulp` below** the exact one and is **never above** it. That is a
one-sided statement, and it is exactly what `>>>` does — a backend can assert it about its own
emitter without simulating anything.

One-sided at one `ulp` beats `sfxmul`'s two-sided two, so the emitted hardware is *better* than
the datapath this corpus was modelling, not worse. Modelling it as `sfxmul` was costing a factor
of two on top of being the wrong function. -/

/-- **A state row built from three downward-truncating products lands within `3·ulp`.**

Stated over the computed products themselves (`pa`, `pb`, `pc`) rather than over any multiplier,
so nothing here mentions bit widths, two's complement, or how the truncation is implemented. The
adders contribute nothing, as always. -/
theorem row_within_three_ulp
    {pa pb pc a x b i c p d : Real}
    (hA₀ : 0 ≤ a * x - pa) (hA₁ : a * x - pa ≤ ulp)
    (hB₀ : 0 ≤ b * i - pb) (hB₁ : b * i - pb ≤ ulp)
    (hC₀ : 0 ≤ c * p - pc) (hC₁ : c * p - pc ≤ ulp) :
    abs ((pa + pb + pc + d) - (a * x + b * i + c * p + d)) ≤ ulp + ulp + ulp := by
  have hsum : (pa + pb + pc + d) - (a * x + b * i + c * p + d)
      = -((a * x - pa) + (b * i - pb) + (c * p - pc)) := by
    mach_mpoly [pa, pb, pc, d, a * x, b * i, c * p]
  have hS0 : (0 : Real) ≤ (a * x - pa) + (b * i - pb) + (c * p - pc) :=
    add_nonneg (add_nonneg hA₀ hB₀) hC₀
  have hSle : (a * x - pa) + (b * i - pb) + (c * p - pc) ≤ ulp + ulp + ulp :=
    add_le_add_both (add_le_add_both hA₁ hB₁) hC₁
  have h3nn : (0 : Real) ≤ ulp + ulp + ulp :=
    add_nonneg (add_nonneg (le_of_lt ulp_pos) (le_of_lt ulp_pos)) (le_of_lt ulp_pos)
  rw [hsum]
  refine abs_le_of ?_ ?_
  · exact le_trans (neg_nonpos_of_nonneg hS0) h3nn
  · rw [neg_neg_helper]
    exact hSle


/-- **The join for a downward-truncating datapath — Forge's, given only what `>>>` does.**

The hypotheses are: the state row is three products plus the constant (`hrow`), and each product
is at most one `ulp` below the exact one and never above it (`hA`, `hB`, `hC`). Nothing else. No
bit widths, no two's complement, no reference multiplier, and no simulation — those three
inequalities are the arithmetic shift's defining behaviour on the Q-grid, and they are what a
backend can assert about its own emitter.

The per-step term is `K·3·ulp`, against `K·6·ulp` for the `sfxmul` datapath. The hardware is
better than the model this corpus started with, which is worth saying plainly after the model
turned out to be the wrong function. -/
theorem spidloopOf_tracks_exact_floor
    (step : SVec → SVec → SVec → SVec) (GF X0 I0 P0 : SVec)
    {A B C D : Real} {l₁ l₂ l₃ L K : Real}
    {pA pB pC : SVec → SVec → SVec → Real}
    (hrow : ∀ X I P : SVec, sval (step X I P) = pA X I P + pB X I P + pC X I P + D)
    (hA : ∀ X I P : SVec, 0 ≤ A * sval X - pA X I P ∧ A * sval X - pA X I P ≤ ulp)
    (hB : ∀ X I P : SVec, 0 ≤ B * sval I - pB X I P ∧ B * sval I - pB X I P ≤ ulp)
    (hC : ∀ X I P : SVec, 0 ≤ C * sval P - pC X I P ∧ C * sval P - pC X I P ≤ ulp)
    (heigA : A = (l₁ + l₂ + l₃) - 1)
    (heigB : B = (l₁*l₂ + l₁*l₃ + l₂*l₃) - (l₁ + l₂ + l₃) + 1 - l₁*l₂*l₃)
    (heigC : C = -(l₁*l₂*l₃))
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
        (sval (spidloopOf step GF X0 I0 P0 n).1
          - (exactPID A B C D (sval GF) (sval X0) (sval I0) (sval P0) n).1)
        (sval (spidloopOf step GF X0 I0 P0 n).2.1
          - (exactPID A B C D (sval GF) (sval X0) (sval I0) (sval P0) n).2.1)
        (sval (spidloopOf step GF X0 I0 P0 n).2.2
          - (exactPID A B C D (sval GF) (sval X0) (sval I0) (sval P0) n).2.2)
      ≤ npow n L
          * m3 (l₁ * (l₁ - 1)) (l₁ * ((l₁*l₂ + l₁*l₃ + l₂*l₃) - (l₁ + l₂ + l₃) + 1 - l₁*l₂*l₃))
                 ((l₁ - 1) * (-(l₁*l₂*l₃)))
               (l₂ * (l₂ - 1)) (l₂ * ((l₁*l₂ + l₁*l₃ + l₂*l₃) - (l₁ + l₂ + l₃) + 1 - l₁*l₂*l₃))
                 ((l₂ - 1) * (-(l₁*l₂*l₃)))
               (l₃ * (l₃ - 1)) (l₃ * ((l₁*l₂ + l₁*l₃ + l₂*l₃) - (l₁ + l₂ + l₃) + 1 - l₁*l₂*l₃))
                 ((l₃ - 1) * (-(l₁*l₂*l₃)))
              (sval (spidloopOf step GF X0 I0 P0 0).1
                - (exactPID A B C D (sval GF) (sval X0) (sval I0) (sval P0) 0).1)
              (sval (spidloopOf step GF X0 I0 P0 0).2.1
                - (exactPID A B C D (sval GF) (sval X0) (sval I0) (sval P0) 0).2.1)
              (sval (spidloopOf step GF X0 I0 P0 0).2.2
                - (exactPID A B C D (sval GF) (sval X0) (sval I0) (sval P0) 0).2.2)
        + K * (ulp + ulp + ulp) * geom L n := by
  refine spidloopOf_tracks_exact step GF X0 I0 P0 (ε := ulp + ulp + ulp)
    ?_ heigA heigB heigC h₁ h₂ h₃ hL hK₁ hK₂ hK₃ n
  intro X I P
  rw [hrow X I P]
  obtain ⟨a₀, a₁⟩ := hA X I P
  obtain ⟨b₀, b₁⟩ := hB X I P
  obtain ⟨c₀, c₁⟩ := hC X I P
  exact row_within_three_ulp a₀ a₁ b₀ b₁ c₀ c₁

end Real

end MachLib
