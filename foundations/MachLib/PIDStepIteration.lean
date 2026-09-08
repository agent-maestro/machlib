import MachLib.SignedPIDLoop

/-!
# Iterating a compiler-emitted step function IS the exact PID trajectory

`spidloopOf_tracks_exact_floor` bounds how far a fixed-point loop drifts from `exactPID`, the
exact real PID trajectory. That is only useful to a compiler if the compiler's *own* artifact is
`exactPID` — and a compiler does not emit a trajectory. It emits a **step**: one function from the
current state to the next.

Forge emits exactly that. For a stateful PID kernel its Lean backend produces

```lean
noncomputable def pid_loop_step (x i p r : Real) : Real × Real × Real :=
  let nx := A * x + B * i + C * p
  let ni := i - x + r
  let np := x
  ...
  (x, i, p)
```

and `pid_loop_step x i p r = (A*x + B*i + C*p, (i − x) + r, x)` holds **by `rfl`**. This file
supplies the missing half: iterating any such step reproduces `exactPID`, so the trajectory bound
is a statement about the artifact the compiler actually wrote.

## Why this needs proving rather than observing

The two are not syntactically the same recurrence. `exactPID`'s middle and last rows are written
in the coefficient form `three_state_tracks_exact` consumes — `(−1)·x + 1·i + 0·p + F` and
`1·x + 0·i + 0·p + 0` — because that shape is what the eigen machinery matches against. A compiler
emits the form a person writes, `(i − x) + r` and `x`. They agree by ring, and the ring step has
to happen somewhere; doing it here means every backend gets it once instead of each rediscovering
it, and means the `0 * p` terms never reach a caller's normaliser.

## Scope

This is the EXACT side of the join, and it is the half a compiler can discharge today. The other
half — that the *fixed-point* loop is `spidloopOf` with a floor-truncating row — is a statement
about emitted RTL rather than emitted Lean, and is not made here.
-/

namespace MachLib

namespace Real

/-- Iterating a three-state step from a starting state. The argument order matches `exactPID`'s,
so the two can be compared componentwise without reassociating anything. -/
noncomputable def iterState (step : Real → Real → Real → Real × Real × Real)
    (x0 i0 p0 : Real) : Nat → Real × Real × Real
  | 0 => (x0, i0, p0)
  | k + 1 =>
      let st := iterState step x0 i0 p0 k
      step st.1 st.2.1 st.2.2

/-! ### The two row forms agree

Factored over fresh variables, and proved with `zero_mul`/`add_zero` rewrites rather than the
normaliser: `CLAUDE.md` records that a literal `0 * t` makes `mach_mpoly` **grind rather than
fail**, and both rows below carry one. -/

/-- **Both differing rows at once**, over fresh variables.

One lemma rather than two, because rewriting them separately over-rewrites: the delay row's `x`
also occurs *inside* the integrator row as `−1 · x`, so a `rw` of the delay form rebuilds the
integrator row around it and the goal stops matching. Splitting the tuple with `Prod.mk.injEq`
first keeps each component's rewrite where it belongs. -/
private theorem step_rows_agree (e1 e2 e3 A B C D F : Real) :
    ((A * e1 + B * e2 + C * e3 + D : Real), (e2 - e1) + F, e1)
      = (A * e1 + B * e2 + C * e3 + D,
         (-1) * e1 + 1 * e2 + 0 * e3 + F,
         1 * e1 + 0 * e2 + 0 * e3 + 0) := by
  simp only [Prod.mk.injEq]
  refine ⟨trivial, ?_, ?_⟩
  · rw [zero_mul, add_zero, one_mul_thm]
    mach_mpoly [e1, e2, F]
  · rw [zero_mul, zero_mul, one_mul_thm, add_zero, add_zero, add_zero]

/-! ### The bridge -/

/-- **Iterating a step function that is the PID recurrence reproduces `exactPID`.**

`hstep` is the compiler's side of the contract, in the form a backend can discharge by `rfl`:
the emitted step maps `(x, i, p)` to `(A·x + B·i + C·p + D, (i − x) + F, x)`. Nothing else about
the step is assumed — not how it was written, not what language produced it.

With this, `spidloopOf_tracks_exact_floor`'s conclusion is about the compiler's own artifact:
the fixed-point loop stays within `K·3·ulp · geom L n` of the trajectory obtained by iterating the
emitted step. -/
theorem iterState_eq_exactPID
    (step : Real → Real → Real → Real × Real × Real) {A B C D F : Real}
    (hstep : ∀ x i p : Real,
        step x i p = (A * x + B * i + C * p + D, (i - x) + F, x))
    (x0 i0 p0 : Real) :
    ∀ n : Nat, iterState step x0 i0 p0 n = exactPID A B C D F x0 i0 p0 n := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
      show step (iterState step x0 i0 p0 k).1 (iterState step x0 i0 p0 k).2.1
             (iterState step x0 i0 p0 k).2.2 = _
      rw [ih, hstep]
      exact step_rows_agree _ _ _ A B C D F

/-- **A specimen in the shape a compiler backend hands over.** The hypothesis a backend must
discharge is `rfl`-shaped, so this is what the discharge looks like from the other side: define
the step exactly as Forge emits it, and the bridge applies with no further work. -/
noncomputable def emittedStepSpecimen (A B C : Real) (r : Real)
    (x i p : Real) : Real × Real × Real :=
  (A * x + B * i + C * p + 0, (i - x) + r, x)

theorem emittedStepSpecimen_iterates_to_exactPID (A B C r x0 i0 p0 : Real) (n : Nat) :
    iterState (emittedStepSpecimen A B C r) x0 i0 p0 n
      = exactPID A B C 0 r x0 i0 p0 n :=
  iterState_eq_exactPID (emittedStepSpecimen A B C r) (fun _ _ _ => rfl) x0 i0 p0 n

end Real

end MachLib
