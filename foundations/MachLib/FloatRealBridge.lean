import MachLib.EMLToC
import MachLib.ForwardError
import MachLib.ErrorAlgebra

/-!
# certcom Theorem A — the Float↔Real bridge (getting started)

The certcom Theorem-A stack has two layers proven in *different worlds*:

  * **T1/T2** (`EMLToC.lean`, `EMLToCRuntime.lean`) live in exact Lean `Float`: the emitted C computes
    *identically* to the EML source (translation validation), the `mg_*` runtime discharged to a
    shared primitive basis.
  * **T3** (`CompositeRuntimeError.lean`) lives in `MachLib.Real` with the `RoundsW`/`Renc`
    forward-error model: the float *result*, viewed as a real, is within a ULP-derived bound of the
    exact math.

Connecting them needs a **`Float → Real` abstraction** — the value a double *denotes*. Lean's `Float`
is an opaque native type, so this map, and the facts relating float ops to real ops, cannot be
*computed or proven* inside Lean: they are the IEEE-754 model, and they must be **hypotheses**. This
file makes that bridge an explicit, enumerable interface (`FPBridge`) — the same move T1/T2 used for
the `mg_*` runtime (`hrt`) and the primitive basis (`Prims`) — and proves the first **connecting
theorem**: given the bridge, T2's own `evalEML` (the Float translation-validation evaluator), composed
with `toR`, lands inside a T3-style forward-error bound, on a concrete kernel.

`FPBridge` is the honest trust boundary of the whole Float↔Real connection: one `RoundsW` fact per
basic operation ("every basic float op is correctly rounded — relative error ≤ `u`"), the standard
model. It is *satisfiable* (the degenerate zero map witnesses consistency below; the real IEEE-754
`toR` is the intended model, which is what grounding it — Flocq-scale — would establish).

**Scope (honest).** The worked connection is `x²+y²` — a **cancellation-free** kernel, so the
relative `Renc` fold applies. General EML arithmetic can cancel (`a−b` with `a≈b`), where a relative
forward-error bound is *false* and one needs condition-number / absolute analysis; that general
accumulation over the whole AST is the remaining CompCert-scale T3 work, not claimed here. This is the
bridge's first load-bearing step: interface + one end-to-end Float→Real forward-error certificate.
-/

namespace Certcom
open MachLib.Real

/-- **The Float→Real bridge**, as an explicit interface. `toR` is the value a `Float` denotes as a
`MachLib.Real`. Each field is the standard IEEE-754 fact that a basic float op, viewed through `toR`,
rounds the exact `Real` op within unit roundoff `u` (`RoundsW u`). This bundle is the honest trust
connecting T2's exact-`Float` world to T3's `Real`+`Rounds` world — one rounding fact per operation.
(Division, negation, and the primitive transcendentals extend it with the same shape,
`RoundsW u (toR (mg_f x)) (Real.f (toR x))` — the T3 primitive specs, now viewed through `toR`.) -/
structure FPBridge (toR : Float → MachLib.Real) : Prop where
  add : ∀ a b : Float, RoundsW u (toR (a + b)) (toR a + toR b)
  sub : ∀ a b : Float, RoundsW u (toR (a - b)) (toR a - toR b)
  mul : ∀ a b : Float, RoundsW u (toR (a * b)) (toR a * toR b)

/-- **Consistency witness.** The bridge interface is satisfiable — the degenerate zero map obeys every
field (`0` rounds `0`) — so theorems taking an `FPBridge` are not vacuous. This is NOT a real model
(it collapses every float to `0`); the intended model is the IEEE-754 `toR`, whose existence is the
trust that grounding the bridge (Flocq-scale) would discharge. -/
example : FPBridge (fun _ => 0) := by
  have hz : ∀ e : MachLib.Real, e = 0 → RoundsW u (0 : MachLib.Real) e := by
    intro e he
    exact ⟨0, neg_nonpos_of_nonneg u_nonneg, u_nonneg, by rw [he]; mach_ring⟩
  exact ⟨fun a b => hz _ (by mach_ring), fun a b => hz _ (by mach_ring),
         fun a b => hz _ (by mach_ring)⟩

/-- **Worked bridge — the first load.** The *actual* Float computation `x·x + y·y`, viewed through
`toR`, is within the standard relative forward-error `((1+u)²−1)·(X²+Y²)` (`X = toR x`) of the exact
real `X²+Y²`, GIVEN the bridge. This is a one-line composition of the bridge's `mul`/`add` roundings
with T3's `length_sq2_fwd_compose` — the exact-`Float` and `Real`-forward-error layers meeting on a
concrete kernel. -/
theorem length_sq2_bridge {toR : Float → MachLib.Real} (br : FPBridge toR) (ex ey : Float) :
    abs (toR (ex * ex + ey * ey) - (toR ex * toR ex + toR ey * toR ey))
      ≤ (npow 2 (1 + u) - 1) * (toR ex * toR ex + toR ey * toR ey) :=
  length_sq2_fwd_compose u_nonneg u_le_one
    (br.mul ex ex) (br.mul ey ey) (br.add (ex * ex) (ey * ey))

/-- The EML expression `x² + y²` (the certifier's canonical kernel). -/
def sqSumEML : EML :=
  .bin .add (.bin .mul (.var "x") (.var "x")) (.bin .mul (.var "y") (.var "y"))

/-- **Bridge capstone (this fragment).** T2's own `evalEML` — the Float translation-validation
evaluator that T1/T2 prove the emitted C matches — composed with `toR`, lands inside T3's relative
forward-error bound. This literally connects the two certcom layers end-to-end on `x²+y²`: the emitted
C runs it in Float (T1/T2), and its real value is provably within `((1+u)²−1)·(X²+Y²)` of the exact
math (T3), given only the `FPBridge`. -/
theorem evalEML_forward_error {toR : Float → MachLib.Real} (br : FPBridge toR)
    (i1 : Trans1 → Float → Float) (i2 : Trans2 → Float → Float → Float) (env : Env) :
    abs (toR (evalEML i1 i2 env sqSumEML).toF
          - (toR (env "x").toF * toR (env "x").toF + toR (env "y").toF * toR (env "y").toF))
      ≤ (npow 2 (1 + u) - 1)
        * (toR (env "x").toF * toR (env "x").toF + toR (env "y").toF * toR (env "y").toF) := by
  have h : (evalEML i1 i2 env sqSumEML).toF
      = (env "x").toF * (env "x").toF + (env "y").toF * (env "y").toF := rfl
  rw [h]
  exact length_sq2_bridge br (env "x").toF (env "y").toF

end Certcom
