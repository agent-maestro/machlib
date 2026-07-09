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

/-! ## A compositional toolkit — the bridge folds over any cancellation-free tree

`length_sq2_bridge` hardcoded one kernel. These three lemmas turn the bridge into a REUSABLE fold:
a `Renc` enclosure for the float image of any leaf, product, or (equal-exponent) sum, built from the
bridge's per-op roundings. With them, the forward-error bound for an arbitrary nonneg-leaf
cancellation-free arithmetic tree is assembled node-by-node — the certifier's job, now carrying a
real Float computation across the bridge. (Nonnegativity of leaves is inherent to a *relative*
forward-error bound — `Renc` is two-sided about a nonneg exact; cancellation is the open regime.) -/

/-- Leaf: a variable/constant float value is its own exact real, exponent 0 (no rounding). -/
theorem bridge_leaf {toR : Float → MachLib.Real} (v : Float) (hv : 0 ≤ toR v) :
    Renc 0 u (toR v) (toR v) :=
  renc_leaf hv

/-- Product node: the float product's image is within `Renc (a+b+1)` of the exact product, given the
subtrees' enclosures and the bridge's `mul` rounding. Exponents compose freely — no lift needed. -/
theorem bridge_mul {toR : Float → MachLib.Real} (br : FPBridge toR) {a b : Nat}
    {flx fly : Float} {xe ye : MachLib.Real} (hxe : 0 ≤ xe) (hye : 0 ≤ ye)
    (hx : Renc a u (toR flx) xe) (hy : Renc b u (toR fly) ye) :
    Renc (a + b + 1) u (toR (flx * fly)) (xe * ye) :=
  renc_mul u_nonneg u_le_one hxe hye hx hy (br.mul flx fly)

/-- Sum node (equal exponent): `Renc (a+1)`, via the bridge's `add` rounding. Mixed-exponent sums
lift to a common exponent first (the certifier's balanced-fold discipline). -/
theorem bridge_add {toR : Float → MachLib.Real} (br : FPBridge toR) {a : Nat}
    {flx fly : Float} {xe ye : MachLib.Real} (hxe : 0 ≤ xe) (hye : 0 ≤ ye)
    (hx : Renc a u (toR flx) xe) (hy : Renc a u (toR fly) ye) :
    Renc (a + 1) u (toR (flx + fly)) (xe + ye) :=
  renc_add u_nonneg u_le_one hxe hye hx hy (br.add flx fly)

/-- **Depth-3 worked kernel — the fold generalizes past the fixed 2-term kernel.** The actual Float
computation `(x·y)·z` (nonneg inputs), through `toR`, is within `((1+u)²−1)·(X·Y·Z)` of the exact
`X·Y·Z` — assembled by `bridge_leaf → bridge_mul → bridge_mul → renc_fwd`, two rounding levels deep. -/
theorem prod3_bridge {toR : Float → MachLib.Real} (br : FPBridge toR) (ex ey ez : Float)
    (hx : 0 ≤ toR ex) (hy : 0 ≤ toR ey) (hz : 0 ≤ toR ez) :
    abs (toR ((ex * ey) * ez) - (toR ex * toR ey * toR ez))
      ≤ (npow 2 (1 + u) - 1) * (toR ex * toR ey * toR ez) := by
  have lxy : Renc 1 u (toR (ex * ey)) (toR ex * toR ey) :=
    bridge_mul br hx hy (bridge_leaf ex hx) (bridge_leaf ey hy)
  have lxyz : Renc 2 u (toR ((ex * ey) * ez)) ((toR ex * toR ey) * toR ez) :=
    bridge_mul br (mul_nonneg hx hy) hz lxy (bridge_leaf ez hz)
  exact renc_fwd u_nonneg u_le_one (mul_nonneg (mul_nonneg hx hy) hz) lxyz

/-- The EML expression `(x·y)·z`. -/
def prod3EML : EML :=
  .bin .mul (.bin .mul (.var "x") (.var "y")) (.var "z")

/-- The depth-3 bridge, connected to T2's `evalEML` — the capstone at a deeper expression: the emitted
C runs `(x·y)·z` in Float, and its real value is within the T3 forward-error bound of the exact
product, given the bridge. -/
theorem evalEML_prod3_fwd {toR : Float → MachLib.Real} (br : FPBridge toR)
    (i1 : Trans1 → Float → Float) (i2 : Trans2 → Float → Float → Float) (env : Env)
    (hx : 0 ≤ toR (env "x").toF) (hy : 0 ≤ toR (env "y").toF) (hz : 0 ≤ toR (env "z").toF) :
    abs (toR (evalEML i1 i2 env prod3EML).toF
          - (toR (env "x").toF * toR (env "y").toF * toR (env "z").toF))
      ≤ (npow 2 (1 + u) - 1)
        * (toR (env "x").toF * toR (env "y").toF * toR (env "z").toF) := by
  have h : (evalEML i1 i2 env prod3EML).toF
      = ((env "x").toF * (env "y").toF) * (env "z").toF := rfl
  rw [h]
  exact prod3_bridge br (env "x").toF (env "y").toF (env "z").toF hx hy hz

/-! ## The pipeline, connected end-to-end — from EMITTED C to the real forward-error bound

`evalEML_forward_error`/`evalEML_prod3_fwd` stop at T2's `evalEML` (the Float translation-validation
evaluator). The genuinely end-to-end link is the **emitted C itself**: T1's `emitC_correct` says
`evalC r1 r2 env (emitC e) = evalEML i1 i2 env e` — the emitted C AST, evaluated in Float, IS the EML
Float value. Composing that with the bridge gives one theorem spanning every layer:

    EML source ──emitC (T1)──▶ C AST ──evalC (T1)──▶ Float result ──toR (bridge)──▶ Real image
                                                                     ⤷ within T3 forward-error of exact ℝ

The `Real` these are measured against is the one Theorem B (`certcom` soundness) proves models the
`MachLib.Real` axioms — so the whole chain rests on an explicit, enumerable trust boundary (`FPBridge`'s
per-op roundings + the C compiler), nothing hidden. -/

/-- **End-to-end pipeline capstone (`x²+y²`).** The value the *emitted C* computes — `evalC` of `emitC`,
the actual translated program — viewed through `toR`, is within T3's relative forward-error bound of the
exact real `X²+Y²`. Proof: rewrite the emitted-C result to the EML Float value by `emitC_correct` (T1),
then apply the bridge capstone (T3). Two proven layers, one statement. -/
theorem pipeline_sqSum {toR : Float → MachLib.Real} (br : FPBridge toR)
    (i1 : Trans1 → Float → Float) (i2 : Trans2 → Float → Float → Float)
    (r1 : String → Float → Float) (r2 : String → Float → Float → Float)
    (hrt1 : ∀ (t : Trans1) (v : Float), r1 t.cName v = i1 t v)
    (hrt2 : ∀ (t : Trans2) (u v : Float), r2 t.cName u v = i2 t u v) (env : Env) :
    abs (toR (evalC r1 r2 env (emitC sqSumEML)).toF
          - (toR (env "x").toF * toR (env "x").toF + toR (env "y").toF * toR (env "y").toF))
      ≤ (npow 2 (1 + u) - 1)
        * (toR (env "x").toF * toR (env "x").toF + toR (env "y").toF * toR (env "y").toF) := by
  rw [emitC_correct i1 i2 r1 r2 hrt1 hrt2 sqSumEML env]
  exact evalEML_forward_error br i1 i2 env

/-- **End-to-end pipeline capstone (`(x·y)·z`, depth 3).** Same span, deeper kernel: the emitted C's
result for `(x·y)·z`, through `toR`, is within the T3 forward-error bound of the exact `X·Y·Z`. -/
theorem pipeline_prod3 {toR : Float → MachLib.Real} (br : FPBridge toR)
    (i1 : Trans1 → Float → Float) (i2 : Trans2 → Float → Float → Float)
    (r1 : String → Float → Float) (r2 : String → Float → Float → Float)
    (hrt1 : ∀ (t : Trans1) (v : Float), r1 t.cName v = i1 t v)
    (hrt2 : ∀ (t : Trans2) (u v : Float), r2 t.cName u v = i2 t u v) (env : Env)
    (hx : 0 ≤ toR (env "x").toF) (hy : 0 ≤ toR (env "y").toF) (hz : 0 ≤ toR (env "z").toF) :
    abs (toR (evalC r1 r2 env (emitC prod3EML)).toF
          - (toR (env "x").toF * toR (env "y").toF * toR (env "z").toF))
      ≤ (npow 2 (1 + u) - 1)
        * (toR (env "x").toF * toR (env "y").toF * toR (env "z").toF) := by
  rw [emitC_correct i1 i2 r1 r2 hrt1 hrt2 prod3EML env]
  exact evalEML_prod3_fwd br i1 i2 env hx hy hz

end Certcom
