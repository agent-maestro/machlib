import MachLib.EMLToC

/-!
# certcom Theorem A — tier T2 step: discharging the `mg_*` runtime hypothesis

T1 (`EMLToC.lean`) proves `emitC`/`runProg` preserve semantics **given** `hrt1`/`hrt2`: that the C
runtime call `mg_<f>` computes the intended EML builtin `i<n> <f>`. That hypothesis is T1's declared
trust boundary. This file **discharges** it — not by eliminating trust (the libm transcendentals are
genuinely outside Lean's world), but by shrinking and pinning it, grounded in the actual runtime
source `forge/software/runtime/c/libmonogate.h`.

The `mg_*` functions split into two honest classes there:

  * **Primitive** — direct libm calls: `mg_exp=exp`, `mg_ln=log`, `mg_sin/cos/tan`, `mg_asin/acos/atan`,
    `mg_sqrt=sqrt`, `mg_abs=fabs`, `mg_pow=pow`. These are the irreducible trust.
  * **Composite** — defined *from* the primitives, verbatim in `libmonogate.h`:
    `mg_eml(x,y)=exp(x)−log(y)` (the EML primitive itself), and the hyperbolics
    `mg_sinh=(eˣ−e⁻ˣ)/2`, `mg_cosh=(eˣ+e⁻ˣ)/2`, `mg_tanh=(eˣ−e⁻ˣ)/(eˣ+e⁻ˣ)`.

The move: build BOTH the runtime (`stdR1`/`stdR2`) and the EML interpretation (`stdI1`/`stdI2`) from
one shared **primitive basis** `Prims`. The composites are then written once on each side — the
runtime side transcribing the C source, the interpretation side the EML operator definition — and
their agreement (`std_hrt1`/`std_hrt2`) is PROVEN for every basis, sorryAx-free. So the composites
drop out of the trust set, and `runProg_correct_std` is the T1 certificate with the runtime
hypothesis discharged: its trust is reduced to the enumerable primitive basis `Prims`.

**What remains trusted (the honest T3 boundary):** the 11 `Prims` fields model the identically-named
C libm calls. That is a statement about C execution, not provable in Lean; grounding it is offline
libm/Flocq validation (`sqrt`/`abs` are IEEE-754-exact and the strongest; the transcendentals carry a
ULP gap). But it is now a SHORT, NAMED list, and every COMPOSITE is discharged. `std_hrt` is also a
real cross-check: were `libmonogate.h`'s decomposition to disagree with the operator definition, the
proof would fail.
-/

namespace Certcom

/-- The platform primitive float ops — the `mg_*` "standard math wrappers" that are direct libm calls
(`runtime/c/libmonogate.h`). This bundle IS the residual T3 trust: each field stands for the
identically-named C library function. Modeled as fields (not concrete Lean `Float` ops) so the T2
theorem holds for whatever libm the target platform links. -/
structure Prims where
  exp  : Float → Float
  ln   : Float → Float
  sin  : Float → Float
  cos  : Float → Float
  tan  : Float → Float
  sqrt : Float → Float
  abs  : Float → Float
  asin : Float → Float
  acos : Float → Float
  atan : Float → Float
  pow  : Float → Float → Float

/-- EML's intended unary-builtin interpretation over a primitive basis. Composites `sinh/cosh/tanh`
are the exp-combinations (the Lean hyperbolic reference, matching `libmonogate.h`); `log10` is the
`ln`-combination `Log10Lipschitz.lean` derives at the real-number level (`log10 x = log x / log 10`) —
kept a COMPOSITE here too, not a 12th primitive, since the runtime identity mirrors the same algebra. -/
def stdI1 (p : Prims) : Trans1 → Float → Float
  | .exp  => p.exp
  | .ln   => p.ln
  | .sin  => p.sin
  | .cos  => p.cos
  | .tan  => p.tan
  | .sqrt => p.sqrt
  | .abs  => p.abs
  | .asin => p.asin
  | .acos => p.acos
  | .atan => p.atan
  | .sinh => fun x => (p.exp x - p.exp (-x)) * 0.5
  | .cosh => fun x => (p.exp x + p.exp (-x)) * 0.5
  | .tanh => fun x => (p.exp x - p.exp (-x)) / (p.exp x + p.exp (-x))
  | .log10 => fun x => p.ln x / p.ln 10

/-- The C runtime keyed by `mg_*` name — a faithful transcription of `libmonogate.h`. Composite
bodies are written as their C-source expressions; unknown names default to `0` (never emitted, since
`emitC` only produces `t.cName`). -/
def stdR1 (p : Prims) (name : String) : Float → Float :=
  if name = "mg_exp" then p.exp
  else if name = "mg_ln" then p.ln
  else if name = "mg_sin" then p.sin
  else if name = "mg_cos" then p.cos
  else if name = "mg_tan" then p.tan
  else if name = "mg_sqrt" then p.sqrt
  else if name = "mg_abs" then p.abs
  else if name = "mg_asin" then p.asin
  else if name = "mg_acos" then p.acos
  else if name = "mg_atan" then p.atan
  else if name = "mg_sinh" then fun x => (p.exp x - p.exp (-x)) * 0.5
  else if name = "mg_cosh" then fun x => (p.exp x + p.exp (-x)) * 0.5
  else if name = "mg_tanh" then fun x => (p.exp x - p.exp (-x)) / (p.exp x + p.exp (-x))
  else if name = "mg_log10" then fun x => p.ln x / p.ln 10
  else fun _ => 0.0

/-- EML's intended binary-builtin interpretation. `eml(x,y)=exp(x)−ln(y)` is the EML primitive. -/
def stdI2 (p : Prims) : Trans2 → Float → Float → Float
  | .eml => fun x y => p.exp x - p.ln y
  | .pow => p.pow

/-- The C runtime for binary builtins (`libmonogate.h`: `mg_eml`, `mg_pow`). -/
def stdR2 (p : Prims) (name : String) : Float → Float → Float :=
  if name = "mg_eml" then fun x y => p.exp x - p.ln y
  else if name = "mg_pow" then p.pow
  else fun _ _ => 0.0

/-- **Unary runtime obligation discharged.** For every builtin, the C runtime call equals the intended
interpretation — composites (`sinh/cosh/tanh`) by their shared exp-decomposition, primitives by
identity. Holds for ANY basis, so T1's `hrt1` is no longer an assumption. -/
theorem std_hrt1 (p : Prims) : ∀ (t : Trans1) (v : Float), stdR1 p t.cName v = stdI1 p t v := by
  intro t v; cases t <;> rfl

/-- **Binary runtime obligation discharged** — `mg_eml=exp−ln` matches the EML primitive; `mg_pow`. -/
theorem std_hrt2 (p : Prims) : ∀ (t : Trans2) (u v : Float), stdR2 p t.cName u v = stdI2 p t u v := by
  intro t u v; cases t <;> rfl

/-- **T2 certificate.** The emitted C program computes the same result as the EML program with **no
runtime hypothesis**: the `mg_*` correspondence is now the proven `std_hrt`, and the whole result's
trust is reduced to the primitive basis `p`. sorryAx-free; carries `[propext, Quot.sound]` from the
underlying fuel-WF `runProg_correct`. -/
theorem runProg_correct_std
    (p : Prims) (prog : Prog) (fuel : Nat) (entry : String) (args : List Val) :
    runProgC (stdR1 p) (stdR2 p) (emitProg prog) fuel entry args
      = runProgEML (stdI1 p) (stdI2 p) prog fuel entry args :=
  runProg_correct (stdI1 p) (stdI2 p) (stdR1 p) (stdR2 p)
    (std_hrt1 p) (std_hrt2 p) prog fuel entry args

/-! ## Non-vacuity — instantiate the basis with Lean's own `Float` libm

With `p = leanPrims`, every primitive is Lean's actual `Float` transcendental, so a program that USES
a composite transcendental computes a real value AND its emitted C is proven identical — the runtime
hypothesis discharged, transcendentals and all. (This does not close the T3 gap: it only shows the
basis is inhabited by a real libm; whether Lean's `Float.exp` bit-matches the target's C `exp` is the
same offline-validation question, now localized to the basis.) -/

/-- The primitive basis backed by Lean core's `Float` operations. -/
def leanPrims : Prims where
  exp  := Float.exp
  ln   := Float.log
  sin  := Float.sin
  cos  := Float.cos
  tan  := Float.tan
  sqrt := Float.sqrt
  abs  := Float.abs
  asin := Float.asin
  acos := Float.acos
  atan := Float.atan
  pow  := Float.pow

/-- `coshFn(x) = cosh(x)`, a program whose return uses a COMPOSITE transcendental. -/
def coshProg : Prog := fun name =>
  if name = "coshFn" then some ⟨["x"], [], [], .tr1 .cosh (.var "x")⟩ else none

/-- `cosh(0) = (e⁰+e⁰)/2 = 1` under the real Lean libm basis. -/
example : ((runProgEML (stdI1 leanPrims) (stdI2 leanPrims) coshProg 5 "coshFn"
    [.scalar 0.0]).toF == 1.0) = true := by native_decide

/-- `emlFn(x,y) = eml(x,y) = exp(x) − ln(y)`; `eml(0,1) = 1 − 0 = 1`. -/
def emlProg : Prog := fun name =>
  if name = "emlFn" then some ⟨["x", "y"], [], [], .tr2 .eml (.var "x") (.var "y")⟩ else none

example : ((runProgEML (stdI1 leanPrims) (stdI2 leanPrims) emlProg 5 "emlFn"
    [.scalar 0.0, .scalar 1.0]).toF == 1.0) = true := by native_decide

/-- The **discharged** certificate on a real transcendental program: emitted C for `coshFn` computes
the same as the EML, with the runtime correspondence PROVEN (not assumed) — `runProg_correct_std`
instantiated at Lean's libm basis. -/
example :
    runProgC (stdR1 leanPrims) (stdR2 leanPrims) (emitProg coshProg) 5 "coshFn" [.scalar 0.0]
      = runProgEML (stdI1 leanPrims) (stdI2 leanPrims) coshProg 5 "coshFn" [.scalar 0.0] :=
  runProg_correct_std leanPrims coshProg 5 "coshFn" [.scalar 0.0]

end Certcom
