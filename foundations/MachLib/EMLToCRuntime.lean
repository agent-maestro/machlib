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
  * **Composite** — defined *from* the primitives in `libmonogate.h`: `mg_eml(x,y)=exp(x)−log(y)` (the
    EML primitive itself), and the hyperbolics. Since forge `51337a3` those are built from `exp`,
    `fabs` and `copysign` so that they do not overflow before the answer does:
    `mg_tanh(x) = copysign((1−t)/(1+t), x)` with `t = exp(−2|x|)`; `mg_sinh` and `mg_cosh` take
    `(eᵃ ∓ e⁻ᵃ)·½` at `a = |x| ≤ 709.78` and `(½·w)·w` with `w = exp(a/2)` above it, and `mg_sinh`
    then takes `x`'s sign.

The move: build BOTH the runtime (`stdR1`/`stdR2`) and the EML interpretation (`stdI1`/`stdI2`) from
one shared **primitive basis** `Prims`. The composites are then written once on each side — the
runtime side transcribing the C source, the interpretation side the operator's float algorithm (which
`stdI1`'s docstring argues must be the same composition) — and their agreement (`std_hrt1`/`std_hrt2`)
is PROVEN for every basis, sorryAx-free. So the composites drop out of the trust set, and
`runProg_correct_std` is the T1 certificate with the runtime hypothesis discharged: its trust is
reduced to the enumerable primitive basis `Prims`.

**What remains trusted (the honest T3 boundary):** the 12 `Prims` fields model the corresponding C
library calls. That is a statement about C execution, not provable in Lean; grounding it is offline
libm/Flocq validation (`sqrt`, `abs` and `copysign` are IEEE-754-exact and the strongest; the
transcendentals carry a ULP gap). But it is a SHORT, NAMED list, and every COMPOSITE is discharged.
**The basis grew by one exact operation on 2026-09-13: `copysign`**, which the overflow-safe
hyperbolics call. The alternative, three more trusted transcendentals, is argued against at `stdI1`.

**Where this copy comes from, and what checks it.** `stdR1`/`stdR2` transcribe forge's
`software/runtime/c/libmonogate.h` at forge master `bd4cc0d`. The hyperbolic bodies last changed in
forge `51337a3` (2026-09-13); until that day's machlib change this file transcribed the bodies before
it. **PyPI `monogate-forge` 0.14.4**, which is what `pip install` gives a reader, still ships those
OLD bodies (`(exp(x) ± exp(-x)) * 0.5` and the quotient of the two), so C emitted by that release
computes what this file no longer describes. `std_hrt` compares the two Lean sides with each other
and never reads C. What compares `stdR1`/`stdR2` with the header is forge's
`tests/test_machlib_runtime_transcription.py` (written 2026-09-13 on forge branch
`test/machlib-runtime-copy-gate`; forge CI links this checkout as `../machlib`): it reduces each
transcribed case and each C body to an operation tree and fails on any difference. It cannot compare
`mg_log10`, because the header defines no such function: forge's C backend emits libm `log10(x)` for
`log10`, so the `"mg_log10"` case below models a call emitted C never makes.
-/

namespace Certcom

/-- The platform primitive float ops — the `mg_*` "standard math wrappers" that are direct libm calls
(`runtime/c/libmonogate.h`), plus `copysign`, which the header's hyperbolics call directly. This bundle
IS the residual T3 trust: each field stands for one C library function (`ln` is `log`, `abs` is
`fabs`; the others share the C name). Modeled as fields (not concrete Lean `Float` ops) so the T2
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
  /-- C `copysign(x, y)`: the bits of `x` with the sign bit of `y`. IEEE 754 defines it exactly (a
  quiet, non-arithmetic sign operation), as it does `abs` (`fabs`). The twelfth field, added
  2026-09-13 for the hyperbolics forge `51337a3` builds from it. -/
  copysign : Float → Float → Float

/-- EML's intended unary-builtin interpretation over a primitive basis.

**For `sinh`/`cosh`/`tanh` this is a FLOAT ALGORITHM, and it is deliberately the runtime's own.** A
float `tanh` has no canonical definition; an interpretation has to pick one. This picks the
overflow-safe composition `libmonogate.h` ships since forge `51337a3`, written exactly as `stdR1`
transcribes it. Of the ways to keep a certificate:

  * **Keep a textbook form**, `(eˣ−e⁻ˣ)/(eˣ+e⁻ˣ)`, which this definition used until 2026-09-13. The
    interpretation then disagrees with the runtime: at `1000` the quotient is NaN over `leanPrims`
    (an example at the end of this file) and the runtime gives `1.0`. So `std_hrt1` is false at
    `leanPrims` and cannot be proved.
  * **Move the hyperbolics into `Prims`** as three more trusted fields. `stdR1` must still transcribe
    the C, which never calls libm's `sinh`/`cosh`/`tanh`, so `std_hrt1` would need a hypothesis equating
    the new fields with the `exp`-composites. That weakens `runProg_correct_std`, and it adds three
    transcendentals with ULP gaps to the trust set.
  * **Adopt the runtime's composition (chosen).** The trust set grows by one IEEE-exact field,
    `copysign`; every composite stays discharged by `rfl`; `runProg_correct_std` is unchanged.

Over the reals the forms agree. Multiplying the numerator and denominator of `(eˣ−e⁻ˣ)/(eˣ+e⁻ˣ)` by
`e^−|x|` gives `sgn(x)·(1−t)/(1+t)` with `t = e^−2|x|`, exactly. The large-argument `sinh`/`cosh`
branch computes `eᵃ/2` and drops `e⁻ᵃ/2`, a relative change below `e^−1419` wherever it is taken
(`a > 709.78`). The float results differ, which is the point.

`log10` is the `ln`-combination `Log10Lipschitz.lean` derives at the real-number level
(`log10 x = log x / log 10`) — kept a COMPOSITE here too, not a primitive, since the runtime identity
mirrors the same algebra. -/
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
  | .sinh => fun x =>
      let a := p.abs x;
      p.copysign (if a > 709.78 then (let w := p.exp (0.5 * a); (0.5 * w) * w)
        else (p.exp a - p.exp (-a)) * 0.5) x
  | .cosh => fun x =>
      let a := p.abs x;
      if a > 709.78 then (let w := p.exp (0.5 * a); (0.5 * w) * w)
      else (p.exp a + p.exp (-a)) * 0.5
  | .tanh => fun x =>
      let t := p.exp ((-2.0) * p.abs x);
      p.copysign ((1.0 - t) / (1.0 + t)) x
  | .log10 => fun x => p.ln x / p.ln 10

/-- The C runtime keyed by `mg_*` name — a transcription of `libmonogate.h` at forge `bd4cc0d` (the
module docstring says what checks it and what it cannot). Composite bodies are the C bodies over the
basis: a C local is a `let`, `if (a > MG_EXP_ARG_MAX)` is `if a > 709.78` (the macro's value, whose
bits are pinned at the end of this file), `fabs` is `p.abs` and `copysign` is `p.copysign`. Write a
`let` with `;` rather than a line break: that is the form forge's gate reads. Unknown names default to
`0` (never emitted, since `emitC` only produces `t.cName`). -/
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
  else if name = "mg_sinh" then fun x =>
      let a := p.abs x;
      p.copysign (if a > 709.78 then (let w := p.exp (0.5 * a); (0.5 * w) * w)
        else (p.exp a - p.exp (-a)) * 0.5) x
  else if name = "mg_cosh" then fun x =>
      let a := p.abs x;
      if a > 709.78 then (let w := p.exp (0.5 * a); (0.5 * w) * w)
      else (p.exp a + p.exp (-a)) * 0.5
  else if name = "mg_tanh" then fun x =>
      let t := p.exp ((-2.0) * p.abs x);
      p.copysign ((1.0 - t) / (1.0 + t)) x
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
interpretation — composites (`sinh/cosh/tanh`, `log10`) by their shared composition over the basis,
primitives by identity. Holds for ANY basis, so T1's `hrt1` is no longer an assumption. -/
theorem std_hrt1 (p : Prims) : ∀ (t : Trans1) (v : Float), stdR1 p t.cName v = stdI1 p t v := by
  intro t v; cases t <;> rfl

/-- **Binary runtime obligation discharged** — `mg_eml=exp−ln` matches the EML primitive; `mg_pow`. -/
theorem std_hrt2 (p : Prims) : ∀ (t : Trans2) (u v : Float), stdR2 p t.cName u v = stdI2 p t u v := by
  intro t u v; cases t <;> rfl

/-- **T2 certificate.** The emitted C program computes the same result as the EML program with **no
runtime hypothesis**: the `mg_*` correspondence is now the proven `std_hrt`, and the whole result's
trust is reduced to the primitive basis `p`. sorryAx-free; `#print axioms` reports
`[propext, Classical.choice, Quot.sound]` (measured 2026-09-13, before and after `copysign` joined
the basis; this docstring said `[propext, Quot.sound]` until then). -/
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

/-- `copysign` for `leanPrims`, which Lean core does not provide: IEEE 754's bit definition — the bits
of `x` with the sign bit of `y` — over `Float.toBits`/`Float.ofBits`, with no branch.

**It is not faithful on NaN, and no Lean `Float` function can be.** `Float.toBits` returns
`0x7ff8000000000000` for EVERY NaN: the v4.32.2 runtime compares the value with itself and substitutes
that constant when unordered (`lean_float_to_bits` in `libleanrt.a`, aarch64:
`fcmp d0, d0; …; csel x0, x8, x9, vs`). So Lean code cannot read a NaN's sign bit or payload.
Measured 2026-09-13 against glibc 2.39 `copysign` (aarch64, gcc 13.3 at `-O0` and `-O2`): bit-identical
on all 154 tested pairs in which neither argument is a NaN (`±0`, `±1`, `±∞`, the smallest subnormals,
`1.5`, `−2.5`; 100 pairs built by arithmetic, 54 from bits). Of the 42 pairs involving a NaN it
matches 13, and each of the other 29 differs because glibc's result is a NaN carrying a sign bit or
payload, or because the sign source is a negative NaN, which reads as positive here. The certificate
only ever uses the abstract `Prims.copysign`; this instance serves the examples. -/
def floatCopySign (x y : Float) : Float :=
  Float.ofBits ((x.toBits &&& 0x7FFFFFFFFFFFFFFF) ||| (y.toBits &&& 0x8000000000000000))

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
  copysign := floatCopySign

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

/-! ## The overflow region — where the bodies before forge `51337a3` were wrong

Each example here was first run against this file's previous definitions (machlib `013ee5c0`), and
every one failed there: `tanh 1000` was NaN, `sinh 710` and `cosh 710` were `inf`, and `tanh (-0.0)`
was `+0.0`. -/

/-- `tanhFn(x) = tanh(x)`. -/
def tanhProg : Prog := fun name =>
  if name = "tanhFn" then some ⟨["x"], [], [], .tr1 .tanh (.var "x")⟩ else none

/-- `sinhFn(x) = sinh(x)`. -/
def sinhProg : Prog := fun name =>
  if name = "sinhFn" then some ⟨["x"], [], [], .tr1 .sinh (.var "x")⟩ else none

/-- `tanh(1000) = 1.0`. The quotient this replaced divided `inf` by `inf`. -/
example : ((runProgEML (stdI1 leanPrims) (stdI2 leanPrims) tanhProg 5 "tanhFn"
    [.scalar 1000.0]).toF == 1.0) = true := by native_decide

/-- The same on the emitted-C side, through the transcription `stdR1` itself. -/
example : ((runProgC (stdR1 leanPrims) (stdR2 leanPrims) (emitProg tanhProg) 5 "tanhFn"
    [.scalar 1000.0]).toF == 1.0) = true := by native_decide

/-- `sinh(710)` is finite (about `1.117e308`); `exp 710 − exp (−710)` was `inf`. -/
example : (let v := (runProgEML (stdI1 leanPrims) (stdI2 leanPrims) sinhProg 5 "sinhFn"
    [.scalar 710.0]).toF; v.isFinite && decide (1.0e308 < v)) = true := by native_decide

/-- `cosh(710)` is finite in the same way. -/
example : (let v := (runProgEML (stdI1 leanPrims) (stdI2 leanPrims) coshProg 5 "coshFn"
    [.scalar 710.0]).toF; v.isFinite && decide (1.0e308 < v)) = true := by native_decide

/-- `tanh(-0.0)` is `-0.0`: the result's sign bit is set. The quotient gave `+0.0`. -/
example : ((runProgEML (stdI1 leanPrims) (stdI2 leanPrims) tanhProg 5 "tanhFn"
    [.scalar (-0.0)]).toF.toBits == 0x8000000000000000) = true := by native_decide

/-- For contrast: the textbook quotient `stdI1` used until 2026-09-13, over the same basis, IS NaN at
`1000`. This is why that form could not stay once the runtime changed (see `stdI1`). -/
example : (let q : Float → Float := fun x =>
    (leanPrims.exp x - leanPrims.exp (-x)) / (leanPrims.exp x + leanPrims.exp (-x));
  (q 1000.0).isNaN) = true := by native_decide

/-- `MG_EXP_ARG_MAX = 709.78` as Lean elaborates the literal: the correctly rounded double, the bits a
C compiler gives the same spelling. Forge's gate requires a pin like this for every transcribed
literal that no double represents exactly, because `Float.ofScientific` is not assumed to round like C. -/
example : (709.78 : Float).toBits = 0x40862E3D70A3D70A := by native_decide

end Certcom
