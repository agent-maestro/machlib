import MachLib.MultiPolyCanonYN
import MachLib.PolynomialCanonical

/-!
# Route A, brick 1 — the Horner bridge (reduces the `y`-PIT to the existing x-PIT)

Piece 3 step 2 (the canonical inner descent) needs `cdegY0` to be an **eval-invariant** — a polynomial
identity in `y₀`. The codebase already has the x-version (`evalCoeffs_zero_iff_all_zero` /
`polyTrueDegree_eq_of_evalCoeffs_eq` on `List Real`). This file supplies the bridge that lets the x-PIT
be reused *in the `y_i` variable*:

  `listEvalN i L x env = evalCoeffs (L.map (fun c => eval c x env)) (env i)`.

The left side is `MultiPoly`'s Horner evaluation of a `y_i`-coefficient list (`Σ eval(L[k])·(env i)^k`);
the right side is the *scalar* Horner evaluation (`evalCoeffs`) of the list of coefficient-values at the
point `env i`. They are equal because both are the same polynomial in `env i`. Consequently a `y_i`
polynomial that vanishes for all `env i` has canonically-zero coefficients — the `y`-PIT — via the x-PIT.

Foundational only (about `listEvalN`/`evalCoeffs`); no chain-2 specifics, `ChainExp2SDR` + single-exp
untouched.
-/

namespace MachLib.ChainExp2YPIT

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.MultiPolyMod.MultiPoly
open MachLib.PolynomialCanonical

/-- **Aux Horner bridge** (with offset `k`): `listEvalAuxN i L k` factors as `(env i)^k` times the scalar
Horner evaluation of the coefficient-values at `env i`. Induction on `L` (generalising `k`); the `cons`
step uses `eval_pow_succ` (`(env i)^{k+1} = (env i)·(env i)^k`) and distributes. -/
theorem listEvalAuxN_eq_pow_mul_evalCoeffs_map {n : Nat} (i : Fin n)
    (L : List (MultiPoly n)) (k : Nat) (x : Real) (env : Fin n → Real) :
    listEvalAuxN i L k x env
    = MultiPoly.eval (MultiPoly.pow (MultiPoly.varY i) k) x env
      * evalCoeffs (L.map (fun c => MultiPoly.eval c x env)) (env i) := by
  induction L generalizing k with
  | nil =>
    show (0 : Real)
       = MultiPoly.eval (MultiPoly.pow (MultiPoly.varY i) k) x env * evalCoeffs [] (env i)
    rw [evalCoeffs_nil, MachLib.Real.mul_zero]
  | cons c rest ih =>
    show MultiPoly.eval c x env * MultiPoly.eval (MultiPoly.pow (MultiPoly.varY i) k) x env
           + listEvalAuxN i rest (k + 1) x env
       = MultiPoly.eval (MultiPoly.pow (MultiPoly.varY i) k) x env
         * evalCoeffs (MultiPoly.eval c x env :: rest.map (fun c => MultiPoly.eval c x env)) (env i)
    rw [ih (k + 1), evalCoeffs_cons,
        MultiPoly.eval_pow_succ (MultiPoly.varY i) k x env, MultiPoly.eval_varY]
    -- goal: ec·Pk + (Y·Pk)·R = Pk·(ec + Y·R); abstract the atoms and ring.
    generalize MultiPoly.eval c x env = ec
    generalize MultiPoly.eval (MultiPoly.pow (MultiPoly.varY i) k) x env = Pk
    generalize env i = Y
    generalize evalCoeffs (rest.map (fun c => MultiPoly.eval c x env)) (env i) = R
    mach_ring

/-- **The Horner bridge.** `listEvalN i L` (MultiPoly Horner eval of the `y_i`-coefficient list) equals the
scalar Horner evaluation `evalCoeffs` of the coefficient-values at `env i`. (`k = 0` case of the aux
lemma; `(env i)^0 = 1`.) -/
theorem listEvalN_eq_evalCoeffs_map {n : Nat} (i : Fin n)
    (L : List (MultiPoly n)) (x : Real) (env : Fin n → Real) :
    listEvalN i L x env = evalCoeffs (L.map (fun c => MultiPoly.eval c x env)) (env i) := by
  show listEvalAuxN i L 0 x env = _
  rw [listEvalAuxN_eq_pow_mul_evalCoeffs_map i L 0 x env,
      MultiPoly.eval_pow_zero (MultiPoly.varY i) x env]
  mach_ring

end MachLib.ChainExp2YPIT
