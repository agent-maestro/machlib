import MachLib.MultiPoly
import MachLib.PolynomialEvidence
import MachLib.Exp
import MachLib.MultiPolyCanonYN
import MachLib.PfaffianFnBound

/-!
# MachLib.ChainExpPoly — nested ExpPoly-like representation for arbitrary chain length

Generalizes `ExpPoly` (single-exp, length-1 chain) to arbitrary chain
length N via a type-level recursive definition (not an inductive,
since Lean's kernel disallows nested inductive types parameterized
by local variables).

  `ChainExpPolyT 0 = Poly` (univariate polynomial in x).
  `ChainExpPolyT (N+1) = List (ChainExpPolyT N)` (polynomial in y_{N+1}
    with coefficients in the smaller chain).

So `ChainExpPolyT 1 = List Poly = ExpPoly.coeffs` — the bridge to the
single-exp track.
-/

namespace MachLib
namespace ChainExpPolyMod

open MachLib.PolynomialEvidence

/-- The nested type for chain length N. -/
def ChainExpPolyT : Nat → Type
  | 0     => Poly
  | N + 1 => List (ChainExpPolyT N)

/-- Iterated multiplication: `iterMul y k = y · y · ... · y` (k times). -/
noncomputable def iterMul (y : MachLib.Real) : Nat → MachLib.Real
  | 0     => 1
  | k + 1 => y * iterMul y k

theorem iterMul_zero (y : MachLib.Real) : iterMul y 0 = 1 := rfl

theorem iterMul_succ (y : MachLib.Real) (k : Nat) :
    iterMul y (k + 1) = y * iterMul y k := rfl

/-- Sum a list of `Real` values weighted by powers of `y_val`:
`r_0 + r_1 · y + r_2 · y^2 + ...`. -/
noncomputable def sumWithPowers :
    List MachLib.Real → Nat → MachLib.Real → MachLib.Real
  | [],         _, _     => 0
  | r :: rest, k, y_val =>
      r * iterMul y_val k + sumWithPowers rest (k + 1) y_val

theorem sumWithPowers_nil (k : Nat) (y_val : MachLib.Real) :
    sumWithPowers [] k y_val = 0 := rfl

theorem sumWithPowers_cons (r : MachLib.Real) (rest : List MachLib.Real)
    (k : Nat) (y_val : MachLib.Real) :
    sumWithPowers (r :: rest) k y_val =
    r * iterMul y_val k + sumWithPowers rest (k + 1) y_val := rfl

/-- Eval a `ChainExpPolyT N` at `x : Real` with env `Fin N → Real`.
Structurally recursive on N. -/
noncomputable def chainEval : (N : Nat) → ChainExpPolyT N →
    MachLib.Real → (Fin N → MachLib.Real) → MachLib.Real
  | 0,     p,      x, _   => Poly.eval p x
  | N + 1, coeffs, x, env =>
      sumWithPowers
        (coeffs.map (fun c => chainEval N c x
          (fun i => env ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)))
        0
        (env ⟨N, Nat.lt_succ_self N⟩)

theorem chainEval_zero (p : Poly) (x : MachLib.Real)
    (env : Fin 0 → MachLib.Real) :
    chainEval 0 p x env = Poly.eval p x := rfl

theorem chainEval_succ {N : Nat} (coeffs : ChainExpPolyT (N + 1))
    (x : MachLib.Real) (env : Fin (N + 1) → MachLib.Real) :
    chainEval (N + 1) coeffs x env =
    sumWithPowers
      (coeffs.map (fun c => chainEval N c x
        (fun i => env ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)))
      0
      (env ⟨N, Nat.lt_succ_self N⟩) := rfl

/-! ## Bridge to ExpPoly: ChainExpPolyT 1 is essentially ExpPoly's coeffs

A `ChainExpPolyT 1` is a `List (ChainExpPolyT 0) = List Poly`, which
matches the coefficient structure of `SingleExpKhovanskii.ExpPoly`.
The chain length-1 case of the multi-chain framework specializes to
the single-exp case shipped in `ExpPolyBridge`. -/

theorem ChainExpPolyT_zero : ChainExpPolyT 0 = Poly := rfl

theorem ChainExpPolyT_one : ChainExpPolyT 1 = List Poly := rfl

theorem ChainExpPolyT_succ (N : Nat) :
    ChainExpPolyT (N + 1) = List (ChainExpPolyT N) := rfl

/-! ## Bridge MultiPoly N → ChainExpPolyT N

The recursive bridge: for chain length 0, use `multiPolyToPoly`
(from PfaffianFnBound). For chain length N+1, decompose via
`yCoeffsAtLast_dropped` to get a `List (MultiPoly N)`, then recurse
on each element to get a `List (ChainExpPolyT N) = ChainExpPolyT (N+1)`.

This is the multi-chain analog of `ExpPoly.toMultiPoly1`'s inverse
direction. -/

open MachLib.MultiPolyMod (MultiPoly)
open MachLib.MultiPolyMod.MultiPoly

/-- **The recursive bridge**: convert a `MultiPoly N` into a
`ChainExpPolyT N` by structural recursion on N. -/
noncomputable def multiPolyToChainExpPolyT : (N : Nat) → MultiPoly N →
    ChainExpPolyT N
  | 0,     p => MachLib.PfaffianFnBound.multiPolyToPoly p
  | N + 1, p =>
      (yCoeffsAtLast_dropped p).map (multiPolyToChainExpPolyT N)

theorem multiPolyToChainExpPolyT_zero (p : MultiPoly 0) :
    multiPolyToChainExpPolyT 0 p = MachLib.PfaffianFnBound.multiPolyToPoly p := rfl

theorem multiPolyToChainExpPolyT_succ {N : Nat} (p : MultiPoly (N + 1)) :
    multiPolyToChainExpPolyT (N + 1) p =
    (yCoeffsAtLast_dropped p).map (multiPolyToChainExpPolyT N) := rfl

/-! ## iterMul ↔ MultiPoly.pow(varY) bridge

`iterMul (env i) k` (the eval-side iterated multiplication used by
`chainEval`) coincides with `MultiPoly.eval (pow (varY i) k) x env`
(the polynomial-side iterated power). Inductive proof. -/

theorem iterMul_eq_eval_pow_varY {n : Nat} (i : Fin n) (k : Nat)
    (x : MachLib.Real) (env : Fin n → MachLib.Real) :
    iterMul (env i) k =
    MultiPoly.eval (MultiPoly.pow (MultiPoly.varY i) k) x env := by
  induction k with
  | zero =>
    show (1 : MachLib.Real) =
         MultiPoly.eval (MultiPoly.pow (MultiPoly.varY i) 0) x env
    rw [MultiPoly.eval_pow_zero]
  | succ k ih =>
    show env i * iterMul (env i) k =
         MultiPoly.eval (MultiPoly.pow (MultiPoly.varY i) (k + 1)) x env
    rw [MultiPoly.eval_pow_succ, ih]
    rfl

/-! ## Base case eval correctness -/

theorem chainEval_multiPolyToChainExpPolyT_zero (p : MultiPoly 0)
    (x : MachLib.Real) (env : Fin 0 → MachLib.Real) :
    chainEval 0 (multiPolyToChainExpPolyT 0 p) x env =
    MultiPoly.eval p x env := by
  rw [multiPolyToChainExpPolyT_zero, chainEval_zero]
  exact MachLib.PfaffianFnBound.multiPolyToPoly_eval rfl p x env

/-! ## listEvalAuxN ↔ sumWithPowers bridge

The two evaluators connect via the iterMul ↔ pow identity (when the
coefficients are evaluated to Real values first). This is the
conversion lemma needed for the inductive case of the eval correctness
theorem. -/

theorem listEvalAuxN_eq_sumWithPowers_map_eval {n : Nat} (i : Fin n)
    (coeffs : List (MultiPoly n)) (k : Nat)
    (x : MachLib.Real) (env : Fin n → MachLib.Real) :
    MultiPoly.listEvalAuxN i coeffs k x env =
    sumWithPowers (coeffs.map (fun c => MultiPoly.eval c x env)) k (env i) := by
  induction coeffs generalizing k with
  | nil =>
    show (0 : MachLib.Real) = 0
    rfl
  | cons c rest ih =>
    show MultiPoly.eval c x env *
         MultiPoly.eval (MultiPoly.pow (MultiPoly.varY i) k) x env +
         MultiPoly.listEvalAuxN i rest (k + 1) x env =
         MultiPoly.eval c x env * iterMul (env i) k +
         sumWithPowers (rest.map (fun c => MultiPoly.eval c x env))
                       (k + 1) (env i)
    rw [← iterMul_eq_eval_pow_varY i k x env, ih (k + 1)]

end ChainExpPolyMod
end MachLib
