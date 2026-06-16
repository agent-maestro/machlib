import MachLib.MultiPoly
import MachLib.PolynomialEvidence
import MachLib.Exp
import MachLib.MultiPolyCanonYN
import MachLib.PfaffianFnBound
import MachLib.KhovanskiiReduction
import MachLib.SingleExpKhovanskii

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

/-! ## Inductive case eval correctness — via List.map and eval_dropLastY

For chain length N+1, the bridge composes IH (chainEval on dropped
coefficients = eval on dropped coefficients) with eval_dropLastY (in
restricted env = in full env, given y-freeness) and the
sumWithPowers ↔ listEvalAuxN bridge. -/

/-- Helper: `sumWithPowers` over `(coeffs.map dropLastY).map eval` equals
the same over `coeffs.map eval`, when all entries are y-free. The bridge
between "evaluated dropped coefficient in restricted env" and "evaluated
original in full env". -/
theorem sumWithPowers_map_dropLastY_eval_eq_sumWithPowers_map_eval
    {N : Nat} (coeffs : List (MultiPoly (N + 1)))
    (h_free : ∀ c ∈ coeffs,
      MultiPoly.degreeY (MultiPoly.lastIdx N) c = 0)
    (k : Nat) (x : MachLib.Real) (env : Fin (N + 1) → MachLib.Real) :
    sumWithPowers
      ((coeffs.map MultiPoly.dropLastY).map
        (fun d => MultiPoly.eval d x
          (fun i => env ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)))
      k (env ⟨N, Nat.lt_succ_self N⟩) =
    sumWithPowers
      (coeffs.map (fun c => MultiPoly.eval c x env))
      k (env ⟨N, Nat.lt_succ_self N⟩) := by
  induction coeffs generalizing k with
  | nil =>
    show (0 : MachLib.Real) = 0
    rfl
  | cons c rest ih =>
    show MultiPoly.eval (MultiPoly.dropLastY c) x
          (fun i => env ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) *
         iterMul (env ⟨N, Nat.lt_succ_self N⟩) k +
         sumWithPowers
           ((rest.map MultiPoly.dropLastY).map
             (fun d => MultiPoly.eval d x
               (fun i => env ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)))
           (k + 1) (env ⟨N, Nat.lt_succ_self N⟩) =
         MultiPoly.eval c x env *
         iterMul (env ⟨N, Nat.lt_succ_self N⟩) k +
         sumWithPowers
           (rest.map (fun c => MultiPoly.eval c x env))
           (k + 1) (env ⟨N, Nat.lt_succ_self N⟩)
    have h_c_free : MultiPoly.degreeY (MultiPoly.lastIdx N) c = 0 :=
      h_free c (List.mem_cons_self _ _)
    have h_rest_free :
        ∀ c' ∈ rest, MultiPoly.degreeY (MultiPoly.lastIdx N) c' = 0 := by
      intro c' hc'
      exact h_free c' (List.mem_cons_of_mem _ hc')
    rw [MultiPoly.eval_dropLastY c h_c_free x env, ih h_rest_free (k + 1)]

/-- **The capstone bridge theorem**: `chainEval N (multiPolyToChainExpPolyT N p) x env =
MultiPoly.eval p x env`. Proven by induction on N. -/
theorem chainEval_multiPolyToChainExpPolyT :
    ∀ (N : Nat) (p : MultiPoly N) (x : MachLib.Real)
      (env : Fin N → MachLib.Real),
    chainEval N (multiPolyToChainExpPolyT N p) x env =
    MultiPoly.eval p x env
  | 0,     p, x, env => chainEval_multiPolyToChainExpPolyT_zero p x env
  | N + 1, p, x, env => by
    rw [multiPolyToChainExpPolyT_succ, chainEval_succ, List.map_map]
    -- Apply IH per entry via List.map_congr_left.
    have h_ih_pointwise :
        ((fun c => chainEval N c x
          (fun i => env ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩))
            ∘ multiPolyToChainExpPolyT N) =
        (fun d => MultiPoly.eval d x
          (fun i => env ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)) := by
      funext d
      exact chainEval_multiPolyToChainExpPolyT N d x _
    rw [h_ih_pointwise]
    -- Unfold yCoeffsAtLast_dropped + dropLastY per entry.
    show sumWithPowers
          (((MultiPoly.yCoeffsAt (MultiPoly.lastIdx N) p).map MultiPoly.dropLastY).map
            (fun d => MultiPoly.eval d x
              (fun i => env ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)))
          0 (env ⟨N, Nat.lt_succ_self N⟩) =
         MultiPoly.eval p x env
    rw [sumWithPowers_map_dropLastY_eval_eq_sumWithPowers_map_eval
          (MultiPoly.yCoeffsAt (MultiPoly.lastIdx N) p)
          (MultiPoly.yCoeffsAt_entries_degreeY_zero (MultiPoly.lastIdx N) p)
          0 x env]
    -- Now use listEvalAuxN_eq_sumWithPowers_map_eval to bridge.
    -- Need to align env ⟨N, ...⟩ with env (lastIdx N). They're defeq.
    show sumWithPowers
          ((MultiPoly.yCoeffsAt (MultiPoly.lastIdx N) p).map
            (fun c => MultiPoly.eval c x env))
          0 (env (MultiPoly.lastIdx N)) =
         MultiPoly.eval p x env
    rw [← listEvalAuxN_eq_sumWithPowers_map_eval (MultiPoly.lastIdx N)
          (MultiPoly.yCoeffsAt (MultiPoly.lastIdx N) p) 0 x env]
    -- Goal: listEvalAuxN last (yCoeffsAt last p) 0 x env = MultiPoly.eval p x env
    exact MultiPoly.yCoeffsAt_last_eval p x env

/-! ## PfaffianFn over MultiExpChain correspondence

The final piece: connect `PfaffianFn over MultiExpChain N` to
`ChainExpPolyT N`. The eval correspondence falls out from the bridge
+ MultiExpChain's chainValues structure (each y_i evaluates to exp x). -/

open MachLib.PfaffianChainMod

/-- **The bridge PfaffianFn over MultiExpChain N**: any MultiPoly N
gives rise to a PfaffianFn with chain MultiExpChain N. -/
noncomputable def MultiPolyToPfaffianFn (N : Nat) (poly : MultiPoly N) :
    PfaffianFn :=
  { n := N
    chain := MultiExpChain N
    poly := poly }

theorem MultiPolyToPfaffianFn_n (N : Nat) (poly : MultiPoly N) :
    (MultiPolyToPfaffianFn N poly).n = N := rfl

theorem MultiPolyToPfaffianFn_chain (N : Nat) (poly : MultiPoly N) :
    (MultiPolyToPfaffianFn N poly).chain = MultiExpChain N := rfl

/-- **MultiExpChain's chainValues at every index = `Real.exp x`**.
Direct from the chain definition (all evals = Real.exp). -/
theorem MultiExpChain_chainValues_const (N : Nat) (x : MachLib.Real)
    (i : Fin N) :
    (MultiExpChain N).chainValues x i = Real.exp x := rfl

/-- **Bridge eval correctness**: `PfaffianFn over MultiExpChain` eval
matches `chainEval` on the bridged ChainExpPolyT, when the env is
`MultiExpChain N`'s chainValues. -/
theorem MultiPolyToPfaffianFn_eval_eq_chainEval (N : Nat)
    (poly : MultiPoly N) (x : MachLib.Real) :
    (MultiPolyToPfaffianFn N poly).eval x =
    chainEval N (multiPolyToChainExpPolyT N poly) x
      ((MultiExpChain N).chainValues x) := by
  -- (PfaffianFn over MultiExpChain N).eval x = MultiPoly.eval poly x (chain.chainValues x).
  show MultiPoly.eval poly x ((MultiExpChain N).chainValues x) =
       chainEval N (multiPolyToChainExpPolyT N poly) x
         ((MultiExpChain N).chainValues x)
  exact (chainEval_multiPolyToChainExpPolyT N poly x _).symm

/-! ## Recursive auto-bound for ChainExpPolyT

A Khovanskii-style upper bound that recursively counts:
  - chain length 0: `degreeUpper poly` (polynomial FTA bound).
  - chain length N+1: list length + Σ recursive bounds on each coefficient.

This is the multi-chain analog of `expPolyAutoBound` from
`SingleExpKhovanskii`. For chain length 1 (= List Poly), it
specializes to `length + Σ degreeUpper coeffs[i]` which matches the
single-exp track (modulo `polySimplify`). -/

/-- Recursive auto-bound for ChainExpPolyT N. -/
noncomputable def chainExpPolyAutoBound : (N : Nat) → ChainExpPolyT N → Nat
  | 0,     p      => PolynomialRootCount.degreeUpper p
  | _ + 1, coeffs =>
      coeffs.length + (coeffs.map (chainExpPolyAutoBound _)).foldr (· + ·) 0

theorem chainExpPolyAutoBound_zero (p : Poly) :
    chainExpPolyAutoBound 0 p = PolynomialRootCount.degreeUpper p := rfl

theorem chainExpPolyAutoBound_succ {N : Nat}
    (coeffs : ChainExpPolyT (N + 1)) :
    chainExpPolyAutoBound (N + 1) coeffs =
    coeffs.length +
      (coeffs.map (chainExpPolyAutoBound N)).foldr (· + ·) 0 := rfl

/-! ## Bound theorem — chain length 0 base case

For a PfaffianFn over `MultiExpChain 0` (chain length 0, no chain
variables), the eval is a polynomial in x, and the bound follows
directly from `PolynomialRootCount.poly_root_count_bound`. -/

/-- **Bound for chain length 0**: zero count ≤ chainExpPolyAutoBound. -/
theorem MultiExp_zero_count_bound_zero (poly : MultiPoly 0)
    (a b : MachLib.Real) (hab : a < b)
    (hne : ∃ x : MachLib.Real,
      (MultiPolyToPfaffianFn 0 poly).eval x ≠ 0) :
    ∀ zeros : List MachLib.Real,
      zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧
        (MultiPolyToPfaffianFn 0 poly).eval z = 0) →
      zeros.length ≤
      chainExpPolyAutoBound 0 (multiPolyToChainExpPolyT 0 poly) := by
  intro zeros hnodup hzeros
  -- Translate eval through the bridge: f.eval z = Poly.eval (multiPolyToPoly poly) z.
  have h_eval_bridge :
      ∀ z : MachLib.Real,
        (MultiPolyToPfaffianFn 0 poly).eval z =
        Poly.eval (MachLib.PfaffianFnBound.multiPolyToPoly poly) z := by
    intro z
    show MultiPoly.eval poly z ((MultiExpChain 0).chainValues z) =
         Poly.eval (MachLib.PfaffianFnBound.multiPolyToPoly poly) z
    exact (MachLib.PfaffianFnBound.multiPolyToPoly_eval rfl poly z _).symm
  -- Translate hne to Poly form.
  have hne_poly : ∃ x : MachLib.Real,
      Poly.eval (MachLib.PfaffianFnBound.multiPolyToPoly poly) x ≠ 0 := by
    obtain ⟨x, hx⟩ := hne
    refine ⟨x, ?_⟩
    rw [← h_eval_bridge x]
    exact hx
  -- Translate zeros to Poly form.
  have hzeros_poly : ∀ z ∈ zeros,
      a < z ∧ z < b ∧
      Poly.eval (MachLib.PfaffianFnBound.multiPolyToPoly poly) z = 0 := by
    intro z hz
    obtain ⟨ha, hb, heval⟩ := hzeros z hz
    refine ⟨ha, hb, ?_⟩
    rw [← h_eval_bridge z]
    exact heval
  -- Apply poly_root_count_bound + match the bound to chainExpPolyAutoBound.
  show zeros.length ≤
       chainExpPolyAutoBound 0
         (MachLib.PfaffianFnBound.multiPolyToPoly poly)
  show zeros.length ≤
       PolynomialRootCount.degreeUpper
         (MachLib.PfaffianFnBound.multiPolyToPoly poly)
  exact PolynomialRootCount.poly_root_count_bound
          (MachLib.PfaffianFnBound.multiPolyToPoly poly)
          a b hab hne_poly zeros hnodup hzeros_poly

/-! ## Bridge to SingleExp: chain length 1 unfolds to `List Poly` bound

For `N = 1` (= List Poly = `ExpPoly.coeffs`), the recursive
`chainExpPolyAutoBound` unfolds to `length + Σ degreeUpper`. This
matches SingleExpKhovanskii's auto-bound structure (modulo
`polySimplify`, which gives a tighter bound but the same shape). -/

theorem chainExpPolyAutoBound_one_unfold (coeffs : List Poly) :
    chainExpPolyAutoBound 1 coeffs =
    coeffs.length +
    (coeffs.map PolynomialRootCount.degreeUpper).foldr (· + ·) 0 := rfl

/-! ## Structural length lemma for multiPolyToChainExpPolyT

The length of the recursive bridge's output at N+1 equals the length
of `yCoeffsAt last` applied to the input. Useful for the inductive
bound argument: the outer list length is preserved through the
bridge. -/

theorem multiPolyToChainExpPolyT_succ_length {N : Nat}
    (p : MultiPoly (N + 1)) :
    (multiPolyToChainExpPolyT (N + 1) p).length =
    (MultiPoly.yCoeffsAt (MultiPoly.lastIdx N) p).length := by
  rw [multiPolyToChainExpPolyT_succ]
  show ((MultiPoly.yCoeffsAtLast_dropped p).map _).length =
       (MultiPoly.yCoeffsAt (MultiPoly.lastIdx N) p).length
  rw [List.length_map]
  show ((MultiPoly.yCoeffsAt (MultiPoly.lastIdx N) p).map _).length =
       (MultiPoly.yCoeffsAt (MultiPoly.lastIdx N) p).length
  rw [List.length_map]

/-! ## Real-level iterMul ↔ exp identity

The Real-level `iterMul (exp x) k = exp((natCast k) * x)` identity.
This connects `chainEval`'s iterated-mul evaluator (with `env i = exp x`)
to ExpPoly's `exp(k · x)` evaluator. Inductive proof using
`Real.exp_add`. -/

theorem iterMul_exp_eq_exp_natCast_mul (x : MachLib.Real) (k : Nat) :
    iterMul (Real.exp x) k = Real.exp ((Real.natCast k) * x) := by
  induction k with
  | zero =>
    show (1 : MachLib.Real) = Real.exp (Real.natCast 0 * x)
    rw [Real.natCast_zero, Real.zero_mul, Real.exp_zero]
  | succ k ih =>
    show Real.exp x * iterMul (Real.exp x) k =
         Real.exp (Real.natCast (k + 1) * x)
    rw [ih, Real.natCast_succ, Real.mul_distrib_right, Real.one_mul_thm,
        Real.exp_add, Real.mul_comm]

/-! ## chainEval at chain length 1 = ExpPoly eval

For `coeffs : List Poly = ChainExpPolyT 1`, `chainEval 1` matches
SingleExpKhovanskii's `evalAux` evaluator when the env's single
y-variable is `exp x`. This bridges the multi-chain framework's
chain-length-1 case to the existing single-exp track. -/

theorem sumWithPowers_eq_evalAux_when_env_is_exp
    (coeffs : List Poly) (k : Nat) (x : MachLib.Real) :
    sumWithPowers (coeffs.map (fun p => Poly.eval p x)) k (Real.exp x) =
    MachLib.SingleExpKhovanskii.ExpPoly.evalAux coeffs k x := by
  induction coeffs generalizing k with
  | nil =>
    show (0 : MachLib.Real) = 0
    rfl
  | cons p rest ih =>
    show Poly.eval p x * iterMul (Real.exp x) k +
         sumWithPowers (rest.map (fun p => Poly.eval p x))
                       (k + 1) (Real.exp x) =
         Poly.eval p x * Real.exp ((Real.natCast k) * x) +
         MachLib.SingleExpKhovanskii.ExpPoly.evalAux rest (k + 1) x
    rw [iterMul_exp_eq_exp_natCast_mul, ih (k + 1)]

/-- **chainEval 1 = ExpPoly.eval bridge**: when env 0 = exp x, the
chain-length-1 nested evaluator coincides with ExpPoly's `evalAux`. -/
theorem chainEval_one_eq_evalAux (coeffs : List Poly) (x : MachLib.Real)
    (env : Fin 1 → MachLib.Real) (h_env : env 0 = Real.exp x) :
    chainEval 1 coeffs x env =
    MachLib.SingleExpKhovanskii.ExpPoly.evalAux coeffs 0 x := by
  show sumWithPowers (coeffs.map (fun p => chainEval 0 p x _)) 0 (env 0) =
       MachLib.SingleExpKhovanskii.ExpPoly.evalAux coeffs 0 x
  have h_map :
      coeffs.map (fun p => chainEval 0 p x
        (fun i => env ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)) =
      coeffs.map (fun p => Poly.eval p x) := by
    apply List.map_congr_left
    intro p _
    exact chainEval_zero p x _
  rw [h_map, h_env]
  exact sumWithPowers_eq_evalAux_when_env_is_exp coeffs 0 x

/-! ## Bound comparison: chainExpPolyAutoBound 1 ≥ ExpPoly's autoBound

The multi-chain bound at chain length 1 (using raw `degreeUpper`) is
weaker than (but ≥) SingleExpKhovanskii's bound (using
`degreeUpper · polySimplify`). This means any ExpPoly bound transfers
to a multi-chain bound. -/

theorem sumSimplifiedDegrees_le_sum_degreeUpper (coeffs : List Poly) :
    MachLib.SingleExpKhovanskii.ExpPoly.sumSimplifiedDegrees coeffs ≤
    (coeffs.map PolynomialRootCount.degreeUpper).foldr (· + ·) 0 := by
  induction coeffs with
  | nil =>
    show (0 : Nat) ≤ 0
    exact Nat.le_refl 0
  | cons p rest ih =>
    show PolynomialRootCount.degreeUpper
           (MachLib.PolynomialRootCount.polySimplify p) +
         MachLib.SingleExpKhovanskii.ExpPoly.sumSimplifiedDegrees rest ≤
         PolynomialRootCount.degreeUpper p +
         (rest.map PolynomialRootCount.degreeUpper).foldr (· + ·) 0
    have h_p : PolynomialRootCount.degreeUpper
                 (MachLib.PolynomialRootCount.polySimplify p) ≤
               PolynomialRootCount.degreeUpper p :=
      MachLib.PolynomialRootCount.degreeUpper_polySimplify_le_self p
    exact Nat.add_le_add h_p ih

theorem ExpPoly_M_le_chainExpPolyAutoBound_one (coeffs : List Poly) :
    coeffs.length +
    MachLib.SingleExpKhovanskii.ExpPoly.sumSimplifiedDegrees coeffs ≤
    chainExpPolyAutoBound 1 coeffs := by
  rw [chainExpPolyAutoBound_one_unfold]
  exact Nat.add_le_add_left
    (sumSimplifiedDegrees_le_sum_degreeUpper coeffs) _

/-! ## Multi-chain Khovanskii sprint summary (substrate complete)

After 8 commits in this push chain (e3d2617 → b5cc2d7), the
constructive substrate for multi-chain Khovanskii over `MultiExpChain N`
is fully in place. The end-to-end picture:

  Any MultiPoly N polynomial poly
       ↓ MultiPolyToPfaffianFn N (wraps with MultiExpChain N)
  PfaffianFn over MultiExpChain N
       ↓ .eval x
  Real value = MultiPoly.eval poly x ((MultiExpChain N).chainValues x)
       ↓ chainEval_multiPolyToChainExpPolyT (eval bridge)
       ↓ chainEval N (multiPolyToChainExpPolyT N poly) x (chainValues x)
       ↓
  Zero count bounded by chainExpPolyAutoBound N (multiPolyToChainExpPolyT N poly)
  (N=0 ✓ shipped; N+1 inductive step is the remaining frontier)

The N+1 inductive step requires generalizing
`expPoly_auto_bound_with_propagation_aux` (SingleExpKhovanskii) to
accept an arbitrary per-coefficient bound function. This is mechanical
~150 lines of work mirroring the existing strict-descent argument
but parameterized over the inner bound rather than using `degreeUpper · polySimplify`.

The bridge work shipped in this push gives every load-bearing piece
needed for that generalization. -/

/-! ## Inductive bound theorem statement (the next-session frontier)

The full multi-chain bound theorem:

  ∀ N, ∀ poly : MultiPoly N, ∀ a b interval, ∀ nonzero witness,
    zero count of (MultiPolyToPfaffianFn N poly).eval on (a, b) ≤
    chainExpPolyAutoBound N (multiPolyToChainExpPolyT N poly)

Proof by induction on N:
  - N=0: MultiExp_zero_count_bound_zero (shipped above).
  - N+1: composition of
    1. The bridge: PfaffianFn over MultiExpChain (N+1) evaluates as
       chainEval (N+1) of the bridged ChainExpPolyT (= layer of
       List (ChainExpPolyT N)).
    2. The outer list bound: each ChainExpPolyT N coefficient
       contributes ≤ chainExpPolyAutoBound N to the total. By IH each
       contribution is bounded; the SingleExp auto-bound-style
       argument then gives the outer list's zero count bound of
       `length + Σ inner_bounds`.

The inductive step requires generalizing SingleExpKhovanskii's
auto-bound to accept an arbitrary per-coefficient bound function
(rather than the hardcoded `degreeUpper · polySimplify`). This is
mechanical but non-trivial (~150 lines).

Once shipped, the full constructive multi-chain Khovanskii closure
ships for every triangular Pfaffian chain of the MultiExpChain form:
each y_i' = y_i with y_i = exp x. Specialization to other coefficient-
linear triangular chains (y_i' = c_i · y_i for varying c_i) is a
straightforward parameter generalization. -/

end ChainExpPolyMod
end MachLib
