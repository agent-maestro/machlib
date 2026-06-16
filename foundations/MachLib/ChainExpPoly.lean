import MachLib.MultiPoly
import MachLib.PolynomialEvidence
import MachLib.Exp
import MachLib.MultiPolyCanonYN
import MachLib.PfaffianFnBound
import MachLib.KhovanskiiReduction

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

/-! ## Status of multi-chain Khovanskii (after this commit)

The recursive bound definition + base case (N=0) are in place. The
remaining piece for chain length N+1 is the inductive bound:
SingleExp auto-bound applied to the outer list structure, with each
coefficient's zero-count contribution bounded by the recursive
chain-length-N bound (by IH).

The substrate is fully in place: every PfaffianFn over MultiExpChain N
has a constructive ChainExpPolyT N representation with matching eval,
so the zero count analysis can proceed recursively. -/

end ChainExpPolyMod
end MachLib
