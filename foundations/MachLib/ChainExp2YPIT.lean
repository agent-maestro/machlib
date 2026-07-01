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

/-! ### Brick 2a — a `degreeY i = 0` polynomial's eval does not depend on `env i` -/

/-- If `q` has `degreeY i = 0`, its evaluation is unchanged by the `i`-th environment component: any two
environments agreeing off `i` give the same value. (Structural induction; the `varY j` case uses
`degreeY i (varY j) = 0 ⇒ j ≠ i`.) This is what lets the `y`-PIT vary `env i` freely over the (`y_i`-free)
coefficient entries. -/
theorem eval_eq_of_env_agree_off {n : Nat} (i : Fin n) (q : MultiPoly n)
    (x : Real) (env1 env2 : Fin n → Real)
    (henv : ∀ j : Fin n, j ≠ i → env1 j = env2 j) :
    MultiPoly.degreeY i q = 0 → MultiPoly.eval q x env1 = MultiPoly.eval q x env2 := by
  induction q with
  | const c => intro _; rfl
  | varX => intro _; rfl
  | varY j =>
    intro hdeg
    have hij : j ≠ i := by
      intro heq; rw [heq] at hdeg; simp [MultiPoly.degreeY] at hdeg
    show env1 j = env2 j
    exact henv j hij
  | add p q ihp ihq =>
    intro hdeg
    have h' : Nat.max (MultiPoly.degreeY i p) (MultiPoly.degreeY i q) = 0 := hdeg
    have hp : MultiPoly.degreeY i p = 0 := by
      have hle : MultiPoly.degreeY i p
               ≤ Nat.max (MultiPoly.degreeY i p) (MultiPoly.degreeY i q) := Nat.le_max_left _ _
      omega
    have hq : MultiPoly.degreeY i q = 0 := by
      have hle : MultiPoly.degreeY i q
               ≤ Nat.max (MultiPoly.degreeY i p) (MultiPoly.degreeY i q) := Nat.le_max_right _ _
      omega
    show MultiPoly.eval p x env1 + MultiPoly.eval q x env1
       = MultiPoly.eval p x env2 + MultiPoly.eval q x env2
    rw [ihp hp, ihq hq]
  | sub p q ihp ihq =>
    intro hdeg
    have h' : Nat.max (MultiPoly.degreeY i p) (MultiPoly.degreeY i q) = 0 := hdeg
    have hp : MultiPoly.degreeY i p = 0 := by
      have hle : MultiPoly.degreeY i p
               ≤ Nat.max (MultiPoly.degreeY i p) (MultiPoly.degreeY i q) := Nat.le_max_left _ _
      omega
    have hq : MultiPoly.degreeY i q = 0 := by
      have hle : MultiPoly.degreeY i q
               ≤ Nat.max (MultiPoly.degreeY i p) (MultiPoly.degreeY i q) := Nat.le_max_right _ _
      omega
    show MultiPoly.eval p x env1 - MultiPoly.eval q x env1
       = MultiPoly.eval p x env2 - MultiPoly.eval q x env2
    rw [ihp hp, ihq hq]
  | mul p q ihp ihq =>
    intro hdeg
    have h' : MultiPoly.degreeY i p + MultiPoly.degreeY i q = 0 := hdeg
    have hp : MultiPoly.degreeY i p = 0 := by omega
    have hq : MultiPoly.degreeY i q = 0 := by omega
    show MultiPoly.eval p x env1 * MultiPoly.eval q x env1
       = MultiPoly.eval p x env2 * MultiPoly.eval q x env2
    rw [ihp hp, ihq hq]

/-! ### Brick 2b — the `y`-PIT: a MultiPoly vanishing everywhere has canonically-zero `y_i`-coefficients -/

/-- **The `y`-PIT.** If `q` evaluates to `0` at every point, then every `y_i`-coefficient of `q` (each entry
of `yCoeffsAt i q`) also evaluates to `0` at every point. Proof: fix `(x, env)`; varying `env i` over the
scalar Horner polynomial `evalCoeffs ((yCoeffsAt i q).map (eval · x env))` (via the bridge, `eval_yCoeffsAt`,
and env-independence of the `y_i`-free entries) shows it is `0` for all `env i`, so the x-PIT
(`evalCoeffs_zero_iff_all_zero`) forces every coefficient-value to `0`. -/
theorem yCoeffsAt_entry_eval_zero_of_eval_zero {n : Nat} (i : Fin n) (q : MultiPoly n)
    (h : ∀ (x : Real) (env : Fin n → Real), MultiPoly.eval q x env = 0)
    (x : Real) (env : Fin n → Real) :
    ∀ c ∈ yCoeffsAt i q, MultiPoly.eval c x env = 0 := by
  have hall : ∀ y : Real,
      evalCoeffs ((yCoeffsAt i q).map (fun c' => MultiPoly.eval c' x env)) y = 0 := by
    intro y
    let env' : Fin n → Real := fun j => if j = i then y else env j
    have hoff : ∀ j : Fin n, j ≠ i → env' j = env j := by
      intro j hj; show (if j = i then y else env j) = env j; rw [if_neg hj]
    have hi : env' i = y := by show (if i = i then y else env i) = y; rw [if_pos rfl]
    have hmap : (yCoeffsAt i q).map (fun c' => MultiPoly.eval c' x env')
              = (yCoeffsAt i q).map (fun c' => MultiPoly.eval c' x env) := by
      apply List.map_congr_left
      intro c' hc'
      exact eval_eq_of_env_agree_off i c' x env' env hoff
        (yCoeffsAt_entries_degreeY_zero i q c' hc')
    have hbridge := listEvalN_eq_evalCoeffs_map i (yCoeffsAt i q) x env'
    rw [eval_yCoeffsAt i q x env', hi, hmap, h x env'] at hbridge
    exact hbridge.symm
  intro c hc
  exact evalCoeffs_zero_iff_all_zero _ hall (MultiPoly.eval c x env)
    (List.mem_map_of_mem _ hc)

end MachLib.ChainExp2YPIT
