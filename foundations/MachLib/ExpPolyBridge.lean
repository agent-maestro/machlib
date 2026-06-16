import MachLib.MultiPoly
import MachLib.PolynomialEvidence
import MachLib.PolynomialRootCount
import MachLib.Exp
import MachLib.SingleExpKhovanskii
import MachLib.KhovanskiiReduction
import MachLib.MultiPolyCanonY

/-!
# MachLib.ExpPolyBridge — Poly → MultiPoly 1 embedding

The bridge for option B of the Khovanskii sprint: translate the
single-variable `Poly` AST (in `PolynomialEvidence`) into the
two-variable `MultiPoly 1` AST (in `MultiPoly`). This is the
foundational step toward bridging the constructive `ExpPoly` track in
`SingleExpKhovanskii.lean` to the abstract `PfaffianFn` framework.

## What ships in this commit

- `Poly.toMultiPoly1 : Poly → MultiPoly 1`: the structural embedding
  (Poly.var → MultiPoly.varX, all other constructors mirrored).
- `Poly.eval_toMultiPoly1`: eval correctness — Poly.eval p x equals
  MultiPoly.eval (toMultiPoly1 p) x env for any env.
- `Poly.PolynomialRootCount.degreeUpper_toMultiPoly1`: degreeX correspondence.

The Poly variable maps to x (varX), not to y_0. The y_0 variable
slot in MultiPoly 1 is reserved for the chain variable
(exp(x) in SingleExpChain).
-/

namespace MachLib
namespace ExpPolyBridge

open MachLib.MultiPolyMod
open MachLib.PolynomialEvidence
open MachLib.PolynomialRootCount

/-- **Structural embedding** `Poly → MultiPoly 1`. The Poly's `var`
(univariate variable, treated as x) maps to MultiPoly's `varX`. The
y_0 slot in MultiPoly 1 is unused (no `varY` in the image). -/
noncomputable def Poly.toMultiPoly1 : Poly → MultiPoly 1
  | Poly.const c => MultiPoly.const c
  | Poly.var     => MultiPoly.varX
  | Poly.add p q => MultiPoly.add (Poly.toMultiPoly1 p) (Poly.toMultiPoly1 q)
  | Poly.sub p q => MultiPoly.sub (Poly.toMultiPoly1 p) (Poly.toMultiPoly1 q)
  | Poly.mul p q => MultiPoly.mul (Poly.toMultiPoly1 p) (Poly.toMultiPoly1 q)

/-- **Eval correctness**: `Poly.eval p x` equals
`MultiPoly.eval (toMultiPoly1 p) x env` for any environment `env`.
The y_0 slot doesn't appear in the image, so the eval is
env-independent. -/
theorem Poly.eval_toMultiPoly1 (p : Poly) (x : Real) (env : Fin 1 → Real) :
    MultiPoly.eval (Poly.toMultiPoly1 p) x env = Poly.eval p x := by
  induction p with
  | const c => rfl
  | var => rfl
  | add p q ihp ihq =>
    show MultiPoly.eval (Poly.toMultiPoly1 p) x env +
         MultiPoly.eval (Poly.toMultiPoly1 q) x env =
         Poly.eval p x + Poly.eval q x
    rw [ihp, ihq]
  | sub p q ihp ihq =>
    show MultiPoly.eval (Poly.toMultiPoly1 p) x env -
         MultiPoly.eval (Poly.toMultiPoly1 q) x env =
         Poly.eval p x - Poly.eval q x
    rw [ihp, ihq]
  | mul p q ihp ihq =>
    show MultiPoly.eval (Poly.toMultiPoly1 p) x env *
         MultiPoly.eval (Poly.toMultiPoly1 q) x env =
         Poly.eval p x * Poly.eval q x
    rw [ihp, ihq]

/-- **degreeY 0 is always 0** for the image: `toMultiPoly1` never
introduces `varY 0`. -/
theorem Poly.degreeY_toMultiPoly1 (p : Poly) :
    MultiPoly.degreeY 0 (Poly.toMultiPoly1 p) = 0 := by
  induction p with
  | const c => rfl
  | var => rfl
  | add p q ihp ihq =>
    show Nat.max (MultiPoly.degreeY 0 (Poly.toMultiPoly1 p))
                  (MultiPoly.degreeY 0 (Poly.toMultiPoly1 q)) = 0
    rw [ihp, ihq]; rfl
  | sub p q ihp ihq =>
    show Nat.max (MultiPoly.degreeY 0 (Poly.toMultiPoly1 p))
                  (MultiPoly.degreeY 0 (Poly.toMultiPoly1 q)) = 0
    rw [ihp, ihq]; rfl
  | mul p q ihp ihq =>
    show MultiPoly.degreeY 0 (Poly.toMultiPoly1 p) +
         MultiPoly.degreeY 0 (Poly.toMultiPoly1 q) = 0
    rw [ihp, ihq]

/-- **degreeX correspondence**: the MultiPoly 1 image has the same
formal x-degree (degreeX) as the original Poly's PolynomialRootCount.degreeUpper. -/
theorem Poly.PolynomialRootCount.degreeUpper_toMultiPoly1 (p : Poly) :
    MultiPoly.degreeX (Poly.toMultiPoly1 p) = PolynomialRootCount.degreeUpper p := by
  induction p with
  | const c => rfl
  | var => rfl
  | add p q ihp ihq =>
    show Nat.max (MultiPoly.degreeX (Poly.toMultiPoly1 p))
                  (MultiPoly.degreeX (Poly.toMultiPoly1 q))
         = Nat.max (PolynomialRootCount.degreeUpper p) (PolynomialRootCount.degreeUpper q)
    rw [ihp, ihq]
  | sub p q ihp ihq =>
    show Nat.max (MultiPoly.degreeX (Poly.toMultiPoly1 p))
                  (MultiPoly.degreeX (Poly.toMultiPoly1 q))
         = Nat.max (PolynomialRootCount.degreeUpper p) (PolynomialRootCount.degreeUpper q)
    rw [ihp, ihq]
  | mul p q ihp ihq =>
    show MultiPoly.degreeX (Poly.toMultiPoly1 p) +
         MultiPoly.degreeX (Poly.toMultiPoly1 q)
         = PolynomialRootCount.degreeUpper p + PolynomialRootCount.degreeUpper q
    rw [ihp, ihq]

/-! ## Exp ↔ pow identity (the core bridge fact)

`Real.exp (k · x) = (Real.exp x)^k` where `^` is iterated multiplication
(via `MultiPoly.pow (varY 0) k` evaluated against env = exp x).

Inductive proof using `exp_add` and `natCast_succ`. This identity is
what makes ExpPoly's `exp(k·x)` correspond to `(exp x)^k = y_0^k` in
the PfaffianFn formulation. -/

/-- **The exp-to-pow identity.** For env mapping `0 ↦ Real.exp x_val`,
`Real.exp ((natCast k) * x_val) = MultiPoly.eval (pow (varY 0) k) x_val env`.

The proof: induction on k. Base case (k = 0) collapses both sides to 1.
Step case (k+1) distributes `(natCast k + 1) * x_val` via `mul_distrib_right`,
applies `exp_add` to split, applies IH, and reassociates via `mul_comm`. -/
theorem exp_eq_pow_varY {n : Nat} (k : Nat) (x_val : Real)
    (env : Fin n → Real) (i : Fin n) (h_env : env i = Real.exp x_val) :
    Real.exp ((Real.natCast k) * x_val) =
    MultiPoly.eval (MultiPoly.pow (MultiPoly.varY i) k) x_val env := by
  induction k with
  | zero =>
    show Real.exp (Real.natCast 0 * x_val) =
         MultiPoly.eval (MultiPoly.one (n := n)) x_val env
    rw [Real.natCast_zero, Real.zero_mul, Real.exp_zero]
    rfl
  | succ k ih =>
    show Real.exp (Real.natCast (k + 1) * x_val) =
         MultiPoly.eval
          (MultiPoly.mul (MultiPoly.varY i)
            (MultiPoly.pow (MultiPoly.varY i) k))
          x_val env
    -- LHS: exp((natCast k + 1) * x_val) = exp(natCast k * x_val + x_val)
    --      = exp(natCast k * x_val) * exp(x_val).
    rw [Real.natCast_succ, Real.mul_distrib_right, Real.one_mul_thm,
        Real.exp_add]
    -- RHS: eval(varY i) * eval(pow (varY i) k) = env i * eval(pow ...)
    --     = exp x_val * eval(pow ...) (via h_env).
    show Real.exp (Real.natCast k * x_val) * Real.exp x_val =
         env i * MultiPoly.eval (MultiPoly.pow (MultiPoly.varY i) k) x_val env
    rw [h_env, ← ih, Real.mul_comm]

/-! ## ExpPoly → MultiPoly 1 translation

The full bridge: translate ExpPoly's coefficient list into a MultiPoly 1
polynomial. Eval correctness composes the Poly embedding, exp-pow
identity, and pow eval. -/

open MachLib.SingleExpKhovanskii (ExpPoly)
open MachLib.SingleExpKhovanskii.ExpPoly (evalAux)

/-- **Auxiliary translation** with offset. For coefficients
`[p_0, p_1, ..., p_n]` at offset `o`, produces
`Σ_k (toMultiPoly1 p_k) · (varY 0)^(o+k)`. -/
noncomputable def expPolyAuxToMultiPoly1 : List Poly → Nat → MultiPoly 1
  | [], _ => MultiPoly.const 0
  | p :: rest, o =>
      MultiPoly.add
        (MultiPoly.mul (Poly.toMultiPoly1 p)
                        (MultiPoly.pow (MultiPoly.varY 0) o))
        (expPolyAuxToMultiPoly1 rest (o + 1))

/-- **Full ExpPoly → MultiPoly 1 translation.** Wrapper at offset 0. -/
noncomputable def ExpPoly.toMultiPoly1 (ep : ExpPoly) : MultiPoly 1 :=
  expPolyAuxToMultiPoly1 ep.coeffs 0

/-- **Auxiliary eval correctness.** For env mapping `0 ↦ Real.exp x_val`,
the translation's eval matches ExpPoly's evalAux at the corresponding
offset. -/
theorem evalAux_toMultiPoly1 (coeffs : List Poly) (o : Nat) (x_val : Real)
    (env : Fin 1 → Real) (h_env : env 0 = Real.exp x_val) :
    MultiPoly.eval (expPolyAuxToMultiPoly1 coeffs o) x_val env =
    evalAux coeffs o x_val := by
  induction coeffs generalizing o with
  | nil =>
    show MultiPoly.eval (MultiPoly.const 0 : MultiPoly 1) x_val env =
         (0 : Real)
    rfl
  | cons p rest ih =>
    show MultiPoly.eval
          (MultiPoly.add
            (MultiPoly.mul (Poly.toMultiPoly1 p)
                            (MultiPoly.pow (MultiPoly.varY 0) o))
            (expPolyAuxToMultiPoly1 rest (o + 1)))
          x_val env =
         Poly.eval p x_val * Real.exp ((Real.natCast o) * x_val) +
         evalAux rest (o + 1) x_val
    -- LHS: eval(add ...) = eval(mul ...) + eval(rest_translation).
    show MultiPoly.eval (MultiPoly.mul (Poly.toMultiPoly1 p)
                                       (MultiPoly.pow (MultiPoly.varY 0) o))
                       x_val env +
         MultiPoly.eval (expPolyAuxToMultiPoly1 rest (o + 1)) x_val env =
         Poly.eval p x_val * Real.exp ((Real.natCast o) * x_val) +
         evalAux rest (o + 1) x_val
    -- mul step: eval(mul a b) = eval a * eval b.
    show MultiPoly.eval (Poly.toMultiPoly1 p) x_val env *
         MultiPoly.eval (MultiPoly.pow (MultiPoly.varY 0) o) x_val env +
         MultiPoly.eval (expPolyAuxToMultiPoly1 rest (o + 1)) x_val env =
         Poly.eval p x_val * Real.exp ((Real.natCast o) * x_val) +
         evalAux rest (o + 1) x_val
    rw [Poly.eval_toMultiPoly1 p x_val env]
    rw [← exp_eq_pow_varY o x_val env 0 h_env]
    rw [ih (o + 1)]

/-- **Full eval correctness**: `ep.toMultiPoly1` translates to a
MultiPoly 1 with the same eval as `ep.eval` when env carries `exp x_val`. -/
theorem ExpPoly.eval_toMultiPoly1 (ep : ExpPoly) (x_val : Real)
    (env : Fin 1 → Real) (h_env : env 0 = Real.exp x_val) :
    MultiPoly.eval (ExpPoly.toMultiPoly1 ep) x_val env = ep.eval x_val := by
  show MultiPoly.eval (expPolyAuxToMultiPoly1 ep.coeffs 0) x_val env =
       evalAux ep.coeffs 0 x_val
  exact evalAux_toMultiPoly1 ep.coeffs 0 x_val env h_env

/-! ## SingleExpChain bridge — connecting ExpPoly to PfaffianFn

The final piece: any ExpPoly corresponds to a PfaffianFn with SingleExpChain
whose underlying polynomial is `ExpPoly.toMultiPoly1 ep` and whose eval
matches `ep.eval`. -/

open MachLib.PfaffianChainMod

/-- **SingleExpChain's chainValues at index 0 = `Real.exp`.** Direct
unfolding of the chain definition. -/
theorem SingleExpChain_chainValues_zero (x : Real) :
    SingleExpChain.chainValues x 0 = Real.exp x := rfl

/-- **The bridge PfaffianFn**: given an ExpPoly `ep`, build a PfaffianFn
with chain length 1 (SingleExpChain) whose polynomial is `ep.toMultiPoly1`.
The eval matches `ep.eval`. -/
noncomputable def ExpPoly.toPfaffianFn (ep : ExpPoly) : PfaffianFn :=
  { n := 1
    chain := SingleExpChain
    poly := ExpPoly.toMultiPoly1 ep }

/-- **Bridge eval correctness**: the PfaffianFn's eval matches `ep.eval`. -/
theorem ExpPoly.eval_toPfaffianFn (ep : ExpPoly) (x : Real) :
    (ExpPoly.toPfaffianFn ep).eval x = ep.eval x := by
  show MultiPoly.eval (ExpPoly.toMultiPoly1 ep) x (SingleExpChain.chainValues x) =
       ep.eval x
  exact ExpPoly.eval_toMultiPoly1 ep x _ (SingleExpChain_chainValues_zero x)

/-- **Bridge chain length is 1.** -/
theorem ExpPoly.toPfaffianFn_n (ep : ExpPoly) :
    (ExpPoly.toPfaffianFn ep).n = 1 := rfl

/-- **Bridge chain is SingleExpChain.** -/
theorem ExpPoly.toPfaffianFn_chain (ep : ExpPoly) :
    (ExpPoly.toPfaffianFn ep).chain = SingleExpChain := rfl

/-! ## End-to-end demonstration — length-1 bound via the bridge

The simplest wire-through: for an ExpPoly ⟨[p]⟩ (length-1), the
PfaffianFn obtained via the bridge has zero count bounded by
`degreeUpper p`. This composes:
  - `SingleExpKhovanskii.length_one_full_bound` (ExpPoly side,
    constructive).
  - `ExpPoly.eval_toPfaffianFn` (the bridge eval correctness).

The result is a PfaffianFn-level Khovanskii bound that doesn't require
the abstract SDR machinery — the ExpPoly's constructive auto-witness
is "smuggled through" the bridge as the eval-preservation. This is a
proof-of-concept that the bridge correctly connects the two tracks. -/

open MachLib.SingleExpKhovanskii.ExpPoly in
/-- **End-to-end length-1 bound for the bridge image**: for any Poly p
and interval (a, b) where Poly.eval p has a nonzero point, the
PfaffianFn `(⟨[p]⟩).toPfaffianFn` has zero count on (a, b) bounded by
`degreeUpper p`. Wire-through of ExpPoly's constructive bound. -/
theorem PfaffianFn_singleExp_length_one_bound
    (p : Poly) (a b : Real) (hab : a < b)
    (hne : ∃ x : Real, Poly.eval p x ≠ 0) :
    ∀ zeros : List Real,
      zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧
        (ExpPoly.toPfaffianFn (⟨[p]⟩ : ExpPoly)).eval z = 0) →
      zeros.length ≤ PolynomialRootCount.degreeUpper p := by
  intro zeros hnodup hzeros
  -- Translate the zero-conditions through the bridge.
  have hzeros_ep : ∀ z ∈ zeros,
      a < z ∧ z < b ∧ (⟨[p]⟩ : ExpPoly).eval z = 0 := by
    intro z hz
    obtain ⟨haz, hzb, hf_z⟩ := hzeros z hz
    refine ⟨haz, hzb, ?_⟩
    rw [← ExpPoly.eval_toPfaffianFn (⟨[p]⟩ : ExpPoly) z]
    exact hf_z
  exact MachLib.SingleExpKhovanskii.ExpPoly.length_one_full_bound p a b
          hab hne zeros hnodup hzeros_ep

/-- **General auto-bound via the bridge**: the propagation+strict-last
auto-bound for ExpPoly (any length) translated to the PfaffianFn level.
All ExpPoly-track hypotheses are passed through; the eval condition
on `(toPfaffianFn ep).eval` is bridged to `ep.eval` via
`ExpPoly.eval_toPfaffianFn`. -/
theorem PfaffianFn_singleExp_auto_bound_via_bridge
    (M : Nat) (ep : ExpPoly)
    (h_meas : ep.coeffs.length +
              MachLib.SingleExpKhovanskii.ExpPoly.sumSimplifiedDegrees
                ep.coeffs ≤ M)
    (h_prop : ∀ ep' : ExpPoly,
       ep'.coeffs.length +
         MachLib.SingleExpKhovanskii.ExpPoly.sumSimplifiedDegrees
           ep'.coeffs ≤ M →
       (∃ x, ep'.eval x ≠ 0))
    (h_strict_last : ∀ ep' : ExpPoly,
       ∀ (hne_coeffs : ep'.coeffs ≠ []),
       ep'.coeffs.length ≥ 2 →
       ep'.coeffs.length +
         MachLib.SingleExpKhovanskii.ExpPoly.sumSimplifiedDegrees
           ep'.coeffs ≤ M →
       PolynomialRootCount.degreeUpper
         (polySimplify (ep'.coeffs.getLast hne_coeffs)) > 0)
    (a b : Real) (hab : a < b) :
    ∀ zeros : List Real,
      zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧
        (ExpPoly.toPfaffianFn ep).eval z = 0) →
      zeros.length ≤ M := by
  intro zeros hnodup hzeros
  have hzeros_ep : ∀ z ∈ zeros, a < z ∧ z < b ∧ ep.eval z = 0 := by
    intro z hz
    obtain ⟨haz, hzb, hf_z⟩ := hzeros z hz
    refine ⟨haz, hzb, ?_⟩
    rw [← ExpPoly.eval_toPfaffianFn ep z]
    exact hf_z
  exact MachLib.SingleExpKhovanskii.ExpPoly.expPoly_auto_bound_with_propagation_aux
          M ep h_meas h_prop h_strict_last a b hab zeros hnodup hzeros_ep

/-! ## Inverse direction: MultiPoly 1 → Poly (y-free polynomials)

Closes the loop with option A's canonical form. A y-free `MultiPoly 1`
(satisfying `degreeY 0 = 0`) can be exactly converted to a `Poly` via
a structural mirror of `Poly.toMultiPoly1`. -/

/-- **Inverse embedding** `MultiPoly 1 → Poly`. The `varY 0` case ships
`Poly.const 0` (impossible under the degreeY 0 = 0 hypothesis but
serves as a structural placeholder). -/
noncomputable def MultiPoly1ToPoly : MultiPoly 1 → Poly
  | MultiPoly.const c   => Poly.const c
  | MultiPoly.varX      => Poly.var
  | MultiPoly.varY _    => Poly.const 0
  | MultiPoly.add p q   =>
      Poly.add (MultiPoly1ToPoly p) (MultiPoly1ToPoly q)
  | MultiPoly.sub p q   =>
      Poly.sub (MultiPoly1ToPoly p) (MultiPoly1ToPoly q)
  | MultiPoly.mul p q   =>
      Poly.mul (MultiPoly1ToPoly p) (MultiPoly1ToPoly q)

/-- **Eval correctness for the inverse embedding.** Under the hypothesis
`degreeY 0 p = 0` (no dependence on the y_0 chain variable), the inverse
embedding's eval matches the original MultiPoly's eval at any
environment (since the y_0 slot is irrelevant). -/
theorem MultiPoly1ToPoly_eval (p : MultiPoly 1)
    (h_deg : MultiPoly.degreeY 0 p = 0)
    (x : Real) (env : Fin 1 → Real) :
    Poly.eval (MultiPoly1ToPoly p) x = MultiPoly.eval p x env := by
  induction p with
  | const c => rfl
  | varX => rfl
  | varY j =>
    -- degreeY 0 (varY j) = if 0 = j then 1 else 0. The hypothesis says
    -- this equals 0, so 0 ≠ j, i.e., j ≠ 0.
    have hj : (0 : Fin 1) ≠ j := by
      intro hjeq
      have : (if (0 : Fin 1) = j then (1 : Nat) else 0) = 0 := h_deg
      rw [if_pos hjeq] at this
      exact Nat.one_ne_zero this
    -- For Fin 1, this means j ≠ 0, but there's no such j.
    have : j = 0 := by
      apply Fin.eq_of_val_eq
      have := j.isLt
      omega
    exact absurd this.symm hj
  | add p q ihp ihq =>
    have hmax : Nat.max (MultiPoly.degreeY 0 p) (MultiPoly.degreeY 0 q) = 0 := h_deg
    have ⟨h_le_p, h_le_q⟩ :
        MultiPoly.degreeY 0 p ≤ 0 ∧ MultiPoly.degreeY 0 q ≤ 0 :=
      Nat.max_le.mp (Nat.le_of_eq hmax)
    have h_deg_p : MultiPoly.degreeY 0 p = 0 := Nat.le_zero.mp h_le_p
    have h_deg_q : MultiPoly.degreeY 0 q = 0 := Nat.le_zero.mp h_le_q
    show Poly.eval (MultiPoly1ToPoly p) x + Poly.eval (MultiPoly1ToPoly q) x =
         MultiPoly.eval p x env + MultiPoly.eval q x env
    rw [ihp h_deg_p, ihq h_deg_q]
  | sub p q ihp ihq =>
    have hmax : Nat.max (MultiPoly.degreeY 0 p) (MultiPoly.degreeY 0 q) = 0 := h_deg
    have ⟨h_le_p, h_le_q⟩ :
        MultiPoly.degreeY 0 p ≤ 0 ∧ MultiPoly.degreeY 0 q ≤ 0 :=
      Nat.max_le.mp (Nat.le_of_eq hmax)
    have h_deg_p : MultiPoly.degreeY 0 p = 0 := Nat.le_zero.mp h_le_p
    have h_deg_q : MultiPoly.degreeY 0 q = 0 := Nat.le_zero.mp h_le_q
    show Poly.eval (MultiPoly1ToPoly p) x - Poly.eval (MultiPoly1ToPoly q) x =
         MultiPoly.eval p x env - MultiPoly.eval q x env
    rw [ihp h_deg_p, ihq h_deg_q]
  | mul p q ihp ihq =>
    have hsum : MultiPoly.degreeY 0 p + MultiPoly.degreeY 0 q = 0 := h_deg
    have h_deg_p : MultiPoly.degreeY 0 p = 0 := by omega
    have h_deg_q : MultiPoly.degreeY 0 q = 0 := by omega
    show Poly.eval (MultiPoly1ToPoly p) x * Poly.eval (MultiPoly1ToPoly q) x =
         MultiPoly.eval p x env * MultiPoly.eval q x env
    rw [ihp h_deg_p, ihq h_deg_q]

end ExpPolyBridge
end MachLib
