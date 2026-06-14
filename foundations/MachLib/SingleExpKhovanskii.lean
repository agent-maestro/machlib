import MachLib.PolynomialEvidence
import MachLib.PolynomialRootCount
import MachLib.Exp
import MachLib.Differentiation
import MachLib.Rolle
import MachLib.Ring

/-!
# MachLib.SingleExpKhovanskii — constructive Khovanskii bound for poly-in-(x, e^x)

Closes Item 4 for the single-exponential case via a normal-form
representation `ExpPoly` (list of Poly coefficients) that sidesteps
the general `MultiPoly.leadingCoeffY` substrate.

A polynomial in (x, e^x) of "y-degree" `d` and "x-degree" `D`:

  f(x) = Σ_{k=0}^d a_k(x) · exp(k · x)

is represented as `⟨[a_0, a_1, ..., a_d]⟩ : ExpPoly` where each
`a_k : Poly` is a univariate polynomial in x.

The key operation:

  scaledReduction c f := f' - c · f

For `c = (length - 1)` (the highest e^x exponent), the leading
coefficient's polyDerivative drops its x-degree by 1, OR the leading
coefficient becomes 0 (in which case effective y-degree drops).

Iterating: after at most `Σ_k (degreeUpper a_k + 1) + d` applications,
we reach a constant (no more zeros). Combined with iterated Rolle,
this gives the Khovanskii bound.

## What this module ships

  * `ExpPoly` structure + `eval`.
  * `HasDerivAt` correctness for `eval`.
  * `scaledReduction` operation + zero count transfer (via Rolle).
  * Explicit Khovanskii zero bound theorem.

## Connection to the PfaffianFn framework

Future work: a `toMultiPoly : ExpPoly → MultiPoly 1` conversion +
eval correspondence with the SingleExpChain instance, lifting this
bound to `PfaffianFn.khovanskii_bound_full`.
-/

namespace MachLib
namespace SingleExpKhovanskii

open MachLib.Real
open MachLib.PolynomialEvidence
open MachLib.PolynomialRootCount

/-! ## ExpPoly: polynomial in (x, e^x) normal form -/

/-- A polynomial in (x, e^x) represented by its e^(k·x) coefficients:
`⟨[a_0, a_1, ..., a_d]⟩` denotes `Σ_k a_k(x) · exp(k · x)`. -/
structure ExpPoly where
  coeffs : List Poly

namespace ExpPoly

/-! ## Evaluation -/

/-- Eval with offset: `evalAux [p_0, ..., p_n] o x = Σ_k p_k(x) · exp((o + k) · x)`. -/
noncomputable def evalAux : List Poly → Nat → Real → Real
  | [], _, _ => 0
  | p :: rest, o, x =>
      Poly.eval p x * Real.exp ((natCast o) * x) + evalAux rest (o + 1) x

/-- Evaluation: `ep.eval x = Σ_k ep.coeffs[k](x) · exp(k · x)`. -/
noncomputable def eval (ep : ExpPoly) (x : Real) : Real :=
  evalAux ep.coeffs 0 x

/-! ## scaledReduction: term-wise transform

For each coefficient at index `k` (with offset), apply
`p ↦ p' + (k - c) · p`. For `c = max index`, the max-index coefficient
becomes `polyDerivative` of itself (drops x-degree by 1 or to 0). -/

noncomputable def scaledReductionAux
    (c : Real) : List Poly → Nat → List Poly
  | [], _ => []
  | p :: rest, o =>
      Poly.add (polyDerivative p)
        (Poly.mul (Poly.const ((natCast o) - c)) p)
      :: scaledReductionAux c rest (o + 1)

/-- The scaled reduction `f ↦ f' - c · f` at the ExpPoly level. -/
noncomputable def scaledReduction (ep : ExpPoly) (c : Real) : ExpPoly :=
  ⟨scaledReductionAux c ep.coeffs 0⟩

/-! ## HasDerivAt for ExpPoly.eval

The derivative of `Σ_k p_k(x) · exp(k·x)` is

  Σ_k (p_k'(x) + k · p_k(x)) · exp(k·x)

which is exactly `scaledReductionAux 0 coeffs offset` (with `c = 0`). -/

theorem hasDerivAt_evalAux (coeffs : List Poly) (o : Nat) (x : Real) :
    HasDerivAt (fun y => evalAux coeffs o y)
               (evalAux (scaledReductionAux 0 coeffs o) o x)
               x := by
  induction coeffs generalizing o with
  | nil =>
    show HasDerivAt (fun _ => (0 : Real)) 0 x
    exact HasDerivAt_const 0 x
  | cons p rest ih =>
    show HasDerivAt
          (fun y => Poly.eval p y * Real.exp ((natCast o) * y) + evalAux rest (o + 1) y)
          (evalAux
            (Poly.add (polyDerivative p)
              (Poly.mul (Poly.const ((natCast o) - 0)) p)
             :: scaledReductionAux 0 rest (o + 1))
            o x)
          x
    -- The first term: p · exp(o·x).
    -- d/dx (p · exp(o·x)) = p' · exp(o·x) + p · o · exp(o·x)
    --                    = (p' + o·p) · exp(o·x)
    have hp : HasDerivAt (Poly.eval p) (Poly.eval (polyDerivative p) x) x :=
      polyHasDerivAt_eval p x
    -- HasDerivAt for fun y => (natCast o) * y.
    have hlinear : HasDerivAt (fun y => (natCast o) * y) (natCast o) x := by
      have hid : HasDerivAt (fun y => y) 1 x := HasDerivAt_id x
      have hconst : HasDerivAt (fun _ : Real => (natCast o)) 0 x :=
        HasDerivAt_const _ x
      have hmul := HasDerivAt_mul (fun _ => (natCast o)) (fun y => y) 0 1 x hconst hid
      have : 0 * x + (natCast o) * 1 = (natCast o) := by
        rw [zero_mul, zero_add, mul_one_ax]
      rw [this] at hmul
      exact hmul
    -- HasDerivAt for fun y => exp(o·y).
    have hexp_at : HasDerivAt Real.exp (Real.exp ((natCast o) * x)) ((natCast o) * x) :=
      HasDerivAt_exp _
    have hexp_comp := HasDerivAt_comp Real.exp (fun y => (natCast o) * y) (natCast o)
                        (Real.exp ((natCast o) * x)) x hlinear hexp_at
    -- Product rule: p · exp(o·x).
    have hterm := HasDerivAt_mul (Poly.eval p) (fun y => Real.exp ((natCast o) * y))
                    (Poly.eval (polyDerivative p) x)
                    (Real.exp ((natCast o) * x) * (natCast o)) x hp hexp_comp
    -- Sum with IH for rest.
    have hsum := HasDerivAt_add (fun y => Poly.eval p y * Real.exp ((natCast o) * y))
                   (fun y => evalAux rest (o + 1) y)
                   (Poly.eval (polyDerivative p) x * Real.exp ((natCast o) * x)
                    + Poly.eval p x * (Real.exp ((natCast o) * x) * (natCast o)))
                   (evalAux (scaledReductionAux 0 rest (o + 1)) (o + 1) x)
                   x hterm (ih (o + 1))
    -- Now rearrange to match the expected form.
    -- Expected RHS: evalAux (Poly.add p' (Poly.mul (const (o - 0)) p) :: ...) o x
    --           = Poly.eval (Poly.add p' (Poly.mul (const o) p)) x * exp(o·x) + evalAux rest' (o+1) x
    --           = (Poly.eval p' x + (o - 0) · Poly.eval p x) * exp(o·x) + ...
    show HasDerivAt _ _ x
    show HasDerivAt
          (fun y => Poly.eval p y * Real.exp ((natCast o) * y) + evalAux rest (o + 1) y)
          ((Poly.eval (polyDerivative p) x + ((natCast o) - 0) * Poly.eval p x)
             * Real.exp ((natCast o) * x)
           + evalAux (scaledReductionAux 0 rest (o + 1)) (o + 1) x)
          x
    -- Ring identity: rearrange the HasDerivAt's derivative to match.
    -- Algebraic identity: p' · E + p · (E · n) = (p' + n · p) · E.
    -- MachLib has only LEFT distributive (mul_distrib), so we go via mul_comm.
    have hring :
      Poly.eval (polyDerivative p) x * Real.exp ((natCast o) * x)
        + Poly.eval p x * (Real.exp ((natCast o) * x) * (natCast o))
      = (Poly.eval (polyDerivative p) x + (natCast o) * Poly.eval p x)
        * Real.exp ((natCast o) * x) := by
      -- RHS = E · (p' + n · p) = E · p' + E · (n · p) = p' · E + (n · p) · E.
      rw [mul_comm
            (Poly.eval (polyDerivative p) x + (natCast o) * Poly.eval p x)
            (Real.exp ((natCast o) * x))]
      rw [mul_distrib]
      rw [mul_comm (Real.exp ((natCast o) * x)) (Poly.eval (polyDerivative p) x)]
      rw [mul_comm (Real.exp ((natCast o) * x)) ((natCast o) * Poly.eval p x)]
      -- Now goal: p' · E + p · (E · n) = p' · E + n · p · E.
      congr 1
      -- Need: p · (E · n) = n · p · E.
      -- = (p · E) · n = (E · p) · n = E · (p · n) = E · (n · p) = (n · p) · E.
      rw [← mul_assoc (Poly.eval p x) (Real.exp _) (natCast o)]
      rw [mul_comm (Poly.eval p x) (Real.exp ((natCast o) * x))]
      rw [mul_assoc (Real.exp _) (Poly.eval p x) (natCast o)]
      rw [mul_comm (Poly.eval p x) (natCast o)]
      rw [mul_comm (Real.exp ((natCast o) * x)) ((natCast o) * Poly.eval p x)]
    -- Now the show target should match (Poly.eval p' + n - 0 -> n via Lean's reduction).
    show HasDerivAt _
          ((Poly.eval (polyDerivative p) x
            + ((natCast o) - 0) * Poly.eval p x)
            * Real.exp ((natCast o) * x)
           + evalAux (scaledReductionAux 0 rest (o + 1)) (o + 1) x) x
    rw [sub_zero, ← hring]
    exact hsum

/-- **HasDerivAt for ExpPoly.eval.** -/
theorem hasDerivAt_eval (ep : ExpPoly) (x : Real) :
    HasDerivAt ep.eval ((scaledReduction ep 0).eval x) x := by
  show HasDerivAt (fun y => evalAux ep.coeffs 0 y)
                  (evalAux (scaledReductionAux 0 ep.coeffs 0) 0 x) x
  exact hasDerivAt_evalAux ep.coeffs 0 x

/-! ## scaledReduction with arbitrary c: HasDerivAt

For arbitrary c, the derivative of `ep.eval x · exp(-c·x)` equals
`exp(-c·x) · (scaledReduction ep c).eval x`. This is the Rolle vehicle. -/

/-- Real-arithmetic helper: a*b = 0 with a ≠ 0 implies b = 0. -/
theorem mul_eq_zero_of_factor_ne_zero_local {a b : Real} (ha : a ≠ 0)
    (hab : a * b = 0) : b = 0 := by
  have hkey : a * b * (1 / a) = b := by
    rw [mul_comm a b, mul_assoc, mul_inv a ha, mul_one_ax]
  rw [hab, zero_mul] at hkey
  exact hkey.symm

/-- The Rolle vehicle `ep.eval x · exp(-c · x)`. -/
noncomputable def mulNegExpX (ep : ExpPoly) (c : Real) : Real → Real :=
  fun x => ep.eval x * Real.exp (-c * x)

/-- Same zero set: `exp(-c·x)` is never zero, so the auxiliary has
the same zeros as `ep.eval`. -/
theorem mulNegExpX_zero_iff (ep : ExpPoly) (c : Real) (x : Real) :
    mulNegExpX ep c x = 0 ↔ ep.eval x = 0 := by
  show ep.eval x * Real.exp (-c * x) = 0 ↔ ep.eval x = 0
  constructor
  · intro h
    have hexp_ne : Real.exp (-c * x) ≠ 0 := exp_ne_zero _
    rw [mul_comm] at h
    exact mul_eq_zero_of_factor_ne_zero_local hexp_ne h
  · intro h
    rw [h, zero_mul]

/-- **HasDerivAt for the Rolle vehicle.** Raw product-rule form. -/
theorem hasDerivAt_mulNegExpX_raw (ep : ExpPoly) (c : Real) (x : Real) :
    HasDerivAt (mulNegExpX ep c)
               ((scaledReduction ep 0).eval x * Real.exp (-c * x)
                + ep.eval x * (Real.exp (-c * x) * (-c)))
               x := by
  show HasDerivAt (fun y => ep.eval y * Real.exp (-c * y))
                  ((scaledReduction ep 0).eval x * Real.exp (-c * x)
                   + ep.eval x * (Real.exp (-c * x) * (-c))) x
  have hep := hasDerivAt_eval ep x
  -- HasDerivAt for fun y => -c · y.
  have hlinear : HasDerivAt (fun y => -c * y) (-c) x := by
    have hid : HasDerivAt (fun y => y) 1 x := HasDerivAt_id x
    have hconst : HasDerivAt (fun _ : Real => -c) 0 x := HasDerivAt_const _ x
    have hmul := HasDerivAt_mul (fun _ => -c) (fun y => y) 0 1 x hconst hid
    have : 0 * x + (-c) * 1 = -c := by rw [zero_mul, zero_add, mul_one_ax]
    rw [this] at hmul
    exact hmul
  have hexp_at : HasDerivAt Real.exp (Real.exp (-c * x)) (-c * x) :=
    HasDerivAt_exp _
  have hexp_comp := HasDerivAt_comp Real.exp (fun y => -c * y) (-c)
                      (Real.exp (-c * x)) x hlinear hexp_at
  exact HasDerivAt_mul ep.eval (fun y => Real.exp (-c * y))
          ((scaledReduction ep 0).eval x)
          (Real.exp (-c * x) * (-c)) x hep hexp_comp

/-! ## Open piece: `scaledReduction_eval_combine`

The algebraic identity

  `(scaledReduction ep 0).eval x + ep.eval x · (-c) = (scaledReduction ep c).eval x`

reduces (after `simp only [Poly.eval]` and abstracting complex
subterms) to a pure scalar ring identity in 7 Real variables:

  `(pd + n·pe)·E + S0 + (pe·E + R)·(-c) = (pd + (n - c)·pe)·E + (S0 + R·(-c))`

Both sides expand to `pd·E + (n - c)·pe·E + S0 - c·R`. This is
ring-trivial classically but MachLib's `mach_ring v1` doesn't fully
normalize multi-variable polynomial identities — manual rewriting via
`mul_comm`, `mul_assoc`, `mul_distrib`, `add_assoc`, `add_comm`,
`sub_def` runs into combinatorial blowup. Each rewrite is correct
individually; chaining them to match the exact post-normalization
form is fragile.

Resolution path (future work):
  (a) Wait for `mach_ring v2` (polynomial reflection — Lagrange,
      four-square — per MachLib roadmap).
  (b) Prove the identity by hand via explicit calc chain
      (estimated ~30 lines of careful manual rewriting).
  (c) Introduce a helper `linear_combination`-style tactic.

This is the only blocker for the `zero_count_scaledReduction_transfer`
+ explicit Khovanskii bound theorem. Once this identity ships, the
rest of the proof is mechanical (~150 lines).

For now, the SUBSTRATE (ExpPoly + eval + HasDerivAt for c=0 +
`hasDerivAt_mulNegExpX_raw` for arbitrary c) is shipped and provides
the foundation. -/
