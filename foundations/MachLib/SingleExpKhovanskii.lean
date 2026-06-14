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

/-! ## The pure scalar ring identity (path (b): hand-proved via calc)

Reduces to the 7-variable Real identity:

  `(pd + n·pe)·E + S0 + (pe·E + R)·(-c) = (pd + (n - c)·pe)·E + (S0 + R·(-c))`

Both sides expand to `pd·E + (n - c)·pe·E + S0 - c·R`. We hand-prove
this via an explicit calc chain. -/

/-- Right-distributive `(a + b) * c = a * c + b * c` derived from MachLib's
left-distributive `mul_distrib`. -/
theorem add_mul_local (a b c : Real) : (a + b) * c = a * c + b * c := by
  rw [mul_comm (a + b) c, mul_distrib, mul_comm c a, mul_comm c b]

/-- Helper: `n * pe * E + pe * E * (-c) = (n - c) * pe * E` for Reals. -/
theorem combine_pe_E (n pe E c : Real) :
    n * pe * E + pe * E * (-c) = (n - c) * pe * E := by
  -- = n·(pe·E) + (-c)·(pe·E) = (n + -c)·(pe·E) = (n - c)·(pe·E)
  rw [mul_assoc n pe E]
  rw [show pe * E * -c = -c * (pe * E) from mul_comm _ _]
  rw [show n * (pe * E) + -c * (pe * E) = (n + -c) * (pe * E) from by
    rw [mul_comm n (pe * E), mul_comm (-c) (pe * E)]
    rw [← mul_distrib]
    rw [mul_comm (pe * E) (n + -c)]]
  rw [show n + -c = n - c from (sub_def n c).symm]
  rw [mul_assoc]

/-- The scalar ring identity that powers the inductive step. -/
theorem expPoly_step_ring_identity (pd n pe E S0 R c : Real) :
    (pd + (n - 0) * pe) * E + S0 + (pe * E + R) * -c
    = (pd + (n - c) * pe) * E + (S0 + R * -c) := by
  rw [sub_zero]
  rw [add_mul_local (pe * E) R (-c)]
  rw [add_mul_local pd (n * pe) E]
  rw [add_mul_local pd ((n - c) * pe) E]
  rw [← combine_pe_E n pe E c]
  -- Goal (post-rewrites): pd·E + n·pe·E + S0 + (pe·E·(-c) + R·(-c))
  --                    = pd·E + (n·pe·E + pe·E·(-c)) + (S0 + R·(-c))
  -- mach_ring partially normalizes but leaves additive residue.
  -- Close by explicit add_comm + add_assoc.
  mach_ring
  -- Residue: S0 + (pd*E + (E*(n*pe) + (-(R*c) + -(c*(pe*E)))))
  --        = S0 + (-(R*c) + (pd*E + (E*(n*pe) + -(c*(pe*E)))))
  congr 1
  -- Inner: pd*E + (E*(n*pe) + (-(R*c) + -(c*(pe*E))))
  --      = -(R*c) + (pd*E + (E*(n*pe) + -(c*(pe*E))))
  -- Move -(R*c) from position 3 to position 1.
  rw [← add_assoc (E * (n * pe)) (-(R * c)) (-(c * (pe * E)))]
  rw [add_comm (E * (n * pe)) (-(R * c))]
  rw [add_assoc (-(R * c)) (E * (n * pe)) (-(c * (pe * E)))]
  rw [← add_assoc (pd * E) (-(R * c)) (E * (n * pe) + -(c * (pe * E)))]
  rw [add_comm (pd * E) (-(R * c))]
  rw [add_assoc (-(R * c)) (pd * E) (E * (n * pe) + -(c * (pe * E)))]

/-- Algebraic identity:
  `(scaledReduction ep 0).eval x + ep.eval x · (-c) = (scaledReduction ep c).eval x`
We need this to factor the derivative into Rolle-friendly form. Proved
at the eval level via list-recursive matching + the scalar ring identity. -/
theorem scaledReduction_eval_combine (ep : ExpPoly) (c : Real) (x : Real) :
    (scaledReduction ep 0).eval x + ep.eval x * (-c)
    = (scaledReduction ep c).eval x := by
  show evalAux (scaledReductionAux 0 ep.coeffs 0) 0 x + evalAux ep.coeffs 0 x * (-c)
     = evalAux (scaledReductionAux c ep.coeffs 0) 0 x
  generalize 0 = o
  induction ep.coeffs generalizing o with
  | nil =>
    show (0 : Real) + 0 * (-c) = 0
    rw [zero_mul, zero_add]
  | cons p rest ih =>
    have hih := ih (o + 1)
    show (Poly.eval (Poly.add (polyDerivative p) (Poly.mul (Poly.const (natCast o - 0)) p)) x
            * Real.exp (natCast o * x)
          + evalAux (scaledReductionAux 0 rest (o + 1)) (o + 1) x)
         + (Poly.eval p x * Real.exp (natCast o * x)
            + evalAux rest (o + 1) x) * (-c)
       = Poly.eval (Poly.add (polyDerivative p) (Poly.mul (Poly.const (natCast o - c)) p)) x
            * Real.exp (natCast o * x)
         + evalAux (scaledReductionAux c rest (o + 1)) (o + 1) x
    rw [← hih]
    simp only [Poly.eval]
    exact expPoly_step_ring_identity
            (Poly.eval (polyDerivative p) x) (natCast o) (Poly.eval p x)
            (Real.exp (natCast o * x))
            (evalAux (scaledReductionAux 0 rest (o + 1)) (o + 1) x)
            (evalAux rest (o + 1) x) c

/-! ## Zero count transfer via Rolle -/

theorem scaledReduction_eval_zero_of_aux_deriv_zero
    (ep : ExpPoly) (c : Real) (z : Real)
    (g'' : Real)
    (hg''_deriv : HasDerivAt (mulNegExpX ep c) g'' z)
    (hg''_zero : g'' = 0) :
    (scaledReduction ep c).eval z = 0 := by
  have hcanonical := hasDerivAt_mulNegExpX_raw ep c z
  have huniq := HasDerivAt_unique (mulNegExpX ep c) g''
                  ((scaledReduction ep 0).eval z * Real.exp (-c * z)
                   + ep.eval z * (Real.exp (-c * z) * (-c)))
                  z hg''_deriv hcanonical
  have hcan_zero : (scaledReduction ep 0).eval z * Real.exp (-c * z)
                   + ep.eval z * (Real.exp (-c * z) * (-c)) = 0 := by
    rw [← huniq]; exact hg''_zero
  have hfact : (scaledReduction ep 0).eval z * Real.exp (-c * z)
                + ep.eval z * (Real.exp (-c * z) * (-c))
             = Real.exp (-c * z) * (scaledReduction ep c).eval z := by
    rw [← scaledReduction_eval_combine ep c z]
    rw [show (scaledReduction ep 0).eval z * Real.exp (-c * z)
          = Real.exp (-c * z) * (scaledReduction ep 0).eval z from mul_comm _ _]
    rw [show ep.eval z * (Real.exp (-c * z) * (-c))
          = Real.exp (-c * z) * (ep.eval z * (-c)) from by
      rw [← mul_assoc, mul_comm (ep.eval z) (Real.exp _), mul_assoc]]
    rw [← mul_distrib]
  rw [hfact] at hcan_zero
  have hexp_ne : Real.exp (-c * z) ≠ 0 := exp_ne_zero _
  exact mul_eq_zero_of_factor_ne_zero_local hexp_ne hcan_zero

theorem zero_count_scaledReduction_transfer_raw
    (ep : ExpPoly) (c : Real) (a b : Real) (hab : a < b)
    (N : Nat)
    (h_reduced_bound : ∀ zeros' : List Real,
        zeros'.Nodup →
        (∀ z ∈ zeros', a < z ∧ z < b ∧
          ∃ f'' : Real, HasDerivAt (mulNegExpX ep c) f'' z ∧ f'' = 0) →
        zeros'.length ≤ N) :
    ∀ zeros_f : List Real,
      zeros_f.Nodup →
      (∀ z ∈ zeros_f, a < z ∧ z < b ∧ ep.eval z = 0) →
      zeros_f.length ≤ N + 1 := by
  intro zeros_f hnodup hzeros
  have hzeros_g : ∀ z ∈ zeros_f, a < z ∧ z < b ∧ mulNegExpX ep c z = 0 := by
    intro z hz
    obtain ⟨haz, hzb, hfz⟩ := hzeros z hz
    refine ⟨haz, hzb, ?_⟩
    exact (mulNegExpX_zero_iff ep c z).mpr hfz
  have hdiff : ∀ x : Real, a < x → x < b →
                ∃ f' : Real, HasDerivAt (mulNegExpX ep c) f' x := by
    intro x _ _
    refine ⟨_, hasDerivAt_mulNegExpX_raw ep c x⟩
  exact zero_count_bound_by_deriv (mulNegExpX ep c) a b hab hdiff N
          h_reduced_bound zeros_f hnodup hzeros_g

theorem zero_count_scaledReduction_transfer
    (ep : ExpPoly) (c : Real) (a b : Real) (hab : a < b)
    (N : Nat)
    (h_red_bound_eval : ∀ zeros' : List Real,
        zeros'.Nodup →
        (∀ z ∈ zeros', a < z ∧ z < b ∧ (scaledReduction ep c).eval z = 0) →
        zeros'.length ≤ N) :
    ∀ zeros_f : List Real,
      zeros_f.Nodup →
      (∀ z ∈ zeros_f, a < z ∧ z < b ∧ ep.eval z = 0) →
      zeros_f.length ≤ N + 1 := by
  apply zero_count_scaledReduction_transfer_raw ep c a b hab N
  intro zeros' hnodup' hzeros'_prop
  apply h_red_bound_eval zeros' hnodup'
  intro z hz
  obtain ⟨haz, hzb, g'', hg''_deriv, hg''_zero⟩ := hzeros'_prop z hz
  refine ⟨haz, hzb, ?_⟩
  exact scaledReduction_eval_zero_of_aux_deriv_zero ep c z g'' hg''_deriv hg''_zero

/-! ## Base case: length-1 ExpPoly (univariate polynomial)

When `ep.coeffs = [p]`, `ep.eval x = Poly.eval p x * exp(0 * x) = Poly.eval p x`.
Reduces to `poly_root_count_bound`. -/

/-- `exp(0 * x) = 1`. Helper for the length-1 reduction. -/
theorem exp_zero_mul (x : Real) : Real.exp (0 * x) = 1 := by
  rw [zero_mul, exp_zero]

/-- For a length-1 ExpPoly, eval reduces to the univariate polynomial eval. -/
theorem eval_singleton (p : Poly) (x : Real) :
    (⟨[p]⟩ : ExpPoly).eval x = Poly.eval p x := by
  show evalAux [p] 0 x = Poly.eval p x
  show Poly.eval p x * Real.exp ((natCast 0) * x) + evalAux [] (0 + 1) x = Poly.eval p x
  show Poly.eval p x * Real.exp ((natCast 0) * x) + 0 = Poly.eval p x
  rw [show (natCast 0 : Real) = 0 from natCast_zero]
  rw [exp_zero_mul, mul_one_ax, add_zero]

/-- **Base case bound**: length-1 ExpPoly has zero count ≤ `degreeUpper` of its
single coefficient. -/
theorem expPoly_zero_count_bound_length_one
    (p : Poly) (a b : Real) (hab : a < b)
    (hne : ∃ x : Real, (⟨[p]⟩ : ExpPoly).eval x ≠ 0) :
    ∀ zeros : List Real,
      zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ (⟨[p]⟩ : ExpPoly).eval z = 0) →
      zeros.length ≤ degreeUpper p := by
  intro zeros hnodup hzeros
  -- Convert to univariate poly bound.
  have hne' : ∃ x : Real, Poly.eval p x ≠ 0 := by
    obtain ⟨x, hx⟩ := hne
    refine ⟨x, ?_⟩
    rw [← eval_singleton]
    exact hx
  have hzeros' : ∀ z ∈ zeros, a < z ∧ z < b ∧ Poly.eval p z = 0 := by
    intro z hz
    obtain ⟨haz, hzb, hev⟩ := hzeros z hz
    refine ⟨haz, hzb, ?_⟩
    rw [← eval_singleton]
    exact hev
  exact poly_root_count_bound p a b hab hne' zeros hnodup hzeros'

/-! ## Iteration arithmetic (parametric in a reduction witness)

Parallel to the PfaffianFn `IsKhovanskiiReducible` track. Bundle a sequence
of `scaledReduction` applications as a witness, then prove that each step
adds 1 to the Rolle bound. -/

/-- Witness predicate: `ep →* target` via a list of `c` values applied as
successive `scaledReduction` steps. -/
inductive IsIteratedScaledReduction : ExpPoly → ExpPoly → List Real → Prop where
  | refl (ep : ExpPoly) : IsIteratedScaledReduction ep ep []
  | step (ep target : ExpPoly) (c : Real) (cs : List Real)
      (h : IsIteratedScaledReduction (scaledReduction ep c) target cs) :
      IsIteratedScaledReduction ep target (c :: cs)

/-- **Iterated zero count bound (eval form).** Given a reduction witness
`ep →* target` of length `cs.length`, and a bound `N` on `target`'s zeros,
conclude `zeros(ep) ≤ N + cs.length`. -/
theorem expPoly_zero_count_iter_bound
    (ep target : ExpPoly) (cs : List Real)
    (h_iter : IsIteratedScaledReduction ep target cs)
    (a b : Real) (hab : a < b)
    (N : Nat)
    (h_target_bound : ∀ zeros' : List Real,
        zeros'.Nodup →
        (∀ z ∈ zeros', a < z ∧ z < b ∧ target.eval z = 0) →
        zeros'.length ≤ N) :
    ∀ zeros_f : List Real,
      zeros_f.Nodup →
      (∀ z ∈ zeros_f, a < z ∧ z < b ∧ ep.eval z = 0) →
      zeros_f.length ≤ N + cs.length := by
  revert h_target_bound
  induction h_iter with
  | refl ep =>
      intro h_target_bound zeros_f hnodup hzeros
      have := h_target_bound zeros_f hnodup hzeros
      simp
      exact this
  | step ep target c cs h_next ih =>
      intro h_target_bound
      have hred_bound := ih h_target_bound
      have hstep := zero_count_scaledReduction_transfer ep c a b hab (N + cs.length) hred_bound
      intro zeros_f hnodup hzeros
      have := hstep zeros_f hnodup hzeros
      show zeros_f.length ≤ N + (c :: cs).length
      have hlen : (c :: cs).length = cs.length + 1 := rfl
      rw [hlen]
      omega

/-- **Capstone (parametric Khovanskii bound).** Given a reduction witness
landing at a length-1 `target`, with bound on the target via polynomial root
count, conclude an explicit Khovanskii bound on `ep`. -/
theorem expPoly_khovanskii_bound
    (ep : ExpPoly) (p : Poly) (cs : List Real)
    (h_iter : IsIteratedScaledReduction ep ⟨[p]⟩ cs)
    (a b : Real) (hab : a < b)
    (hne : ∃ x : Real, (⟨[p]⟩ : ExpPoly).eval x ≠ 0) :
    ∀ zeros : List Real,
      zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ ep.eval z = 0) →
      zeros.length ≤ degreeUpper p + cs.length := by
  apply expPoly_zero_count_iter_bound ep ⟨[p]⟩ cs h_iter a b hab (degreeUpper p)
  exact expPoly_zero_count_bound_length_one p a b hab hne

end ExpPoly
end SingleExpKhovanskii
end MachLib
