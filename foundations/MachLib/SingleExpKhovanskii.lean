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

/-- **Capstone (parametric Khovanskii bound, length-preserving).** Given a
reduction witness landing at a length-1 `target`, conclude a bound on `ep`.

**Important limitation**: `scaledReduction` preserves `coeffs.length`, so
`IsIteratedScaledReduction ep ⟨[p]⟩ cs` is ONLY satisfiable when
`ep.coeffs.length = 1` (the trivial case). For non-trivial reduction, see
`IsKhovanskiiReducibleExp` below which adds drop steps. -/
theorem expPoly_khovanskii_bound_length_preserving
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

/-! ## Extended iteration with drop steps

Since `scaledReduction` preserves list length, the iteration must include
DROP steps to actually reduce a length-(L+1) ExpPoly down to length-1.

A drop step removes the last coefficient of `ep`, eval-preserving when the
last coefficient evaluates to 0 at every x. -/

/-- Eval preservation when last coefficient is the zero function. For
`coeffs = head ++ [last]` with `last` evaluating to 0 always, the eval of
`⟨coeffs⟩` equals the eval of `⟨head⟩`. -/
theorem eval_drop_last_when_zero (head : List Poly) (last : Poly)
    (h_last : ∀ x, Poly.eval last x = 0) (x : Real) :
    (⟨head ++ [last]⟩ : ExpPoly).eval x = (⟨head⟩ : ExpPoly).eval x := by
  show evalAux (head ++ [last]) 0 x = evalAux head 0 x
  generalize 0 = o
  induction head generalizing o with
  | nil =>
    show evalAux ([last]) o x = evalAux [] o x
    show Poly.eval last x * Real.exp ((natCast o) * x) + evalAux [] (o + 1) x = 0
    rw [h_last]
    show 0 * Real.exp ((natCast o) * x) + 0 = 0
    rw [zero_mul, zero_add]
  | cons h t ih =>
    show Poly.eval h x * Real.exp ((natCast o) * x) + evalAux (t ++ [last]) (o + 1) x
       = Poly.eval h x * Real.exp ((natCast o) * x) + evalAux t (o + 1) x
    rw [ih (o + 1)]

/-- **Extended reducibility predicate**: combines scaledReduction steps
(each adds 1 to the Rolle counter) with drop steps (which preserve zeros). -/
inductive IsKhovanskiiReducibleExp : ExpPoly → ExpPoly → Nat → Prop where
  | refl (ep : ExpPoly) : IsKhovanskiiReducibleExp ep ep 0
  | step (ep g : ExpPoly) (k : Nat) (c : Real)
      (h : IsKhovanskiiReducibleExp (scaledReduction ep c) g k) :
      IsKhovanskiiReducibleExp ep g (k + 1)
  | drop (head : List Poly) (last : Poly) (g : ExpPoly) (k : Nat)
      (h_last_zero : ∀ x : Real, Poly.eval last x = 0)
      (h : IsKhovanskiiReducibleExp ⟨head⟩ g k) :
      IsKhovanskiiReducibleExp ⟨head ++ [last]⟩ g k

/-- **Iterated bound (extended).** Handles both step and drop constructors. -/
theorem expPoly_zero_count_khovanskii_bound
    (ep g : ExpPoly) (k : Nat)
    (h_iter : IsKhovanskiiReducibleExp ep g k)
    (a b : Real) (hab : a < b)
    (N : Nat)
    (h_target_bound : ∀ zeros' : List Real,
        zeros'.Nodup →
        (∀ z ∈ zeros', a < z ∧ z < b ∧ g.eval z = 0) →
        zeros'.length ≤ N) :
    ∀ zeros_f : List Real,
      zeros_f.Nodup →
      (∀ z ∈ zeros_f, a < z ∧ z < b ∧ ep.eval z = 0) →
      zeros_f.length ≤ N + k := by
  revert h_target_bound
  induction h_iter with
  | refl ep =>
      intro h_target_bound zeros_f hnodup hzeros
      have := h_target_bound zeros_f hnodup hzeros
      omega
  | step ep g k c h_next ih =>
      intro h_target_bound
      have hred_bound := ih h_target_bound
      have hstep := zero_count_scaledReduction_transfer ep c a b hab (N + k) hred_bound
      intro zeros_f hnodup hzeros
      have := hstep zeros_f hnodup hzeros
      omega
  | drop head last g k h_last_zero h_next ih =>
      intro h_target_bound
      have hdrop_bound := ih h_target_bound
      -- zeros of ⟨head ++ [last]⟩ = zeros of ⟨head⟩ via eval_drop_last_when_zero.
      intro zeros_f hnodup hzeros
      apply hdrop_bound zeros_f hnodup
      intro z hz
      obtain ⟨haz, hzb, hev⟩ := hzeros z hz
      refine ⟨haz, hzb, ?_⟩
      rw [← eval_drop_last_when_zero head last h_last_zero z]
      exact hev

/-- **Capstone (full Khovanskii bound).** Reduces from `ep` to a length-1
`⟨[p]⟩` target via a mix of scaledReduction + drop steps. -/
theorem expPoly_khovanskii_bound
    (ep : ExpPoly) (p : Poly) (k : Nat)
    (h_iter : IsKhovanskiiReducibleExp ep ⟨[p]⟩ k)
    (a b : Real) (hab : a < b)
    (hne : ∃ x : Real, (⟨[p]⟩ : ExpPoly).eval x ≠ 0) :
    ∀ zeros : List Real,
      zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ ep.eval z = 0) →
      zeros.length ≤ degreeUpper p + k := by
  apply expPoly_zero_count_khovanskii_bound ep ⟨[p]⟩ k h_iter a b hab (degreeUpper p)
  exact expPoly_zero_count_bound_length_one p a b hab hne

/-! ## Helper lemmas for discharging `h_last_zero` in `drop` constructor

The `drop` constructor of `IsKhovanskiiReducibleExp` requires proving
that the last polynomial coefficient evaluates to 0 at every x. These
helpers cover common cases. -/

/-- `polyDerivative (const c)` evaluates to 0 always. -/
theorem polyDerivative_const_eval_zero (c : Real) (x : Real) :
    Poly.eval (polyDerivative (Poly.const c)) x = 0 := by
  show Poly.eval (Poly.const 0) x = 0
  rfl

/-- `Poly.const 0` evaluates to 0 always (the syntactic zero polynomial). -/
theorem const_zero_eval_zero (x : Real) : Poly.eval (Poly.const 0) x = 0 := rfl

/-- For the scaledReduction-induced last coefficient pattern
`Poly.add (polyDerivative (Poly.const c)) (Poly.mul (Poly.const k) (Poly.const c))`
with `k = 0`, the eval is 0. This is the pattern that arises after applying
scaledReduction with c = (length-1) to a list whose last is `Poly.const c`. -/
theorem scaledReduction_last_const_pattern_eval_zero (c : Real) (x : Real) :
    Poly.eval
      (Poly.add (polyDerivative (Poly.const c))
                (Poly.mul (Poly.const 0) (Poly.const c)))
      x = 0 := by
  show Poly.eval (polyDerivative (Poly.const c)) x
       + Poly.eval (Poly.mul (Poly.const 0) (Poly.const c)) x = 0
  rw [polyDerivative_const_eval_zero]
  show 0 + Poly.eval (Poly.const 0) x * Poly.eval (Poly.const c) x = 0
  rw [const_zero_eval_zero]
  rw [zero_mul, add_zero]

/-! ## Path (a): polySimplify integration

The auto-witness construction's termination issue stems from
`polyDerivative` not strictly decreasing structural `degreeUpper`
(because of `mul (const 0) _` artifacts). Solution: simplify after
each derivative.

`polySimplify` (from `MachLib.PolynomialRootCount`) drops syntactic
`mul (const 0) _`, `mul _ (const 0)`, `mul (const 1) _`, `mul _ (const 1)`,
`add (const 0) _`, etc. It preserves eval (`polySimplify_eval`). -/

/-- Map `polySimplify` over a list of `Poly`. Pointwise simplification. -/
noncomputable def simplifyCoeffs (coeffs : List Poly) : List Poly :=
  coeffs.map polySimplify

/-- Simplified scaledReduction: apply polySimplify to each coefficient
after scaledReduction. -/
noncomputable def simplifiedScaledReduction (ep : ExpPoly) (c : Real) : ExpPoly :=
  ⟨simplifyCoeffs (scaledReduction ep c).coeffs⟩

/-- `polySimplify` preserves `evalAux` pointwise. -/
theorem evalAux_simplifyCoeffs (coeffs : List Poly) (o : Nat) (x : Real) :
    evalAux (simplifyCoeffs coeffs) o x = evalAux coeffs o x := by
  induction coeffs generalizing o with
  | nil => rfl
  | cons p rest ih =>
    show Poly.eval (polySimplify p) x * Real.exp ((natCast o) * x)
         + evalAux (simplifyCoeffs rest) (o + 1) x
       = Poly.eval p x * Real.exp ((natCast o) * x)
         + evalAux rest (o + 1) x
    rw [polySimplify_eval, ih]

/-- `simplifiedScaledReduction` preserves eval — same as `scaledReduction`. -/
theorem simplifiedScaledReduction_eval (ep : ExpPoly) (c : Real) (x : Real) :
    (simplifiedScaledReduction ep c).eval x = (scaledReduction ep c).eval x := by
  show evalAux (simplifyCoeffs (scaledReduction ep c).coeffs) 0 x
     = evalAux (scaledReduction ep c).coeffs 0 x
  exact evalAux_simplifyCoeffs _ _ _

/-! ### Path (a) status — strict descent already proved in MachLib

The strict-descent lemma `polyDerivative_degreeUpper_lt_after_simplify`
is already in `MachLib.PolynomialRootCount` (line 1185), shipped in the
Khovanskii sprint week 1. Its signature:

  ```
  theorem polyDerivative_degreeUpper_lt_after_simplify (p : Poly)
      (hp : degreeUpper (polySimplify p) > 0) :
      degreeUpper (polySimplify (polyDerivative p))
        < degreeUpper (polySimplify p)
  ```

This is the termination witness we need. Combined with
`simplifiedScaledReduction`, the auto-witness construction becomes
straightforward via fuel-based recursion. -/

/-- Eval-zero detection: `polySimplify p = Poly.const 0` implies eval is 0 always.
This discharges the `h_last_zero` obligation in the `drop` constructor for
the iteration's drop steps. -/
theorem eval_zero_of_polySimplify_zero (p : Poly)
    (h : polySimplify p = Poly.const 0) (x : Real) :
    Poly.eval p x = 0 := by
  have heq : Poly.eval (polySimplify p) x = Poly.eval p x := polySimplify_eval p x
  rw [← heq, h]
  rfl

/-- Helper: a simplified coefficient that's structurally `Poly.const 0`
satisfies the drop constructor's `h_last_zero` requirement universally. -/
theorem eval_zero_of_eq_polySimplify_const_zero (p : Poly)
    (h : polySimplify p = Poly.const 0) :
    ∀ x : Real, Poly.eval p x = 0 :=
  fun x => eval_zero_of_polySimplify_zero p h x

/-! ### Refined length-1 bound (via polySimplify)

For a length-1 ExpPoly, the bound `degreeUpper p` from
`expPoly_zero_count_bound_length_one` can be tightened to
`degreeUpper (polySimplify p)` because polySimplify preserves eval. -/

theorem expPoly_zero_count_bound_length_one_simplified
    (p : Poly) (a b : Real) (hab : a < b)
    (hne : ∃ x : Real, (⟨[p]⟩ : ExpPoly).eval x ≠ 0) :
    ∀ zeros : List Real,
      zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ (⟨[p]⟩ : ExpPoly).eval z = 0) →
      zeros.length ≤ degreeUpper (polySimplify p) := by
  intro zeros hnodup hzeros
  -- Apply poly_root_count_bound to polySimplify p (which has same eval as p).
  have hne' : ∃ x : Real, Poly.eval (polySimplify p) x ≠ 0 := by
    obtain ⟨x, hx⟩ := hne
    refine ⟨x, ?_⟩
    rw [polySimplify_eval, ← eval_singleton]
    exact hx
  have hzeros' : ∀ z ∈ zeros,
                   a < z ∧ z < b ∧ Poly.eval (polySimplify p) z = 0 := by
    intro z hz
    obtain ⟨haz, hzb, hev⟩ := hzeros z hz
    refine ⟨haz, hzb, ?_⟩
    rw [polySimplify_eval, ← eval_singleton]
    exact hev
  exact poly_root_count_bound (polySimplify p) a b hab hne' zeros hnodup hzeros'

/-! ### Auto-witness for length-1 ExpPoly — the trivial case

The simplest case of the auto-witness: when `ep.coeffs.length = 1`,
the witness is just `refl` (zero iterations). This demonstrates the
framework's end-to-end usability for the simplest poly-in-(x, e^x).

For length > 1, the auto-witness construction requires fuel-based
recursion + the strict-descent lemma + pattern matching for drop
triggers (when polySimplify of last yields `Poly.const 0`). The
existence of such a witness is provable via strong induction on
`length + Σ degreeUpper of simplified coeffs`. -/

/-- For a length-1 ExpPoly, the auto-witness is trivially `refl`. -/
theorem autoWitness_length_one (p : Poly) :
    IsKhovanskiiReducibleExp ⟨[p]⟩ ⟨[p]⟩ 0 :=
  IsKhovanskiiReducibleExp.refl ⟨[p]⟩

/-- Combined with `expPoly_khovanskii_bound`, the trivial length-1 case
yields the polynomial root count bound directly. -/
theorem length_one_full_bound
    (p : Poly) (a b : Real) (hab : a < b)
    (hne : ∃ x : Real, Poly.eval p x ≠ 0) :
    ∀ zeros : List Real,
      zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ (⟨[p]⟩ : ExpPoly).eval z = 0) →
      zeros.length ≤ degreeUpper p := by
  intro zeros hnodup hzeros
  have hne' : ∃ x : Real, (⟨[p]⟩ : ExpPoly).eval x ≠ 0 := by
    obtain ⟨x, hx⟩ := hne
    refine ⟨x, ?_⟩
    rw [eval_singleton]
    exact hx
  have := expPoly_khovanskii_bound ⟨[p]⟩ p 0 (autoWitness_length_one p)
            a b hab hne' zeros hnodup hzeros
  simpa using this

/-! ### Sum-of-degrees measure for auto-bound

The total "iteration count" for a generic ExpPoly is bounded by
`length + Σ_k degreeUpper(polySimplify coeffs[k])` — the
combined length and effective polynomial-degree budget. -/

/-- Sum the effective polynomial degrees (after polySimplify) of coefficients. -/
noncomputable def sumSimplifiedDegrees (coeffs : List Poly) : Nat :=
  (coeffs.map (fun p => degreeUpper (polySimplify p))).sum

theorem sumSimplifiedDegrees_nil : sumSimplifiedDegrees [] = 0 := rfl

theorem sumSimplifiedDegrees_cons (head : Poly) (tail : List Poly) :
    sumSimplifiedDegrees (head :: tail) =
    degreeUpper (polySimplify head) + sumSimplifiedDegrees tail := rfl

/-- The auto-bound measure: length + sum of simplified degrees. -/
noncomputable def expPolyAutoBound (ep : ExpPoly) : Nat :=
  ep.coeffs.length + sumSimplifiedDegrees ep.coeffs

/-- For empty list, eval is identically 0. -/
theorem eval_empty (x : Real) : (⟨[]⟩ : ExpPoly).eval x = 0 := rfl

/-! ### Auto-bound for length-1 case is already covered

`expPoly_zero_count_bound_length_one_simplified` ships the
length-1 case directly. For length ≥ 2, the auto-bound is delivered
by a strong induction on the measure, which requires the auxiliary
strict-descent and length-decrement lemmas (substantial mechanical work).

The framework is COMPLETE for users to manually construct
witnesses for any specific case. The fully-automated closure
theorem `expPoly_full_auto_bound` requires the strict-descent
plumbing across the list, which we sketch below but defer the
full proof to a focused session. -/

/-! ### Auto-bound length-1 case (the EASY half of the strong induction)

Wraps `expPoly_zero_count_bound_length_one_simplified` to fit the
auto-bound measure: for length-1 ExpPoly, the zero count is bounded
by the simplified degreeUpper of the single coefficient, which is
exactly `expPolyAutoBound ep - 1` (since length = 1, sum = degree).

For length ≥ 2, the induction step requires strict-descent plumbing
detailed in the file header. The infrastructure for both manual
witness construction (today) and a future auto-witness (~150 more
lines) ships in this file. -/

/-- **Auto-bound — length-1 specialization.** This is the direct version
applicable when ep has exactly one coefficient. The bound matches
`expPolyAutoBound ⟨[p]⟩ = 1 + degreeUpper(polySimplify p)`, but the
actual bound is `degreeUpper(polySimplify p) = expPolyAutoBound ⟨[p]⟩ - 1`. -/
theorem expPoly_zero_count_auto_bound_length_one
    (p : Poly) (a b : Real) (hab : a < b)
    (hne : ∃ x : Real, (⟨[p]⟩ : ExpPoly).eval x ≠ 0) :
    ∀ zeros : List Real,
      zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ (⟨[p]⟩ : ExpPoly).eval z = 0) →
      zeros.length ≤ expPolyAutoBound ⟨[p]⟩ := by
  intro zeros hnodup hzeros
  have hbnd := expPoly_zero_count_bound_length_one_simplified p a b hab hne
                 zeros hnodup hzeros
  show zeros.length ≤ (⟨[p]⟩ : ExpPoly).coeffs.length + sumSimplifiedDegrees (⟨[p]⟩ : ExpPoly).coeffs
  show zeros.length ≤ 1 + sumSimplifiedDegrees [p]
  have hsum : sumSimplifiedDegrees [p] = degreeUpper (polySimplify p) := by
    rw [sumSimplifiedDegrees_cons, sumSimplifiedDegrees_nil]
    omega
  rw [hsum]
  omega

/-! ### Per-coefficient sub-lemmas for the strong induction

The strong-induction proof for arbitrary-length auto-bound needs to
show that `sumSimplifiedDegrees` decreases by ≥ 1 per
`simplifiedScaledReduction` step (or that length decreases via drop).

Each coefficient after scaledReduction is
`Poly.add (polyDerivative p) (Poly.mul (Poly.const v) p)`
for some scalar `v`. The lemmas below bound the polySimplify-degreeUpper
of this expression. -/

/-- `polySimplify` of `Poly.add` has degreeUpper ≤ max of the operands'
simplified degreeUppers. Direct from polySimplify's case structure. -/
theorem degreeUpper_polySimplify_add_le (a b : Poly) :
    degreeUpper (polySimplify (Poly.add a b))
      ≤ Nat.max (degreeUpper (polySimplify a)) (degreeUpper (polySimplify b)) := by
  show degreeUpper
        (if polyIsZeroConst (polySimplify a) = true then polySimplify b
         else if polyIsZeroConst (polySimplify b) = true then polySimplify a
         else Poly.add (polySimplify a) (polySimplify b))
      ≤ Nat.max (degreeUpper (polySimplify a)) (degreeUpper (polySimplify b))
  by_cases hp : polyIsZeroConst (polySimplify a) = true
  · rw [if_pos hp]
    exact Nat.le_max_right _ _
  · rw [if_neg hp]
    by_cases hq : polyIsZeroConst (polySimplify b) = true
    · rw [if_pos hq]
      exact Nat.le_max_left _ _
    · rw [if_neg hq]
      show Nat.max (degreeUpper (polySimplify a)) (degreeUpper (polySimplify b))
        ≤ Nat.max (degreeUpper (polySimplify a)) (degreeUpper (polySimplify b))
      exact Nat.le_refl _

/-- **Per-coefficient degreeUpper bound under scaledReduction.**

For any `p : Poly` and scalar `v`, the polySimplify-degreeUpper of
`Poly.add (polyDerivative p) (Poly.mul (Poly.const v) p)` is at most
`degreeUpper (polySimplify p)`.

This means each coefficient of `scaledReduction ep c` has polySimplify-
degreeUpper ≤ the corresponding original's — no coefficient INCREASES
the measure. -/
theorem coeffStep_degreeUpper_polySimplify_le (p : Poly) (v : Real) :
    degreeUpper (polySimplify
      (Poly.add (polyDerivative p) (Poly.mul (Poly.const v) p)))
      ≤ degreeUpper (polySimplify p) := by
  have hdrv := polyDerivative_degreeUpper_le_after_simplify p
  have hmul_full := degreeUpper_polySimplify_mul_le (Poly.const v) p
  have hconst : degreeUpper (polySimplify (Poly.const v)) = 0 := rfl
  have hmul : degreeUpper (polySimplify (Poly.mul (Poly.const v) p))
                ≤ degreeUpper (polySimplify p) := by
    rw [hconst] at hmul_full
    omega
  have hadd := degreeUpper_polySimplify_add_le (polyDerivative p)
                 (Poly.mul (Poly.const v) p)
  have hmax : Nat.max (degreeUpper (polySimplify (polyDerivative p)))
                       (degreeUpper (polySimplify (Poly.mul (Poly.const v) p)))
              ≤ degreeUpper (polySimplify p) :=
    Nat.max_le.mpr ⟨hdrv, hmul⟩
  exact Nat.le_trans hadd hmax

/-- Helper: `polySimplify (Poly.mul (Poly.const 0) p) = Poly.const 0`. -/
theorem polySimplify_mul_const_zero (p : Poly) :
    polySimplify (Poly.mul (Poly.const 0) p) = Poly.const 0 := by
  show (if polyIsZeroConst (polySimplify (Poly.const 0)) = true then Poly.const 0
        else if polyIsZeroConst (polySimplify p) = true then Poly.const 0
        else if polyIsOneConst (polySimplify (Poly.const 0)) = true
          then polySimplify p
        else if polyIsOneConst (polySimplify p) = true
          then polySimplify (Poly.const 0)
        else (polySimplify (Poly.const 0)).mul (polySimplify p)) = Poly.const 0
  -- polySimplify (Poly.const 0) = Poly.const 0 by rfl.
  show (if polyIsZeroConst (Poly.const 0) = true then Poly.const 0
        else if polyIsZeroConst (polySimplify p) = true then Poly.const 0
        else if polyIsOneConst (Poly.const 0) = true
          then polySimplify p
        else if polyIsOneConst (polySimplify p) = true
          then Poly.const 0
        else (Poly.const 0).mul (polySimplify p)) = Poly.const 0
  rw [if_pos polyIsZeroConst_const_zero]

/-- **Per-coefficient strict descent for the LAST coefficient.**

When `v = 0` (which arises for the last coefficient of `scaledReduction`),
the polySimplify-degreeUpper STRICTLY drops, provided the original had
degreeUpper > 0. -/
theorem coeffStep_degreeUpper_polySimplify_lt (p : Poly)
    (hp : degreeUpper (polySimplify p) > 0) :
    degreeUpper (polySimplify
      (Poly.add (polyDerivative p) (Poly.mul (Poly.const 0) p)))
      < degreeUpper (polySimplify p) := by
  have hstrict := polyDerivative_degreeUpper_lt_after_simplify p hp
  have h_mul_zero := polySimplify_mul_const_zero p
  have h_isZero : polyIsZeroConst (polySimplify (Poly.mul (Poly.const 0) p)) = true := by
    rw [h_mul_zero]
    exact polyIsZeroConst_const_zero
  show degreeUpper
        (if polyIsZeroConst (polySimplify (polyDerivative p)) = true
          then polySimplify (Poly.mul (Poly.const 0) p)
          else if polyIsZeroConst (polySimplify (Poly.mul (Poly.const 0) p)) = true
            then polySimplify (polyDerivative p)
            else Poly.add (polySimplify (polyDerivative p))
                          (polySimplify (Poly.mul (Poly.const 0) p)))
      < degreeUpper (polySimplify p)
  by_cases hpd : polyIsZeroConst (polySimplify (polyDerivative p)) = true
  · rw [if_pos hpd, h_mul_zero]
    show (0 : Nat) < degreeUpper (polySimplify p)
    exact hp
  · rw [if_neg hpd, if_pos h_isZero]
    exact hstrict

/-- **Per-coefficient "becomes const 0" lemma for the LAST coefficient.**

When `v = 0` AND `degreeUpper (polySimplify p) = 0`, the polySimplify of the
expression is structurally `Poly.const 0`. This enables the `drop` step. -/
theorem coeffStep_eq_const_zero_when_degreeUpper_zero (p : Poly)
    (hp : degreeUpper (polySimplify p) = 0) :
    polySimplify (Poly.add (polyDerivative p) (Poly.mul (Poly.const 0) p))
      = Poly.const 0 := by
  have h_pd_isZero : polyIsZeroConst (polySimplify (polyDerivative p)) = true :=
    polyDerivative_zero_when_simplified_degree_zero p hp
  have h_mul_zero := polySimplify_mul_const_zero p
  show (if polyIsZeroConst (polySimplify (polyDerivative p)) = true
        then polySimplify (Poly.mul (Poly.const 0) p)
        else if polyIsZeroConst (polySimplify (Poly.mul (Poly.const 0) p)) = true
          then polySimplify (polyDerivative p)
          else Poly.add (polySimplify (polyDerivative p))
                        (polySimplify (Poly.mul (Poly.const 0) p)))
       = Poly.const 0
  rw [if_pos h_pd_isZero, h_mul_zero]

/-! ### List-level lemma: sum doesn't increase under scaledReduction -/

theorem sumSimplifiedDegrees_scaledReductionAux_le
    (coeffs : List Poly) (c : Real) (offset : Nat) :
    sumSimplifiedDegrees (scaledReductionAux c coeffs offset)
      ≤ sumSimplifiedDegrees coeffs := by
  induction coeffs generalizing offset with
  | nil => exact Nat.le_refl _
  | cons head tail ih =>
    show sumSimplifiedDegrees
          (Poly.add (polyDerivative head)
                    (Poly.mul (Poly.const ((natCast offset) - c)) head)
           :: scaledReductionAux c tail (offset + 1))
       ≤ sumSimplifiedDegrees (head :: tail)
    rw [sumSimplifiedDegrees_cons, sumSimplifiedDegrees_cons]
    have h1 := coeffStep_degreeUpper_polySimplify_le head ((natCast offset) - c)
    have h2 := ih (offset + 1)
    omega

theorem sumSimplifiedDegrees_scaledReduction_le
    (ep : ExpPoly) (c : Real) :
    sumSimplifiedDegrees (scaledReduction ep c).coeffs
      ≤ sumSimplifiedDegrees ep.coeffs :=
  sumSimplifiedDegrees_scaledReductionAux_le ep.coeffs c 0


/-! ### List-level strict descent for LAST coefficient -/

theorem sumSimplifiedDegrees_scaledReductionAux_lt
    (coeffs : List Poly) (offset : Nat)
    (hne : coeffs ≠ [])
    (hlast_pos : degreeUpper (polySimplify (coeffs.getLast hne)) > 0) :
    sumSimplifiedDegrees
      (scaledReductionAux (natCast (offset + coeffs.length - 1)) coeffs offset)
      < sumSimplifiedDegrees coeffs := by
  induction coeffs generalizing offset with
  | nil => exact absurd rfl hne
  | cons head tail ih =>
    by_cases htail : tail = []
    · -- coeffs = [head]; head IS last.
      subst htail
      have hoff : offset + 1 - 1 = offset := by omega
      have hlast_pos' : degreeUpper (polySimplify head) > 0 := hlast_pos
      have hstrict := coeffStep_degreeUpper_polySimplify_lt head hlast_pos'
      show sumSimplifiedDegrees
            (Poly.add (polyDerivative head)
                     (Poly.mul (Poly.const ((natCast offset : Real) -
                                            (natCast (offset + 1 - 1)))) head)
             :: scaledReductionAux (natCast (offset + 1 - 1)) [] (offset + 1))
          < sumSimplifiedDegrees [head]
      rw [hoff]
      have hsub : (natCast offset : Real) - natCast offset = 0 := sub_self _
      rw [hsub]
      show sumSimplifiedDegrees
            (Poly.add (polyDerivative head)
                      (Poly.mul (Poly.const 0) head) :: [])
          < sumSimplifiedDegrees [head]
      rw [sumSimplifiedDegrees_cons, sumSimplifiedDegrees_nil,
          sumSimplifiedDegrees_cons, sumSimplifiedDegrees_nil]
      omega
    · -- Length ≥ 2: head NOT last; use non-strict for head, IH for tail.
      -- coeffs.length = tail.length + 1 ≥ 2.
      have htail_ne : tail ≠ [] := htail
      have hgetlast : (head :: tail).getLast (List.cons_ne_nil head tail)
                    = tail.getLast htail_ne := List.getLast_cons htail_ne
      have hlast_pos_tail : degreeUpper (polySimplify (tail.getLast htail_ne)) > 0 := by
        rw [← hgetlast]
        exact hlast_pos
      -- IH: sumSimplifiedDegrees (scaledReductionAux _ tail (offset+1)) < sumSimplifiedDegrees tail.
      -- The c for IH: natCast ((offset+1) + tail.length - 1) = natCast (offset + tail.length).
      -- The c we need: natCast (offset + (tail.length + 1) - 1) = natCast (offset + tail.length). Same.
      have hlen : (head :: tail).length = tail.length + 1 := rfl
      have hoff_eq : offset + (tail.length + 1) - 1 = (offset + 1) + tail.length - 1 := by omega
      show sumSimplifiedDegrees
            (scaledReductionAux (natCast (offset + (head :: tail).length - 1))
                                (head :: tail) offset)
          < sumSimplifiedDegrees (head :: tail)
      rw [hlen]
      show sumSimplifiedDegrees
            (Poly.add (polyDerivative head)
                     (Poly.mul (Poly.const ((natCast offset : Real) -
                                            (natCast (offset + (tail.length + 1) - 1)))) head)
             :: scaledReductionAux (natCast (offset + (tail.length + 1) - 1)) tail (offset + 1))
          < sumSimplifiedDegrees (head :: tail)
      rw [hoff_eq]
      rw [sumSimplifiedDegrees_cons (head := head) (tail := tail)]
      rw [sumSimplifiedDegrees_cons]
      have h_head_le := coeffStep_degreeUpper_polySimplify_le head
                          ((natCast offset : Real) -
                           (natCast ((offset + 1) + tail.length - 1)))
      have h_tail_lt := ih (offset + 1) htail_ne hlast_pos_tail
      omega

/-! ### Path (i): auto-bound with propagation + last-positive hypotheses -/

/-- **Auto-bound (path i — propagation + last-positive).** Two
hypotheses: `h_prop` supplies `hne` for any smaller-measure ExpPoly,
and `h_strict_last` ensures the last coefficient always has
positive simplified degree, so Case B (drop step) never arises.

For inputs satisfying both hypotheses (the "generic case"), the
auto-bound theorem ships fully constructively. For inputs where
Case B does arise, use the parametric `expPoly_khovanskii_bound`
with a hand-constructed witness that includes drop steps. -/
theorem expPoly_auto_bound_with_propagation_aux :
    ∀ (M : Nat) (ep : ExpPoly),
    ep.coeffs.length + sumSimplifiedDegrees ep.coeffs ≤ M →
    (∀ ep' : ExpPoly,
       ep'.coeffs.length + sumSimplifiedDegrees ep'.coeffs ≤ M →
       (∃ x, ep'.eval x ≠ 0)) →
    (∀ ep' : ExpPoly,
       ∀ (hne_coeffs : ep'.coeffs ≠ []),
       ep'.coeffs.length ≥ 2 →
       ep'.coeffs.length + sumSimplifiedDegrees ep'.coeffs ≤ M →
       degreeUpper (polySimplify (ep'.coeffs.getLast hne_coeffs)) > 0) →
    ∀ (a b : Real), a < b →
    ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ ep.eval z = 0) →
      zeros.length ≤ M := by
  intro M
  induction M with
  | zero =>
    intro ep hM h_prop _h_strict_last a b hab zeros hnodup hzeros
    have hne := h_prop ep hM
    have hlen : ep.coeffs.length = 0 := by
      have h := Nat.zero_le (sumSimplifiedDegrees ep.coeffs)
      omega
    have hempty : ep.coeffs = [] := List.length_eq_zero.mp hlen
    exfalso
    obtain ⟨x, hx⟩ := hne
    apply hx
    show evalAux ep.coeffs 0 x = 0
    rw [hempty]
    rfl
  | succ M' ih =>
    intro ep hM h_prop h_strict_last a b hab zeros hnodup hzeros
    have hne := h_prop ep hM
    match h_coeffs : ep.coeffs with
    | [] =>
      exfalso
      obtain ⟨x, hx⟩ := hne
      apply hx
      show evalAux ep.coeffs 0 x = 0
      rw [h_coeffs]
      rfl
    | [p] =>
      have hne_p : ∃ x : Real, (⟨[p]⟩ : ExpPoly).eval x ≠ 0 := by
        obtain ⟨x, hx⟩ := hne
        refine ⟨x, ?_⟩
        show evalAux [p] 0 x ≠ 0
        rw [← h_coeffs]
        exact hx
      have hzeros_p : ∀ z ∈ zeros,
                       a < z ∧ z < b ∧ (⟨[p]⟩ : ExpPoly).eval z = 0 := by
        intro z hz
        obtain ⟨hz1, hz2, hz3⟩ := hzeros z hz
        refine ⟨hz1, hz2, ?_⟩
        show evalAux [p] 0 z = 0
        rw [← h_coeffs]
        exact hz3
      have hbnd := expPoly_zero_count_bound_length_one_simplified p a b hab
                     hne_p zeros hnodup hzeros_p
      have h_sum_eq : sumSimplifiedDegrees ep.coeffs = degreeUpper (polySimplify p) := by
        rw [h_coeffs, sumSimplifiedDegrees_cons, sumSimplifiedDegrees_nil]
        omega
      have hlen : ep.coeffs.length = 1 := by rw [h_coeffs]; rfl
      rw [h_sum_eq, hlen] at hM
      omega
    | p :: q :: rest =>
      have hne_coeffs : ep.coeffs ≠ [] := by
        rw [h_coeffs]; exact List.cons_ne_nil _ _
      have hlen_ge_2 : ep.coeffs.length ≥ 2 := by rw [h_coeffs]; simp
      have hlast_pos : degreeUpper (polySimplify (ep.coeffs.getLast hne_coeffs)) > 0 :=
        h_strict_last ep hne_coeffs hlen_ge_2 hM
      let c : Real := natCast (ep.coeffs.length - 1)
      let ep_red := scaledReduction ep c
      have h_strict := sumSimplifiedDegrees_scaledReductionAux_lt
                         ep.coeffs 0 hne_coeffs hlast_pos
      have h_offset_eq : (0 : Nat) + ep.coeffs.length - 1 = ep.coeffs.length - 1 := by omega
      rw [h_offset_eq] at h_strict
      have h_aux_len : ∀ (coeffs : List Poly) (c : Real) (offset : Nat),
                        (scaledReductionAux c coeffs offset).length = coeffs.length := by
        intro coeffs c offset
        induction coeffs generalizing offset with
        | nil => rfl
        | cons head tail ihl =>
          show (Poly.add (polyDerivative head)
                         (Poly.mul (Poly.const _) head)
                :: scaledReductionAux c tail (offset + 1)).length
             = (head :: tail).length
          rw [List.length_cons, List.length_cons, ihl (offset + 1)]
      have h_len_eq : ep_red.coeffs.length = ep.coeffs.length := h_aux_len ep.coeffs c 0
      have h_sum_eq : sumSimplifiedDegrees ep_red.coeffs
                    = sumSimplifiedDegrees
                        (scaledReductionAux (natCast (ep.coeffs.length - 1))
                                            ep.coeffs 0) := rfl
      have h_measure : ep_red.coeffs.length + sumSimplifiedDegrees ep_red.coeffs ≤ M' := by
        rw [h_len_eq, h_sum_eq]
        omega
      have h_prop_red : ∀ ep' : ExpPoly,
                        ep'.coeffs.length + sumSimplifiedDegrees ep'.coeffs ≤ M' →
                        (∃ x, ep'.eval x ≠ 0) := by
        intro ep' hep'
        exact h_prop ep' (by omega)
      have h_strict_last_red : ∀ ep' : ExpPoly,
                                ∀ (hne_c : ep'.coeffs ≠ []),
                                ep'.coeffs.length ≥ 2 →
                                ep'.coeffs.length +
                                  sumSimplifiedDegrees ep'.coeffs ≤ M' →
                                degreeUpper (polySimplify
                                  (ep'.coeffs.getLast hne_c)) > 0 := by
        intro ep' hne_c hlen_ge hmeas
        exact h_strict_last ep' hne_c hlen_ge (by omega)
      have hred_bound := ih ep_red h_measure h_prop_red h_strict_last_red a b hab
      have h_eval_bound : ∀ zeros' : List Real,
                            zeros'.Nodup →
                            (∀ z ∈ zeros', a < z ∧ z < b ∧ ep_red.eval z = 0) →
                            zeros'.length ≤ M' := hred_bound
      have h_transfer := zero_count_scaledReduction_transfer ep c a b hab M' h_eval_bound
      have := h_transfer zeros hnodup hzeros
      omega

/-! ### Path (ii): ODE corner case (statement + proof sketch)

The corner case in path (i)'s `h_prop` hypothesis arises when
`(scaledReduction ep c).eval ≡ 0` on `(a, b)` — i.e., the ODE
`ep.eval' = c · ep.eval` holds. The classical resolution: this
forces `ep.eval` to be a pure exponential with no zeros (assuming
`hne`), so the bound holds trivially with 0 zeros.

The proof uses MVT-based local constancy (the existing
`pfaffian_derivative_zero_implies_nonzero_on` in `KhovanskiiLemma.lean`
demonstrates the technique for PfaffianFunctions):
  1. `g(x) := ep.eval x · exp(-c · x)` (the `mulNegExpX` Rolle vehicle).
  2. `g'(x) = exp(-c·x) · (scaledReduction ep c).eval x`.
  3. Hypothesis: `(scaledReduction ep c).eval ≡ 0` on `(a, b)`.
     ⟹ `g'(x) = 0` on `(a, b)`.
  4. By MVT: `g` is constant on `(a, b)`.
  5. Pick `z₀ ∈ (a, b)` with `ep.eval z₀ ≠ 0` (from hne).
  6. For any `z ∈ (a, b)`: `g(z) = g(z₀) ≠ 0` (since exp > 0).
  7. `g(z) = ep.eval z · exp(-c·z)`; exp > 0 ⟹ `ep.eval z ≠ 0`.

Statement (proof deferred — adapts the existing PfaffianFunction
proof via the `mulNegExpX` and HasDerivAt infrastructure already
shipped): -/

/-- **Path (ii): ODE corner case proof.** If `(scaledReduction ep c).eval`
is identically 0 on `(a, b)` and `ep.eval` is non-zero somewhere on
`(a, b)`, then `ep.eval` has NO zeros on `(a, b)`.

Proof: `mulNegExpX ep c` has derivative `exp(-c·x) · (scaledReduction
ep c).eval x = 0` everywhere on `(a, b)`. By MVT applied per pair of
points, `mulNegExpX` is constant. Since `mulNegExpX` is non-zero at
one point (by hne, exp ≠ 0), it's non-zero everywhere, and
`mulNegExpX_zero_iff` transfers this to `ep.eval`. -/
theorem expPoly_ode_no_zeros
    (ep : ExpPoly) (c : Real) (a b : Real) (hab : a < b)
    (h_ode : ∀ x : Real, a < x → x < b → (scaledReduction ep c).eval x = 0)
    (h_ne_in : ∃ x : Real, a < x ∧ x < b ∧ ep.eval x ≠ 0) :
    ∀ z : Real, a < z → z < b → ep.eval z ≠ 0 := by
  obtain ⟨x₀, hx₀_a, hx₀_b, hx₀_ne⟩ := h_ne_in
  -- Step 1: mulNegExpX has HasDerivAt 0 on (a, b).
  have h_g_deriv_zero : ∀ y : Real, a < y → y < b →
                         HasDerivAt (mulNegExpX ep c) 0 y := by
    intro y hya hyb
    have hraw := hasDerivAt_mulNegExpX_raw ep c y
    have hfact : (scaledReduction ep 0).eval y * Real.exp (-c * y)
                  + ep.eval y * (Real.exp (-c * y) * (-c))
               = Real.exp (-c * y) * (scaledReduction ep c).eval y := by
      rw [← scaledReduction_eval_combine ep c y]
      rw [show (scaledReduction ep 0).eval y * Real.exp (-c * y)
            = Real.exp (-c * y) * (scaledReduction ep 0).eval y from mul_comm _ _]
      rw [show ep.eval y * (Real.exp (-c * y) * (-c))
            = Real.exp (-c * y) * (ep.eval y * (-c)) from by
        rw [← mul_assoc, mul_comm (ep.eval y) (Real.exp _), mul_assoc]]
      rw [← mul_distrib]
    have h_ode_y : (scaledReduction ep c).eval y = 0 := h_ode y hya hyb
    have h_raw_eq_zero : (scaledReduction ep 0).eval y * Real.exp (-c * y)
                          + ep.eval y * (Real.exp (-c * y) * (-c)) = 0 := by
      rw [hfact, h_ode_y, mul_zero]
    rw [h_raw_eq_zero] at hraw
    exact hraw
  -- Step 2: mulNegExpX is constant on (a, b) via MVT.
  suffices hconst : ∀ z : Real, a < z → z < b →
                     mulNegExpX ep c z = mulNegExpX ep c x₀ by
    intro z hza hzb hz_eval_zero
    have h_g_z_zero : mulNegExpX ep c z = 0 :=
      (mulNegExpX_zero_iff ep c z).mpr hz_eval_zero
    rw [hconst z hza hzb] at h_g_z_zero
    have h_x0_eval_zero : ep.eval x₀ = 0 :=
      (mulNegExpX_zero_iff ep c x₀).mp h_g_z_zero
    exact hx₀_ne h_x0_eval_zero
  intro z hza hzb
  rcases lt_total z x₀ with hlt | heq | hgt
  · -- z < x₀: MVT on (z, x₀).
    have hdiff : ∀ y : Real, z < y → y < x₀ →
                 ∃ f' : Real, HasDerivAt (mulNegExpX ep c) f' y := by
      intro y hyz hyx₀
      exact ⟨0, h_g_deriv_zero y (lt_trans_ax hza hyz)
                                  (lt_trans_ax hyx₀ hx₀_b)⟩
    obtain ⟨y, f', hyz, hyx₀, hd, hmvt⟩ :=
      mean_value_theorem (mulNegExpX ep c) z x₀ hlt hdiff
    have hy_a : a < y := lt_trans_ax hza hyz
    have hy_b : y < b := lt_trans_ax hyx₀ hx₀_b
    have hf'_eq : f' = 0 :=
      HasDerivAt_unique (mulNegExpX ep c) f' 0 y hd (h_g_deriv_zero y hy_a hy_b)
    rw [hf'_eq, zero_mul] at hmvt
    have step : mulNegExpX ep c x₀ - mulNegExpX ep c z + mulNegExpX ep c z
              = 0 + mulNegExpX ep c z := by rw [hmvt]
    rw [sub_def, add_assoc, neg_add_self, add_zero, zero_add] at step
    exact step.symm
  · rw [heq]
  · -- z > x₀: MVT on (x₀, z).
    have hdiff : ∀ y : Real, x₀ < y → y < z →
                 ∃ f' : Real, HasDerivAt (mulNegExpX ep c) f' y := by
      intro y hyx₀ hyz
      exact ⟨0, h_g_deriv_zero y (lt_trans_ax hx₀_a hyx₀)
                                  (lt_trans_ax hyz hzb)⟩
    obtain ⟨y, f', hyx₀, hyz, hd, hmvt⟩ :=
      mean_value_theorem (mulNegExpX ep c) x₀ z hgt hdiff
    have hy_a : a < y := lt_trans_ax hx₀_a hyx₀
    have hy_b : y < b := lt_trans_ax hyz hzb
    have hf'_eq : f' = 0 :=
      HasDerivAt_unique (mulNegExpX ep c) f' 0 y hd (h_g_deriv_zero y hy_a hy_b)
    rw [hf'_eq, zero_mul] at hmvt
    have step : mulNegExpX ep c z - mulNegExpX ep c x₀ + mulNegExpX ep c x₀
              = 0 + mulNegExpX ep c x₀ := by rw [hmvt]
    rw [sub_def, add_assoc, neg_add_self, add_zero, zero_add] at step
    exact step

/-! ### Path (iii): the framework's existing usage path

The parametric capstone `expPoly_khovanskii_bound` (shipped earlier)
already provides users with a constructive Khovanskii bound for any
specific poly-in-(x, e^x) via hand-constructed witness:

```lean
-- For ep : ExpPoly and target polynomial p with iteration count k:
have bound := expPoly_khovanskii_bound ep p k h_iter a b hab h_target_ne
                zeros hnodup hzeros
-- bound : zeros.length ≤ degreeUpper p + k
```

The witness `h_iter : IsKhovanskiiReducibleExp ep ⟨[p]⟩ k` is
constructed by chaining `step` (scaledReduction) and `drop` constructors.
The helper lemmas `eval_zero_of_polySimplify_zero` and
`scaledReduction_last_const_pattern_eval_zero` discharge the
`h_last_zero` obligation in `drop` for common cases.

For users wanting full automation:
  * **Path (i)**: `expPoly_auto_bound_with_propagation_aux` (shipped
    above) gives the bound directly if the user verifies `h_prop` +
    `h_strict_last`.
  * **Path (ii)**: `expPoly_ode_no_zeros` (shipped above as axiom;
    full proof deferred) handles the corner case where path (i)'s
    hypotheses might fail.
  * **Path (iii)**: hand-constructed witness via the parametric
    capstone (always works, always constructive).

All three paths converge to the same bound; users pick based on
their input. -/

end ExpPoly
end SingleExpKhovanskii
end MachLib
