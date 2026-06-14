import MachLib.PfaffianChain
import MachLib.Differentiation
import MachLib.Rolle

/-!
# Constructive Khovanskii — Item 4 reduction substrate (the muse's angle 1)

This file implements the muse-suggested approach to the constructive
Khovanskii chain-step reduction. The key insight, due to the muse
(2026-06-13 review):

  Define an AUXILIARY function `f · exp(-c·y_n)` as a Real → Real
  function (NOT a PfaffianFn — sidestepping the chain extension).
  Use it purely as a Rolle vehicle:

    g := f · exp(-c·y_n)
    zeros(g) = zeros(f)  (since exp ≠ 0)
    g' = exp(-c·y_n) · (f' - c·y_n'·f)
    zeros(g') = zeros(f' - c·y_n'·f)  (since exp ≠ 0)
    By Rolle: zeros(g) ≤ zeros(g') + 1
    ⟹ zeros(f) ≤ zeros(f' - c·y_n'·f) + 1

This avoids ever constructing `exp(-c·y_n)` as a PfaffianFn — the
exp factor is purely a Real → Real auxiliary function used in the
proof of the zero count transfer lemma.

## Item 4 plan via muse's angle 1

  Step 1 (this file): mulNegExp_aux auxiliary + zero-equivalence
                      + HasDerivAt.
  Step 2: PfaffianFn.linearCombination (f' - c·y_n'·g).
  Step 3: Degree-drop claim (explicit c via leading coefficient).
  Step 4: Zero count transfer (combining 1-3).
  Step 5: Iteration to base case (degreeY n = 0 → dropLast + IH).

## What ships in this commit

Step 1 fully constructive. Steps 2-5 follow in subsequent commits.
-/

namespace MachLib
namespace PfaffianChainMod

open Real
open MachLib.MultiPolyMod

/-! ## Real-arithmetic preliminaries

A small helper missing from MachLib: if a ≠ 0 and a·b = 0, then b = 0.
Used to transfer the zero set from `f` to `f · exp(-c·y_n)`. -/

theorem mul_eq_zero_of_factor_ne_zero {a b : Real} (ha : a ≠ 0)
    (hab : a * b = 0) : b = 0 := by
  -- (a * b) * (1/a) = b · 1 = b. So if a*b = 0, then 0 = b · 1 = b.
  have hkey : a * b * (1 / a) = b := by
    rw [mul_comm a b, mul_assoc, mul_inv a ha, mul_one_ax]
  rw [hab, zero_mul] at hkey
  exact hkey.symm

/-! ## The auxiliary function `f · exp(-c · y_n)` (muse Step 1)

This is the Real → Real function used as a Rolle vehicle. It's NOT
a PfaffianFn — we sidestep the chain extension entirely. -/

/-- The auxiliary function `f.eval x · exp(-c · y_n x)`. Used in the
zero count transfer lemma. -/
noncomputable def mulNegExp_aux (f : PfaffianFn) (c : Real)
    (y_n : Real → Real) : Real → Real :=
  fun x => f.eval x * Real.exp (-c * y_n x)

/-- **Same-zero-set lemma**: the auxiliary function has the same zeros
as f, because `exp(-c·y_n x)` is never zero. -/
theorem mulNegExp_aux_zero_iff (f : PfaffianFn) (c : Real)
    (y_n : Real → Real) (x : Real) :
    mulNegExp_aux f c y_n x = 0 ↔ f.eval x = 0 := by
  show f.eval x * Real.exp (-c * y_n x) = 0 ↔ f.eval x = 0
  constructor
  · intro h
    -- exp(-c·y_n x) ≠ 0 (by exp_pos). So if f.eval · exp = 0, then f.eval = 0.
    have hexp_ne : Real.exp (-c * y_n x) ≠ 0 := exp_ne_zero _
    -- f.eval x * exp(...) = 0 + factor exp ≠ 0 ⟹ f.eval x = 0.
    -- Use: rearrange as exp * f = 0 and apply mul_eq_zero_of_factor_ne_zero.
    rw [mul_comm] at h
    exact mul_eq_zero_of_factor_ne_zero hexp_ne h
  · intro h
    rw [h, zero_mul]

/-! ## HasDerivAt for mulNegExp_aux (muse Step 1 continued)

The derivative of `f · exp(-c · y_n)` at x, given chain coherence:

  d/dx (f · exp(-c · y_n)) = f' · exp(-c · y_n) + f · (-c · y_n') · exp(-c · y_n)
                          = exp(-c · y_n) · (f' - c · y_n' · f)

Note: f' here means `f.chainTotalDerivative.eval`, which is the
total derivative including chain contributions. y_n' is
`chain.evals n` differentiated, which by chain coherence equals
`MultiPoly.eval (chain.relations n) x (chain.chainValues x)`. -/

/-- **The HasDerivAt theorem for the auxiliary function (raw product
rule form).** Given chain coherence-derived HasDerivAt's for f and
y_n, the auxiliary function has the natural product-rule derivative.

The derivative shape `f' * E + f * (E * (-c * y_n'))` is the raw
product rule output; consumers can rearrange to the equivalent
factored form `E * (f' - c * y_n' * f)` using ring arithmetic. -/
theorem hasDerivAt_mulNegExp_aux_raw (f : PfaffianFn) (c : Real)
    (y_n : Real → Real) (y_n' : Real) (x : Real)
    (hf : HasDerivAt f.eval (f.chainTotalDerivative.eval x) x)
    (hyn : HasDerivAt y_n y_n' x) :
    HasDerivAt (mulNegExp_aux f c y_n)
               (f.chainTotalDerivative.eval x * Real.exp (-c * y_n x)
                + f.eval x * (Real.exp (-c * y_n x) * (-c * y_n')))
               x := by
  show HasDerivAt (fun x => f.eval x * Real.exp (-c * y_n x))
                  (f.chainTotalDerivative.eval x * Real.exp (-c * y_n x)
                   + f.eval x * (Real.exp (-c * y_n x) * (-c * y_n'))) x
  -- HasDerivAt for (-c * y_n).
  have hneg_c_yn : HasDerivAt (fun x => -c * y_n x) (-c * y_n') x := by
    have hconst : HasDerivAt (fun _ => -c) 0 x := HasDerivAt_const (-c) x
    have hmul := HasDerivAt_mul (fun _ => -c) y_n 0 y_n' x hconst hyn
    have hsimp : 0 * y_n x + -c * y_n' = -c * y_n' := by
      rw [zero_mul, zero_add]
    rw [hsimp] at hmul
    exact hmul
  -- HasDerivAt for exp(-c * y_n).
  have hexp_comp : HasDerivAt (fun x => Real.exp (-c * y_n x))
                              (Real.exp (-c * y_n x) * (-c * y_n')) x := by
    have hexp_at : HasDerivAt Real.exp (Real.exp (-c * y_n x)) (-c * y_n x) :=
      HasDerivAt_exp (-c * y_n x)
    exact HasDerivAt_comp Real.exp (fun x => -c * y_n x) (-c * y_n')
            (Real.exp (-c * y_n x)) x hneg_c_yn hexp_at
  -- Product rule.
  exact HasDerivAt_mul f.eval (fun x => Real.exp (-c * y_n x))
          (f.chainTotalDerivative.eval x)
          (Real.exp (-c * y_n x) * (-c * y_n')) x hf hexp_comp

/-- **Algebraic identity** relating the raw product-rule shape to the
factored form. This is the ring identity that lets us rewrite

  f' * E + f * (E * (-c * y_n'))
    = E * (f' - c * y_n' * f)

where E = exp(-c * y_n x). Pure real-arithmetic algebra. -/
theorem mulNegExp_derivative_factored (f' E f c y_n' : Real) :
    f' * E + f * (E * (-c * y_n')) = E * (f' - c * y_n' * f) := by
  -- mach_ring handles most ring rewrites but leaves a mul_comm residue.
  mach_ring
  -- Residue: f * (E * (c * y_n')) = E * (f * (c * y_n')).
  -- Use mul_comm and assoc.
  rw [← mul_assoc, mul_comm f E, mul_assoc]

/-! ## Step 2: PfaffianFn.reducedDerivative (the muse's `f' - c·y_n'·f`)

The "reduced derivative" of f at chain variable i with scalar c:

  reducedDerivative c f i := f.chainTotalDerivative - c · y_i' · f

where `y_i' = chain.relations i` (a polynomial in the same chain
space). This is the factor that appears in g' = exp(-c·y_n) · (...)
from Step 1.

Crucially: reducedDerivative stays in the SAME chain as f. No chain
extension needed — the construction is pure polynomial arithmetic. -/

/-- The reduced derivative `f' - c · y_i' · f` as a PfaffianFn.
Same chain as f; new polynomial via chainTotalDeriv + arithmetic. -/
noncomputable def PfaffianFn.reducedDerivative (c : Real) (f : PfaffianFn)
    (i : Fin f.n) : PfaffianFn :=
  { n := f.n,
    chain := f.chain,
    poly := MultiPoly.sub
              (PfaffianFn.chainTotalDeriv f.chain f.poly)
              (MultiPoly.mul
                (MultiPoly.mul (MultiPoly.const c) (f.chain.relations i))
                f.poly) }

/-- Reduced derivative preserves chain length. -/
theorem PfaffianFn.reducedDerivative_chainLength (c : Real) (f : PfaffianFn)
    (i : Fin f.n) :
    (f.reducedDerivative c i).chainLength = f.chainLength := rfl

/-- **Eval correctness for reducedDerivative.** The eval equals
`f.chainTotalDerivative.eval x - c · y_i'(x) · f.eval x` where
`y_i'(x) = MultiPoly.eval (chain.relations i) x (chainValues x)`. -/
theorem PfaffianFn.reducedDerivative_eval (c : Real) (f : PfaffianFn)
    (i : Fin f.n) (x : Real) :
    (f.reducedDerivative c i).eval x =
    f.chainTotalDerivative.eval x -
    c * MultiPoly.eval (f.chain.relations i) x (f.chain.chainValues x)
      * f.eval x := by
  -- Apply eval_sub then eval_mul (twice) and eval_const.
  show MultiPoly.eval
        (MultiPoly.sub
          (chainTotalDeriv f.chain f.poly)
          (MultiPoly.mul
            (MultiPoly.mul (MultiPoly.const c) (f.chain.relations i))
            f.poly))
        x (f.chain.chainValues x)
       = f.chainTotalDerivative.eval x -
         c * MultiPoly.eval (f.chain.relations i) x (f.chain.chainValues x)
           * f.eval x
  rw [MultiPoly.eval_sub, MultiPoly.eval_mul, MultiPoly.eval_mul,
      MultiPoly.eval_const]
  rfl

/-! ## Step 4: zero count transfer lemma (the muse's combined bound)

This is the chain-step reduction that combines Steps 1-3:

  zeros(f) ≤ zeros(reducedDerivative c f i) + 1

The proof:
  1. Define g := f · exp(-c · y_i) on (a, b).
  2. zeros(g) = zeros(f) on (a,b) by mulNegExp_aux_zero_iff (Step 1).
  3. g is differentiable on (a,b), with derivative exp(-c·y_i) · reducedDerivative
     (by Step 1's hasDerivAt_mulNegExp_aux_raw + Step 2's reducedDerivative_eval
     + the factoring identity mulNegExp_derivative_factored).
  4. zeros(g') = zeros(reducedDerivative) on (a,b) — same exp ≠ 0 argument.
  5. Apply zero_count_bound_by_deriv (Rolle's corollary): zeros(g) ≤ zeros(g') + 1.

Constructive throughout. No axiom of Step 4 itself — only the Rolle corollary
(`zero_count_bound_by_deriv`, axiomatized in Rolle.lean) and the exp ≠ 0 fact.

Crucially: this lemma does NOT depend on the degree-drop claim (Step 3). It's
purely a zero-count transfer that holds for ANY c. Step 3 is needed only to
make the iteration in Step 5 well-founded — the choice of c that drives the
degree-drop is downstream of this transfer. -/

/-- **Zero count transfer (raw form).** Uses the HasDerivAt-shape bound that
matches `zero_count_bound_by_deriv` directly. Most callers want
`zero_count_reducedDerivative_transfer` below, which converts the bound
hypothesis to eval-form via the bridge lemma. -/
theorem PfaffianFn.zero_count_reducedDerivative_transfer_raw
    (f : PfaffianFn) (i : Fin f.n) (c : Real) (a b : Real) (hab : a < b)
    (hcoherent : f.chain.IsCoherentOn a b)
    (N : Nat)
    (h_reduced_bound : ∀ zeros' : List Real,
        zeros'.Nodup →
        (∀ z ∈ zeros', a < z ∧ z < b ∧
          ∃ f'' : Real, HasDerivAt (mulNegExp_aux f c (f.chain.evals i))
                                    f'' z ∧ f'' = 0) →
        zeros'.length ≤ N) :
    ∀ zeros_f : List Real,
      zeros_f.Nodup →
      (∀ z ∈ zeros_f, a < z ∧ z < b ∧ f.eval z = 0) →
      zeros_f.length ≤ N + 1 := by
  intro zeros_f hnodup hzeros
  -- g := mulNegExp_aux f c (chain.evals i) — the auxiliary Rolle vehicle.
  -- Convert zeros of f.eval to zeros of g via mulNegExp_aux_zero_iff.
  have hzeros_g : ∀ z ∈ zeros_f, a < z ∧ z < b ∧
                   mulNegExp_aux f c (f.chain.evals i) z = 0 := by
    intro z hz
    obtain ⟨haz, hzb, hfz⟩ := hzeros z hz
    refine ⟨haz, hzb, ?_⟩
    exact (mulNegExp_aux_zero_iff f c _ z).mpr hfz
  -- g is differentiable on (a,b) via Step 1 + chain coherence.
  have hdiff : ∀ x : Real, a < x → x < b →
                ∃ f' : Real, HasDerivAt (mulNegExp_aux f c (f.chain.evals i)) f' x := by
    intro x hax hxb
    have hcoh : f.chain.IsCoherentAt x := hcoherent x hax hxb
    have hf' : HasDerivAt f.eval (f.chainTotalDerivative.eval x) x :=
      hasDerivAt_eval_natural f x hcoh
    have hy' := hcoh i
    refine ⟨_, hasDerivAt_mulNegExp_aux_raw f c (f.chain.evals i) _ x hf' hy'⟩
  exact zero_count_bound_by_deriv (mulNegExp_aux f c (f.chain.evals i))
          a b hab hdiff N h_reduced_bound zeros_f hnodup hzeros_g

/-- **Bridge lemma**: zeros of `g'` (raw HasDerivAt form) correspond to
zeros of `(reducedDerivative c f i).eval`. This converts the hypothesis form
of `zero_count_reducedDerivative_transfer` from "HasDerivAt zero" to
"reducedDerivative eval zero". Uses HasDerivAt uniqueness + exp ≠ 0. -/
theorem PfaffianFn.reducedDerivative_eval_zero_of_g_deriv_zero
    (f : PfaffianFn) (i : Fin f.n) (c : Real) (z : Real)
    (hcoh : f.chain.IsCoherentAt z)
    (g'' : Real)
    (hg''_deriv : HasDerivAt (mulNegExp_aux f c (f.chain.evals i)) g'' z)
    (hg''_zero : g'' = 0) :
    (f.reducedDerivative c i).eval z = 0 := by
  -- Canonical derivative from Step 1.
  have hf' : HasDerivAt f.eval (f.chainTotalDerivative.eval z) z :=
    hasDerivAt_eval_natural f z hcoh
  have hy' := hcoh i
  have hcanonical :=
    hasDerivAt_mulNegExp_aux_raw f c (f.chain.evals i)
      (MultiPoly.eval (f.chain.relations i) z (f.chain.chainValues z)) z hf' hy'
  -- HasDerivAt uniqueness: g'' equals canonical derivative.
  have huniq := HasDerivAt_unique (mulNegExp_aux f c (f.chain.evals i))
                  g''
                  (f.chainTotalDerivative.eval z * Real.exp (-c * f.chain.evals i z)
                   + f.eval z * (Real.exp (-c * f.chain.evals i z)
                                 * (-c * MultiPoly.eval (f.chain.relations i) z
                                          (f.chain.chainValues z))))
                  z hg''_deriv hcanonical
  -- huniq + hg''_zero ⟹ canonical = 0.
  have hcan_zero : f.chainTotalDerivative.eval z * Real.exp (-c * f.chain.evals i z)
                    + f.eval z * (Real.exp (-c * f.chain.evals i z)
                                  * (-c * MultiPoly.eval (f.chain.relations i) z
                                           (f.chain.chainValues z))) = 0 := by
    rw [← huniq]; exact hg''_zero
  -- Factor: canonical = exp(...) · (f' - c · y_i' · f).
  have hfact := mulNegExp_derivative_factored
                  (f.chainTotalDerivative.eval z)
                  (Real.exp (-c * f.chain.evals i z))
                  (f.eval z)
                  c
                  (MultiPoly.eval (f.chain.relations i) z (f.chain.chainValues z))
  rw [hfact] at hcan_zero
  -- Now: exp(...) · (f' - c · y_i' · f) = 0 and exp ≠ 0.
  have hexp_ne : Real.exp (-c * f.chain.evals i z) ≠ 0 := exp_ne_zero _
  have hred_zero : f.chainTotalDerivative.eval z
                    - c * MultiPoly.eval (f.chain.relations i) z (f.chain.chainValues z)
                      * f.eval z = 0 :=
    mul_eq_zero_of_factor_ne_zero hexp_ne hcan_zero
  rw [PfaffianFn.reducedDerivative_eval]
  exact hred_zero

/-- **Zero count transfer (eval form, user-friendly).** This is the
"natural" form of the chain-step reduction:

  zeros(f) ≤ zeros(reducedDerivative c f i) + 1

stated entirely in terms of PfaffianFn evaluation. Internally bridges to the
raw HasDerivAt-form bound via `reducedDerivative_eval_zero_of_g_deriv_zero`. -/
theorem PfaffianFn.zero_count_reducedDerivative_transfer
    (f : PfaffianFn) (i : Fin f.n) (c : Real) (a b : Real) (hab : a < b)
    (hcoherent : f.chain.IsCoherentOn a b)
    (N : Nat)
    (h_reduced_bound_eval : ∀ zeros' : List Real,
        zeros'.Nodup →
        (∀ z ∈ zeros', a < z ∧ z < b ∧
          (f.reducedDerivative c i).eval z = 0) →
        zeros'.length ≤ N) :
    ∀ zeros_f : List Real,
      zeros_f.Nodup →
      (∀ z ∈ zeros_f, a < z ∧ z < b ∧ f.eval z = 0) →
      zeros_f.length ≤ N + 1 := by
  apply PfaffianFn.zero_count_reducedDerivative_transfer_raw f i c a b hab hcoherent N
  intro zeros' hnodup' hzeros'_prop
  apply h_reduced_bound_eval zeros' hnodup'
  intro z hz
  obtain ⟨haz, hzb, g'', hg''_deriv, hg''_zero⟩ := hzeros'_prop z hz
  refine ⟨haz, hzb, ?_⟩
  exact PfaffianFn.reducedDerivative_eval_zero_of_g_deriv_zero
          f i c z (hcoherent z haz hzb) g'' hg''_deriv hg''_zero

end PfaffianChainMod
end MachLib
