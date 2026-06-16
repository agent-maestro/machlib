import MachLib.PfaffianChain
import MachLib.Differentiation
import MachLib.Rolle
import MachLib.MultiPolyToPoly

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

/-! ## Step 5: iteration to a base function (parametric)

Iterate Step 4: each application reduces the zero count by 1. After k
applications, we reach a target function g whose zero count we assume
is bounded by N (the base bound). Conclude zero count of f ≤ N + k.

Crucially: this iteration is PARAMETRIC. The choice of (i_j, c_j) at
each step is supplied as data (the `IsIteratedReducedDerivative`
predicate), NOT derived. Step 3 (the classical degree-drop) would
provide a constructive existence proof — Step 5 here only handles
the iteration ARITHMETIC modulo that existence.

A consequence: if Step 3 is ever closed (or supplied as a hypothesis
in a different proof), Step 5's iteration arithmetic doesn't need
to change. -/

/-- **Iterated reducedDerivative predicate.** `IsIteratedReducedDerivative
f g k` means that g can be obtained from f by k applications of
`reducedDerivative` (with arbitrary intermediate index/scalar choices). -/
inductive PfaffianFn.IsIteratedReducedDerivative :
    PfaffianFn → PfaffianFn → Nat → Prop where
  | refl (f : PfaffianFn) : IsIteratedReducedDerivative f f 0
  | step (f g : PfaffianFn) (k : Nat) (i : Fin f.n) (c : Real)
      (h_next : IsIteratedReducedDerivative (f.reducedDerivative c i) g k) :
      IsIteratedReducedDerivative f g (k + 1)

/-- **Iterated chain-step reduction bound.** If g is the result of k
applications of `reducedDerivative` to f, and g's zero count on (a, b)
is bounded by N, then f's zero count is bounded by N + k. Proved by
induction on the iteration count. -/
theorem PfaffianFn.zero_count_iter_bound
    (f g : PfaffianFn) (k : Nat) (h_iter : f.IsIteratedReducedDerivative g k)
    (a b : Real) (hab : a < b)
    (hcoherent : f.chain.IsCoherentOn a b)
    (N : Nat)
    (hN_bound : ∀ zeros' : List Real,
        zeros'.Nodup →
        (∀ z ∈ zeros', a < z ∧ z < b ∧ g.eval z = 0) →
        zeros'.length ≤ N) :
    ∀ zeros_f : List Real,
      zeros_f.Nodup →
      (∀ z ∈ zeros_f, a < z ∧ z < b ∧ f.eval z = 0) →
      zeros_f.length ≤ N + k := by
  -- Revert all hypotheses that depend on the inductively-varying f
  -- so the IH for `step` is parametric in them.
  revert hcoherent hN_bound
  induction h_iter with
  | refl f =>
      intro _hcoh hN_bound zeros_f hnodup hzeros
      have := hN_bound zeros_f hnodup hzeros
      omega
  | step f g k i c h_next ih =>
      intro hcoherent hN_bound
      -- Coherence of `(f.reducedDerivative c i).chain` = coherence of `f.chain`.
      have hred_coh : (f.reducedDerivative c i).chain.IsCoherentOn a b := hcoherent
      -- IH: with coherence and the bound on g, zeros of (reducedDerivative) ≤ N + k.
      have hred_bound := ih hred_coh hN_bound
      -- Apply Step 4 (eval form): zeros of f ≤ (N + k) + 1 = N + (k + 1).
      have hstep := PfaffianFn.zero_count_reducedDerivative_transfer
                      f i c a b hab hcoherent (N + k) hred_bound
      intro zeros_f hnodup hzeros
      have := hstep zeros_f hnodup hzeros
      omega

/-! ## Bound when the base function has chainLength 0 (polynomial case)

When the iteration terminates at a chainLength-0 PfaffianFn, the
function is effectively a univariate polynomial in x (the `Fin 0`
chain is empty). `MultiPolyToPoly.multiPoly_root_count_bound_at_fixed_env`
delivers the polynomial root count, and the env-invariance lemma for
n = 0 bridges the fact that `chainValues` varies with x (irrelevantly,
since for `n = 0` the env is vacuous).

This closes the polynomial base case constructively. Combined with
`zero_count_iter_bound`, the only remaining obligation for the full
constructive Khovanskii bound is Step 3 (the existence of a
degree-drop iteration chain). -/

/-- **Base case bound for chain length 0.** A PfaffianFn whose chain
is empty has zero count bounded by its underlying polynomial's
x-degree, on any bounded open interval where the function is
nonzero somewhere. -/
theorem PfaffianFn.zero_count_bound_chainLength_zero
    (f : PfaffianFn) (h0 : f.n = 0) (a b : Real) (hab : a < b)
    (hne : ∃ x : Real, f.eval x ≠ 0) :
    ∀ zeros : List Real,
      zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ f.eval z = 0) →
      zeros.length ≤ MultiPoly.degreeX f.poly := by
  intro zeros hnodup hzeros
  -- Fix env := chainValues at anchor `a`. For n = 0 the env is vacuous,
  -- so MultiPoly.eval is invariant in env (env_invariant lemma).
  let env : Fin f.n → Real := f.chain.chainValues a
  -- Convert hypothesis hne: f.eval x = MultiPoly.eval f.poly x (chainValues x).
  have hne' : ∃ x : Real, MultiPoly.eval f.poly x env ≠ 0 := by
    obtain ⟨x, hx⟩ := hne
    refine ⟨x, ?_⟩
    have heq : MultiPoly.eval f.poly x env
             = MultiPoly.eval f.poly x (f.chain.chainValues x) :=
      MultiPolyToPoly.multiPoly_eval_env_invariant_n_zero h0 f.poly x env
        (f.chain.chainValues x)
    rw [heq]
    exact hx
  -- Convert zeros: f.eval z = 0 ⟹ MultiPoly.eval f.poly z env = 0.
  have hzeros' : ∀ z ∈ zeros, a < z ∧ z < b ∧ MultiPoly.eval f.poly z env = 0 := by
    intro z hz
    obtain ⟨haz, hzb, hfz⟩ := hzeros z hz
    refine ⟨haz, hzb, ?_⟩
    have heq : MultiPoly.eval f.poly z env
             = MultiPoly.eval f.poly z (f.chain.chainValues z) :=
      MultiPolyToPoly.multiPoly_eval_env_invariant_n_zero h0 f.poly z env
        (f.chain.chainValues z)
    rw [heq]
    exact hfz
  -- Apply the multivariate polynomial root count bound.
  exact MultiPolyToPoly.multiPoly_root_count_bound_at_fixed_env
          f.poly env a b hab hne' zeros hnodup hzeros'

/-! ## PfaffianFn-level dropLast eval bridge

The MultiPoly-level `eval_dropLastY` (PfaffianChain.lean line 410)
needs a PfaffianFn-level wrapper for use in the Khovanskii iteration:
when `f.n = N+1` and the polynomial doesn't depend on `y_N`,
`(f.dropLast hN).eval x = f.eval x`. This is the bridge that lets
`dropLast` steps integrate with the zero-count framework without
changing the zero set.

**Architectural significance**: this discovery is the missing piece
in the iteration framework. Step 5's `IsIteratedReducedDerivative`
preserves chain length (reducedDerivative is chain-preserving), so
it alone cannot reduce a positive-chain-length PfaffianFn to a
chainLength-0 polynomial. We need INTERLEAVED reduce + drop steps.
This bridge is the foundation for that. -/

theorem PfaffianFn.dropLast_eval {N : Nat} (f : PfaffianFn)
    (hN : f.n = N + 1)
    (h_deg_zero : MultiPoly.degreeY ⟨N, hN.symm ▸ Nat.lt_succ_self N⟩ f.poly = 0)
    (x : Real) :
    (f.dropLast hN).eval x = f.eval x := by
  -- Destructure f to expose n as a local variable.
  obtain ⟨n, chain, poly⟩ := f
  -- Now hN : n = N + 1 with n a local var; subst works.
  cases hN
  -- After subst: n = N + 1 literally; no casts.
  show MultiPoly.eval (MultiPoly.dropLastY poly) x
         ((PfaffianChain.dropLast chain).chainValues x)
       = MultiPoly.eval poly x (chain.chainValues x)
  have hcv : (PfaffianChain.dropLast chain).chainValues x
           = fun i => chain.chainValues x ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ := by
    funext i
    exact PfaffianChain.dropLast_chainValues_lower chain x i
  rw [hcv]
  exact MultiPoly.eval_dropLastY poly h_deg_zero x (chain.chainValues x)

/-! ## Capstone: the constructive Khovanskii bound (modulo Step 3)

Compose `zero_count_iter_bound` (Step 5) with `zero_count_bound_chainLength_zero`
(the base case). The result is the **full constructive Khovanskii zero
bound**, modulo the existence of a degree-drop iteration chain that
takes f down to a chainLength-0 PfaffianFn.

The only piece NOT yet constructive is the EXISTENCE proof for the
iteration chain (Step 3 — classical degree-drop). Callers can either:
  - Construct an iteration chain by hand for specific PfaffianFns.
  - Eventually invoke the closed Step 3 theorem when it ships.

Either way, this capstone makes the connection point explicit. -/

/-- **Constructive Khovanskii zero bound (modulo Step 3).** Given a
k-step degree-drop iteration chain `f →* g` with `g` of chain length
zero, the zero count of `f` on `(a, b)` is bounded by
`degreeX(g.poly) + k`. -/
theorem PfaffianFn.khovanskii_bound_modulo_step_3
    (f g : PfaffianFn) (k : Nat)
    (h_iter : f.IsIteratedReducedDerivative g k)
    (hg0 : g.n = 0)
    (a b : Real) (hab : a < b)
    (hcoherent : f.chain.IsCoherentOn a b)
    (hne : ∃ x : Real, g.eval x ≠ 0) :
    ∀ zeros : List Real,
      zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ f.eval z = 0) →
      zeros.length ≤ MultiPoly.degreeX g.poly + k := by
  apply PfaffianFn.zero_count_iter_bound f g k h_iter a b hab hcoherent
          (MultiPoly.degreeX g.poly)
  exact PfaffianFn.zero_count_bound_chainLength_zero g hg0 a b hab hne

/-! ## Step 3 reformulation: the scaledReduction operator

Today's attempt to close Step 3 (machlib `3922049`) discovered that
the muse's exact plan — pick c so that `degreeY_last (f' - c·y_n'·f)
< degreeY_last f` — likely fails for the general case. In the
simplest single-exp chain, no choice of c drops the y-degree.

The classical Khovanskii argument uses a DIFFERENT auxiliary factor:
`exp(-c · x)` (linear in x), NOT `exp(-c · y_n)` (linear in last
chain variable). The resulting chain-step operator is

  `scaledReduction c f := f' - c · f`

(NOT `f' - c · y_n' · f`). The corresponding zero count transfer:

  g(x) := f(x) · exp(-c · x)
  g'(x) = exp(-c·x) · (f'(x) - c · f(x))
  By Rolle: zeros(f) ≤ zeros(scaledReduction c f) + 1.

And the **complexity measure** that actually decreases:

  μ(f) := (degreeY_last f.poly, degreeX (leadingCoeffY_last f.poly))
          lexicographic

For the single-exp chain `y' = y` with `c = degreeY_last(f)`:
  y^d coefficient of `f' - d·f`
    = (a_d' + d·a_d) - d · a_d
    = a_d'
  ⟹ x-degree of leading y-coefficient drops by 1.

After deg(a_d) + 1 applications, a_d reaches degree 0 then constant 0,
at which point `degreeY_last` drops by 1. Iterating brings the chain
down to chainLength 0 (polynomial). This is the right
classical-Khovanskii argument shape.

This section ships the analog of Steps 1, 2, 4 for the new operator.
Step 5 (iteration) and the full Step 3 (existence + termination
argument with the lex measure) follow in subsequent commits. -/

/-! ### Auxiliary function exp(-c · x) -/

/-- The auxiliary `f.eval x · exp(-c · x)`. Real → Real function,
NOT a PfaffianFn. Used as the Rolle vehicle for `scaledReduction`. -/
noncomputable def mulNegExpX_aux (f : PfaffianFn) (c : Real) : Real → Real :=
  fun x => f.eval x * Real.exp (-c * x)

/-- **Same-zero-set lemma**: the auxiliary has the same zeros as f,
because `exp(-c · x)` is never zero. -/
theorem mulNegExpX_aux_zero_iff (f : PfaffianFn) (c : Real) (x : Real) :
    mulNegExpX_aux f c x = 0 ↔ f.eval x = 0 := by
  show f.eval x * Real.exp (-c * x) = 0 ↔ f.eval x = 0
  constructor
  · intro h
    have hexp_ne : Real.exp (-c * x) ≠ 0 := exp_ne_zero _
    rw [mul_comm] at h
    exact mul_eq_zero_of_factor_ne_zero hexp_ne h
  · intro h
    rw [h, zero_mul]

/-- **HasDerivAt for the exp(-c·x) auxiliary (raw product rule form).** -/
theorem hasDerivAt_mulNegExpX_aux_raw (f : PfaffianFn) (c : Real) (x : Real)
    (hf : HasDerivAt f.eval (f.chainTotalDerivative.eval x) x) :
    HasDerivAt (mulNegExpX_aux f c)
               (f.chainTotalDerivative.eval x * Real.exp (-c * x)
                + f.eval x * (Real.exp (-c * x) * (-c)))
               x := by
  show HasDerivAt (fun x => f.eval x * Real.exp (-c * x))
                  (f.chainTotalDerivative.eval x * Real.exp (-c * x)
                   + f.eval x * (Real.exp (-c * x) * (-c))) x
  -- HasDerivAt for (-c * x): use HasDerivAt_id and HasDerivAt_mul with const.
  have hid : HasDerivAt (fun x => x) 1 x := HasDerivAt_id x
  have hconst : HasDerivAt (fun _ : Real => -c) 0 x := HasDerivAt_const (-c) x
  have hmul := HasDerivAt_mul (fun _ => -c) (fun x => x) 0 1 x hconst hid
  have hsimp : 0 * x + -c * 1 = -c := by
    rw [zero_mul, zero_add, mul_one_ax]
  rw [hsimp] at hmul
  -- HasDerivAt for exp(-c·x).
  have hexp_at : HasDerivAt Real.exp (Real.exp (-c * x)) (-c * x) :=
    HasDerivAt_exp (-c * x)
  have hexp_comp := HasDerivAt_comp Real.exp (fun x => -c * x) (-c)
                      (Real.exp (-c * x)) x hmul hexp_at
  -- Product rule.
  exact HasDerivAt_mul f.eval (fun x => Real.exp (-c * x))
          (f.chainTotalDerivative.eval x)
          (Real.exp (-c * x) * (-c)) x hf hexp_comp

/-- **Algebraic identity (factored form for exp(-c·x) variant).**

  f' · E + f · (E · (-c)) = E · (f' - c · f)

where E = exp(-c · x). Pure ring identity. -/
theorem mulNegExpX_derivative_factored (f' E f c : Real) :
    f' * E + f * (E * (-c)) = E * (f' - c * f) := by
  mach_ring
  rw [← mul_assoc, mul_comm f E, mul_assoc]

/-! ### The scaledReduction operator (Step 2 analog) -/

/-- The scaled reduction `f' - c · f` as a PfaffianFn. Same chain as
`f`; new polynomial via `chainTotalDeriv f.chain f.poly` minus
`c · f.poly`. -/
noncomputable def PfaffianFn.scaledReduction (c : Real) (f : PfaffianFn) :
    PfaffianFn :=
  { n := f.n,
    chain := f.chain,
    poly := MultiPoly.sub
              (PfaffianFn.chainTotalDeriv f.chain f.poly)
              (MultiPoly.mul (MultiPoly.const c) f.poly) }

theorem PfaffianFn.scaledReduction_chainLength (c : Real) (f : PfaffianFn) :
    (f.scaledReduction c).chainLength = f.chainLength := rfl

/-- **Eval correctness for scaledReduction.** -/
theorem PfaffianFn.scaledReduction_eval (c : Real) (f : PfaffianFn) (x : Real) :
    (f.scaledReduction c).eval x = f.chainTotalDerivative.eval x - c * f.eval x := by
  show MultiPoly.eval
        (MultiPoly.sub
          (PfaffianFn.chainTotalDeriv f.chain f.poly)
          (MultiPoly.mul (MultiPoly.const c) f.poly))
        x (f.chain.chainValues x)
      = f.chainTotalDerivative.eval x - c * f.eval x
  rw [MultiPoly.eval_sub, MultiPoly.eval_mul, MultiPoly.eval_const]
  rfl

/-! ### Step 4 analog: zero count transfer via scaledReduction -/

/-- **Bridge lemma (scaledReduction variant)**: at a point z where
`mulNegExpX_aux f c` has zero derivative, `(scaledReduction c f).eval z = 0`. -/
theorem PfaffianFn.scaledReduction_eval_zero_of_g_deriv_zero
    (f : PfaffianFn) (c : Real) (z : Real)
    (hcoh : f.chain.IsCoherentAt z)
    (g'' : Real)
    (hg''_deriv : HasDerivAt (mulNegExpX_aux f c) g'' z)
    (hg''_zero : g'' = 0) :
    (f.scaledReduction c).eval z = 0 := by
  have hf' : HasDerivAt f.eval (f.chainTotalDerivative.eval z) z :=
    hasDerivAt_eval_natural f z hcoh
  have hcanonical := hasDerivAt_mulNegExpX_aux_raw f c z hf'
  have huniq := HasDerivAt_unique (mulNegExpX_aux f c)
                  g''
                  (f.chainTotalDerivative.eval z * Real.exp (-c * z)
                   + f.eval z * (Real.exp (-c * z) * (-c)))
                  z hg''_deriv hcanonical
  have hcan_zero : f.chainTotalDerivative.eval z * Real.exp (-c * z)
                    + f.eval z * (Real.exp (-c * z) * (-c)) = 0 := by
    rw [← huniq]; exact hg''_zero
  have hfact := mulNegExpX_derivative_factored
                  (f.chainTotalDerivative.eval z)
                  (Real.exp (-c * z)) (f.eval z) c
  rw [hfact] at hcan_zero
  have hexp_ne : Real.exp (-c * z) ≠ 0 := exp_ne_zero _
  have hred_zero : f.chainTotalDerivative.eval z - c * f.eval z = 0 :=
    mul_eq_zero_of_factor_ne_zero hexp_ne hcan_zero
  rw [PfaffianFn.scaledReduction_eval]
  exact hred_zero

/-- **Zero count transfer via scaledReduction (raw HasDerivAt form).** -/
theorem PfaffianFn.zero_count_scaledReduction_transfer_raw
    (f : PfaffianFn) (c : Real) (a b : Real) (hab : a < b)
    (hcoherent : f.chain.IsCoherentOn a b)
    (N : Nat)
    (h_reduced_bound : ∀ zeros' : List Real,
        zeros'.Nodup →
        (∀ z ∈ zeros', a < z ∧ z < b ∧
          ∃ f'' : Real, HasDerivAt (mulNegExpX_aux f c) f'' z ∧ f'' = 0) →
        zeros'.length ≤ N) :
    ∀ zeros_f : List Real,
      zeros_f.Nodup →
      (∀ z ∈ zeros_f, a < z ∧ z < b ∧ f.eval z = 0) →
      zeros_f.length ≤ N + 1 := by
  intro zeros_f hnodup hzeros
  have hzeros_g : ∀ z ∈ zeros_f, a < z ∧ z < b ∧ mulNegExpX_aux f c z = 0 := by
    intro z hz
    obtain ⟨haz, hzb, hfz⟩ := hzeros z hz
    refine ⟨haz, hzb, ?_⟩
    exact (mulNegExpX_aux_zero_iff f c z).mpr hfz
  have hdiff : ∀ x : Real, a < x → x < b →
                ∃ f' : Real, HasDerivAt (mulNegExpX_aux f c) f' x := by
    intro x hax hxb
    have hcoh : f.chain.IsCoherentAt x := hcoherent x hax hxb
    have hf' : HasDerivAt f.eval (f.chainTotalDerivative.eval x) x :=
      hasDerivAt_eval_natural f x hcoh
    refine ⟨_, hasDerivAt_mulNegExpX_aux_raw f c x hf'⟩
  exact zero_count_bound_by_deriv (mulNegExpX_aux f c) a b hab hdiff N
          h_reduced_bound zeros_f hnodup hzeros_g

/-- **Zero count transfer via scaledReduction (eval form, user-friendly).** -/
theorem PfaffianFn.zero_count_scaledReduction_transfer
    (f : PfaffianFn) (c : Real) (a b : Real) (hab : a < b)
    (hcoherent : f.chain.IsCoherentOn a b)
    (N : Nat)
    (h_reduced_bound_eval : ∀ zeros' : List Real,
        zeros'.Nodup →
        (∀ z ∈ zeros', a < z ∧ z < b ∧ (f.scaledReduction c).eval z = 0) →
        zeros'.length ≤ N) :
    ∀ zeros_f : List Real,
      zeros_f.Nodup →
      (∀ z ∈ zeros_f, a < z ∧ z < b ∧ f.eval z = 0) →
      zeros_f.length ≤ N + 1 := by
  apply PfaffianFn.zero_count_scaledReduction_transfer_raw f c a b hab hcoherent N
  intro zeros' hnodup' hzeros'_prop
  apply h_reduced_bound_eval zeros' hnodup'
  intro z hz
  obtain ⟨haz, hzb, g'', hg''_deriv, hg''_zero⟩ := hzeros'_prop z hz
  refine ⟨haz, hzb, ?_⟩
  exact PfaffianFn.scaledReduction_eval_zero_of_g_deriv_zero
          f c z (hcoherent z haz hzb) g'' hg''_deriv hg''_zero

/-! ### Step 5 analog: iteration arithmetic for scaledReduction

Parallel to `IsIteratedReducedDerivative` + `zero_count_iter_bound`,
but for `scaledReduction`. The classical Khovanskii termination
argument uses this operator (not reducedDerivative), so this is the
ITERATION FRAMEWORK that the closed Step 3 will plug into.

Important property: like reducedDerivative, scaledReduction
preserves chain length (same `chain` field). So this iteration is
also chain-length-preserving and must be interleaved with `dropLast`
steps to reach chainLength 0 from positive chain length. -/

/-- **Iterated scaledReduction predicate.** `IsIteratedScaledReduction
f g k` means g is obtained from f by k applications of
`scaledReduction` (with arbitrary intermediate scalar choices). -/
inductive PfaffianFn.IsIteratedScaledReduction :
    PfaffianFn → PfaffianFn → Nat → Prop where
  | refl (f : PfaffianFn) : IsIteratedScaledReduction f f 0
  | step (f g : PfaffianFn) (k : Nat) (c : Real)
      (h_next : IsIteratedScaledReduction (f.scaledReduction c) g k) :
      IsIteratedScaledReduction f g (k + 1)

/-- **Iterated chain-step reduction bound (scaledReduction variant).**
Same structure as `zero_count_iter_bound`. -/
theorem PfaffianFn.zero_count_iter_bound_scaledReduction
    (f g : PfaffianFn) (k : Nat) (h_iter : f.IsIteratedScaledReduction g k)
    (a b : Real) (hab : a < b)
    (hcoherent : f.chain.IsCoherentOn a b)
    (N : Nat)
    (hN_bound : ∀ zeros' : List Real,
        zeros'.Nodup →
        (∀ z ∈ zeros', a < z ∧ z < b ∧ g.eval z = 0) →
        zeros'.length ≤ N) :
    ∀ zeros_f : List Real,
      zeros_f.Nodup →
      (∀ z ∈ zeros_f, a < z ∧ z < b ∧ f.eval z = 0) →
      zeros_f.length ≤ N + k := by
  revert hcoherent hN_bound
  induction h_iter with
  | refl f =>
      intro _hcoh hN_bound zeros_f hnodup hzeros
      have := hN_bound zeros_f hnodup hzeros
      omega
  | step f g k c h_next ih =>
      intro hcoherent hN_bound
      -- scaledReduction preserves chain, so coherence transfers.
      have hred_coh : (f.scaledReduction c).chain.IsCoherentOn a b := hcoherent
      have hred_bound := ih hred_coh hN_bound
      have hstep := PfaffianFn.zero_count_scaledReduction_transfer
                      f c a b hab hcoherent (N + k) hred_bound
      intro zeros_f hnodup hzeros
      have := hstep zeros_f hnodup hzeros
      omega

/-- **Capstone for the scaledReduction track (modulo Step 3).**
Compose the iteration bound with the chainLength-0 base case. Same
limitation as the reducedDerivative capstone: scaledReduction
preserves chain length, so this is degenerate (g.n = f.n) unless
combined with dropLast steps. -/
theorem PfaffianFn.khovanskii_bound_scaledReduction_modulo_step_3
    (f g : PfaffianFn) (k : Nat)
    (h_iter : f.IsIteratedScaledReduction g k)
    (hg0 : g.n = 0)
    (a b : Real) (hab : a < b)
    (hcoherent : f.chain.IsCoherentOn a b)
    (hne : ∃ x : Real, g.eval x ≠ 0) :
    ∀ zeros : List Real,
      zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ f.eval z = 0) →
      zeros.length ≤ MultiPoly.degreeX g.poly + k := by
  apply PfaffianFn.zero_count_iter_bound_scaledReduction f g k h_iter a b hab
          hcoherent (MultiPoly.degreeX g.poly)
  exact PfaffianFn.zero_count_bound_chainLength_zero g hg0 a b hab hne

/-! ## Triangularity preservation under dropLast (foundation for (2))

For the Khovanskii iteration to extend to interleaved reduce + drop
steps in the general case, we need:

  (i)  `dropLast` preserves `IsTriangular`.
  (ii) `dropLast` preserves `IsCoherentAt` when the chain is triangular.

The triangularity hypothesis is essential — without it, dropLast may
break coherence because the dropped relations could have y_n
dependencies that don't vanish under `dropLastY`.

This section ships both lemmas, foundation for the eventual extension
of `IsIteratedScaledReduction` to include drop steps. -/

/-- **Triangularity preservation under dropLast.** Uses
`MultiPoly.degreeY_dropLastY_le` to push the degreeY = 0 property
through dropLastY. -/
theorem PfaffianChain.dropLast_preserves_triangular {n : Nat}
    (c : PfaffianChain (n + 1)) (htri : c.IsTriangular) :
    (PfaffianChain.dropLast c).IsTriangular := by
  intro i j hij
  -- New relation at i is dropLastY of old relation at ⟨i.val, _⟩.
  show MultiPoly.degreeY j
        (MultiPoly.dropLastY (c.relations ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩))
       = 0
  -- By degreeY_dropLastY_le ≤ degreeY ⟨j.val, _⟩ of original relation.
  -- Original triangularity gives that = 0.
  have h_orig : MultiPoly.degreeY
                  ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩
                  (c.relations ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) = 0 := by
    apply htri ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
               ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩
    exact hij
  have h_le := MultiPoly.degreeY_dropLastY_le
                 (c.relations ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) j
  omega

/-- **Coherence preservation under dropLast (given triangularity).**
The dropped chain is coherent at x whenever the original was, provided
the original was triangular. The triangularity ensures that each
lower relation's last-y-degree is 0, so dropLastY preserves its eval. -/
theorem PfaffianChain.dropLast_coherent_of_triangular {n : Nat}
    (c : PfaffianChain (n + 1)) (htri : c.IsTriangular)
    (x : Real) (hcoh : c.IsCoherentAt x) :
    (PfaffianChain.dropLast c).IsCoherentAt x := by
  intro i
  -- Need: HasDerivAt ((dropLast c).evals i)
  --                  ((dropLast c).relations i evaluated) x.
  -- (dropLast c).evals i = c.evals ⟨i.val, _⟩.
  -- (dropLast c).relations i = dropLastY (c.relations ⟨i.val, _⟩).
  show HasDerivAt (c.evals ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
        (MultiPoly.eval
          (MultiPoly.dropLastY (c.relations ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩))
          x ((PfaffianChain.dropLast c).chainValues x))
        x
  -- Original coherence: HasDerivAt c.evals ⟨i.val, _⟩ (orig_relation eval) x.
  have h_orig := hcoh ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
  -- The eval of dropLastY of the original relation equals the original
  -- relation's eval at the same point, by eval_dropLastY + triangularity.
  -- Triangularity at j = ⟨n, _⟩ > i: degreeY n (relations ⟨i.val, _⟩) = 0.
  have h_deg_zero : MultiPoly.degreeY
                      ⟨n, Nat.lt_succ_self n⟩
                      (c.relations ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) = 0 := by
    apply htri ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ ⟨n, Nat.lt_succ_self n⟩
    -- Need: n > i.val. i.val < n so OK.
    show n > i.val
    exact i.isLt
  -- Bridge chainValues of dropLast with chainValues of original.
  have hcv : (PfaffianChain.dropLast c).chainValues x
           = fun k => c.chainValues x ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩ := by
    funext k
    exact PfaffianChain.dropLast_chainValues_lower c x k
  rw [hcv]
  -- Apply eval_dropLastY to rewrite the eval.
  rw [MultiPoly.eval_dropLastY _ h_deg_zero x (c.chainValues x)]
  exact h_orig

/-- **Coherence preservation on an interval (given triangularity).**
Lifts `dropLast_coherent_of_triangular` from a single point to an
interval. -/
theorem PfaffianChain.dropLast_coherent_on_of_triangular {n : Nat}
    (c : PfaffianChain (n + 1)) (htri : c.IsTriangular)
    (a b : Real) (hcoh : c.IsCoherentOn a b) :
    (PfaffianChain.dropLast c).IsCoherentOn a b := by
  intro x hax hxb
  exact PfaffianChain.dropLast_coherent_of_triangular c htri x (hcoh x hax hxb)

/-! ## Extended iteration: IsKhovanskiiReducible (reduce + drop)

The full Khovanskii iteration interleaves scaledReduction steps (each
adding 1 to the Rolle counter) with dropLast steps (which preserve
zeros, hence preserve the counter). For triangular Pfaffian chains,
both operations are well-defined and chain coherence is preserved
through the iteration.

The predicate `IsKhovanskiiReducible f g k` is the extension of
`IsIteratedScaledReduction` with a third constructor for drop steps. -/

/-- **Khovanskii reducibility predicate.** Extended `IsIteratedScaledReduction`
allowing interleaved `dropLast` steps (which don't increment the Rolle
counter k, since they preserve zeros). The triangularity hypothesis is
external to the predicate; the iteration theorem requires it. -/
inductive PfaffianFn.IsKhovanskiiReducible :
    PfaffianFn → PfaffianFn → Nat → Prop where
  | refl (f : PfaffianFn) : IsKhovanskiiReducible f f 0
  | reduce (f g : PfaffianFn) (k : Nat) (c : Real)
      (h_next : IsKhovanskiiReducible (f.scaledReduction c) g k) :
      IsKhovanskiiReducible f g (k + 1)
  | drop (f g : PfaffianFn) (k : Nat) (N : Nat) (hN : f.n = N + 1)
      (h_deg_zero : MultiPoly.degreeY ⟨N, hN.symm ▸ Nat.lt_succ_self N⟩
                                      f.poly = 0)
      (h_next : IsKhovanskiiReducible (f.dropLast hN) g k) :
      IsKhovanskiiReducible f g k

/-- **Iterated bound for IsKhovanskiiReducible (triangular chains).** The
zero count of f is bounded by N + k, where N bounds the zeros of g
(after k reduce steps + arbitrarily many drop steps), provided the
starting chain is triangular (so coherence is preserved through drops).

Like `zero_count_iter_bound_scaledReduction` but handling drop too. -/
theorem PfaffianFn.zero_count_khovanskii_bound
    (f g : PfaffianFn) (k : Nat) (h_iter : f.IsKhovanskiiReducible g k)
    (htri : f.chain.IsTriangular)
    (a b : Real) (hab : a < b)
    (hcoherent : f.chain.IsCoherentOn a b)
    (N : Nat)
    (hN_bound : ∀ zeros' : List Real,
        zeros'.Nodup →
        (∀ z ∈ zeros', a < z ∧ z < b ∧ g.eval z = 0) →
        zeros'.length ≤ N) :
    ∀ zeros_f : List Real,
      zeros_f.Nodup →
      (∀ z ∈ zeros_f, a < z ∧ z < b ∧ f.eval z = 0) →
      zeros_f.length ≤ N + k := by
  revert htri hcoherent hN_bound
  induction h_iter with
  | refl f =>
      intro _htri _hcoh hN_bound zeros_f hnodup hzeros
      have := hN_bound zeros_f hnodup hzeros
      omega
  | reduce f g k c h_next ih =>
      intro htri hcoherent hN_bound
      -- scaledReduction preserves chain, so triangularity + coherence transfer.
      have hred_tri : (f.scaledReduction c).chain.IsTriangular := htri
      have hred_coh : (f.scaledReduction c).chain.IsCoherentOn a b := hcoherent
      have hred_bound := ih hred_tri hred_coh hN_bound
      have hstep := PfaffianFn.zero_count_scaledReduction_transfer
                      f c a b hab hcoherent (N + k) hred_bound
      intro zeros_f hnodup hzeros
      have := hstep zeros_f hnodup hzeros
      omega
  | drop f g k N_inner hN h_deg_zero h_next ih =>
      intro htri hcoherent hN_bound
      -- Destructure f to expose n as a local variable so we can substitute hN.
      -- For dropLast, triangularity + coherence preservation give us the
      -- analogous hypotheses on (f.dropLast hN).
      -- The eval bridge (dropLast_eval) ensures zeros of f = zeros of dropLast f.
      have hdrop_eval := PfaffianFn.dropLast_eval f hN h_deg_zero
      -- Coherence + triangularity for dropLast.
      -- We need to use the triangularity-preservation theorems, which require
      -- the chain to be PfaffianChain (n+1). The hN cast makes this delicate.
      have hdrop_tri : (f.dropLast hN).chain.IsTriangular := by
        -- (f.dropLast hN).chain = PfaffianChain.dropLast (hN ▸ f.chain).
        -- (hN ▸ f.chain).IsTriangular follows from htri (transports cleanly).
        obtain ⟨n, chain, poly⟩ := f
        cases hN
        exact PfaffianChain.dropLast_preserves_triangular chain htri
      have hdrop_coh : (f.dropLast hN).chain.IsCoherentOn a b := by
        obtain ⟨n, chain, poly⟩ := f
        cases hN
        exact PfaffianChain.dropLast_coherent_on_of_triangular chain htri a b
                hcoherent
      -- Apply IH on f.dropLast hN.
      have hdrop_bound := ih hdrop_tri hdrop_coh hN_bound
      -- Convert: zeros of f via dropLast_eval are the same as zeros of f.dropLast.
      intro zeros_f hnodup hzeros
      apply hdrop_bound zeros_f hnodup
      intro z hz
      obtain ⟨haz, hzb, hfz⟩ := hzeros z hz
      refine ⟨haz, hzb, ?_⟩
      rw [hdrop_eval z]
      exact hfz

/-- **Extended capstone** using IsKhovanskiiReducible with triangularity.
For a triangular chain, the iteration can drop chain length to 0
constructively (given a witness chain of reduce + drop steps). -/
theorem PfaffianFn.khovanskii_bound_full
    (f g : PfaffianFn) (k : Nat)
    (h_iter : f.IsKhovanskiiReducible g k)
    (htri : f.chain.IsTriangular)
    (hg0 : g.n = 0)
    (a b : Real) (hab : a < b)
    (hcoherent : f.chain.IsCoherentOn a b)
    (hne : ∃ x : Real, g.eval x ≠ 0) :
    ∀ zeros : List Real,
      zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ f.eval z = 0) →
      zeros.length ≤ MultiPoly.degreeX g.poly + k := by
  apply PfaffianFn.zero_count_khovanskii_bound f g k h_iter htri a b hab
          hcoherent (MultiPoly.degreeX g.poly)
  exact PfaffianFn.zero_count_bound_chainLength_zero g hg0 a b hab hne

/-! ## SingleExp chain instance (foundation for Item 1)

The canonical single-exponential chain (chain length 1, evals = exp,
relations = varY 0) with its triangularity + coherence proofs ready
to plug into `khovanskii_bound_full`. Any PfaffianFn whose chain is
this single-exp chain — i.e., a polynomial in (x, e^x) — can use the
full Khovanskii framework once a reduction-chain witness is provided. -/

/-- The canonical single-exp chain `(exp, exp')` with relation y_0' = y_0. -/
noncomputable def SingleExpChain : PfaffianChain 1 :=
  { evals := fun _ => Real.exp,
    relations := fun _ => MultiPoly.varY 0 }

/-- The single-exp chain is triangular. Vacuous for n = 1: there are no
pairs (i, j) with j.val > i.val in `Fin 1`. -/
theorem SingleExpChain_isTriangular : SingleExpChain.IsTriangular := by
  intro i j hij
  exfalso
  have hi := i.isLt
  have hj := j.isLt
  omega

/-- The single-exp chain is coherent at every x. The chain relation
y_0' = y_0 is satisfied by exp because `HasDerivAt exp (exp x) x`. -/
theorem SingleExpChain_isCoherentAt (x : Real) :
    SingleExpChain.IsCoherentAt x := by
  intro i
  show HasDerivAt Real.exp
        (MultiPoly.eval (MultiPoly.varY 0) x (SingleExpChain.chainValues x)) x
  show HasDerivAt Real.exp (Real.exp x) x
  exact HasDerivAt_exp x

/-- The single-exp chain is coherent on any interval. -/
theorem SingleExpChain_isCoherentOn (a b : Real) :
    SingleExpChain.IsCoherentOn a b := by
  intro x _ _
  exact SingleExpChain_isCoherentAt x

/-! ## Step 3c — dropLast applicability via lex measure

When the lex measure's first component reaches 0 (degreeY of the last
chain variable is 0), the polynomial doesn't depend on `y_{n-1}` and
`dropLast` applies cleanly. This section ships the bridge lemmas and
one-step witness constructors for IsKhovanskiiReducible.

Combined with Step 3b's strict-decrease (for the reduce step) and
Step 3a's well-foundedness, Step 3d will orchestrate the full witness
construction via strong recursion on the lex measure. -/

/-- **Bridge**: lex measure first component being 0 IS the dropLast
applicability hypothesis. The `lastChainIdx` index matches the
index used in `IsKhovanskiiReducible.drop`'s `h_deg_zero`. -/
theorem PfaffianFn.lex_first_zero_iff_dropLast_applicable
    {N : Nat} (f : PfaffianFn) (hN : f.n = N + 1) :
    (f.lexMeasure hN).1 = 0 ↔
    MultiPoly.degreeY ⟨N, hN.symm ▸ Nat.lt_succ_self N⟩ f.poly = 0 := by
  -- Both sides are defeq via `lastChainIdx` unfolding.
  show MultiPoly.degreeY (lastChainIdx f hN) f.poly = 0 ↔
       MultiPoly.degreeY ⟨N, hN.symm ▸ Nat.lt_succ_self N⟩ f.poly = 0
  rfl

/-- **One-step drop witness**: when the lex measure's first component
is 0, `IsKhovanskiiReducible f (f.dropLast hN) 0` holds via the drop
constructor + refl. -/
theorem PfaffianFn.IsKhovanskiiReducible.drop_one
    {N : Nat} (f : PfaffianFn) (hN : f.n = N + 1)
    (h_lex_zero : (f.lexMeasure hN).1 = 0) :
    PfaffianFn.IsKhovanskiiReducible f (f.dropLast hN) 0 :=
  PfaffianFn.IsKhovanskiiReducible.drop f (f.dropLast hN) 0 N hN
    h_lex_zero
    (PfaffianFn.IsKhovanskiiReducible.refl (f.dropLast hN))

/-- **One-step reduce witness**: `IsKhovanskiiReducible f (scaledReduction c f) 1`
via the reduce constructor + refl. Independent of the lex measure. -/
theorem PfaffianFn.IsKhovanskiiReducible.reduce_one
    (f : PfaffianFn) (c : Real) :
    PfaffianFn.IsKhovanskiiReducible f (f.scaledReduction c) 1 :=
  PfaffianFn.IsKhovanskiiReducible.reduce f (f.scaledReduction c) 0 c
    (PfaffianFn.IsKhovanskiiReducible.refl (f.scaledReduction c))

/-- **Drop preserves chain length**: after dropLast, the result's chain
length is N (one less than f.n). Used in the Step 3d termination
argument to track that the outer recursion measure (chain length) drops. -/
theorem PfaffianFn.dropLast_n
    {N : Nat} (f : PfaffianFn) (hN : f.n = N + 1) :
    (f.dropLast hN).n = N := rfl

/-- **Reduce preserves chain length**: scaledReduction keeps the chain
intact. Used in the Step 3d termination argument to track that the
inner recursion measure (lex measure) drops while chain length is
unchanged. -/
theorem PfaffianFn.scaledReduction_n (c : Real) (f : PfaffianFn) :
    (f.scaledReduction c).n = f.n := rfl

end PfaffianChainMod
end MachLib
