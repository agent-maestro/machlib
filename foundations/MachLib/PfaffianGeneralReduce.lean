import MachLib.IterExpDepthNVehicleNoZeros

/-!
# Generalize — the general reduce framework for arbitrary Pfaffian chains

The iterated-exponential reduce `chainNReduce M m p = chainTotalDeriv (IterExpChain (M+2)) p − m·p`
bakes in `IterExpChain`. Here we lift it: for an ARBITRARY `PfaffianChain c`,

    chainReduce c m p := chainTotalDeriv c p − m·p

(`chainTotalDeriv` is already chain-parametric — the derivative of `varY i` is `c.relations i`). Its
evaluation along a coherent chain is the first-order ODE residual `f′ − eval(m)·f` where
`f = pfaffianChainFn c p`. Consequently the reduce arm's **"no zeros" branch generalizes to any chain**:
if `chainReduce c m p ≡ 0` on `(a,b)` and the multiplier `eval(m)` admits an integrating-factor exponent
`E` (an antiderivative of `−eval(m)`), then `f` has no zeros on `(a,b)` — the chain-and-multiplier
agnostic vehicle `pfaffianFn_no_zeros_of_ode_gen` fires directly.

This is the structural counterpart to the (already general) vehicle: it packages the general reduce +
the general vehicle into the reduce arm's terminal branch, for arbitrary Pfaffian chains. The remaining
iterated-exp-specific work is the reduce *descent* (that a graded multiplier lowers the degree measure),
which needs the "exponential-type" chain property `relations i = y_i · G_i` (`G_i` top-free).

No new axioms beyond the general vehicle's (`rolle` + `HasDerivAt` calculus + `exp`).
-/

namespace MachLib.PfaffianGeneralReduce

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.PfaffianChainMod
open MachLib.PfaffianChainMod.PfaffianChain
open MachLib.PfaffianChainMod.PfaffianFn
open MachLib.IterExpDepthN

/-- The general Pfaffian function `⟨n, c, p⟩` for an arbitrary chain (the analog of `chainNFn`, which
is the `c := IterExpChain` case). -/
noncomputable def pfaffianChainFn {n : Nat} (c : PfaffianChain n) (p : MultiPoly n) : PfaffianFn :=
  ⟨n, c, p⟩

/-- The general reduce: `chainTotalDeriv c p − m·p`, arbitrary chain + arbitrary multiplier. -/
noncomputable def chainReduce {n : Nat} (c : PfaffianChain n) (m p : MultiPoly n) : MultiPoly n :=
  MultiPoly.sub (chainTotalDeriv c p) (MultiPoly.mul m p)

/-- **The general reduce evaluated along the chain is the ODE residual** `f′ − eval(m)·f`, where
`f = pfaffianChainFn c p` (`f′ = f.chainTotalDerivative.eval`, its natural derivative under coherence). -/
theorem chainReduce_eval_along {n : Nat} (c : PfaffianChain n) (m p : MultiPoly n) (z : Real) :
    MultiPoly.eval (chainReduce c m p) z (c.chainValues z)
      = (pfaffianChainFn c p).chainTotalDerivative.eval z
        - MultiPoly.eval m z (c.chainValues z) * (pfaffianChainFn c p).eval z := rfl

/-- **Reduce arm "no zeros" branch — arbitrary Pfaffian chain.** If the general reduce vanishes on
`(a,b)` and the reduce multiplier `eval(m)` has an integrating-factor exponent `E` (with
`E′ = −eval(m)`), then `pfaffianChainFn c p` has no zeros on `(a,b)`. Instantiation of the general
vehicle `pfaffianFn_no_zeros_of_ode_gen` with `M := −eval(m)` and the reduce-as-residual identity. -/
theorem pfaffianChainFn_no_zeros_of_reduce_zero {n : Nat} (c : PfaffianChain n) (m p : MultiPoly n)
    (a b : Real) (hab : a < b) (hcoh : c.IsCoherentOn a b)
    (E : Real → Real)
    (hE : ∀ z, a < z → z < b →
      HasDerivAt E (- MultiPoly.eval m z (c.chainValues z)) z)
    (h_reduce : ∀ z, a < z → z < b →
      MultiPoly.eval (chainReduce c m p) z (c.chainValues z) = 0)
    (z₀ : Real) (hz₀a : a < z₀) (hz₀b : z₀ < b) (hne₀ : (pfaffianChainFn c p).eval z₀ ≠ 0) :
    ∀ z, a < z → z < b → (pfaffianChainFn c p).eval z ≠ 0 := by
  refine pfaffianFn_no_zeros_of_ode_gen (pfaffianChainFn c p) a b hab E
    (fun z => - MultiPoly.eval m z (c.chainValues z)) hcoh hE ?_ z₀ hz₀a hz₀b hne₀
  intro z hza hzb
  show (pfaffianChainFn c p).chainTotalDerivative.eval z
      + (- MultiPoly.eval m z (c.chainValues z)) * (pfaffianChainFn c p).eval z = 0
  have hr := h_reduce z hza hzb
  rw [chainReduce_eval_along] at hr
  generalize (pfaffianChainFn c p).chainTotalDerivative.eval z = A at hr ⊢
  generalize MultiPoly.eval m z (c.chainValues z) = B at hr ⊢
  generalize (pfaffianChainFn c p).eval z = C at hr ⊢
  -- hr : A - B * C = 0 ; goal : A + (-B) * C = 0
  rw [show A + (-B) * C = A - B * C from by mach_mpoly [A, B, C]]
  exact hr

/-! ## Descent foundation: the top-degree of `chainTotalDeriv` for exponential-type chains

The reduce descent rests on `degreeY_top (chainTotalDeriv c p) = degreeY_top p`. For the iterated-exp
chain this is `degreeYtop_cTD_eq`, whose only chain-dependence is the `varY` case. That case needs
exactly two facts, which characterize the **exponential-type + triangular** chains:

* `degreeY_top (relations top) = 1`  — the top relation is *linear* in the top variable
  (`relations top = y_top · G`, `G` top-free); and
* `degreeY_top (relations j) = 0` for `j ≠ top` — triangularity (lower relations omit `y_top`).

Everything else (`const`/`varX`/`add`/`sub`/`mul`) is chain-agnostic — `chainTotalDeriv` is a structural
derivation, so its top-degree recurrence holds for ANY chain. This is the substantive base lemma of the
generalized descent; the iterated-exp `degreeYtop_cTD_eq` is its instantiation. -/
theorem degreeYtop_cTD_eq_gen {N : Nat} (c : PfaffianChain N) (top : Fin N)
    (h_top : MultiPoly.degreeY top (c.relations top) = 1)
    (h_tri : ∀ j : Fin N, j ≠ top → MultiPoly.degreeY top (c.relations j) = 0)
    (p : MultiPoly N) :
    MultiPoly.degreeY top (chainTotalDeriv c p) = MultiPoly.degreeY top p := by
  induction p with
  | const cval => rfl
  | varX => rfl
  | varY j =>
    show MultiPoly.degreeY top (c.relations j) = MultiPoly.degreeY top (MultiPoly.varY j)
    by_cases hj : j = top
    · rw [hj, h_top]
      show (1 : Nat) = (if top = top then 1 else 0)
      rw [if_pos rfl]
    · rw [h_tri j hj]
      show (0 : Nat) = (if top = j then 1 else 0)
      rw [if_neg (fun h => hj h.symm)]
  | add p q ihp ihq =>
    show Nat.max (MultiPoly.degreeY top (chainTotalDeriv c p))
                 (MultiPoly.degreeY top (chainTotalDeriv c q))
       = Nat.max (MultiPoly.degreeY top p) (MultiPoly.degreeY top q)
    rw [ihp, ihq]
  | sub p q ihp ihq =>
    show Nat.max (MultiPoly.degreeY top (chainTotalDeriv c p))
                 (MultiPoly.degreeY top (chainTotalDeriv c q))
       = Nat.max (MultiPoly.degreeY top p) (MultiPoly.degreeY top q)
    rw [ihp, ihq]
  | mul p q ihp ihq =>
    show Nat.max (MultiPoly.degreeY top (chainTotalDeriv c p) + MultiPoly.degreeY top q)
                 (MultiPoly.degreeY top p + MultiPoly.degreeY top (chainTotalDeriv c q))
       = MultiPoly.degreeY top p + MultiPoly.degreeY top q
    rw [ihp, ihq]; exact Nat.max_self _

end MachLib.PfaffianGeneralReduce
