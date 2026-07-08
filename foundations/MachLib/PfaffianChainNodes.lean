import MachLib.PfaffianChainExtend
import MachLib.Exp
import MachLib.Differentiation
import MachLib.SturmNonOscillation

/-!
# Encoder node steps — add an `exp` variable to a chain

The recursive EMLTree→chain encoder adds, at each `exp(sub)` sub-expression,
a fresh top chain variable `y = exp(sub-value)` with the exp-type relation
`y' = sub' · y`. This file proves that step's coherence obligation: the new
variable genuinely has the derivative its relation prescribes.

`chainExtend_exp_isCoherentAt` — for `ne = exp ∘ (eval b along c)` and
relation `nr = (liftLastY (chainTotalDeriv c b)) · y_top`, the coherence
condition `HasDerivAt ne (eval nr …) x` holds at every point where `c` is
coherent. Proof: the chain-derivative bridge `multiPolyHasDerivAt_eval_with_
chain` differentiates the exponent, `HasDerivAt_exp`/`HasDerivAt_comp` chain
through `exp`, and the relation's eval collapses through
`eval_liftLastY_chainExtend` (`liftLastY` factor) + `eval_varY` (the new top
= `ne x`) to the same product.

This is the exp-node inductive step; combined with `chainExtend_isCoherentOn`
it discharges coherence for an exp extension. No new axioms.
-/

namespace MachLib

open MachLib.Real MachLib.MultiPolyMod MachLib.MultiPolyMod.MultiPoly
  MachLib.PfaffianChainMod MachLib.PfaffianChainMod.PfaffianChain
  MachLib.PfaffianChainMod.PfaffianFn MachLib.PfaffianGeneralReduce

/-- **Add-exp-node coherence.** The new variable `ne = exp(eval b along c)`
with exp-type relation `nr = liftLastY(cTD b) · y_top` has exactly the
derivative `nr` prescribes at any coherent point `x`. -/
theorem chainExtend_exp_isCoherentAt {n : Nat} (c : PfaffianChain n)
    (b : MultiPoly n) (x : Real) (hcoh : c.IsCoherentAt x)
    (ne : Real → Real)
    (hne : ne = fun y => Real.exp (MultiPoly.eval b y (c.chainValues y)))
    (nr : MultiPoly (n + 1))
    (hnr : nr = MultiPoly.mul (MultiPoly.liftLastY (chainTotalDeriv c b))
              (MultiPoly.varY (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)))) :
    HasDerivAt ne (MultiPoly.eval nr x ((chainExtend c ne nr).chainValues x)) x := by
  have hval : MultiPoly.eval nr x ((chainExtend c ne nr).chainValues x)
      = Real.exp (MultiPoly.eval b x (c.chainValues x))
        * MultiPoly.eval (chainTotalDeriv c b) x (c.chainValues x) := by
    rw [hnr]
    show MultiPoly.eval (MultiPoly.liftLastY (chainTotalDeriv c b)) x
            ((chainExtend c ne nr).chainValues x)
         * MultiPoly.eval (MultiPoly.varY (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1))) x
            ((chainExtend c ne nr).chainValues x)
       = Real.exp (MultiPoly.eval b x (c.chainValues x))
         * MultiPoly.eval (chainTotalDeriv c b) x (c.chainValues x)
    rw [eval_liftLastY_chainExtend c ne nr (chainTotalDeriv c b) x, MultiPoly.eval_varY]
    show MultiPoly.eval (chainTotalDeriv c b) x (c.chainValues x)
          * (chainExtend c ne nr).evals (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) x
       = Real.exp (MultiPoly.eval b x (c.chainValues x))
         * MultiPoly.eval (chainTotalDeriv c b) x (c.chainValues x)
    rw [chainExtend_evals_last c ne nr, hne, mul_comm]
  rw [hval, hne]
  exact HasDerivAt_comp Real.exp (fun y => MultiPoly.eval b y (c.chainValues y))
    (MultiPoly.eval (chainTotalDeriv c b) x (c.chainValues x))
    (Real.exp (MultiPoly.eval b x (c.chainValues x))) x
    (multiPolyHasDerivAt_eval_with_chain c b x hcoh)
    (HasDerivAt_exp (MultiPoly.eval b x (c.chainValues x)))

/-- `eval` of `MultiPoly.neg` negates. (`neg p = sub zero p`.) -/
private theorem eval_neg_mp {m : Nat} (p : MultiPoly m) (x : Real) (env : Fin m → Real) :
    MultiPoly.eval (MultiPoly.neg p) x env = -(MultiPoly.eval p x env) := by
  show MultiPoly.eval (MultiPoly.sub MultiPoly.zero p) x env = -(MultiPoly.eval p x env)
  rw [MultiPoly.eval_sub]
  show (0 : Real) - MultiPoly.eval p x env = -(MultiPoly.eval p x env)
  rw [sub_def, zero_add]

/-- **Add-reciprocal-node coherence.** The new variable `ne = 1/(eval w along
c)` with recip-type relation `nr = (−liftLastY(cTD w))·y_top²` has exactly the
derivative `nr` prescribes at any coherent point where `w > 0`. Proof: the
relation's eval collapses to `−(cTD w along c)·(1/w)²`, matched to the
`HasDerivAt_inv` derivative `−(cTD w)/(w·w)` via `one_div_mul_one_div`. -/
theorem chainExtend_recip_isCoherentAt {n : Nat} (c : PfaffianChain n)
    (w : MultiPoly n) (x : Real) (hcoh : c.IsCoherentAt x)
    (hwpos : 0 < MultiPoly.eval w x (c.chainValues x))
    (ne : Real → Real)
    (hne : ne = fun y => 1 / MultiPoly.eval w y (c.chainValues y))
    (nr : MultiPoly (n + 1))
    (hnr : nr = MultiPoly.mul (MultiPoly.neg (MultiPoly.liftLastY (chainTotalDeriv c w)))
              (MultiPoly.mul (MultiPoly.varY (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)))
                             (MultiPoly.varY (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1))))) :
    HasDerivAt ne (MultiPoly.eval nr x ((chainExtend c ne nr).chainValues x)) x := by
  have hww : MultiPoly.eval w x (c.chainValues x) ≠ 0 := ne_of_gt hwpos
  have hval : MultiPoly.eval nr x ((chainExtend c ne nr).chainValues x)
      = -(MultiPoly.eval (chainTotalDeriv c w) x (c.chainValues x))
        / (MultiPoly.eval w x (c.chainValues x) * MultiPoly.eval w x (c.chainValues x)) := by
    rw [hnr]
    show MultiPoly.eval (MultiPoly.neg (MultiPoly.liftLastY (chainTotalDeriv c w))) x
            ((chainExtend c ne nr).chainValues x)
         * (MultiPoly.eval (MultiPoly.varY (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1))) x
              ((chainExtend c ne nr).chainValues x)
            * MultiPoly.eval (MultiPoly.varY (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1))) x
              ((chainExtend c ne nr).chainValues x))
       = _
    rw [eval_neg_mp, eval_liftLastY_chainExtend c ne nr (chainTotalDeriv c w) x,
        MultiPoly.eval_varY]
    show -(MultiPoly.eval (chainTotalDeriv c w) x (c.chainValues x))
          * ((chainExtend c ne nr).evals (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) x
             * (chainExtend c ne nr).evals (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) x)
       = _
    rw [chainExtend_evals_last c ne nr, hne, one_div_mul_one_div hwpos,
        div_def (-(MultiPoly.eval (chainTotalDeriv c w) x (c.chainValues x)))
          (MultiPoly.eval w x (c.chainValues x) * MultiPoly.eval w x (c.chainValues x))
          (ne_of_gt (mul_pos hwpos hwpos))]
  rw [hval, hne]
  exact HasDerivAt_inv (fun y => MultiPoly.eval w y (c.chainValues y))
    (MultiPoly.eval (chainTotalDeriv c w) x (c.chainValues x)) x hww
    (multiPolyHasDerivAt_eval_with_chain c w x hcoh)

end MachLib
