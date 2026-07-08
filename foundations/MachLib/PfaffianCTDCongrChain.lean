import MachLib.PfaffianChain

/-!
# `cTD` respects eval-equality along the chain (general chain)

The enabling lemma for `log_hard`'s L2 inductive cases. `eval_cTD_congr_y1free_gen`
gave this for `Fin 2` + general env, via a partial-derivative decomposition. But
everything in the descent is evaluated ALONG THE CHAIN, and along the chain the
chain-rule theorem `multiPolyHasDerivAt_eval_with_chain` says `eval(cTD r)` is the
derivative of `eval r` along the chain — so `HasDerivAt_unique` gives congruence
directly, for a general chain, in five lines and with NO sum-over-`Fin n`
decomposition. This is what L2's `add`/`sub`/`varY`/`mul` cases use to split
`eval(cTD(getD_d(listAddN…)))` (`getD` commutes with the list ops only at the
eval level; `cTD` respecting that eval-equality closes the gap).
-/
namespace MachLib
open MachLib.Real MachLib.MultiPolyMod
open MachLib.PfaffianChainMod MachLib.PfaffianChainMod.PfaffianChain MachLib.PfaffianChainMod.PfaffianFn

theorem eval_cTD_congr_chain {n : Nat} (c : PfaffianChain n) (a b : MultiPoly n) (x : Real)
    (hcohx : c.IsCoherentAt x)
    (hab : ∀ y : Real, MultiPoly.eval a y (c.chainValues y) = MultiPoly.eval b y (c.chainValues y)) :
    MultiPoly.eval (chainTotalDeriv c a) x (c.chainValues x)
      = MultiPoly.eval (chainTotalDeriv c b) x (c.chainValues x) := by
  have hda := multiPolyHasDerivAt_eval_with_chain c a x hcohx
  have hdb := multiPolyHasDerivAt_eval_with_chain c b x hcohx
  have hfeq : (fun y => MultiPoly.eval a y (c.chainValues y))
      = (fun y => MultiPoly.eval b y (c.chainValues y)) := funext hab
  rw [hfeq] at hda
  exact HasDerivAt_unique _ _ _ x hda hdb

end MachLib
