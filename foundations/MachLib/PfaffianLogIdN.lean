import MachLib.MultiPolyCoeffEntry
import MachLib.PfaffianCTDCongrChain

/-!
# L2 idN-log identity — inductive step lemmas (along-chain)

The along-chain per-degree `cTD`-coefficient identity for a log top, as
committable step lemmas (mirroring the exp `idN_{add,sub,mul}_gen` family). Each
uses the L1 `getD_list*_eval` commute lemmas + `eval_cTD_congr_chain` (`cTD`
respects eval-equality along the chain) + the induction hypotheses. The `add`/`sub`
cases here; `varY` (base) and `mul` (convolution) follow, then they assemble into
the full `idN_log` induction, whose specialisation at `d = degreeY_top` (the
correction vanishes) gives the Wronskian degree-drop for `log_hard`.

`IdNLogChain c top p d x` is the identity at one `(p,d,x)`:
`getD_d(yCoeffsAt top (cTD c p)) ≡ cTD c (getD_d(yCoeffsAt top p))
  + (d+1)·relations_top·getD_{d+1}(yCoeffsAt top p)`, evaluated at `(x, chainValues x)`.
-/
namespace MachLib
namespace PfaffianLogIdN
open MachLib.Real
open MachLib.MultiPolyMod MachLib.MultiPolyMod.MultiPoly
open MachLib.PfaffianChainMod MachLib.PfaffianChainMod.PfaffianChain MachLib.PfaffianChainMod.PfaffianFn

/-- The along-chain L2 identity at one `(p, d, x)`. -/
def IdNLogChain {N : Nat} (c : PfaffianChain N) (top : Fin N) (p : MultiPoly N) (d : Nat) (x : Real) : Prop :=
  MultiPoly.eval ((yCoeffsAt top (chainTotalDeriv c p)).getD d (MultiPoly.const 0)) x (c.chainValues x)
    = MultiPoly.eval (chainTotalDeriv c ((yCoeffsAt top p).getD d (MultiPoly.const 0))) x (c.chainValues x)
      + Real.natCast (d + 1) * MultiPoly.eval (c.relations top) x (c.chainValues x)
        * MultiPoly.eval ((yCoeffsAt top p).getD (d + 1) (MultiPoly.const 0)) x (c.chainValues x)

theorem idN_log_add_step {N : Nat} (c : PfaffianChain N) (top : Fin N) (x : Real)
    (hcohx : c.IsCoherentAt x) (p q : MultiPoly N)
    (ihp : ∀ d, IdNLogChain c top p d x) (ihq : ∀ d, IdNLogChain c top q d x) :
    ∀ d, IdNLogChain c top (MultiPoly.add p q) d x := by
  intro d
  -- key eval-splits via getD_listAddN
  have hL : MultiPoly.eval ((yCoeffsAt top (chainTotalDeriv c (MultiPoly.add p q))).getD d (MultiPoly.const 0)) x (c.chainValues x)
      = MultiPoly.eval ((yCoeffsAt top (chainTotalDeriv c p)).getD d (MultiPoly.const 0)) x (c.chainValues x)
        + MultiPoly.eval ((yCoeffsAt top (chainTotalDeriv c q)).getD d (MultiPoly.const 0)) x (c.chainValues x) :=
    getD_listAddN_eval (yCoeffsAt top (chainTotalDeriv c p)) (yCoeffsAt top (chainTotalDeriv c q)) d x (c.chainValues x)
  have hC1 : MultiPoly.eval ((yCoeffsAt top (MultiPoly.add p q)).getD (d+1) (MultiPoly.const 0)) x (c.chainValues x)
      = MultiPoly.eval ((yCoeffsAt top p).getD (d+1) (MultiPoly.const 0)) x (c.chainValues x)
        + MultiPoly.eval ((yCoeffsAt top q).getD (d+1) (MultiPoly.const 0)) x (c.chainValues x) :=
    getD_listAddN_eval (yCoeffsAt top p) (yCoeffsAt top q) (d+1) x (c.chainValues x)
  -- RHS cTD term: cTD(getD_d(yCoeffsAt(add p q))) splits via congruence
  have hcong : MultiPoly.eval (chainTotalDeriv c ((yCoeffsAt top (MultiPoly.add p q)).getD d (MultiPoly.const 0))) x (c.chainValues x)
      = MultiPoly.eval (chainTotalDeriv c (MultiPoly.add ((yCoeffsAt top p).getD d (MultiPoly.const 0)) ((yCoeffsAt top q).getD d (MultiPoly.const 0)))) x (c.chainValues x) := by
    apply eval_cTD_congr_chain c _ _ x hcohx
    intro y
    show MultiPoly.eval ((listAddN (yCoeffsAt top p) (yCoeffsAt top q)).getD d (MultiPoly.const 0)) y (c.chainValues y) = _
    rw [getD_listAddN_eval, MultiPoly.eval_add]
  have hRC : MultiPoly.eval (chainTotalDeriv c (MultiPoly.add ((yCoeffsAt top p).getD d (MultiPoly.const 0)) ((yCoeffsAt top q).getD d (MultiPoly.const 0)))) x (c.chainValues x)
      = MultiPoly.eval (chainTotalDeriv c ((yCoeffsAt top p).getD d (MultiPoly.const 0))) x (c.chainValues x)
        + MultiPoly.eval (chainTotalDeriv c ((yCoeffsAt top q).getD d (MultiPoly.const 0))) x (c.chainValues x) := by
    rw [show chainTotalDeriv c (MultiPoly.add ((yCoeffsAt top p).getD d (MultiPoly.const 0)) ((yCoeffsAt top q).getD d (MultiPoly.const 0)))
          = MultiPoly.add (chainTotalDeriv c ((yCoeffsAt top p).getD d (MultiPoly.const 0))) (chainTotalDeriv c ((yCoeffsAt top q).getD d (MultiPoly.const 0))) from rfl,
        MultiPoly.eval_add]
  show _ = _
  rw [hL, ihp d, ihq d, hC1, hcong, hRC]
  mach_ring

theorem idN_log_sub_step {N : Nat} (c : PfaffianChain N) (top : Fin N) (x : Real)
    (hcohx : c.IsCoherentAt x) (p q : MultiPoly N)
    (ihp : ∀ d, IdNLogChain c top p d x) (ihq : ∀ d, IdNLogChain c top q d x) :
    ∀ d, IdNLogChain c top (MultiPoly.sub p q) d x := by
  intro d
  have hL : MultiPoly.eval ((yCoeffsAt top (chainTotalDeriv c (MultiPoly.sub p q))).getD d (MultiPoly.const 0)) x (c.chainValues x)
      = MultiPoly.eval ((yCoeffsAt top (chainTotalDeriv c p)).getD d (MultiPoly.const 0)) x (c.chainValues x)
        - MultiPoly.eval ((yCoeffsAt top (chainTotalDeriv c q)).getD d (MultiPoly.const 0)) x (c.chainValues x) :=
    getD_listSubN_eval (yCoeffsAt top (chainTotalDeriv c p)) (yCoeffsAt top (chainTotalDeriv c q)) d x (c.chainValues x)
  have hC1 : MultiPoly.eval ((yCoeffsAt top (MultiPoly.sub p q)).getD (d+1) (MultiPoly.const 0)) x (c.chainValues x)
      = MultiPoly.eval ((yCoeffsAt top p).getD (d+1) (MultiPoly.const 0)) x (c.chainValues x)
        - MultiPoly.eval ((yCoeffsAt top q).getD (d+1) (MultiPoly.const 0)) x (c.chainValues x) :=
    getD_listSubN_eval (yCoeffsAt top p) (yCoeffsAt top q) (d+1) x (c.chainValues x)
  have hcong : MultiPoly.eval (chainTotalDeriv c ((yCoeffsAt top (MultiPoly.sub p q)).getD d (MultiPoly.const 0))) x (c.chainValues x)
      = MultiPoly.eval (chainTotalDeriv c (MultiPoly.sub ((yCoeffsAt top p).getD d (MultiPoly.const 0)) ((yCoeffsAt top q).getD d (MultiPoly.const 0)))) x (c.chainValues x) := by
    apply eval_cTD_congr_chain c _ _ x hcohx
    intro y
    show MultiPoly.eval ((listSubN (yCoeffsAt top p) (yCoeffsAt top q)).getD d (MultiPoly.const 0)) y (c.chainValues y) = _
    rw [getD_listSubN_eval, MultiPoly.eval_sub]
  have hRC : MultiPoly.eval (chainTotalDeriv c (MultiPoly.sub ((yCoeffsAt top p).getD d (MultiPoly.const 0)) ((yCoeffsAt top q).getD d (MultiPoly.const 0)))) x (c.chainValues x)
      = MultiPoly.eval (chainTotalDeriv c ((yCoeffsAt top p).getD d (MultiPoly.const 0))) x (c.chainValues x)
        - MultiPoly.eval (chainTotalDeriv c ((yCoeffsAt top q).getD d (MultiPoly.const 0))) x (c.chainValues x) := by
    rw [show chainTotalDeriv c (MultiPoly.sub ((yCoeffsAt top p).getD d (MultiPoly.const 0)) ((yCoeffsAt top q).getD d (MultiPoly.const 0)))
          = MultiPoly.sub (chainTotalDeriv c ((yCoeffsAt top p).getD d (MultiPoly.const 0))) (chainTotalDeriv c ((yCoeffsAt top q).getD d (MultiPoly.const 0))) from rfl,
        MultiPoly.eval_sub]
  show _ = _
  rw [hL, ihp d, ihq d, hC1, hcong, hRC]
  mach_ring

end PfaffianLogIdN
end MachLib
