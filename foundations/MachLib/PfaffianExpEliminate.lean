import MachLib.PfaffianGeneralReduce
import MachLib.IterExpTopIdentity

/-!
# `exp_hard` via `expEliminate` — the Wronskian-normalize elimination (B1)

The mixed-chain `exp_hard` reduce-measure route is structurally blocked (see
`roadmap/exp-hard-mixed-measure-port.md`): the exp reduce's leading-coefficient recursion cannot descend a
mixed chain (reciprocal grows, log needs a Wronskian the reduce can't express). The resolution is a DIRECT
exp-sum zero bound that recurses on `degreeY_top` (a `Nat`) instead of a chain measure, so the reciprocal is
never descended — its zeros enter only through the depth-below bound on the leading coefficient.

This file lays the algebraic core (B1): the elimination polynomial

  `expEliminate c G top p := leadingCoeffY_top p · chainReduce c (D·G) p − p · cTD(leadingCoeffY_top p)`
  (`D := degreeY_top p`)  =  `cTD(p)·lcY − p·cTD(lcY) − D·G·p·lcY`

whose top `y`-coefficient EVALUATES to 0 — it is the polynomial form of `y^D·W(f·y^{−D}, b_D)`, whose top
exponential vanishes. So `leadingCoeffY_top(expEliminate …)` is phantom, and an eval-zero trim (B2) drops
`degreeY_top` to `D−1`. The eval-zero is `chainReduce_lcY_top_cancel` (with the lower multiplier `= 0`).
-/

namespace MachLib.PfaffianExpEliminate

open MachLib.Real
open MachLib.MultiPolyMod MachLib.MultiPolyMod.MultiPoly
open MachLib.PfaffianChainMod
open MachLib.PfaffianChainMod.PfaffianFn
open MachLib.PfaffianGeneralReduce
open MachLib.IterExpTopIdentity
open MachLib.ChainExp2NoZeros

/-- The exp-top elimination polynomial. `lcY·chainReduce(c, D·G, p) − p·cTD(lcY)`, `D = degreeY_top p`. Equals
`cTD(p)·lcY − p·cTD(lcY) − D·G·p·lcY`; its top `y`-coefficient evaluates to 0. -/
noncomputable def expEliminate {N : Nat} (c : PfaffianChain N) (G : MultiPoly N) (top : Fin N)
    (p : MultiPoly N) : MultiPoly N :=
  MultiPoly.sub
    (MultiPoly.mul (MultiPoly.leadingCoeffY top p)
      (chainReduce c (MultiPoly.mul (MultiPoly.const (natCast (MultiPoly.degreeY top p))) G) p))
    (MultiPoly.mul p (chainTotalDeriv c (MultiPoly.leadingCoeffY top p)))

/-- **B1 — the elimination.** The top `y`-coefficient of `expEliminate` evaluates to 0 along the chain: the
exp reduce's leading-coeff cancellation (`chainReduce_lcY_top_cancel`, lower multiplier `0`) makes the
leading coefficient of `chainReduce c (D·G) p` evaluate to `cTD(lcY)`, and the two `lcY·cTD(lcY)` terms cancel. -/
theorem expEliminate_lcY_top_eval_zero {N : Nat} (c : PfaffianChain N) (G : MultiPoly N) (top : Fin N)
    (h_reltop : c.relations top = MultiPoly.mul G (MultiPoly.varY top))
    (h_Gtop : MultiPoly.degreeY top G = 0)
    (h_tri : ∀ j : Fin N, j ≠ top → MultiPoly.degreeY top (c.relations j) = 0)
    (p : MultiPoly N) (x : Real) (env : Fin N → Real) :
    MultiPoly.eval (MultiPoly.leadingCoeffY top (expEliminate c G top p)) x env = 0 := by
  have hvt : MultiPoly.degreeY top (MultiPoly.varY top) = 1 := by
    show (if top = top then (1 : Nat) else 0) = 1; simp
  have h_top : MultiPoly.degreeY top (c.relations top) = 1 := by
    rw [h_reltop, degreeY_mul' top G (MultiPoly.varY top)]; omega
  have hconstD : MultiPoly.degreeY top
      (MultiPoly.const (natCast (MultiPoly.degreeY top p))) = 0 := rfl
  have hm : MultiPoly.degreeY top
      (MultiPoly.mul (MultiPoly.const (natCast (MultiPoly.degreeY top p))) G) = 0 := by
    rw [degreeY_mul' top (MultiPoly.const (natCast (MultiPoly.degreeY top p))) G]; omega
  have hlcY0 : MultiPoly.degreeY top (MultiPoly.leadingCoeffY top p) = 0 := degreeY_leadingCoeffY top p
  have hRdeg : MultiPoly.degreeY top
      (chainReduce c (MultiPoly.mul (MultiPoly.const (natCast (MultiPoly.degreeY top p))) G) p)
      = MultiPoly.degreeY top p :=
    chainReduce_degreeY_top_preserved c top h_top h_tri _ p hm
  have hcTDlcY0 : MultiPoly.degreeY top (chainTotalDeriv c (MultiPoly.leadingCoeffY top p)) = 0 := by
    rw [degreeYtop_cTD_eq_gen c top h_top h_tri (MultiPoly.leadingCoeffY top p)]; exact hlcY0
  have hAdeg : MultiPoly.degreeY top (MultiPoly.mul (MultiPoly.leadingCoeffY top p)
      (chainReduce c (MultiPoly.mul (MultiPoly.const (natCast (MultiPoly.degreeY top p))) G) p))
      = MultiPoly.degreeY top p := by
    rw [degreeY_mul' top (MultiPoly.leadingCoeffY top p)
      (chainReduce c (MultiPoly.mul (MultiPoly.const (natCast (MultiPoly.degreeY top p))) G) p)]; omega
  have hBdeg : MultiPoly.degreeY top
      (MultiPoly.mul p (chainTotalDeriv c (MultiPoly.leadingCoeffY top p)))
      = MultiPoly.degreeY top p := by
    rw [degreeY_mul' top p (chainTotalDeriv c (MultiPoly.leadingCoeffY top p))]; omega
  unfold expEliminate
  rw [leadingCoeffY_sub_of_eq top _ _ (by rw [hAdeg, hBdeg]),
      lcY_mul top _ _, lcY_mul top _ _,
      leadingCoeffY_eq_self_of_degreeY_zero top (MultiPoly.leadingCoeffY top p) hlcY0,
      leadingCoeffY_eq_self_of_degreeY_zero top
        (chainTotalDeriv c (MultiPoly.leadingCoeffY top p)) hcTDlcY0]
  simp only [MultiPoly.eval_sub, MultiPoly.eval_mul]
  have hcancel : MultiPoly.eval (MultiPoly.leadingCoeffY top
        (chainReduce c (MultiPoly.mul (MultiPoly.const (natCast (MultiPoly.degreeY top p))) G) p)) x env
      = MultiPoly.eval (chainTotalDeriv c (MultiPoly.leadingCoeffY top p)) x env := by
    have hc := chainReduce_lcY_top_cancel c G top h_reltop h_Gtop h_tri
      (MultiPoly.mul (MultiPoly.const (natCast (MultiPoly.degreeY top p))) G) (MultiPoly.const 0) p hm
      x env (by simp only [MultiPoly.eval_mul, MultiPoly.eval_const]; mach_ring)
    rw [hc]; simp only [MultiPoly.eval_const]; mach_ring
  rw [hcancel]; mach_ring

end MachLib.PfaffianExpEliminate
