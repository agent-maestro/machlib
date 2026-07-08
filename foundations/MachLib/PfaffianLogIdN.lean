import MachLib.MultiPolyCoeffEntry
import MachLib.PfaffianCTDCongrChain
import MachLib.MultiPolyReconstruct

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
namespace MultiPolyMod
namespace MultiPoly
open MachLib.Real MachLib.MultiPolyReconstruct

/-- **Top-free `getD 0` collapse.** When `r` is `y_top`-free (`degreeY top r = 0`),
its `yCoeffsAt top` list is a singleton, so index `0` recovers `r` at the eval
level. The `varY` (base) `d = 0` ingredient of the `idN`-log induction — the LHS
`yCoeffsAt top (cTD c (varY j)) = yCoeffsAt top (relations j)` is top-free (log
discipline). Reconstructs via `eval_reconstructY_yCoeffsAt` (the `getLast` route
trips a dependent-motive `rw`). -/
theorem topfree_getD0_eval {N : Nat} (top : Fin N) (r : MultiPoly N)
    (hfree : MultiPoly.degreeY top r = 0) (x : Real) (env : Fin N → Real) :
    MultiPoly.eval ((yCoeffsAt top r).getD 0 (MultiPoly.const 0)) x env = MultiPoly.eval r x env := by
  obtain ⟨a, ha⟩ := List.length_eq_one.mp (yCoeffsAt_length_one_when_y_free top r hfree)
  rw [ha]
  show MultiPoly.eval a x env = MultiPoly.eval r x env
  have hrec := eval_reconstructY_yCoeffsAt top r x env
  rw [ha] at hrec
  rw [← hrec]
  show MultiPoly.eval a x env = MultiPoly.eval a x env * 1 + 0
  mach_ring

/-- **Top-free `getD (d+1)` vanishes.** A `y_top`-free `r` has a singleton
`yCoeffsAt top` list, so every positive index is the default `const 0`
(eval `0`). The `varY` (base) `d ≥ 1` ingredient of the `idN`-log induction. -/
theorem topfree_getD_succ_eval {N : Nat} (top : Fin N) (r : MultiPoly N)
    (hfree : MultiPoly.degreeY top r = 0) (d : Nat) (x : Real) (env : Fin N → Real) :
    MultiPoly.eval ((yCoeffsAt top r).getD (d + 1) (MultiPoly.const 0)) x env = 0 := by
  obtain ⟨a, ha⟩ := List.length_eq_one.mp (yCoeffsAt_length_one_when_y_free top r hfree)
  rw [ha]; rfl

end MultiPoly
end MultiPolyMod
end MachLib

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

theorem idN_log_const_step {N : Nat} (c : PfaffianChain N) (top : Fin N) (cval : Real) (x : Real) :
    ∀ d, IdNLogChain c top (MultiPoly.const cval) d x := by
  intro d
  have hL : MultiPoly.eval ((yCoeffsAt top (chainTotalDeriv c (MultiPoly.const cval))).getD d (MultiPoly.const 0)) x (c.chainValues x) = 0 := by
    show MultiPoly.eval (([MultiPoly.const 0] : List (MultiPoly N)).getD d (MultiPoly.const 0)) x (c.chainValues x) = 0
    cases d <;> rfl
  have hR1 : MultiPoly.eval (chainTotalDeriv c ((yCoeffsAt top (MultiPoly.const cval)).getD d (MultiPoly.const 0))) x (c.chainValues x) = 0 := by
    show MultiPoly.eval (chainTotalDeriv c (([MultiPoly.const cval] : List (MultiPoly N)).getD d (MultiPoly.const 0))) x (c.chainValues x) = 0
    cases d <;> rfl
  have hR2 : MultiPoly.eval ((yCoeffsAt top (MultiPoly.const cval)).getD (d + 1) (MultiPoly.const 0)) x (c.chainValues x) = 0 := by
    show MultiPoly.eval (([MultiPoly.const cval] : List (MultiPoly N)).getD (d + 1) (MultiPoly.const 0)) x (c.chainValues x) = 0
    rfl
  show _ = _
  rw [hL, hR1, hR2]; mach_ring

theorem idN_log_varX_step {N : Nat} (c : PfaffianChain N) (top : Fin N) (x : Real) :
    ∀ d, IdNLogChain c top MultiPoly.varX d x := by
  intro d
  have hR2 : MultiPoly.eval ((yCoeffsAt top MultiPoly.varX).getD (d + 1) (MultiPoly.const 0)) x (c.chainValues x) = 0 := by
    show MultiPoly.eval (([MultiPoly.varX] : List (MultiPoly N)).getD (d + 1) (MultiPoly.const 0)) x (c.chainValues x) = 0
    rfl
  show MultiPoly.eval ((yCoeffsAt top (chainTotalDeriv c MultiPoly.varX)).getD d (MultiPoly.const 0)) x (c.chainValues x) = _
  cases d with
  | zero =>
    show MultiPoly.eval (([MultiPoly.const 1] : List (MultiPoly N)).getD 0 (MultiPoly.const 0)) x (c.chainValues x)
        = MultiPoly.eval (chainTotalDeriv c (([MultiPoly.varX] : List (MultiPoly N)).getD 0 (MultiPoly.const 0))) x (c.chainValues x)
          + Real.natCast (0 + 1) * MultiPoly.eval (c.relations top) x (c.chainValues x)
            * MultiPoly.eval ((yCoeffsAt top MultiPoly.varX).getD (0 + 1) (MultiPoly.const 0)) x (c.chainValues x)
    rw [hR2]
    show (1 : Real) = (1 : Real) + Real.natCast 1 * MultiPoly.eval (c.relations top) x (c.chainValues x) * (0 : Real)
    mach_ring
  | succ d =>
    show MultiPoly.eval (([MultiPoly.const 1] : List (MultiPoly N)).getD (d+1) (MultiPoly.const 0)) x (c.chainValues x)
        = MultiPoly.eval (chainTotalDeriv c (([MultiPoly.varX] : List (MultiPoly N)).getD (d+1) (MultiPoly.const 0))) x (c.chainValues x)
          + Real.natCast (d+1+1) * MultiPoly.eval (c.relations top) x (c.chainValues x)
            * MultiPoly.eval ((yCoeffsAt top MultiPoly.varX).getD (d+1+1) (MultiPoly.const 0)) x (c.chainValues x)
    rw [hR2]
    show (0 : Real) = (0 : Real) + Real.natCast (d+1+1) * MultiPoly.eval (c.relations top) x (c.chainValues x) * (0 : Real)
    mach_ring

/-- **`idN`-log `varY` (base) step.** For a `varY j` atom under a LOG-type top
(`relations` all `y_top`-free — hypotheses `h_top`/`h_tri`), the per-degree
identity holds. Two shapes: `j = top` gives `yCoeffsAt top (varY top) = [const 0,
const 1]` (degree 1) — the `d = 0` correction term `(0+1)·relations_top·(getD₁ =
const 1)` is exactly `relations_top`, matching `cTD(varY top) = relations top`
(needs `natCast_succ`/`natCast_zero`); `j ≠ top` gives the singleton `[varY j]`
(top-free), the correction vanishing. Both LHS reductions use the top-free
singleton helpers on `yCoeffsAt top (cTD c (varY j)) = yCoeffsAt top (relations
j)`; every non-surviving term is killed by `mach_ring` (`natCast · _ · 0`). -/
theorem idN_log_varY_step {N : Nat} (c : PfaffianChain N) (top : Fin N)
    (h_top : MultiPoly.degreeY top (c.relations top) = 0)
    (h_tri : ∀ j : Fin N, j ≠ top → MultiPoly.degreeY top (c.relations j) = 0)
    (x : Real) (j : Fin N) :
    ∀ d, IdNLogChain c top (MultiPoly.varY j) d x := by
  intro d
  by_cases hj : j = top
  · -- j = top : yCoeffsAt top (varY j) = [const 0, const 1]
    have hrelfree : MultiPoly.degreeY top (c.relations j) = 0 := by rw [hj]; exact h_top
    cases d with
    | zero =>
      show MultiPoly.eval ((yCoeffsAt top (c.relations j)).getD 0 (MultiPoly.const 0)) x (c.chainValues x)
         = MultiPoly.eval (chainTotalDeriv c ((if j = top then ([MultiPoly.const 0, MultiPoly.const 1] : List (MultiPoly N)) else [MultiPoly.varY j]).getD 0 (MultiPoly.const 0))) x (c.chainValues x)
           + Real.natCast (0 + 1) * MultiPoly.eval (c.relations top) x (c.chainValues x)
             * MultiPoly.eval ((if j = top then ([MultiPoly.const 0, MultiPoly.const 1] : List (MultiPoly N)) else [MultiPoly.varY j]).getD (0 + 1) (MultiPoly.const 0)) x (c.chainValues x)
      rw [if_pos hj, topfree_getD0_eval top (c.relations j) hrelfree x (c.chainValues x), hj]
      show MultiPoly.eval (c.relations top) x (c.chainValues x)
         = (0 : Real) + Real.natCast (0 + 1) * MultiPoly.eval (c.relations top) x (c.chainValues x) * (1 : Real)
      rw [natCast_succ, natCast_zero]
      mach_ring
    | succ d =>
      have hcTD : MultiPoly.eval (chainTotalDeriv c (([MultiPoly.const 0, MultiPoly.const 1] : List (MultiPoly N)).getD (d + 1) (MultiPoly.const 0))) x (c.chainValues x) = 0 := by
        cases d <;> rfl
      show MultiPoly.eval ((yCoeffsAt top (c.relations j)).getD (d + 1) (MultiPoly.const 0)) x (c.chainValues x)
         = MultiPoly.eval (chainTotalDeriv c ((if j = top then ([MultiPoly.const 0, MultiPoly.const 1] : List (MultiPoly N)) else [MultiPoly.varY j]).getD (d + 1) (MultiPoly.const 0))) x (c.chainValues x)
           + Real.natCast (d + 1 + 1) * MultiPoly.eval (c.relations top) x (c.chainValues x)
             * MultiPoly.eval ((if j = top then ([MultiPoly.const 0, MultiPoly.const 1] : List (MultiPoly N)) else [MultiPoly.varY j]).getD (d + 1 + 1) (MultiPoly.const 0)) x (c.chainValues x)
      rw [if_pos hj, topfree_getD_succ_eval top (c.relations j) hrelfree d x (c.chainValues x), hcTD]
      show (0 : Real) = (0 : Real) + Real.natCast (d + 1 + 1) * MultiPoly.eval (c.relations top) x (c.chainValues x) * (0 : Real)
      mach_ring
  · -- j ≠ top : yCoeffsAt top (varY j) = [varY j]
    have hrelfree : MultiPoly.degreeY top (c.relations j) = 0 := h_tri j hj
    cases d with
    | zero =>
      show MultiPoly.eval ((yCoeffsAt top (c.relations j)).getD 0 (MultiPoly.const 0)) x (c.chainValues x)
         = MultiPoly.eval (chainTotalDeriv c ((if j = top then ([MultiPoly.const 0, MultiPoly.const 1] : List (MultiPoly N)) else [MultiPoly.varY j]).getD 0 (MultiPoly.const 0))) x (c.chainValues x)
           + Real.natCast (0 + 1) * MultiPoly.eval (c.relations top) x (c.chainValues x)
             * MultiPoly.eval ((if j = top then ([MultiPoly.const 0, MultiPoly.const 1] : List (MultiPoly N)) else [MultiPoly.varY j]).getD (0 + 1) (MultiPoly.const 0)) x (c.chainValues x)
      rw [if_neg hj, topfree_getD0_eval top (c.relations j) hrelfree x (c.chainValues x)]
      show MultiPoly.eval (c.relations j) x (c.chainValues x)
         = MultiPoly.eval (c.relations j) x (c.chainValues x)
           + Real.natCast (0 + 1) * MultiPoly.eval (c.relations top) x (c.chainValues x) * (0 : Real)
      mach_ring
    | succ d =>
      show MultiPoly.eval ((yCoeffsAt top (c.relations j)).getD (d + 1) (MultiPoly.const 0)) x (c.chainValues x)
         = MultiPoly.eval (chainTotalDeriv c ((if j = top then ([MultiPoly.const 0, MultiPoly.const 1] : List (MultiPoly N)) else [MultiPoly.varY j]).getD (d + 1) (MultiPoly.const 0))) x (c.chainValues x)
           + Real.natCast (d + 1 + 1) * MultiPoly.eval (c.relations top) x (c.chainValues x)
             * MultiPoly.eval ((if j = top then ([MultiPoly.const 0, MultiPoly.const 1] : List (MultiPoly N)) else [MultiPoly.varY j]).getD (d + 1 + 1) (MultiPoly.const 0)) x (c.chainValues x)
      rw [if_neg hj, topfree_getD_succ_eval top (c.relations j) hrelfree d x (c.chainValues x)]
      show (0 : Real) = MultiPoly.eval (chainTotalDeriv c (MultiPoly.const 0)) x (c.chainValues x)
           + Real.natCast (d + 1 + 1) * MultiPoly.eval (c.relations top) x (c.chainValues x) * (0 : Real)
      show (0 : Real) = (0 : Real) + Real.natCast (d + 1 + 1) * MultiPoly.eval (c.relations top) x (c.chainValues x) * (0 : Real)
      mach_ring

end PfaffianLogIdN
end MachLib
