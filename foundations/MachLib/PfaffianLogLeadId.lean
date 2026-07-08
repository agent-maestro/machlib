import MachLib.PfaffianRolleStep
import MachLib.MultiPolyCoeffDegree
import MachLib.IterExpTopIdentity
import MachLib.ChainExp2NoZeros
/-!
# LOG leading-coefficient identity (`idN_log_lead`) — the descent core for `log_hard`

For a LOG-type top (`degreeY top (relations top) = 0`, and every other relation
top-free), the coefficient of `chainTotalDeriv c p` at the FIXED original top
degree `D = degreeY_top p` equals `chainTotalDeriv c (leadingCoeffY top p)`:

    eval(getD_D(yCoeffsAt top (cTD c p))) = eval(cTD c (leadingCoeffY top p)).

This is the log analogue of the exp descent's `PfaffianGeneralReduce.IdNGen`
(`idN_{add,sub,mul}_gen`), with two differences forced by the log level:
  * **getD at the fixed `D`**, not `leadingCoeffY (cTD c p)`. A log `cTD` can DROP
    the top degree (`degreeYtop_cTD_le_log`: `≤`), so `leadingCoeffY (cTD c p)` may
    read a lower degree; `getD_D` always reads the original degree.
  * **NO correction term.** The exp identity carries `+ deg·(G·lcY)` because
    `cTD(y_top) = G·y_top` keeps the degree; log's `cTD(y_top) = w` (top-free)
    LOWERS it, so the correction lands below `D` and vanishes.
The `mul` case is still SINGLE-TERM (via `getD_mul_split_eval`, mirroring the exp
`lcY_mul`): at `D = D_p + D_q` the product convolution collapses to the unique
leading×leading term. `add`/`sub` split on the degree trichotomy, the strictly
lower factor killed by `getD_beyond_degreeY_eval`.

Specialising at `D = degreeY_top p` (where `getD_{D+1} = 0`) is exactly the
Wronskian degree-drop `log_step` needs: `coeffY_D(c_D·cTD(p) − cTD(c_D)·p) = 0`.
Pure algebra + eval — no analytic axiom, no coherence. See exploration PIVOT note.
-/
namespace MachLib
namespace PfaffianLogLead
open MachLib.Real
open MachLib.MultiPolyMod MachLib.MultiPolyMod.MultiPoly
open MachLib.PfaffianChainMod MachLib.PfaffianChainMod.PfaffianFn
open MachLib.PfaffianGeneralReduce
open MachLib.IterExpTopIdentity MachLib.ChainExp2NoZeros
open MachLib.MultiPolyReconstruct

private theorem lcY_add_gt {n : Nat} (i : Fin n) (p q : MultiPoly n) (h : degreeY i q < degreeY i p) :
    leadingCoeffY i (MultiPoly.add p q) = leadingCoeffY i p := by
  show (if degreeY i p > degreeY i q then leadingCoeffY i p
        else if degreeY i q > degreeY i p then leadingCoeffY i q
        else MultiPoly.add (leadingCoeffY i p) (leadingCoeffY i q)) = leadingCoeffY i p
  rw [if_pos h]
private theorem lcY_add_lt {n : Nat} (i : Fin n) (p q : MultiPoly n) (h : degreeY i p < degreeY i q) :
    leadingCoeffY i (MultiPoly.add p q) = leadingCoeffY i q := by
  show (if degreeY i p > degreeY i q then leadingCoeffY i p
        else if degreeY i q > degreeY i p then leadingCoeffY i q
        else MultiPoly.add (leadingCoeffY i p) (leadingCoeffY i q)) = leadingCoeffY i q
  rw [if_neg (Nat.not_lt.mpr (Nat.le_of_lt h)), if_pos h]
private theorem lcY_add_eq {n : Nat} (i : Fin n) (p q : MultiPoly n) (h : degreeY i p = degreeY i q) :
    leadingCoeffY i (MultiPoly.add p q) = MultiPoly.add (leadingCoeffY i p) (leadingCoeffY i q) := by
  show (if degreeY i p > degreeY i q then leadingCoeffY i p
        else if degreeY i q > degreeY i p then leadingCoeffY i q
        else MultiPoly.add (leadingCoeffY i p) (leadingCoeffY i q)) = _
  rw [if_neg (by omega), if_neg (by omega)]
private theorem lcY_sub_gt {n : Nat} (i : Fin n) (p q : MultiPoly n) (h : degreeY i q < degreeY i p) :
    leadingCoeffY i (MultiPoly.sub p q) = leadingCoeffY i p := by
  show (if degreeY i p > degreeY i q then leadingCoeffY i p
        else if degreeY i q > degreeY i p then MultiPoly.sub (MultiPoly.const 0) (leadingCoeffY i q)
        else MultiPoly.sub (leadingCoeffY i p) (leadingCoeffY i q)) = leadingCoeffY i p
  rw [if_pos h]

/-- Log leading-coefficient identity at `(p, x, env)` — the coefficient of `cTD c p`
at the FIXED original top degree equals `cTD` of the leading coefficient. NO
correction term (log's degree-lowering shift). -/
def IdNLogLead {N : Nat} (c : PfaffianChain N) (top : Fin N) (p : MultiPoly N)
    (x : Real) (env : Fin N → Real) : Prop :=
    MultiPoly.eval ((yCoeffsAt top (chainTotalDeriv c p)).getD (MultiPoly.degreeY top p) (MultiPoly.const 0)) x env
    = MultiPoly.eval (chainTotalDeriv c (MultiPoly.leadingCoeffY top p)) x env

theorem idN_log_lead {N : Nat} (c : PfaffianChain N) (top : Fin N)
    (h_top : MultiPoly.degreeY top (c.relations top) = 0)
    (h_tri : ∀ j : Fin N, j ≠ top → MultiPoly.degreeY top (c.relations j) = 0)
    (x : Real) (env : Fin N → Real) (p : MultiPoly N) :
    IdNLogLead c top p x env := by
  have hle : ∀ r : MultiPoly N, MultiPoly.degreeY top (chainTotalDeriv c r) ≤ MultiPoly.degreeY top r :=
    fun r => degreeYtop_cTD_le_log c top h_top h_tri r
  induction p with
  | const cval =>
    show MultiPoly.eval ((yCoeffsAt top (chainTotalDeriv c (MultiPoly.const cval))).getD (MultiPoly.degreeY top (MultiPoly.const cval)) (MultiPoly.const 0)) x env
       = MultiPoly.eval (chainTotalDeriv c (MultiPoly.leadingCoeffY top (MultiPoly.const cval))) x env
    rw [cTD_const c cval]
    show MultiPoly.eval ((yCoeffsAt top (MultiPoly.const 0 : MultiPoly N)).getD 0 (MultiPoly.const 0)) x env
       = MultiPoly.eval (chainTotalDeriv c (MultiPoly.leadingCoeffY top (MultiPoly.const cval))) x env
    show MultiPoly.eval (MultiPoly.const 0 : MultiPoly N) x env
       = MultiPoly.eval (chainTotalDeriv c (MultiPoly.leadingCoeffY top (MultiPoly.const cval))) x env
    rw [show MultiPoly.leadingCoeffY top (MultiPoly.const cval : MultiPoly N) = MultiPoly.const cval from rfl, cTD_const c cval]
  | varX =>
    show MultiPoly.eval ((yCoeffsAt top (chainTotalDeriv c MultiPoly.varX)).getD (MultiPoly.degreeY top MultiPoly.varX) (MultiPoly.const 0)) x env
       = MultiPoly.eval (chainTotalDeriv c (MultiPoly.leadingCoeffY top MultiPoly.varX)) x env
    show MultiPoly.eval (MultiPoly.const 1 : MultiPoly N) x env
       = MultiPoly.eval (chainTotalDeriv c (MultiPoly.leadingCoeffY top MultiPoly.varX)) x env
    rw [show MultiPoly.leadingCoeffY top (MultiPoly.varX : MultiPoly N) = MultiPoly.varX from rfl]
    rfl
  | varY j =>
    show MultiPoly.eval ((yCoeffsAt top (chainTotalDeriv c (MultiPoly.varY j))).getD (MultiPoly.degreeY top (MultiPoly.varY j)) (MultiPoly.const 0)) x env
       = MultiPoly.eval (chainTotalDeriv c (MultiPoly.leadingCoeffY top (MultiPoly.varY j))) x env
    show MultiPoly.eval ((yCoeffsAt top (c.relations j)).getD (MultiPoly.degreeY top (MultiPoly.varY j)) (MultiPoly.const 0)) x env
       = MultiPoly.eval (chainTotalDeriv c (MultiPoly.leadingCoeffY top (MultiPoly.varY j))) x env
    by_cases hj : j = top
    · subst hj
      have hd1 : MultiPoly.degreeY j (MultiPoly.varY j) = 1 := by show (if j = j then 1 else 0) = 1; rw [if_pos rfl]
      rw [hd1, getD_beyond_degreeY_eval j (c.relations j) 1 (by rw [h_top]; exact Nat.zero_lt_one) x env,
          show MultiPoly.leadingCoeffY j (MultiPoly.varY j) = MultiPoly.const 1 from (by show (if j = j then MultiPoly.const 1 else MultiPoly.varY j) = _; rw [if_pos rfl]),
          cTD_const c 1]
      rfl
    · have hd0 : MultiPoly.degreeY top (MultiPoly.varY j) = 0 := by show (if top = j then 1 else 0) = 0; rw [if_neg (fun h => hj h.symm)]
      have hrelfree : MultiPoly.degreeY top (c.relations j) = 0 := h_tri j hj
      rw [hd0, show (0 : Nat) = MultiPoly.degreeY top (c.relations j) from hrelfree.symm,
          getD_at_degreeY_eq_lcY_eval top (c.relations j) x env,
          leadingCoeffY_eq_self_of_degreeY_zero top (c.relations j) hrelfree,
          show MultiPoly.leadingCoeffY top (MultiPoly.varY j) = MultiPoly.varY j from (by show (if j = top then MultiPoly.const 1 else MultiPoly.varY j) = _; rw [if_neg hj])]
      rfl
  | add p q ihp ihq =>
    unfold IdNLogLead at ihp ihq ⊢
    rw [cTD_add c p q]
    have hlaN := getD_listAddN_eval (yCoeffsAt top (chainTotalDeriv c p)) (yCoeffsAt top (chainTotalDeriv c q)) (MultiPoly.degreeY top (MultiPoly.add p q)) x env
    show MultiPoly.eval ((yCoeffsAt top (MultiPoly.add (chainTotalDeriv c p) (chainTotalDeriv c q))).getD (MultiPoly.degreeY top (MultiPoly.add p q)) (MultiPoly.const 0)) x env = _
    rw [show yCoeffsAt top (MultiPoly.add (chainTotalDeriv c p) (chainTotalDeriv c q)) = listAddN (yCoeffsAt top (chainTotalDeriv c p)) (yCoeffsAt top (chainTotalDeriv c q)) from rfl, hlaN]
    rcases Nat.lt_trichotomy (MultiPoly.degreeY top p) (MultiPoly.degreeY top q) with hlt | heq | hgt
    · have hd : MultiPoly.degreeY top (MultiPoly.add p q) = MultiPoly.degreeY top q := Nat.max_eq_right (Nat.le_of_lt hlt)
      rw [hd, getD_beyond_degreeY_eval top (chainTotalDeriv c p) (MultiPoly.degreeY top q) (Nat.lt_of_le_of_lt (hle p) hlt) x env, ihq, lcY_add_lt top p q hlt]
      show (0 : Real) + _ = _; rw [Real.zero_add]
    · have hd : MultiPoly.degreeY top (MultiPoly.add p q) = MultiPoly.degreeY top q := by show Nat.max _ _ = _; rw [heq]; exact Nat.max_self _
      rw [hd, ← heq, ihp, show MultiPoly.degreeY top p = MultiPoly.degreeY top q from heq, ihq, lcY_add_eq top p q heq, cTD_add c (MultiPoly.leadingCoeffY top p) (MultiPoly.leadingCoeffY top q), MultiPoly.eval_add]
    · have hd : MultiPoly.degreeY top (MultiPoly.add p q) = MultiPoly.degreeY top p := Nat.max_eq_left (Nat.le_of_lt hgt)
      rw [hd, getD_beyond_degreeY_eval top (chainTotalDeriv c q) (MultiPoly.degreeY top p) (Nat.lt_of_le_of_lt (hle q) hgt) x env, ihp, lcY_add_gt top p q hgt]
      show _ + (0 : Real) = _; rw [Real.add_zero]
  | sub p q ihp ihq =>
    unfold IdNLogLead at ihp ihq ⊢
    rw [cTD_sub c p q]
    have hlsN := getD_listSubN_eval (yCoeffsAt top (chainTotalDeriv c p)) (yCoeffsAt top (chainTotalDeriv c q)) (MultiPoly.degreeY top (MultiPoly.sub p q)) x env
    show MultiPoly.eval ((yCoeffsAt top (MultiPoly.sub (chainTotalDeriv c p) (chainTotalDeriv c q))).getD (MultiPoly.degreeY top (MultiPoly.sub p q)) (MultiPoly.const 0)) x env = _
    rw [show yCoeffsAt top (MultiPoly.sub (chainTotalDeriv c p) (chainTotalDeriv c q)) = listSubN (yCoeffsAt top (chainTotalDeriv c p)) (yCoeffsAt top (chainTotalDeriv c q)) from rfl, hlsN]
    rcases Nat.lt_trichotomy (MultiPoly.degreeY top p) (MultiPoly.degreeY top q) with hlt | heq | hgt
    · have hd : MultiPoly.degreeY top (MultiPoly.sub p q) = MultiPoly.degreeY top q := Nat.max_eq_right (Nat.le_of_lt hlt)
      rw [hd, getD_beyond_degreeY_eval top (chainTotalDeriv c p) (MultiPoly.degreeY top q) (Nat.lt_of_le_of_lt (hle p) hlt) x env, ihq, leadingCoeffY_sub_of_lt top p q hlt, cTD_sub_const0 c (MultiPoly.leadingCoeffY top q), MultiPoly.eval_sub]
      show (0:Real) - _ = MultiPoly.eval (MultiPoly.const 0) x env - _; rw [MultiPoly.eval_const]
    · have hd : MultiPoly.degreeY top (MultiPoly.sub p q) = MultiPoly.degreeY top q := by show Nat.max _ _ = _; rw [heq]; exact Nat.max_self _
      rw [hd, ← heq, ihp, show MultiPoly.degreeY top p = MultiPoly.degreeY top q from heq, ihq, leadingCoeffY_sub_of_eq top p q heq, cTD_sub c (MultiPoly.leadingCoeffY top p) (MultiPoly.leadingCoeffY top q), MultiPoly.eval_sub]
    · have hd : MultiPoly.degreeY top (MultiPoly.sub p q) = MultiPoly.degreeY top p := Nat.max_eq_left (Nat.le_of_lt hgt)
      rw [hd, getD_beyond_degreeY_eval top (chainTotalDeriv c q) (MultiPoly.degreeY top p) (Nat.lt_of_le_of_lt (hle q) hgt) x env, ihp, lcY_sub_gt top p q hgt]
      show _ - (0 : Real) = _; rw [Real.sub_zero]
  | mul p q ihp ihq =>
    unfold IdNLogLead at ihp ihq ⊢
    rw [cTD_mul c p q]
    show MultiPoly.eval ((yCoeffsAt top (MultiPoly.add (MultiPoly.mul (chainTotalDeriv c p) q) (MultiPoly.mul p (chainTotalDeriv c q)))).getD (MultiPoly.degreeY top (MultiPoly.mul p q)) (MultiPoly.const 0)) x env = _
    rw [show yCoeffsAt top (MultiPoly.add (MultiPoly.mul (chainTotalDeriv c p) q) (MultiPoly.mul p (chainTotalDeriv c q))) = listAddN (yCoeffsAt top (MultiPoly.mul (chainTotalDeriv c p) q)) (yCoeffsAt top (MultiPoly.mul p (chainTotalDeriv c q))) from rfl,
        getD_listAddN_eval (yCoeffsAt top (MultiPoly.mul (chainTotalDeriv c p) q)) (yCoeffsAt top (MultiPoly.mul p (chainTotalDeriv c q))) (MultiPoly.degreeY top (MultiPoly.mul p q)) x env,
        show MultiPoly.degreeY top (MultiPoly.mul p q) = MultiPoly.degreeY top p + MultiPoly.degreeY top q from rfl]
    -- first product: getD_{Dp+Dq}(yCoeffs(mul (cTD p) q)) = getD_{Dp}(yCoeffs(cTD p)) * lcY q
    rw [show yCoeffsAt top (MultiPoly.mul (chainTotalDeriv c p) q) = listMulN (yCoeffsAt top (chainTotalDeriv c p)) (yCoeffsAt top q) from rfl,
        getD_mul_split_eval (yCoeffsAt top (chainTotalDeriv c p)) (yCoeffsAt top q) (MultiPoly.degreeY top p) (MultiPoly.degreeY top q)
          (by rw [yCoeffsAt_length_eq]; exact Nat.add_le_add_right (hle p) 1)
          (Nat.le_of_eq (yCoeffsAt_length_eq top q)) x env,
        show yCoeffsAt top (MultiPoly.mul p (chainTotalDeriv c q)) = listMulN (yCoeffsAt top p) (yCoeffsAt top (chainTotalDeriv c q)) from rfl,
        getD_mul_split_eval (yCoeffsAt top p) (yCoeffsAt top (chainTotalDeriv c q)) (MultiPoly.degreeY top p) (MultiPoly.degreeY top q)
          (Nat.le_of_eq (yCoeffsAt_length_eq top p)) (by rw [yCoeffsAt_length_eq]; exact Nat.add_le_add_right (hle q) 1) x env,
        ihp, getD_at_degreeY_eq_lcY_eval top q x env,
        getD_at_degreeY_eq_lcY_eval top p x env, ihq,
        show MultiPoly.leadingCoeffY top (MultiPoly.mul p q) = MultiPoly.mul (MultiPoly.leadingCoeffY top p) (MultiPoly.leadingCoeffY top q) from rfl,
        cTD_mul c (MultiPoly.leadingCoeffY top p) (MultiPoly.leadingCoeffY top q), MultiPoly.eval_add, MultiPoly.eval_mul, MultiPoly.eval_mul]
    mach_ring

/-! ## Wronskian leading-coefficient cancellation (the degree-drop) -/

/-- Top-free scalar `s` (`degreeY top s = 0`) pulls through fixed-degree coefficient
extraction at any index `d ≥ degreeY_top q` (eval). Instance of `getD_mul_split_eval`
at `m = 0` (`yCoeffsAt` of a top-free poly is length 1). -/
theorem getD_scalar_topfree_eval {N : Nat} (top : Fin N) (s q : MultiPoly N)
    (hs : MultiPoly.degreeY top s = 0) (d : Nat) (hq : MultiPoly.degreeY top q ≤ d)
    (x : Real) (env : Fin N → Real) :
    MultiPoly.eval ((yCoeffsAt top (MultiPoly.mul s q)).getD d (MultiPoly.const 0)) x env
      = MultiPoly.eval s x env
        * MultiPoly.eval ((yCoeffsAt top q).getD d (MultiPoly.const 0)) x env := by
  have hsplit := getD_mul_split_eval (yCoeffsAt top s) (yCoeffsAt top q) 0 d
    (Nat.le_of_eq (by rw [yCoeffsAt_length_eq, hs]))
    (by rw [yCoeffsAt_length_eq]; exact Nat.add_le_add_right hq 1) x env
  rw [Nat.zero_add] at hsplit
  rw [show yCoeffsAt top (MultiPoly.mul s q) = listMulN (yCoeffsAt top s) (yCoeffsAt top q) from rfl, hsplit]
  have h0 : MultiPoly.eval ((yCoeffsAt top s).getD 0 (MultiPoly.const 0)) x env = MultiPoly.eval s x env := by
    rw [show (0 : Nat) = MultiPoly.degreeY top s from hs.symm, getD_at_degreeY_eq_lcY_eval top s x env,
        leadingCoeffY_eq_self_of_degreeY_zero top s hs]
  rw [h0]

/-- **Wronskian leading coefficient vanishes (eval).** For a LOG top, the degree-`D`
coefficient (`D = degreeY_top p`) of
`g = c_D·cTD(p) − cTD(c_D)·p`  (`c_D = leadingCoeffY top p`)
is eval-zero: the leading terms cancel because `coeffY_D(cTD p) = cTD(c_D)` at eval
(`idN_log_lead`) and `coeffY_D(p) = c_D`. So `g`'s canonical top degree is `< D` — the
degree-drop the log Wronskian reducer rests on (feeds the eval-aware WF measure). The
two scalar factors `c_D` and `cTD(c_D)` are top-free (`degreeYtop_cTD_le_log`), so they
pull through `getD_D` via `getD_scalar_topfree_eval`. -/
theorem wronskian_leadY_eval_zero {N : Nat} (c : PfaffianChain N) (top : Fin N)
    (h_top : MultiPoly.degreeY top (c.relations top) = 0)
    (h_tri : ∀ j : Fin N, j ≠ top → MultiPoly.degreeY top (c.relations j) = 0)
    (p : MultiPoly N) (x : Real) (env : Fin N → Real) :
    MultiPoly.eval ((yCoeffsAt top
        (MultiPoly.sub (MultiPoly.mul (MultiPoly.leadingCoeffY top p) (chainTotalDeriv c p))
                       (MultiPoly.mul (chainTotalDeriv c (MultiPoly.leadingCoeffY top p)) p))).getD
        (MultiPoly.degreeY top p) (MultiPoly.const 0)) x env = 0 := by
  have hcD : MultiPoly.degreeY top (MultiPoly.leadingCoeffY top p) = 0 := MultiPoly.degreeY_leadingCoeffY top p
  have hcTDcD : MultiPoly.degreeY top (chainTotalDeriv c (MultiPoly.leadingCoeffY top p)) = 0 := by
    have := degreeYtop_cTD_le_log c top h_top h_tri (MultiPoly.leadingCoeffY top p)
    rw [hcD] at this; exact Nat.le_zero.mp this
  rw [show yCoeffsAt top (MultiPoly.sub (MultiPoly.mul (MultiPoly.leadingCoeffY top p) (chainTotalDeriv c p)) (MultiPoly.mul (chainTotalDeriv c (MultiPoly.leadingCoeffY top p)) p))
        = listSubN (yCoeffsAt top (MultiPoly.mul (MultiPoly.leadingCoeffY top p) (chainTotalDeriv c p))) (yCoeffsAt top (MultiPoly.mul (chainTotalDeriv c (MultiPoly.leadingCoeffY top p)) p)) from rfl,
      getD_listSubN_eval,
      getD_scalar_topfree_eval top (MultiPoly.leadingCoeffY top p) (chainTotalDeriv c p) hcD (MultiPoly.degreeY top p) (degreeYtop_cTD_le_log c top h_top h_tri p) x env,
      getD_scalar_topfree_eval top (chainTotalDeriv c (MultiPoly.leadingCoeffY top p)) p hcTDcD (MultiPoly.degreeY top p) (Nat.le_refl _) x env,
      idN_log_lead c top h_top h_tri x env p,
      getD_at_degreeY_eq_lcY_eval top p x env]
  mach_ring

/-- **Wronskian top-degree bound.** `degreeY_top g ≤ degreeY_top p` for the log
Wronskian `g = c_D·cTD(p) − cTD(c_D)·p` (`c_D = leadingCoeffY top p`). Both scalar
factors are top-free (`degreeY_leadingCoeffY` + `degreeYtop_cTD_le_log`), so
`degreeY_top g = max(degreeY_top(cTD p), degreeY_top p) ≤ degreeY_top p`. With
`wronskian_leadY_eval_zero` (`coeffY_D g` eval-zero), this gives the log WF descent's
degree-drop: `g` has canonical top degree `< D` (drop its eval-zero degree-`D` term). -/
theorem degreeYtop_wronskian_le {N : Nat} (c : PfaffianChain N) (top : Fin N)
    (h_top : MultiPoly.degreeY top (c.relations top) = 0)
    (h_tri : ∀ j : Fin N, j ≠ top → MultiPoly.degreeY top (c.relations j) = 0)
    (p : MultiPoly N) :
    MultiPoly.degreeY top (MultiPoly.sub
        (MultiPoly.mul (MultiPoly.leadingCoeffY top p) (chainTotalDeriv c p))
        (MultiPoly.mul (chainTotalDeriv c (MultiPoly.leadingCoeffY top p)) p))
      ≤ MultiPoly.degreeY top p := by
  have hcD0 : MultiPoly.degreeY top (MultiPoly.leadingCoeffY top p) = 0 := MultiPoly.degreeY_leadingCoeffY top p
  have hcTDcD0 : MultiPoly.degreeY top (chainTotalDeriv c (MultiPoly.leadingCoeffY top p)) = 0 := by
    have h := degreeYtop_cTD_le_log c top h_top h_tri (MultiPoly.leadingCoeffY top p)
    rw [hcD0] at h; exact Nat.le_zero.mp h
  have hcTDp : MultiPoly.degreeY top (chainTotalDeriv c p) ≤ MultiPoly.degreeY top p :=
    degreeYtop_cTD_le_log c top h_top h_tri p
  show Nat.max (MultiPoly.degreeY top (MultiPoly.leadingCoeffY top p) + MultiPoly.degreeY top (chainTotalDeriv c p))
               (MultiPoly.degreeY top (chainTotalDeriv c (MultiPoly.leadingCoeffY top p)) + MultiPoly.degreeY top p)
      ≤ MultiPoly.degreeY top p
  rw [hcD0, hcTDcD0, Nat.zero_add, Nat.zero_add]
  exact Nat.max_le.mpr ⟨hcTDp, Nat.le_refl _⟩

end PfaffianLogLead
end MachLib
