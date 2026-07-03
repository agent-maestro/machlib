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
open MachLib.IterExpTopIdentity
open MachLib.ChainExp2NoZeros
open MachLib.ChainExp2CanonMeasure

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

/-! ## Descent core: the leading-coefficient identity ("lemma 1") for exponential-type chains -/

private theorem lcY_add_of_gt' {n : Nat} (i : Fin n) (p q : MultiPoly n)
    (h : MultiPoly.degreeY i q < MultiPoly.degreeY i p) :
    MultiPoly.leadingCoeffY i (MultiPoly.add p q) = MultiPoly.leadingCoeffY i p := by
  show (if MultiPoly.degreeY i p > MultiPoly.degreeY i q then MultiPoly.leadingCoeffY i p
        else if MultiPoly.degreeY i q > MultiPoly.degreeY i p then MultiPoly.leadingCoeffY i q
        else MultiPoly.add (MultiPoly.leadingCoeffY i p) (MultiPoly.leadingCoeffY i q))
       = MultiPoly.leadingCoeffY i p
  rw [if_pos h]

private theorem lcY_add_of_lt' {n : Nat} (i : Fin n) (p q : MultiPoly n)
    (h : MultiPoly.degreeY i p < MultiPoly.degreeY i q) :
    MultiPoly.leadingCoeffY i (MultiPoly.add p q) = MultiPoly.leadingCoeffY i q := by
  show (if MultiPoly.degreeY i p > MultiPoly.degreeY i q then MultiPoly.leadingCoeffY i p
        else if MultiPoly.degreeY i q > MultiPoly.degreeY i p then MultiPoly.leadingCoeffY i q
        else MultiPoly.add (MultiPoly.leadingCoeffY i p) (MultiPoly.leadingCoeffY i q))
       = MultiPoly.leadingCoeffY i q
  rw [if_neg (Nat.not_lt.mpr (Nat.le_of_lt h)), if_pos h]

private theorem lcY_add_of_eq' {n : Nat} (i : Fin n) (p q : MultiPoly n)
    (h : MultiPoly.degreeY i p = MultiPoly.degreeY i q) :
    MultiPoly.leadingCoeffY i (MultiPoly.add p q)
      = MultiPoly.add (MultiPoly.leadingCoeffY i p) (MultiPoly.leadingCoeffY i q) := by
  show (if MultiPoly.degreeY i p > MultiPoly.degreeY i q then MultiPoly.leadingCoeffY i p
        else if MultiPoly.degreeY i q > MultiPoly.degreeY i p then MultiPoly.leadingCoeffY i q
        else MultiPoly.add (MultiPoly.leadingCoeffY i p) (MultiPoly.leadingCoeffY i q))
       = MultiPoly.add (MultiPoly.leadingCoeffY i p) (MultiPoly.leadingCoeffY i q)
  rw [if_neg (by omega : ¬ MultiPoly.degreeY i p > MultiPoly.degreeY i q),
      if_neg (by omega : ¬ MultiPoly.degreeY i q > MultiPoly.degreeY i p)]

def IdNGen {N : Nat} (c : PfaffianChain N) (G : MultiPoly N) (top : Fin N)
    (p : MultiPoly N) (x : Real) (env : Fin N → Real) : Prop :=
    MultiPoly.eval (MultiPoly.leadingCoeffY top (chainTotalDeriv c p)) x env
    = MultiPoly.eval (chainTotalDeriv c (MultiPoly.leadingCoeffY top p)) x env
      + MachLib.Real.natCast (MultiPoly.degreeY top p)
        * MultiPoly.eval (MultiPoly.mul G (MultiPoly.leadingCoeffY top p)) x env

set_option maxHeartbeats 1200000 in
theorem idN_add_gen {N : Nat} (c : PfaffianChain N) (G : MultiPoly N) (top : Fin N)
    (h_top : MultiPoly.degreeY top (c.relations top) = 1)
    (h_tri : ∀ j : Fin N, j ≠ top → MultiPoly.degreeY top (c.relations j) = 0)
    (p q : MultiPoly N) (x : Real) (env : Fin N → Real)
    (ihp : IdNGen c G top p x env) (ihq : IdNGen c G top q x env) :
    IdNGen c G top (MultiPoly.add p q) x env := by
  unfold IdNGen at ihp ihq ⊢
  have hp_eq := degreeYtop_cTD_eq_gen c top h_top h_tri p
  have hq_eq := degreeYtop_cTD_eq_gen c top h_top h_tri q
  rw [cTD_add c p q]
  rcases Nat.lt_trichotomy (MultiPoly.degreeY top p) (MultiPoly.degreeY top q) with hlt | heq | hgt
  · have hd : MultiPoly.degreeY top (MultiPoly.add p q) = MultiPoly.degreeY top q :=
      Nat.max_eq_right (Nat.le_of_lt hlt)
    rw [lcY_add_of_lt' top (chainTotalDeriv c p) (chainTotalDeriv c q) (by rw [hp_eq, hq_eq]; exact hlt),
        lcY_add_of_lt' top p q hlt, hd]
    exact ihq
  · have hd : MultiPoly.degreeY top (MultiPoly.add p q) = MultiPoly.degreeY top q := by
      show Nat.max _ _ = _; rw [heq]; exact Nat.max_self _
    rw [lcY_add_of_eq' top (chainTotalDeriv c p) (chainTotalDeriv c q) (by rw [hp_eq, hq_eq]; exact heq),
        lcY_add_of_eq' top p q heq, hd,
        cTD_add c (MultiPoly.leadingCoeffY top p) (MultiPoly.leadingCoeffY top q)]
    simp only [MultiPoly.eval_add, MultiPoly.eval_mul] at ihp ihq ⊢
    rw [heq] at ihp
    rw [ihp, ihq]; mach_ring
  · have hd : MultiPoly.degreeY top (MultiPoly.add p q) = MultiPoly.degreeY top p :=
      Nat.max_eq_left (Nat.le_of_lt hgt)
    rw [lcY_add_of_gt' top (chainTotalDeriv c p) (chainTotalDeriv c q) (by rw [hp_eq, hq_eq]; exact hgt),
        lcY_add_of_gt' top p q hgt, hd]
    exact ihp



private theorem lcY_sub_of_gt' {n : Nat} (i : Fin n) (p q : MultiPoly n)
    (h : MultiPoly.degreeY i q < MultiPoly.degreeY i p) :
    MultiPoly.leadingCoeffY i (MultiPoly.sub p q) = MultiPoly.leadingCoeffY i p := by
  show (if MultiPoly.degreeY i p > MultiPoly.degreeY i q then MultiPoly.leadingCoeffY i p
        else if MultiPoly.degreeY i q > MultiPoly.degreeY i p
             then MultiPoly.sub (MultiPoly.const 0) (MultiPoly.leadingCoeffY i q)
             else MultiPoly.sub (MultiPoly.leadingCoeffY i p) (MultiPoly.leadingCoeffY i q))
       = MultiPoly.leadingCoeffY i p
  rw [if_pos h]

private theorem lcY_varY_self' {n : Nat} (i : Fin n) :
    MultiPoly.leadingCoeffY i (MultiPoly.varY i) = MultiPoly.const 1 := by
  show (if i = i then MultiPoly.const 1 else MultiPoly.varY i) = MultiPoly.const 1
  rw [if_pos rfl]

private theorem degreeY_varY_self' {n : Nat} (i : Fin n) :
    MultiPoly.degreeY i (MultiPoly.varY i) = 1 := by
  show (if i = i then 1 else 0) = 1
  rw [if_pos rfl]

private theorem natCast_add_gen (a b : Nat) :
    MachLib.Real.natCast (a + b) = MachLib.Real.natCast a + MachLib.Real.natCast b := by
  induction b with
  | zero => rw [Nat.add_zero, MachLib.Real.natCast_zero, MachLib.Real.add_zero]
  | succ n ih =>
    rw [show a + (n + 1) = (a + n) + 1 from rfl, MachLib.Real.natCast_succ,
        MachLib.Real.natCast_succ, ih, MachLib.Real.add_assoc]

set_option maxHeartbeats 1200000 in
theorem idN_sub_gen {N : Nat} (c : PfaffianChain N) (G : MultiPoly N) (top : Fin N)
    (h_top : MultiPoly.degreeY top (c.relations top) = 1)
    (h_tri : ∀ j : Fin N, j ≠ top → MultiPoly.degreeY top (c.relations j) = 0)
    (p q : MultiPoly N) (x : Real) (env : Fin N → Real)
    (ihp : IdNGen c G top p x env) (ihq : IdNGen c G top q x env) :
    IdNGen c G top (MultiPoly.sub p q) x env := by
  unfold IdNGen at ihp ihq ⊢
  have hp_eq := degreeYtop_cTD_eq_gen c top h_top h_tri p
  have hq_eq := degreeYtop_cTD_eq_gen c top h_top h_tri q
  rw [cTD_sub c p q]
  rcases Nat.lt_trichotomy (MultiPoly.degreeY top p) (MultiPoly.degreeY top q) with hlt | heq | hgt
  · have hd : MultiPoly.degreeY top (MultiPoly.sub p q) = MultiPoly.degreeY top q :=
      Nat.max_eq_right (Nat.le_of_lt hlt)
    rw [MultiPoly.leadingCoeffY_sub_of_lt top (chainTotalDeriv c p) (chainTotalDeriv c q)
          (by rw [hp_eq, hq_eq]; exact hlt),
        MultiPoly.leadingCoeffY_sub_of_lt top p q hlt, hd,
        cTD_sub_const0 c (MultiPoly.leadingCoeffY top q)]
    simp only [MultiPoly.eval_sub, MultiPoly.eval_mul, MultiPoly.eval_add, MultiPoly.eval_const]
      at ihp ihq ⊢
    rw [ihq]; mach_ring
  · have hd : MultiPoly.degreeY top (MultiPoly.sub p q) = MultiPoly.degreeY top q := by
      show Nat.max _ _ = _; rw [heq]; exact Nat.max_self _
    rw [MultiPoly.leadingCoeffY_sub_of_eq top (chainTotalDeriv c p) (chainTotalDeriv c q)
          (by rw [hp_eq, hq_eq]; exact heq),
        MultiPoly.leadingCoeffY_sub_of_eq top p q heq, hd,
        cTD_sub c (MultiPoly.leadingCoeffY top p) (MultiPoly.leadingCoeffY top q)]
    simp only [MultiPoly.eval_sub, MultiPoly.eval_mul, MultiPoly.eval_add] at ihp ihq ⊢
    rw [heq] at ihp
    rw [ihp, ihq]
    generalize MultiPoly.eval (chainTotalDeriv c (MultiPoly.leadingCoeffY top p)) x env = A
    generalize MultiPoly.eval (chainTotalDeriv c (MultiPoly.leadingCoeffY top q)) x env = B
    generalize MultiPoly.eval G x env = Y
    generalize MultiPoly.eval (MultiPoly.leadingCoeffY top p) x env = LP
    generalize MultiPoly.eval (MultiPoly.leadingCoeffY top q) x env = LQ
    generalize MachLib.Real.natCast (MultiPoly.degreeY top q) = Nq
    mach_ring
  · have hd : MultiPoly.degreeY top (MultiPoly.sub p q) = MultiPoly.degreeY top p :=
      Nat.max_eq_left (Nat.le_of_lt hgt)
    rw [lcY_sub_of_gt' top (chainTotalDeriv c p) (chainTotalDeriv c q)
          (by rw [hp_eq, hq_eq]; exact hgt),
        lcY_sub_of_gt' top p q hgt, hd]
    exact ihp

set_option maxHeartbeats 1200000 in
theorem idN_mul_gen {N : Nat} (c : PfaffianChain N) (G : MultiPoly N) (top : Fin N)
    (h_top : MultiPoly.degreeY top (c.relations top) = 1)
    (h_tri : ∀ j : Fin N, j ≠ top → MultiPoly.degreeY top (c.relations j) = 0)
    (p q : MultiPoly N) (x : Real) (env : Fin N → Real)
    (ihp : IdNGen c G top p x env) (ihq : IdNGen c G top q x env) :
    IdNGen c G top (MultiPoly.mul p q) x env := by
  unfold IdNGen at ihp ihq ⊢
  have ha_eq := degreeYtop_cTD_eq_gen c top h_top h_tri p
  have hb_eq := degreeYtop_cTD_eq_gen c top h_top h_tri q
  rw [cTD_mul c p q]
  have hcond : MultiPoly.degreeY top (MultiPoly.mul (chainTotalDeriv c p) q)
             = MultiPoly.degreeY top (MultiPoly.mul p (chainTotalDeriv c q)) := by
    rw [degreeY_mul' top (chainTotalDeriv c p) q,
        degreeY_mul' top p (chainTotalDeriv c q), ha_eq, hb_eq]
  rw [lcY_add_of_eq' top
        (MultiPoly.mul (chainTotalDeriv c p) q)
        (MultiPoly.mul p (chainTotalDeriv c q)) hcond,
      lcY_mul top (chainTotalDeriv c p) q,
      lcY_mul top p (chainTotalDeriv c q),
      lcY_mul top p q,
      degreeY_mul' top p q,
      natCast_add_gen (MultiPoly.degreeY top p) (MultiPoly.degreeY top q),
      cTD_mul c (MultiPoly.leadingCoeffY top p) (MultiPoly.leadingCoeffY top q)]
  simp only [MultiPoly.eval_add, MultiPoly.eval_mul] at ihp ihq ⊢
  rw [ihp, ihq]
  generalize MultiPoly.eval (chainTotalDeriv c (MultiPoly.leadingCoeffY top p)) x env = A
  generalize MultiPoly.eval (chainTotalDeriv c (MultiPoly.leadingCoeffY top q)) x env = B
  generalize MultiPoly.eval G x env = Y
  generalize MultiPoly.eval (MultiPoly.leadingCoeffY top p) x env = LA
  generalize MultiPoly.eval (MultiPoly.leadingCoeffY top q) x env = LB
  generalize MachLib.Real.natCast (MultiPoly.degreeY top p) = Na
  generalize MachLib.Real.natCast (MultiPoly.degreeY top q) = Nb
  mach_ring

set_option maxHeartbeats 1200000 in
theorem idN_general_gen {N : Nat} (c : PfaffianChain N) (G : MultiPoly N) (top : Fin N)
    (h_reltop : c.relations top = MultiPoly.mul G (MultiPoly.varY top))
    (h_Gtop : MultiPoly.degreeY top G = 0)
    (h_tri : ∀ j : Fin N, j ≠ top → MultiPoly.degreeY top (c.relations j) = 0)
    (p : MultiPoly N) (x : Real) (env : Fin N → Real) : IdNGen c G top p x env := by
  have h_top : MultiPoly.degreeY top (c.relations top) = 1 := by
    rw [h_reltop, degreeY_mul' top G (MultiPoly.varY top), h_Gtop, degreeY_varY_self' top]
  induction p with
  | const cval =>
    unfold IdNGen
    rw [cTD_const c cval]
    show MultiPoly.eval (MultiPoly.const 0) x env
        = MultiPoly.eval (chainTotalDeriv c (MultiPoly.const cval)) x env
          + MachLib.Real.natCast 0
            * MultiPoly.eval (MultiPoly.mul G (MultiPoly.const cval)) x env
    rw [cTD_const c cval, MachLib.Real.natCast_zero, MultiPoly.eval_const]
    mach_ring
  | varX =>
    unfold IdNGen
    show MultiPoly.eval (MultiPoly.const 1) x env
        = MultiPoly.eval (chainTotalDeriv c MultiPoly.varX) x env
          + MachLib.Real.natCast 0
            * MultiPoly.eval (MultiPoly.mul G MultiPoly.varX) x env
    rw [MachLib.Real.natCast_zero, MultiPoly.eval_const]
    show (1 : Real)
        = MultiPoly.eval (MultiPoly.const 1) x env
          + 0 * MultiPoly.eval (MultiPoly.mul G MultiPoly.varX) x env
    rw [MultiPoly.eval_const]; mach_ring
  | varY j =>
    by_cases hj : j = top
    · rw [hj]
      unfold IdNGen
      have hcv : chainTotalDeriv c (MultiPoly.varY top) = MultiPoly.mul G (MultiPoly.varY top) :=
        h_reltop
      rw [hcv, lcY_mul top G (MultiPoly.varY top),
          leadingCoeffY_eq_self_of_degreeY_zero top G h_Gtop,
          lcY_varY_self' top, degreeY_varY_self' top, cTD_const c 1,
          MachLib.Real.natCast_succ, MachLib.Real.natCast_zero]
      simp only [MultiPoly.eval_mul, MultiPoly.eval_const]
      generalize MultiPoly.eval G x env = Y
      mach_ring
    · unfold IdNGen
      have hcv : chainTotalDeriv c (MultiPoly.varY j) = c.relations j := rfl
      have hdrel : MultiPoly.degreeY top (c.relations j) = 0 := h_tri j hj
      have hdj : MultiPoly.degreeY top (MultiPoly.varY j) = 0 := by
        show (if top = j then 1 else 0) = 0
        rw [if_neg (fun h => hj h.symm)]
      rw [hcv, leadingCoeffY_eq_self_of_degreeY_zero top (c.relations j) hdrel, hdj,
          MachLib.Real.natCast_zero,
          leadingCoeffY_eq_self_of_degreeY_zero top (MultiPoly.varY j) hdj, hcv]
      generalize MultiPoly.eval (c.relations j) x env = P
      mach_ring
  | add p q ihp ihq => exact idN_add_gen c G top h_top h_tri p q x env ihp ihq
  | sub p q ihp ihq => exact idN_sub_gen c G top h_top h_tri p q x env ihp ihq
  | mul p q ihp ihq => exact idN_mul_gen c G top h_top h_tri p q x env ihp ihq

/-- **Frontier-1 lemma (1), generalized to exponential-type Pfaffian chains.** For any chain `c` whose
top relation is `relations top = G · y_top` with `G` top-free, and triangular below, the leading
`y_top`-coefficient of `chainTotalDeriv c p` decomposes as `cTD(lcY_top p) + degreeY_top·G·lcY_top p`. -/
theorem leadingCoeffYtop_cTD_eval_gen {N : Nat} (c : PfaffianChain N) (G : MultiPoly N) (top : Fin N)
    (h_reltop : c.relations top = MultiPoly.mul G (MultiPoly.varY top))
    (h_Gtop : MultiPoly.degreeY top G = 0)
    (h_tri : ∀ j : Fin N, j ≠ top → MultiPoly.degreeY top (c.relations j) = 0)
    (p : MultiPoly N) (x : Real) (env : Fin N → Real) :
    MultiPoly.eval (MultiPoly.leadingCoeffY top (chainTotalDeriv c p)) x env
    = MultiPoly.eval (chainTotalDeriv c (MultiPoly.leadingCoeffY top p)) x env
      + MachLib.Real.natCast (MultiPoly.degreeY top p)
        * MultiPoly.eval (MultiPoly.mul G (MultiPoly.leadingCoeffY top p)) x env :=
  idN_general_gen c G top h_reltop h_Gtop h_tri p x env

/-! ## The reduce's leading coefficient — depth-`N`→`(N-1)` seam, for exp-type chains

`chainReduce c m p = chainTotalDeriv c p − m·p`. Its leading `y_top`-coefficient, evaluated, is the
depth-`(N-1)` reduce of `lcY_top p`: the leading-coeff identity injects a `degreeY_top · G · lcY_top p`
term, and a graded multiplier `m` whose top term is `(degreeY_top p)·G` will cancel it (that cancellation
is the measure descent, the remaining piece). Here we just expose the formula. -/
theorem chainReduce_lcY_top_eval {N : Nat} (c : PfaffianChain N) (G : MultiPoly N) (top : Fin N)
    (h_reltop : c.relations top = MultiPoly.mul G (MultiPoly.varY top))
    (h_Gtop : MultiPoly.degreeY top G = 0)
    (h_tri : ∀ j : Fin N, j ≠ top → MultiPoly.degreeY top (c.relations j) = 0)
    (m p : MultiPoly N) (hm : MultiPoly.degreeY top m = 0) (x : Real) (env : Fin N → Real) :
    MultiPoly.eval (MultiPoly.leadingCoeffY top (chainReduce c m p)) x env
    = MultiPoly.eval (chainTotalDeriv c (MultiPoly.leadingCoeffY top p)) x env
      + MachLib.Real.natCast (MultiPoly.degreeY top p)
        * (MultiPoly.eval G x env * MultiPoly.eval (MultiPoly.leadingCoeffY top p) x env)
      - MultiPoly.eval m x env * MultiPoly.eval (MultiPoly.leadingCoeffY top p) x env := by
  have h_top : MultiPoly.degreeY top (c.relations top) = 1 := by
    rw [h_reltop, degreeY_mul' top G (MultiPoly.varY top), h_Gtop, degreeY_varY_self' top]
  have h1 := leadingCoeffYtop_cTD_eval_gen c G top h_reltop h_Gtop h_tri p x env
  simp only [MultiPoly.eval_mul] at h1
  unfold chainReduce
  rw [MultiPoly.leadingCoeffY_sub_of_eq top (chainTotalDeriv c p) (MultiPoly.mul m p)
        (by rw [degreeYtop_cTD_eq_gen c top h_top h_tri p, degreeY_mul' top m p, hm, Nat.zero_add]),
      lcY_mul top m p, leadingCoeffY_eq_self_of_degreeY_zero top m hm]
  simp only [MultiPoly.eval_sub, MultiPoly.eval_mul]
  rw [h1]; mach_ring

/-- **The descent cancellation step (exp-type chains).** If the reduce multiplier `m` decomposes, along
the chain, as `m = (degreeY_top p)·G + m'` (its top part cancels the leading-coefficient injection), then
the leading `y_top`-coefficient of `chainReduce c m p` evaluates to the depth-`(N-1)` reduce residual of
`lcY_top p` with the *lower* multiplier `m'`: `cTD(lcY_top p) − m'·lcY_top p`. This is the atomic step of
the recursive measure descent — the graded multiplier (the remaining construction) is exactly the `m`
that supplies `hcancel`, recursively. -/
theorem chainReduce_lcY_top_cancel {N : Nat} (c : PfaffianChain N) (G : MultiPoly N) (top : Fin N)
    (h_reltop : c.relations top = MultiPoly.mul G (MultiPoly.varY top))
    (h_Gtop : MultiPoly.degreeY top G = 0)
    (h_tri : ∀ j : Fin N, j ≠ top → MultiPoly.degreeY top (c.relations j) = 0)
    (m m' p : MultiPoly N) (hm : MultiPoly.degreeY top m = 0) (x : Real) (env : Fin N → Real)
    (hcancel : MultiPoly.eval m x env
        = MachLib.Real.natCast (MultiPoly.degreeY top p) * MultiPoly.eval G x env
          + MultiPoly.eval m' x env) :
    MultiPoly.eval (MultiPoly.leadingCoeffY top (chainReduce c m p)) x env
    = MultiPoly.eval (chainTotalDeriv c (MultiPoly.leadingCoeffY top p)) x env
      - MultiPoly.eval m' x env * MultiPoly.eval (MultiPoly.leadingCoeffY top p) x env := by
  rw [chainReduce_lcY_top_eval c G top h_reltop h_Gtop h_tri m p hm, hcancel]
  mach_ring

/-! ## Chain restriction — the sub-chain on the first `N` of `N+1` variables

The measure descent recurses from depth `N+1` to depth `N`: the leading `y_top`-coefficient of a reduce
lives on the *sub-chain* obtained by dropping the top variable. `chainRestrict c` is that sub-chain — its
`evals` are the first `N` of `c`'s, and its `relations` are `c`'s first `N` relations projected by
`dropLastY` (well-defined because triangularity makes them top-free). The key bridge is that evaluating a
top-free polynomial along `c` equals evaluating its `dropLastY` along `chainRestrict c`. -/
noncomputable def chainRestrict {N : Nat} (c : PfaffianChain (N + 1)) : PfaffianChain N :=
  { evals := fun i => c.evals ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩,
    relations := fun i => MultiPoly.dropLastY (c.relations ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) }

/-- The restricted chain's values are the first `N` of the full chain's (definitionally). -/
theorem chainRestrict_chainValues {N : Nat} (c : PfaffianChain (N + 1)) (z : Real) (i : Fin N) :
    (chainRestrict c).chainValues z i = (c.chainValues z) ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ := rfl

/-- **The chain-restriction eval bridge.** A top-free polynomial `q` evaluated along `c` equals
`dropLastY q` evaluated along the sub-chain `chainRestrict c`. This is the depth-`(N+1)`→depth-`N`
projection the measure descent recurses on (general analog of `dropLastY_eval_IterExp`). -/
theorem dropLastY_eval_chainRestrict {N : Nat} (c : PfaffianChain (N + 1)) (q : MultiPoly (N + 1))
    (hq : MultiPoly.degreeY ⟨N, Nat.lt_succ_self N⟩ q = 0) (z : Real) :
    MultiPoly.eval q z (c.chainValues z)
      = MultiPoly.eval (MultiPoly.dropLastY q) z ((chainRestrict c).chainValues z) := by
  rw [← MultiPoly.eval_dropLastY q hq z (c.chainValues z)]
  congr 1

/-! ## Exponential-type chains — the class the descent recurses within -/

/-- An **exponential-type Pfaffian chain**: at every level `i`, the relation is `y_i · G_i` with `G_i`
top-free (`degreeY i G_i = 0`), and triangular (`relations i` omits `y_j` for `j > i`). Iterated exp is
the case `G_i = y_0·…·y_{i-1}`. Closed under `chainRestrict`, so the descent recurses within it. -/
def IsExpChain {N : Nat} (c : PfaffianChain N) : Prop :=
  ∀ i : Fin N,
    (∃ G : MultiPoly N, MultiPoly.degreeY i G = 0 ∧ c.relations i = MultiPoly.mul G (MultiPoly.varY i))
    ∧ (∀ j : Fin N, i.val < j.val → MultiPoly.degreeY j (c.relations i) = 0)

/-- Extract the top-level `(h_reltop, h_Gtop, h_tri)` triple that the reduce lemmas need. -/
theorem IsExpChain_top {N : Nat} (c : PfaffianChain (N + 1)) (h : IsExpChain c) :
    (∃ G : MultiPoly (N + 1),
        MultiPoly.degreeY ⟨N, Nat.lt_succ_self N⟩ G = 0
        ∧ c.relations ⟨N, Nat.lt_succ_self N⟩
            = MultiPoly.mul G (MultiPoly.varY ⟨N, Nat.lt_succ_self N⟩))
    ∧ (∀ j : Fin (N + 1), j ≠ ⟨N, Nat.lt_succ_self N⟩ →
        MultiPoly.degreeY ⟨N, Nat.lt_succ_self N⟩ (c.relations j) = 0) := by
  refine ⟨(h ⟨N, Nat.lt_succ_self N⟩).1, ?_⟩
  intro j hj
  have hjlt : j.val < N := by
    rcases Nat.lt_or_ge j.val N with h' | h'
    · exact h'
    · exact absurd (Fin.ext (Nat.le_antisymm (Nat.lt_succ_iff.mp j.isLt) h')) hj
  exact (h j).2 ⟨N, Nat.lt_succ_self N⟩ hjlt

/-- **`chainRestrict` preserves `IsExpChain`.** The sub-chain of an exponential-type chain is again
exponential-type — so the measure descent recurses within the class. -/
theorem IsExpChain_chainRestrict {N : Nat} (c : PfaffianChain (N + 1)) (h : IsExpChain c) :
    IsExpChain (chainRestrict c) := by
  intro i
  refine ⟨?_, ?_⟩
  · obtain ⟨G, hG, hrel⟩ := (h ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩).1
    refine ⟨MultiPoly.dropLastY G, ?_, ?_⟩
    · have hle := MultiPoly.degreeY_dropLastY_le G i
      rw [hG] at hle
      exact Nat.le_zero.mp hle
    · show MultiPoly.dropLastY (c.relations ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
          = MultiPoly.mul (MultiPoly.dropLastY G) (MultiPoly.varY i)
      rw [hrel]
      show MultiPoly.mul (MultiPoly.dropLastY G)
            (MultiPoly.dropLastY (MultiPoly.varY ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩))
          = MultiPoly.mul (MultiPoly.dropLastY G) (MultiPoly.varY i)
      congr 1
      show (if hlt : i.val < N then MultiPoly.varY ⟨i.val, hlt⟩ else MultiPoly.const 0)
          = MultiPoly.varY i
      rw [dif_pos i.isLt]
  · intro j hij
    show MultiPoly.degreeY j (MultiPoly.dropLastY (c.relations ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)) = 0
    have hle := MultiPoly.degreeY_dropLastY_le (c.relations ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) j
    rw [(h ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩).2 ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ hij] at hle
    exact Nat.le_zero.mp hle

/-! ## The graded multiplier + the descent step -/

/-- The graded multiplier at one level: top term `(degreeY_top p)·G` (cancels the leading-coeff
injection) plus a lower multiplier `mLow` (supplied recursively by the sub-level graded multiplier,
lifted). -/
noncomputable def gradedMultStep {N : Nat} (G : MultiPoly N) (top : Fin N) (p mLow : MultiPoly N) :
    MultiPoly N :=
  MultiPoly.add (MultiPoly.mul (MultiPoly.const (MachLib.Real.natCast (MultiPoly.degreeY top p))) G) mLow

theorem gradedMultStep_eval {N : Nat} (G : MultiPoly N) (top : Fin N) (p mLow : MultiPoly N)
    (x : Real) (env : Fin N → Real) :
    MultiPoly.eval (gradedMultStep G top p mLow) x env
    = MachLib.Real.natCast (MultiPoly.degreeY top p) * MultiPoly.eval G x env
      + MultiPoly.eval mLow x env := by
  show MultiPoly.eval (MultiPoly.add (MultiPoly.mul (MultiPoly.const _) G) mLow) x env = _
  rw [MultiPoly.eval_add, MultiPoly.eval_mul, MultiPoly.eval_const]

theorem gradedMultStep_degreeY_top_zero {N : Nat} (G : MultiPoly N) (top : Fin N) (p mLow : MultiPoly N)
    (h_Gtop : MultiPoly.degreeY top G = 0) (hmLow : MultiPoly.degreeY top mLow = 0) :
    MultiPoly.degreeY top (gradedMultStep G top p mLow) = 0 := by
  show MultiPoly.degreeY top
      (MultiPoly.add (MultiPoly.mul (MultiPoly.const _) G) mLow) = 0
  show Nat.max (MultiPoly.degreeY top (MultiPoly.mul (MultiPoly.const _) G))
               (MultiPoly.degreeY top mLow) = 0
  rw [degreeY_mul' top (MultiPoly.const (MachLib.Real.natCast (MultiPoly.degreeY top p))) G, hmLow]
  show Nat.max (MultiPoly.degreeY top (MultiPoly.const _) + MultiPoly.degreeY top G) 0 = 0
  rw [h_Gtop]
  show Nat.max (MultiPoly.degreeY top (MultiPoly.const _) + 0) 0 = 0
  show Nat.max (0 + 0) 0 = 0
  rfl

/-- **The descent step (exp-type chains).** With the graded multiplier `gradedMultStep G top p mLow`
(top-free `G`, top-free `mLow`), the leading `y_top`-coefficient of the reduce evaluates to the depth-
`(N-1)` reduce residual of `lcY_top p` with the LOWER multiplier `mLow`:
`cTD(lcY_top p) − mLow·lcY_top p`. This is the recursion step: one reduce drops the problem to `mLow` on
`lcY_top p`, exactly what the sub-level graded multiplier (over `chainRestrict c`) continues. -/
theorem chainReduce_gradedMultStep_lcY_top {N : Nat} (c : PfaffianChain N) (G : MultiPoly N) (top : Fin N)
    (h_reltop : c.relations top = MultiPoly.mul G (MultiPoly.varY top))
    (h_Gtop : MultiPoly.degreeY top G = 0)
    (h_tri : ∀ j : Fin N, j ≠ top → MultiPoly.degreeY top (c.relations j) = 0)
    (p mLow : MultiPoly N) (hmLow : MultiPoly.degreeY top mLow = 0) (x : Real) (env : Fin N → Real) :
    MultiPoly.eval (MultiPoly.leadingCoeffY top (chainReduce c (gradedMultStep G top p mLow) p)) x env
    = MultiPoly.eval (chainTotalDeriv c (MultiPoly.leadingCoeffY top p)) x env
      - MultiPoly.eval mLow x env * MultiPoly.eval (MultiPoly.leadingCoeffY top p) x env := by
  exact chainReduce_lcY_top_cancel c G top h_reltop h_Gtop h_tri
    (gradedMultStep G top p mLow) mLow p
    (gradedMultStep_degreeY_top_zero G top p mLow h_Gtop hmLow) x env
    (gradedMultStep_eval G top p mLow x env)

/-- **Recursion step (eval form).** The reduct's leading `y_top`-coefficient equals the sub-level reduce
`chainReduce c mLow (lcY_top p)` — so one reduce step turns the leading-coefficient problem into the
same shape one degree down. This is the identity the nested measure descends on. -/
theorem chainReduce_gradedMultStep_lcY_top_eq_subreduce {N : Nat} (c : PfaffianChain N)
    (G : MultiPoly N) (top : Fin N)
    (h_reltop : c.relations top = MultiPoly.mul G (MultiPoly.varY top))
    (h_Gtop : MultiPoly.degreeY top G = 0)
    (h_tri : ∀ j : Fin N, j ≠ top → MultiPoly.degreeY top (c.relations j) = 0)
    (p mLow : MultiPoly N) (hmLow : MultiPoly.degreeY top mLow = 0) (x : Real) (env : Fin N → Real) :
    MultiPoly.eval (MultiPoly.leadingCoeffY top (chainReduce c (gradedMultStep G top p mLow) p)) x env
    = MultiPoly.eval (chainReduce c mLow (MultiPoly.leadingCoeffY top p)) x env := by
  rw [chainReduce_gradedMultStep_lcY_top c G top h_reltop h_Gtop h_tri p mLow hmLow x env]
  unfold chainReduce
  rw [MultiPoly.eval_sub, MultiPoly.eval_mul]

/-! ## The recursive graded multiplier

`gradedMult k c q` is the multiplier that makes one reduce step drop the leading-coefficient problem to
the sub-chain (the general analog of the iterated-exp `fullMult`). At each level the top term is
`(degreeY_top q)·G` where `G = leadingCoeffY top (relations top)` (for an exp-type chain, `relations top
= G·y_top`, so this recovers `G`); the lower part is `liftLastY` of the sub-level multiplier over
`chainRestrict c`. Base at depth 2 is the single-exp canonical-degree multiplier. The recursion is on
depth (via `chainRestrict`), and it typechecks without whnf-divergence. -/
noncomputable def gradedMult : (k : Nat) → PfaffianChain (k + 2) → MultiPoly (k + 2) → MultiPoly (k + 2)
  | 0 => fun c q =>
      gradedMultStep
        (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) (c.relations (⟨1, by omega⟩ : Fin 2)))
        (⟨1, by omega⟩ : Fin 2) q
        (MultiPoly.const (MachLib.Real.natCast
          (cdegY0 (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q))))
  | k + 1 => fun c q =>
      gradedMultStep
        (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3))
          (c.relations (⟨k + 2, by omega⟩ : Fin (k + 3))))
        (⟨k + 2, by omega⟩ : Fin (k + 3)) q
        (MultiPoly.liftLastY (gradedMult k (chainRestrict c)
          (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) q))))

/-! ## WF descent port, layer (i) foundation: cTD/dropLastY commutation over restriction -/

/-- **cTD commutes with `dropLastY` over restriction**, for a top-free polynomial. Holds for ANY chain:
the top variable never appears (top-free), so the recurrence rides entirely on `chainRestrict`'s
definition (`relations` match under `dropLastY`). General analog of `dropLastY_cTD_commute`. -/
theorem dropLastY_cTD_commute_gen {N : Nat} (c : PfaffianChain (N + 1))
    (q : MultiPoly (N + 1)) (hq : MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) q = 0) :
    MultiPoly.dropLastY (chainTotalDeriv c q)
      = chainTotalDeriv (chainRestrict c) (MultiPoly.dropLastY q) := by
  induction q with
  | const cval => rfl
  | varX => rfl
  | varY i =>
    rcases i with ⟨v, hv⟩
    have hv2 : v < N := by
      by_cases hvv : v < N
      · exact hvv
      · exfalso
        have hveq : v = N := by omega
        have hd1 : MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1))
                     (MultiPoly.varY (⟨v, hv⟩ : Fin (N + 1))) = 1 := by
          show (if (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) = (⟨v, hv⟩ : Fin (N + 1)) then 1 else 0) = 1
          rw [if_pos (Fin.ext hveq.symm)]
        rw [hd1] at hq
        exact absurd hq (by omega)
    show MultiPoly.dropLastY (c.relations (⟨v, hv⟩ : Fin (N + 1)))
       = chainTotalDeriv (chainRestrict c) (MultiPoly.dropLastY (MultiPoly.varY (⟨v, hv⟩ : Fin (N + 1))))
    have hd : MultiPoly.dropLastY (MultiPoly.varY (⟨v, hv⟩ : Fin (N + 1)))
            = MultiPoly.varY (⟨v, hv2⟩ : Fin N) := by
      show (if h : v < N then MultiPoly.varY (⟨v, h⟩ : Fin N) else MultiPoly.const 0)
         = MultiPoly.varY (⟨v, hv2⟩ : Fin N)
      rw [dif_pos hv2]
    rw [hd]
    show MultiPoly.dropLastY (c.relations (⟨v, hv⟩ : Fin (N + 1)))
       = MultiPoly.dropLastY (c.relations (⟨v, Nat.lt_succ_of_lt hv2⟩ : Fin (N + 1)))
    rfl
  | add p q ihp ihq =>
    have h0 : Nat.max (MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p)
                      (MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) q) = 0 := hq
    have hp : MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p = 0 := Nat.le_zero.mp (h0 ▸ Nat.le_max_left _ _)
    have hq2 : MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) q = 0 := Nat.le_zero.mp (h0 ▸ Nat.le_max_right _ _)
    show MultiPoly.add (MultiPoly.dropLastY (chainTotalDeriv c p))
                       (MultiPoly.dropLastY (chainTotalDeriv c q))
       = MultiPoly.add (chainTotalDeriv (chainRestrict c) (MultiPoly.dropLastY p))
                       (chainTotalDeriv (chainRestrict c) (MultiPoly.dropLastY q))
    rw [ihp hp, ihq hq2]
  | sub p q ihp ihq =>
    have h0 : Nat.max (MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p)
                      (MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) q) = 0 := hq
    have hp : MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p = 0 := Nat.le_zero.mp (h0 ▸ Nat.le_max_left _ _)
    have hq2 : MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) q = 0 := Nat.le_zero.mp (h0 ▸ Nat.le_max_right _ _)
    show MultiPoly.sub (MultiPoly.dropLastY (chainTotalDeriv c p))
                       (MultiPoly.dropLastY (chainTotalDeriv c q))
       = MultiPoly.sub (chainTotalDeriv (chainRestrict c) (MultiPoly.dropLastY p))
                       (chainTotalDeriv (chainRestrict c) (MultiPoly.dropLastY q))
    rw [ihp hp, ihq hq2]
  | mul p q ihp ihq =>
    have h0 : MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p
            + MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) q = 0 := hq
    have hp : MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p = 0 := by omega
    have hq2 : MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) q = 0 := by omega
    show MultiPoly.add
          (MultiPoly.mul (MultiPoly.dropLastY (chainTotalDeriv c p)) (MultiPoly.dropLastY q))
          (MultiPoly.mul (MultiPoly.dropLastY p) (MultiPoly.dropLastY (chainTotalDeriv c q)))
       = MultiPoly.add
          (MultiPoly.mul (chainTotalDeriv (chainRestrict c) (MultiPoly.dropLastY p)) (MultiPoly.dropLastY q))
          (MultiPoly.mul (MultiPoly.dropLastY p) (chainTotalDeriv (chainRestrict c) (MultiPoly.dropLastY q)))
    rw [ihp hp, ihq hq2]

end MachLib.PfaffianGeneralReduce
