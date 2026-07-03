import MachLib.PfaffianGeneralReduce
import MachLib.IterExpDepthNCapstone

/-!
# Generalize — WF assembly (layer v) for arbitrary exponential-type Pfaffian chains

The measure/order infrastructure `chainNMeasure5` / `chainNOrder5` / `chainNOrder5_wf` and the trim
descents (`chainN_degreeYtop_trim_order5`, `innerTrimN_order5`) are **chain-agnostic** — pure polynomial
facts (`IterExpDepthNCapstone` mentions no chain). So the general WF assembly reuses them verbatim; the
only chain-specific measure piece is the reduce arm's M5 descent, which this file supplies by wiring the
general layer (i) syntactic descent (`chainReduce_syntactic_descent_gen`) to the general layer (iii)
recursion (`chainReduce_descends_gen`).

Everything here is conditional on the single-exponential depth-2 base descent `hBase` (the remaining
sub-arc). What is NOT yet ported: the chain-function eval helpers (`chainNFn_*`) that relate the zeros of
`(pfaffianChainFn c p).eval` across trim/reduce — those need the general chain's coherence and are the
next block of layer (v).
-/

namespace MachLib.PfaffianGeneralReduce

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.PfaffianChainMod
open MachLib.PfaffianChainMod.PfaffianFn
open MachLib.IterExpDepthN
open MachLib.IterExpDepth3CdegY1
open MachLib.ChainExp2CanonMeasure
open MachLib.ChainExp2Trim

/-- **Layer (v-a): the general reduce's `chainNMeasureCanon` descent.** The layer (i) syntactic descent
(`chainReduce_syntactic_descent_gen`, top `y`-degree ties, inner measure drops) lifted by the layer (iii)
inner recursion (`chainReduce_descends_gen`), which supplies the inner `chainNMeasureEI` drop. The
multiplier is existential — built from the exp-type factor `G` over the lifted sub-level multiplier.
`chainNMeasureCanon M p = (degreeY_top p, chainNMeasureEI M (dropLastY (lcY_top p)))`, so the syntactic
descent's conclusion IS this after `simp`. Conditional on the depth-2 base `hBase`. -/
theorem chainReduce_orderCanon_gen
    (hBase : ∀ (c : PfaffianChain 2), IsExpChain c → ∀ (q : MultiPoly 2), ReducingGen 0 q →
      ∃ m : MultiPoly 2, MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) m = 0 ∧
        nestedOrder 2 (chainNMeasureEI 0 (chainReduce c m q)) (chainNMeasureEI 0 q))
    {M : Nat} (c : PfaffianChain (M + 3)) (hexp : IsExpChain c) (p : MultiPoly (M + 3))
    (hred : ReducingGen M (MultiPoly.dropLastY
      (MultiPoly.leadingCoeffY (⟨M + 2, by omega⟩ : Fin (M + 3)) p))) :
    ∃ m : MultiPoly (M + 3), MultiPoly.degreeY (⟨M + 2, by omega⟩ : Fin (M + 3)) m = 0 ∧
      nestedOrder (M + 3) (chainNMeasureCanon M (chainReduce c m p)) (chainNMeasureCanon M p) := by
  obtain ⟨⟨G, hG, hrel⟩, htri⟩ := IsExpChain_top c hexp
  obtain ⟨m', hm'0, hm'desc⟩ := chainReduce_descends_gen hBase M (chainRestrict c)
    (IsExpChain_chainRestrict c hexp)
    (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨M + 2, by omega⟩ : Fin (M + 3)) p)) hred
  refine ⟨gradedMultStep G (⟨M + 2, by omega⟩ : Fin (M + 3)) p (MultiPoly.liftLastY m'),
    gradedMultStep_degreeY_top_zero G (⟨M + 2, by omega⟩ : Fin (M + 3)) p (MultiPoly.liftLastY m') hG
      (MultiPoly.degreeY_top_liftLastY m'), ?_⟩
  have hInner : nestedOrder (M + 2)
      (chainNMeasureEI M (chainReduce (chainRestrict c) (MultiPoly.dropLastY (MultiPoly.liftLastY m'))
        (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨M + 2, by omega⟩ : Fin (M + 3)) p))))
      (chainNMeasureEI M (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨M + 2, by omega⟩ : Fin (M + 3)) p))) := by
    rw [MultiPoly.dropLastY_liftLastY]; exact hm'desc
  show nestedOrder (M + 3)
    (chainNMeasureCanon M (chainReduce c (gradedMultStep G (⟨M + 2, by omega⟩ : Fin (M + 3)) p (MultiPoly.liftLastY m')) p))
    (chainNMeasureCanon M p)
  simp only [chainNMeasureCanon]
  exact chainReduce_syntactic_descent_gen c G hrel hG htri (MultiPoly.liftLastY m') p
    (MultiPoly.degreeY_top_liftLastY m') hInner

/-- **Layer (v-a′): the general reduce's `M5` descent.** Lifts the `chainNMeasureCanon` drop to the
augmented measure `chainNMeasure5 = (chainNMeasureCanon, degreeY_{top-1}(lcY_top ·))` by dropping the
first component (`lexProd_of_fst`) — the exact reuse of `chainNReduce_order5`'s pattern, now for a general
exp-type chain. This is the reduce arm the general WF induction will dispatch. -/
theorem chainReduce_order5_gen
    (hBase : ∀ (c : PfaffianChain 2), IsExpChain c → ∀ (q : MultiPoly 2), ReducingGen 0 q →
      ∃ m : MultiPoly 2, MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) m = 0 ∧
        nestedOrder 2 (chainNMeasureEI 0 (chainReduce c m q)) (chainNMeasureEI 0 q))
    {M : Nat} (c : PfaffianChain (M + 3)) (hexp : IsExpChain c) (p : MultiPoly (M + 3))
    (hred : ReducingGen M (MultiPoly.dropLastY
      (MultiPoly.leadingCoeffY (⟨M + 2, by omega⟩ : Fin (M + 3)) p))) :
    ∃ m : MultiPoly (M + 3), MultiPoly.degreeY (⟨M + 2, by omega⟩ : Fin (M + 3)) m = 0 ∧
      chainNOrder5 M (chainReduce c m p) p := by
  obtain ⟨m, hm0, hdesc⟩ := chainReduce_orderCanon_gen hBase c hexp p hred
  exact ⟨m, hm0, lexProd_of_fst hdesc⟩

/-! ## Layer (v) chain-function side — the analytic core

The measure side above is chain-agnostic + wired. The chain-FUNCTION side relates the zeros of
`(pfaffianChainFn c p).eval` across the reduce/trim moves. The shared analytic foundation is the
reduce-eval identity below; the no-zeros arm's integrating factor for an exp-type chain is the monomial
`Π yᵢ^{degᵢ}` in the chain values (since `Gᵢ = yᵢ'/yᵢ`), the general analog of the iterated-exp `vehExpo`. -/

/-- **General reduce-eval identity.** The reduce, evaluated along the chain, is `f' − (m·f)` — the
`f' − M·f` that the Rolle transfer (reduce arm) and the vehicle no-zeros argument both count. Defeq-trivial:
`chainReduce = cTD − m·p` and `(pfaffianChainFn c p).chainTotalDerivative = pfaffianChainFn c (chainTotalDeriv c p)`
by definition, so this is `eval_sub` + `eval_mul`. Chain-agnostic (holds for ANY Pfaffian chain). -/
theorem pfaffianChainFn_reduce_eval {n : Nat} (c : PfaffianChain n) (m p : MultiPoly n) (z : Real) :
    (pfaffianChainFn c (chainReduce c m p)).eval z
    = (pfaffianChainFn c p).chainTotalDerivative.eval z
      - (pfaffianChainFn c m).eval z * (pfaffianChainFn c p).eval z := by
  show MultiPoly.eval (chainReduce c m p) z (c.chainValues z)
    = MultiPoly.eval (chainTotalDeriv c p) z (c.chainValues z)
      - MultiPoly.eval m z (c.chainValues z) * MultiPoly.eval p z (c.chainValues z)
  unfold chainReduce
  rw [MultiPoly.eval_sub, MultiPoly.eval_mul]

/-- **General no-zeros arm, conditional on the integrating factor `E`.** If the reduce vanishes
identically on `(a,b)` and `f = pfaffianChainFn c p` is nonzero at an interior `z₀`, then `f` has no
zeros on `(a,b)`. `f' = M̃·f` (reduce ≡ 0 via the reduce-eval identity), so the vehicle `f·exp(E)` with
`E' = −M̃` is constant and nonvanishing. `E` — an antiderivative of `−M̃ = −(pfaffianChainFn c m).eval` —
is the hypothesis; for a positive coherent exp-type chain it is `−Σ degᵢ·log yᵢ` (`Gᵢ = yᵢ'/yᵢ`), the
general `vehExpo`. Everything else is the chain-agnostic `pfaffianFn_no_zeros_of_ode_gen`. -/
theorem pfaffianChainFn_no_zeros_of_reduct_zero_gen {n : Nat} (c : PfaffianChain n) (m p : MultiPoly n)
    (a b : Real) (hab : a < b) (E : Real → Real)
    (hcoh : c.IsCoherentOn a b)
    (hE : ∀ z, a < z → z < b → HasDerivAt E (-(pfaffianChainFn c m).eval z) z)
    (h_reduct : ∀ z, a < z → z < b → (pfaffianChainFn c (chainReduce c m p)).eval z = 0)
    (z₀ : Real) (hz₀a : a < z₀) (hz₀b : z₀ < b) (hne₀ : (pfaffianChainFn c p).eval z₀ ≠ 0) :
    ∀ z, a < z → z < b → (pfaffianChainFn c p).eval z ≠ 0 := by
  apply pfaffianFn_no_zeros_of_ode_gen (pfaffianChainFn c p) a b hab E
    (fun z => -(pfaffianChainFn c m).eval z) hcoh hE ?_ z₀ hz₀a hz₀b hne₀
  intro z hza hzb
  have hre := pfaffianChainFn_reduce_eval c m p z
  rw [h_reduct z hza hzb] at hre
  show (pfaffianChainFn c p).chainTotalDerivative.eval z
      + (-(pfaffianChainFn c m).eval z) * (pfaffianChainFn c p).eval z = 0
  have hrw : (pfaffianChainFn c p).chainTotalDerivative.eval z
      + (-(pfaffianChainFn c m).eval z) * (pfaffianChainFn c p).eval z
      = (pfaffianChainFn c p).chainTotalDerivative.eval z
        - (pfaffianChainFn c m).eval z * (pfaffianChainFn c p).eval z := by mach_ring
  rw [hrw]; exact hre.symm

/-- **E-abstract Rolle transfer (raw).** Zeros of `f` on `(a,b)` are ≤ zeros of the vehicle derivative
`(vehicleGen f E)'` + 1. The `vehicleGen`/`hasDerivAt_vehicleGen` engine (chain-agnostic) fed to
`zero_count_bound_by_deriv` (the single-axiom Rolle). Mirrors `zero_count_vehicleN_transfer_raw` with the
abstract integrating factor `E` in place of the iterated-exp `vehExpo`. -/
theorem zero_count_vehicleGen_transfer_raw (f : PfaffianFn) (E : Real → Real) (M : Real → Real)
    (a b : Real) (hab : a < b) (hcoherent : f.chain.IsCoherentOn a b)
    (hE : ∀ z, a < z → z < b → HasDerivAt E (M z) z) (N : Nat)
    (h_reduced_bound : ∀ zeros' : List Real, zeros'.Nodup →
        (∀ z ∈ zeros', a < z ∧ z < b ∧
          ∃ f'' : Real, HasDerivAt (vehicleGen f E) f'' z ∧ f'' = 0) →
        zeros'.length ≤ N) :
    ∀ zeros_f : List Real, zeros_f.Nodup →
      (∀ z ∈ zeros_f, a < z ∧ z < b ∧ f.eval z = 0) →
      zeros_f.length ≤ N + 1 := by
  intro zeros_f hnodup hzeros
  have hzeros_g : ∀ z ∈ zeros_f, a < z ∧ z < b ∧ vehicleGen f E z = 0 := by
    intro z hz
    obtain ⟨haz, hzb, hfz⟩ := hzeros z hz
    exact ⟨haz, hzb, (vehicleGen_zero_iff f E z).mpr hfz⟩
  have hdiff : ∀ x : Real, a < x → x < b → ∃ f' : Real, HasDerivAt (vehicleGen f E) f' x := by
    intro x hax hxb
    exact ⟨_, hasDerivAt_vehicleGen f E (M x) x (hasDerivAt_eval_natural f x (hcoherent x hax hxb)) (hE x hax hxb)⟩
  exact zero_count_bound_by_deriv (vehicleGen f E) a b hab hdiff N h_reduced_bound zeros_f hnodup hzeros_g

/-- **E-abstract Rolle transfer (eval form).** If `f' + M·f` has ≤ `N` zeros on `(a,b)`, then `f` has
≤ `N+1`. Converts a vehicle-derivative zero to an `f' + M·f = 0` zero: `(vehicleGen f E)' = exp(E)·(f'+M·f)`
(`hasDerivAt_vehicleGen`), and `exp > 0`. -/
theorem zero_count_vehicleGen_transfer (f : PfaffianFn) (E : Real → Real) (M : Real → Real)
    (a b : Real) (hab : a < b) (hcoherent : f.chain.IsCoherentOn a b)
    (hE : ∀ z, a < z → z < b → HasDerivAt E (M z) z) (N : Nat)
    (h_reduced_bound_eval : ∀ zeros' : List Real, zeros'.Nodup →
        (∀ z ∈ zeros', a < z ∧ z < b ∧
          f.chainTotalDerivative.eval z + M z * f.eval z = 0) →
        zeros'.length ≤ N) :
    ∀ zeros_f : List Real, zeros_f.Nodup →
      (∀ z ∈ zeros_f, a < z ∧ z < b ∧ f.eval z = 0) →
      zeros_f.length ≤ N + 1 := by
  apply zero_count_vehicleGen_transfer_raw f E M a b hab hcoherent hE N
  intro zeros' hnodup' hzeros'_prop
  apply h_reduced_bound_eval zeros' hnodup'
  intro z hz
  obtain ⟨haz, hzb, g'', hg''_deriv, hg''_zero⟩ := hzeros'_prop z hz
  refine ⟨haz, hzb, ?_⟩
  have hf := hasDerivAt_eval_natural f z (hcoherent z haz hzb)
  have hvd := hasDerivAt_vehicleGen f E (M z) z hf (hE z haz hzb)
  have huniq := HasDerivAt_unique (vehicleGen f E)
    (f.chainTotalDerivative.eval z * (E z).exp + f.eval z * ((E z).exp * M z)) g'' z hvd hg''_deriv
  rw [hg''_zero] at huniq
  have hfac : f.chainTotalDerivative.eval z * (E z).exp + f.eval z * ((E z).exp * M z)
      = (E z).exp * (f.chainTotalDerivative.eval z + M z * f.eval z) := by mach_ring
  rw [hfac] at huniq
  exact mul_eq_zero_of_factor_ne_zero (exp_ne_zero (E z)) huniq

/-- **General reduce-step arm (Rolle +1).** If the reduce has ≤ `N` zeros on `(a,b)`, then
`f = pfaffianChainFn c p` has ≤ `N+1`. The reduce arm the WF induction takes when the reduce is ≢ 0:
recurse on the reduce (smaller measure via `chainReduce_order5_gen`) and add one Rolle zero. `M = −(m eval)`,
so `f' + M·f = f' − (m eval)·f = reduce` (reduce-eval identity). Conditional on the integrating factor `E`
+ coherence, exactly like the no-zeros arm. -/
theorem pfaffianChainFn_reduce_step_gen {n : Nat} (c : PfaffianChain n) (m p : MultiPoly n)
    (a b : Real) (hab : a < b) (E : Real → Real) (hcoh : c.IsCoherentOn a b)
    (hE : ∀ z, a < z → z < b → HasDerivAt E (-(pfaffianChainFn c m).eval z) z) (N : Nat)
    (hN : ∀ zeros' : List Real, zeros'.Nodup →
        (∀ z ∈ zeros', a < z ∧ z < b ∧ (pfaffianChainFn c (chainReduce c m p)).eval z = 0) →
        zeros'.length ≤ N) :
    ∀ zeros_f : List Real, zeros_f.Nodup →
      (∀ z ∈ zeros_f, a < z ∧ z < b ∧ (pfaffianChainFn c p).eval z = 0) →
      zeros_f.length ≤ N + 1 := by
  refine zero_count_vehicleGen_transfer (pfaffianChainFn c p) E (fun z => -(pfaffianChainFn c m).eval z)
    a b hab hcoh hE N ?_
  intro zeros' hnodup' hz'
  apply hN zeros' hnodup'
  intro z hzmem
  obtain ⟨haz, hzb, hval⟩ := hz' z hzmem
  refine ⟨haz, hzb, ?_⟩
  rw [pfaffianChainFn_reduce_eval]
  have hrw : (pfaffianChainFn c p).chainTotalDerivative.eval z
        - (pfaffianChainFn c m).eval z * (pfaffianChainFn c p).eval z
      = (pfaffianChainFn c p).chainTotalDerivative.eval z
        + (-(pfaffianChainFn c m).eval z) * (pfaffianChainFn c p).eval z := by mach_ring
  rw [hrw]; exact hval

/-! ## Layer (v) — base + trim arms (eval plumbing) -/

/-- **General base arm.** If the top `y`-variable is absent (`degreeY_top p = 0`), `f = pfaffianChainFn c p`
depends only on the restricted chain, so the depth-`N` bound (`IH` on `chainRestrict c`) transfers.
Chain-agnostic: `eval p z (c.chainValues z) = eval (dropLastY p) z ((chainRestrict c).chainValues z)` via
`eval_dropLastY` + `chainRestrict_chainValues`. -/
theorem pfaffianChainFn_bound_of_degreeYtop_zero {N : Nat} (c : PfaffianChain (N + 1)) (p : MultiPoly (N + 1))
    (hd : MultiPoly.degreeY (⟨N, by omega⟩ : Fin (N + 1)) p = 0) (a b : Real) (hab : a < b)
    (hne : ∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c p).eval z ≠ 0)
    (IH : ∀ (q : MultiPoly N) (a' b' : Real), a' < b' →
        (∃ z, a' < z ∧ z < b' ∧ (pfaffianChainFn (chainRestrict c) q).eval z ≠ 0) →
        ∃ M, ∀ zeros : List Real, zeros.Nodup →
          (∀ z ∈ zeros, a' < z ∧ z < b' ∧ (pfaffianChainFn (chainRestrict c) q).eval z = 0) → zeros.length ≤ M) :
    ∃ M, ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ (pfaffianChainFn c p).eval z = 0) → zeros.length ≤ M := by
  have heval : ∀ z, (pfaffianChainFn c p).eval z
      = (pfaffianChainFn (chainRestrict c) (MultiPoly.dropLastY p)).eval z := by
    intro z
    show MultiPoly.eval p z (c.chainValues z)
      = MultiPoly.eval (MultiPoly.dropLastY p) z ((chainRestrict c).chainValues z)
    have hrestrict : (chainRestrict c).chainValues z
        = (fun i => (c.chainValues z) ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) := by
      funext i; exact chainRestrict_chainValues c z i
    rw [hrestrict, MultiPoly.eval_dropLastY p hd z (c.chainValues z)]
  obtain ⟨z, hza, hzb, hzne⟩ := hne
  obtain ⟨M, hM⟩ := IH (MultiPoly.dropLastY p) a b hab ⟨z, hza, hzb, by rw [← heval]; exact hzne⟩
  refine ⟨M, fun zeros hnd hz => hM zeros hnd (fun z' hz'mem => ?_)⟩
  obtain ⟨ha, hb', hzero⟩ := hz z' hz'mem
  exact ⟨ha, hb', by rw [← heval]; exact hzero⟩

/-- **General degree-trim eval identity.** If the leading `y_top`-coefficient's last `y_{top-1}`-term is
canonically zero, dropping the leading `y_top`-term doesn't change the value along the chain. Chain-agnostic:
`eval_dropLeadingYAt_of_last_canonically_zero` takes an arbitrary env. -/
theorem pfaffianChainFn_degreeYtop_trim_eval {M : Nat} (c : PfaffianChain (M + 3)) (p : MultiPoly (M + 3))
    (h_phantom : ∀ (x : Real) (env : Fin (M + 3) → Real),
      MultiPoly.eval ((MultiPoly.yCoeffsAt (⟨M + 2, by omega⟩ : Fin (M + 3)) p).getLast
        (MultiPoly.yCoeffsAt_nonempty (⟨M + 2, by omega⟩ : Fin (M + 3)) p)) x env = 0) (z : Real) :
    (pfaffianChainFn c p).eval z
      = (pfaffianChainFn c (dropLeadingYAt (⟨M + 2, by omega⟩ : Fin (M + 3)) p)).eval z :=
  (eval_dropLeadingYAt_of_last_canonically_zero (⟨M + 2, by omega⟩ : Fin (M + 3)) p
    (MultiPoly.yCoeffsAt_nonempty (⟨M + 2, by omega⟩ : Fin (M + 3)) p) h_phantom z (c.chainValues z)).symm

/-- **General inner-trim eval identity.** Direct reuse — `eval_innerTrimN` is a pure `MultiPoly` eval
identity (arbitrary env), so it holds along any chain. -/
theorem pfaffianChainFn_innerTrim_eval {M : Nat} (c : PfaffianChain (M + 3)) (p : MultiPoly (M + 3))
    (h_phantom : ∀ (x : Real) (env : Fin (M + 3) → Real),
      MultiPoly.eval ((MultiPoly.yCoeffsAt (⟨M + 1, by omega⟩ : Fin (M + 3))
        (MultiPoly.leadingCoeffY (⟨M + 2, by omega⟩ : Fin (M + 3)) p)).getLast
        (MultiPoly.yCoeffsAt_nonempty (⟨M + 1, by omega⟩ : Fin (M + 3))
          (MultiPoly.leadingCoeffY (⟨M + 2, by omega⟩ : Fin (M + 3)) p))) x env = 0) (z : Real) :
    (pfaffianChainFn c (innerTrimN M p)).eval z = (pfaffianChainFn c p).eval z :=
  eval_innerTrimN M p h_phantom z (c.chainValues z)

end MachLib.PfaffianGeneralReduce
