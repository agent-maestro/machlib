import MachLib.PfaffianLogWronskian
import MachLib.WronskianProportional

/-!
# Concrete discharge of the log `g ≡ 0` leaf (modulo analyticity)

`log_step_multilinear` leaves one isolated obligation, `hDegen`: a
degree-1-in-`y_top` barrier `q` whose Wronskian
`g = c_D·q' − c_D'·q` (with `c_D = leadingCoeffY q`) vanishes identically.
`WronskianProportional` built the analytic engine
(`wronskian_zero_bounded_zeros`). This file WIRES it to the concrete
Pfaffian descent, reducing the entire leaf to a single remaining input —
the analyticity of the concrete barrier and its leading coefficient on
`[a,b]` — which the EMLTree→chain encoder supplies via
`eml_tree_analytic_on_pos`.

`log_hDegen_via_analytic` produces EXACTLY `hDegen`'s conclusion from:
- coherence (for the symbolic-derivative bridge `hasDerivAt_eval_natural`),
- the two analyticity facts,
- the `g ≡ 0` hypothesis (verbatim `hDegen`),
- non-vanishing `hne`,
- a bound `N` on the leading coefficient's zeros (the descent's depth IH).

The derivatives come from `multiPolyHasDerivAt_eval_with_chain`; the
Wronskian `hW` is read off `g ≡ 0` by the (definitional) `eval_sub`/
`eval_mul` homomorphism plus one commutativity rearrangement.

No `zero_count_bound_classical`. No sorryAx.
-/

namespace MachLib

open MachLib.Real MultiPolyMod MultiPolyMod.MultiPoly PfaffianChainMod
  PfaffianChainMod.PfaffianFn PfaffianGeneralReduce

/-- The Wronskian `pfaffianChainFn c (c_D·q' − c_D'·q)` evaluated equals
`q'·c_D − q·c_D'` (up to the `phi_identity` orientation). `eval_sub`/
`eval_mul` are `rfl`, so this is one `mach_ring` commutation. -/
private theorem pf_wronskian_eval {n : Nat} (c : PfaffianChain n)
    (cd dq dcd q : MultiPoly n) (x : Real) :
    (pfaffianChainFn c dq).eval x * (pfaffianChainFn c cd).eval x
      - (pfaffianChainFn c q).eval x * (pfaffianChainFn c dcd).eval x
    = (pfaffianChainFn c (MultiPoly.sub (MultiPoly.mul cd dq)
        (MultiPoly.mul dcd q))).eval x := by
  show MultiPoly.eval dq x (c.chainValues x) * MultiPoly.eval cd x (c.chainValues x)
     - MultiPoly.eval q x (c.chainValues x) * MultiPoly.eval dcd x (c.chainValues x)
     = MultiPoly.eval (MultiPoly.sub (MultiPoly.mul cd dq) (MultiPoly.mul dcd q))
         x (c.chainValues x)
  rw [MultiPoly.eval_sub, MultiPoly.eval_mul, MultiPoly.eval_mul]
  mach_ring

/-- **Concrete `hDegen` discharge (modulo analyticity).** Reduces the log
descent's degenerate leaf to the analyticity of the concrete barrier and
its leading coefficient — the sole input the encoder must still supply. -/
theorem log_hDegen_via_analytic {N : Nat} (c : PfaffianChain (N + 1))
    (a b : Real) (hab : a < b) (hcoh : c.IsCoherentOn a b)
    (q : MultiPoly (N + 1))
    (hFan : IsAnalyticOnReals (pfaffianChainFn c q).eval (Icc a b))
    (hGan : IsAnalyticOnReals
      (pfaffianChainFn c (MultiPoly.leadingCoeffY
        (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) q)).eval (Icc a b))
    (hg_zero : ∀ z, a < z → z < b → (pfaffianChainFn c (MultiPoly.sub
      (MultiPoly.mul (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) q)
        (chainTotalDeriv c q))
      (MultiPoly.mul (chainTotalDeriv c
        (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) q)) q))).eval z = 0)
    (hne : ∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c q).eval z ≠ 0)
    (Nb : Nat)
    (hGbound : ∀ zeros : List Real, zeros.Nodup →
        (∀ z ∈ zeros, a < z ∧ z < b ∧ (pfaffianChainFn c
          (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) q)).eval z = 0) →
        zeros.length ≤ Nb) :
    ∃ M : Nat, ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ (pfaffianChainFn c q).eval z = 0) → zeros.length ≤ M := by
  -- Derivative supply via the symbolic-derivative bridge.
  have hFderiv : ∀ x, a < x → x < b →
      HasDerivAt (pfaffianChainFn c q).eval
        ((pfaffianChainFn c (chainTotalDeriv c q)).eval x) x :=
    fun x h1 h2 => multiPolyHasDerivAt_eval_with_chain c q x (hcoh x h1 h2)
  have hGderiv : ∀ x, a < x → x < b →
      HasDerivAt (pfaffianChainFn c
          (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) q)).eval
        ((pfaffianChainFn c (chainTotalDeriv c
          (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) q))).eval x) x :=
    fun x h1 h2 => multiPolyHasDerivAt_eval_with_chain c
      (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) q) x (hcoh x h1 h2)
  -- Wronskian `hW` off `g ≡ 0` (eval_sub/eval_mul are rfl; comm rearrange).
  have hW : ∀ x, a < x → x < b →
      (pfaffianChainFn c (chainTotalDeriv c q)).eval x
        * (pfaffianChainFn c
            (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) q)).eval x
      - (pfaffianChainFn c q).eval x
        * (pfaffianChainFn c (chainTotalDeriv c
            (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) q))).eval x = 0 := by
    intro x h1 h2
    rw [pf_wronskian_eval c
      (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) q)
      (chainTotalDeriv c q)
      (chainTotalDeriv c (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) q))
      q x]
    exact hg_zero x h1 h2
  -- Non-vanishing in `Ioo` form.
  have hFne : ∃ x : Real, Ioo a b x ∧ (pfaffianChainFn c q).eval x ≠ 0 := by
    obtain ⟨z, hz1, hz2, hzne⟩ := hne
    exact ⟨z, ⟨hz1, hz2⟩, hzne⟩
  exact wronskian_zero_bounded_zeros
    (pfaffianChainFn c q).eval
    (pfaffianChainFn c (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) q)).eval
    (fun x => (pfaffianChainFn c (chainTotalDeriv c q)).eval x)
    (fun x => (pfaffianChainFn c (chainTotalDeriv c
      (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) q))).eval x)
    a b hab hFan hGan hFderiv hGderiv hW hFne Nb hGbound

end MachLib
