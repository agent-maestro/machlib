import MachLib.PfaffianGeneralWF

/-!
# The exp reduce step, assembled for an arbitrary (mixed) chain — toward `exp_hard`

`exp_hard` (the `degreeY_top > 0` exp arm of the 3-type descent) is the last open
classical core of the EML barrier bound, and — unlike `log_hard` — it does **not**
reduce to a simple fuel induction on `degreeY_top`: the exp reduce *preserves* the top
degree (`degreeYtop_cTD_eq_gen`), replacing the leading coefficient `c_d` with its total
derivative `cTD(c_d)`. Termination is governed by a **canonical eval-invariant measure**
(`chainNMeasureEI`), whose descent the exp tower proves **only for `IsExpChain`** (every
lower variable exp-type). For a mixed `IsExpLogRecipW` chain it has no direct analogue —
iterating `cTD` on a reciprocal-type leading coefficient *raises* its degree
(`cTD(1/w) = −w'·(1/w)²`), so the pure-exp measure does not descend. That mixed-chain
measure descent (plus the integrating-factor construction) is the genuine remaining
research content of `exp_hard`.

What this file records is the part that IS chain-agnostic: the **exp reduce STEP** — given
a reduce multiplier `m`, its integrating factor `E`, and a bound on the reduct's zeros,
`pfaffianChainFn c p` has a bounded zero count. It packages the two chain-agnostic engines
`pfaffianChainFn_reduce_step_gen` (Rolle transfer, reduct ≢ 0) and
`pfaffianChainFn_no_zeros_of_reduct_zero_gen` (vehicle no-zeros, reduct ≡ 0) into one total
`BoundedZeros` step — the exp analog of the log side's `chainTotalDeriv_rolle` +
`log_cTD_zero_bounded` split. Any `exp_hard` assembly consumes exactly this, leaving the
measure/integrating-factor as the sole open inputs.

No new axioms — both engines are `rolle`-grounded and chain-agnostic.
-/

namespace MachLib
namespace PfaffianGeneralReduce

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.PfaffianChainMod
open MachLib.PfaffianChainMod.PfaffianFn

/-- **The exp reduce step, for ANY coherent chain.** Given a reduce multiplier `m` with an
integrating factor `E` (an antiderivative of `−(pfaffianChainFn c m).eval` on `(a,b)`), and
`p` somewhere non-vanishing, the zeros of `pfaffianChainFn c p` are bounded — provided the
reduct `chainReduce c m p` either vanishes identically (⇒ `p` has NO zeros, the vehicle is
constant and nonvanishing) or has a bounded zero count `Nr` (⇒ `p` has `≤ Nr + 1`, one Rolle
zero more). Chain-agnostic: reused verbatim for exp, log, or mixed tops — the exp arm feeds
it the graded multiplier `m = (degreeY_top p)·G + …` and the exp vehicle `E`. -/
theorem exp_reduce_step_bounded {n : Nat} (c : PfaffianChain n) (m p : MultiPoly n)
    (a b : Real) (hab : a < b) (E : Real → Real)
    (hcoh : c.IsCoherentOn a b)
    (hE : ∀ z, a < z → z < b → HasDerivAt E (-(pfaffianChainFn c m).eval z) z)
    (hne : ∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c p).eval z ≠ 0)
    (hReduct :
        (∀ z, a < z → z < b → (pfaffianChainFn c (chainReduce c m p)).eval z = 0)
      ∨ (∃ Nr : Nat, ∀ zeros : List Real, zeros.Nodup →
          (∀ z ∈ zeros, a < z ∧ z < b ∧ (pfaffianChainFn c (chainReduce c m p)).eval z = 0) →
          zeros.length ≤ Nr)) :
    ∃ M : Nat, ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ (pfaffianChainFn c p).eval z = 0) → zeros.length ≤ M := by
  rcases hReduct with hrz | ⟨Nr, hNr⟩
  · -- reduct ≡ 0: the vehicle is constant and nonvanishing, so `p` has no zeros.
    obtain ⟨z₀, hz₀a, hz₀b, hne₀⟩ := hne
    have hnoz := pfaffianChainFn_no_zeros_of_reduct_zero_gen c m p a b hab E hcoh hE hrz z₀ hz₀a hz₀b hne₀
    refine ⟨0, fun zeros _ hz => ?_⟩
    cases zeros with
    | nil => exact Nat.le_refl 0
    | cons z zs =>
      obtain ⟨ha, hb', hzero⟩ := hz z (List.mem_cons_self _ _)
      exact absurd hzero (hnoz z ha hb')
  · -- reduct bounded: Rolle transfer adds one zero.
    exact ⟨Nr + 1, pfaffianChainFn_reduce_step_gen c m p a b hab E hcoh hE Nr hNr⟩

/-! ## The exp-top integrating factor — constructed, not assumed -/

/-- **The exp reduce's integrating factor for the top variable, over ANY chain.**
For an exp-type top (`relations top = G · y_top`) that stays positive on `(a,b)`, the
explicit exponent `E = −d·log(y_top)` satisfies `E' = −(pfaffianChainFn c (d·G))`. This
removes the integrating-factor *hypothesis* from the exp reduce with multiplier `m = d·G`:
`(y_top)' = pf(G)·y_top` by coherence, so `(log y_top)' = pf(G)`, and scaling by `−d`
gives `−d·pf(G) = −pf(d·G)`. Chain-agnostic — the general analog of the exp tower's
`HasDerivAt_logVehExpoAux` restricted to the top level, so it needs only the TOP variable
positive (an exp-type top is positive under `PosExceptLog`), NOT the whole chain. Only the
signed *log* levels of a mixed chain would block a full multi-level vehExpo; the top exp
term is always well-defined. -/
theorem exp_top_integrating_factor {n : Nat} (c : PfaffianChain n) (top : Fin n)
    (G : MultiPoly n) (a b : Real)
    (h_reltop : c.relations top = MultiPoly.mul G (MultiPoly.varY top))
    (hcoh : c.IsCoherentOn a b)
    (hpos : ∀ z, a < z → z < b → 0 < c.evals top z) (d : Nat) :
    ∀ z, a < z → z < b →
      HasDerivAt (fun w => -(MachLib.Real.natCast d) * Real.log (c.evals top w))
        (-(pfaffianChainFn c (MultiPoly.mul (MultiPoly.const (MachLib.Real.natCast d)) G)).eval z) z := by
  intro z hza hzb
  have hy : 0 < c.evals top z := hpos z hza hzb
  have hyne : c.evals top z ≠ 0 := ne_of_gt hy
  have hcoh_top := hcoh z hza hzb top
  -- log chain rule: (log y_top)' = (1/y_top)·(relations top)(z)
  have hlog : HasDerivAt (fun w => Real.log (c.evals top w))
      ((1 / c.evals top z) * MultiPoly.eval (c.relations top) z (c.chainValues z)) z :=
    HasDerivAt_comp Real.log (c.evals top)
      (MultiPoly.eval (c.relations top) z (c.chainValues z)) (1 / c.evals top z) z
      hcoh_top (HasDerivAt_log_pos (c.evals top z) hy)
  -- scale by −natCast d
  have hscaled : HasDerivAt (fun w => -(MachLib.Real.natCast d) * Real.log (c.evals top w))
      (-(MachLib.Real.natCast d)
        * ((1 / c.evals top z) * MultiPoly.eval (c.relations top) z (c.chainValues z))) z := by
    have h := HasDerivAt_mul (fun _ => -(MachLib.Real.natCast d)) (fun w => Real.log (c.evals top w))
      0 ((1 / c.evals top z) * MultiPoly.eval (c.relations top) z (c.chainValues z)) z
      (HasDerivAt_const _ z) hlog
    rw [zero_mul, zero_add] at h
    exact h
  -- the derivative value equals −pf(d·G)
  have hval : -(MachLib.Real.natCast d)
        * ((1 / c.evals top z) * MultiPoly.eval (c.relations top) z (c.chainValues z))
      = -(pfaffianChainFn c (MultiPoly.mul (MultiPoly.const (MachLib.Real.natCast d)) G)).eval z := by
    show -(MachLib.Real.natCast d)
          * ((1 / c.evals top z) * MultiPoly.eval (c.relations top) z (c.chainValues z))
       = -(MultiPoly.eval (MultiPoly.mul (MultiPoly.const (MachLib.Real.natCast d)) G) z (c.chainValues z))
    rw [h_reltop, MultiPoly.eval_mul, MultiPoly.eval_varY, MultiPoly.eval_mul, MultiPoly.eval_const]
    -- goal: −d · ((1/y) · (eval G · (chainValues z top))) = −(d · eval G)
    have hcancel : (1 / c.evals top z)
          * (MultiPoly.eval G z (c.chainValues z) * (c.chainValues z) top)
        = MultiPoly.eval G z (c.chainValues z) := by
      show (1 / c.evals top z) * (MultiPoly.eval G z (c.chainValues z) * c.evals top z)
          = MultiPoly.eval G z (c.chainValues z)
      rw [show (1 / c.evals top z) * (MultiPoly.eval G z (c.chainValues z) * c.evals top z)
            = MultiPoly.eval G z (c.chainValues z) * (c.evals top z * (1 / c.evals top z)) from by mach_ring,
          mul_inv (c.evals top z) hyne]
      mach_ring
    rw [hcancel]; mach_ring
  rw [hval] at hscaled
  exact hscaled

/-- **The exp reduce step with an explicit integrating factor (no IF hypothesis).** For an
exp-type top positive on `(a,b)`, with multiplier `m = d·G` and the reduct
`chainReduce c m p = cTD(p) − d·G·p`, the zeros of `pfaffianChainFn c p` are bounded — given
only that the reduct either vanishes identically or has a bounded zero count. Combines
`exp_top_integrating_factor` (the vehicle `E = −d·log(y_top)`) with `exp_reduce_step_bounded`.
The ONLY remaining input is the reduct's bound — i.e. the mixed-chain measure descent, the
sole open piece of `exp_hard`. -/
theorem exp_reduce_step_concrete {n : Nat} (c : PfaffianChain n) (top : Fin n)
    (G p : MultiPoly n) (a b : Real) (hab : a < b)
    (h_reltop : c.relations top = MultiPoly.mul G (MultiPoly.varY top))
    (hcoh : c.IsCoherentOn a b)
    (hpos : ∀ z, a < z → z < b → 0 < c.evals top z) (d : Nat)
    (hne : ∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c p).eval z ≠ 0)
    (hReduct :
        (∀ z, a < z → z < b →
          (pfaffianChainFn c (chainReduce c (MultiPoly.mul (MultiPoly.const (MachLib.Real.natCast d)) G) p)).eval z = 0)
      ∨ (∃ Nr : Nat, ∀ zeros : List Real, zeros.Nodup →
          (∀ z ∈ zeros, a < z ∧ z < b ∧
            (pfaffianChainFn c (chainReduce c (MultiPoly.mul (MultiPoly.const (MachLib.Real.natCast d)) G) p)).eval z = 0) →
          zeros.length ≤ Nr)) :
    ∃ M : Nat, ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ (pfaffianChainFn c p).eval z = 0) → zeros.length ≤ M :=
  exp_reduce_step_bounded c (MultiPoly.mul (MultiPoly.const (MachLib.Real.natCast d)) G) p a b hab
    (fun w => -(MachLib.Real.natCast d) * Real.log (c.evals top w)) hcoh
    (exp_top_integrating_factor c top G a b h_reltop hcoh hpos d) hne hReduct

end PfaffianGeneralReduce
end MachLib
