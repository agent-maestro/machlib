import MachLib.WitnessResidualDirectCrossingUnboundedAbove
import MachLib.WitnessResidualNonMonotonic
import MachLib.WitnessResidualUnboundedBelow
import MachLib.Linarith

/-! # The "wrap once more" lemma — generalizing `nonMonotonicWitness`'s unboundedness proof

`nonMonotonicWitness_unbounded_below` (`WitnessResidualNonMonotonic.lean`) proved ONE specific
tree — `A := var`, `P := eml var (const 1)`, `c := 1+1` — is unbounded below, by an explicit
closed-form witness construction. This file lifts that construction to arbitrary `A` and `P`,
sidestepping the need for a general "EML tree continuous/bounded near a point" theory (not built
in this codebase) by using an EXPLICIT, checkable hypothesis instead: a fixed bound on `A` along
the SAME witness path the construction already uses (`x_d := log(log c + d)`, `d → 0⁺`).

**Why this matters.** `WitnessResidualDirectCrossingUnboundedAbove.lean` showed `eml P (eml var
(const c))` (crossing directly under the root) is unbounded above for ANY `P`. This file shows
that wrapping ONE more layer around it (`eml A (eml P (eml var (const c)))`, matching
`nonMonotonicWitness`'s own two-level shape exactly) is unbounded BELOW, for ANY `A` that stays
bounded along the witness path and ANY `P` at all. Combined, an entire PARAMETRIZED FAMILY of
"crossing wrapped exactly twice" trees are now known to be unbounded below — not just the one
hardcoded instance. The sanity-check corollary at the end confirms this by re-deriving
`nonMonotonicWitness`'s own unboundedness result from the general theorem via direct
instantiation (defeq, not just "similar"). -/

namespace MachLib
namespace Real

open EMLTree

/-- Core algebraic step, fully abstracted over the specific real numbers involved (fought free of
`x_d`'s giant nested expression, mirroring the session's established "extract a small general
helper" pattern). Given `exp(Ax) ≤ K'` and `d` small enough that `log(-(log d))` exceeds `K'-M`,
concludes the full "wrap" expression is below `M`. -/
theorem core_wrap_bound {Ax Px d K' M : Real} (hAK : Real.exp Ax ≤ K')
    (hd0 : 0 < d) (hd1 : d < 1) (hbig : K' - M < Real.log (-(Real.log d))) :
    Real.exp Ax - Real.log (Real.exp Px - Real.log d) < M := by
  have hnegdpos : 0 < -(Real.log d) := neg_pos_of_neg (log_neg_of_lt_one hd0 hd1)
  have hBgt : -(Real.log d) < Real.exp Px - Real.log d := by
    have h := sub_lt_sub_right_of_lt (r := Real.log d) (Real.exp_pos Px)
    rw [sub_def, zero_add] at h
    exact h
  have hlogB : Real.log (-(Real.log d)) < Real.log (Real.exp Px - Real.log d) :=
    log_lt_log hnegdpos hBgt
  have hchain : K' - M < Real.log (Real.exp Px - Real.log d) := lt_trans_ax hbig hlogB
  have hK'subM : K' - Real.log (Real.exp Px - Real.log d) < M := by
    have h := sub_lt_sub_left_local K' hchain
    have e : K' - (K' - M) = M := sub_self_sub_local K' M
    rwa [e] at h
  have hexpAxsubB : Real.exp Ax - Real.log (Real.exp Px - Real.log d)
      ≤ K' - Real.log (Real.exp Px - Real.log d) := by
    rcases (le_iff_lt_or_eq _ _).mp hAK with h | h
    · exact le_of_lt (sub_lt_sub_right_of_lt (r := Real.log (Real.exp Px - Real.log d)) h)
    · exact le_of_eq (by rw [h])
  exact lt_of_le_of_lt hexpAxsubB hK'subM

/-- **The general "wrap once more" theorem.** For `c > 1`: if `A` stays bounded above by some
fixed `K` along the crossing's witness path `x_d := log(log c + d)` (`d ∈ (0,1)`), then
`eml A (eml P (eml var (const c)))` is unbounded BELOW — for ANY `P` at all (only
`exp(P.eval x) > 0` is ever used, same as the direct-crossing lemma). Same explicit closed-form
witness technique throughout: choosing `d` small enough forces the inner crossing's blow-up
(`-log d`) to dominate `A`'s bounded contribution, using `core_wrap_bound` for the final
algebra. -/
theorem eml_unbounded_below_of_wrapped_crossing {A P : EMLTree} {c K : Real} (hc : 1 < c)
    (hAbdd : ∀ d : Real, 0 < d → d < 1 → A.eval (Real.log (Real.log c + d)) ≤ K) :
    ∀ M : Real, ∃ x,
      (EMLTree.eml A (EMLTree.eml P (EMLTree.eml EMLTree.var (EMLTree.const c)))).eval x < M := by
  intro M
  have hlogcpos : 0 < Real.log c := log_pos_of_gt_one hc
  have hEpos : 0 < Real.exp (Real.exp K - M) := Real.exp_pos _
  have hexpneg : -(Real.exp (Real.exp K - M)) - Real.log c < 0 := by
    have h1 : -(Real.exp (Real.exp K - M)) < 0 := neg_neg_of_pos hEpos
    have h2 := sub_lt_sub_right_of_lt (r := Real.log c) h1
    have h3 : (0 : Real) - Real.log c < 0 := by
      rw [sub_def, zero_add]
      exact neg_neg_of_pos hlogcpos
    exact lt_trans_ax h2 h3
  have hd0 : 0 < Real.exp (-(Real.exp (Real.exp K - M)) - Real.log c) := Real.exp_pos _
  have hd1 : Real.exp (-(Real.exp (Real.exp K - M)) - Real.log c) < 1 := by
    have h := Real.exp_lt hexpneg
    rwa [Real.exp_zero] at h
  have hsum_pos : 0 < Real.log c + Real.exp (-(Real.exp (Real.exp K - M)) - Real.log c) :=
    add_pos hlogcpos hd0
  refine ⟨Real.log (Real.log c + Real.exp (-(Real.exp (Real.exp K - M)) - Real.log c)), ?_⟩
  have hexp_x : Real.exp (Real.log (Real.log c + Real.exp (-(Real.exp (Real.exp K - M)) - Real.log c)))
      = Real.log c + Real.exp (-(Real.exp (Real.exp K - M)) - Real.log c) := Real.exp_log hsum_pos
  have hDeval : (EMLTree.eml EMLTree.var (EMLTree.const c)).eval
      (Real.log (Real.log c + Real.exp (-(Real.exp (Real.exp K - M)) - Real.log c)))
      = Real.exp (-(Real.exp (Real.exp K - M)) - Real.log c) := by
    show Real.exp (Real.log (Real.log c + Real.exp (-(Real.exp (Real.exp K - M)) - Real.log c)))
        - Real.log c = Real.exp (-(Real.exp (Real.exp K - M)) - Real.log c)
    rw [hexp_x]
    mach_ring
  have hABval := hAbdd (Real.exp (-(Real.exp (Real.exp K - M)) - Real.log c)) hd0 hd1
  have hexpA_le : Real.exp (A.eval (Real.log (Real.log c
        + Real.exp (-(Real.exp (Real.exp K - M)) - Real.log c)))) ≤ Real.exp K :=
    exp_monotone hABval
  show Real.exp (A.eval (Real.log (Real.log c + Real.exp (-(Real.exp (Real.exp K - M)) - Real.log c))))
      - Real.log ((EMLTree.eml P (EMLTree.eml EMLTree.var (EMLTree.const c))).eval
        (Real.log (Real.log c + Real.exp (-(Real.exp (Real.exp K - M)) - Real.log c)))) < M
  have hBval : (EMLTree.eml P (EMLTree.eml EMLTree.var (EMLTree.const c))).eval
      (Real.log (Real.log c + Real.exp (-(Real.exp (Real.exp K - M)) - Real.log c)))
      = Real.exp (P.eval (Real.log (Real.log c
          + Real.exp (-(Real.exp (Real.exp K - M)) - Real.log c))))
        - Real.log (Real.exp (-(Real.exp (Real.exp K - M)) - Real.log c)) := by
    show Real.exp (P.eval (Real.log (Real.log c
          + Real.exp (-(Real.exp (Real.exp K - M)) - Real.log c))))
        - Real.log ((EMLTree.eml EMLTree.var (EMLTree.const c)).eval
          (Real.log (Real.log c + Real.exp (-(Real.exp (Real.exp K - M)) - Real.log c))))
      = _
    rw [hDeval]
  rw [hBval]
  have hlogd : Real.log (Real.exp (-(Real.exp (Real.exp K - M)) - Real.log c))
      = -(Real.exp (Real.exp K - M)) - Real.log c := Real.log_exp _
  have hbig : Real.exp K - M
      < Real.log (-(Real.log (Real.exp (-(Real.exp (Real.exp K - M)) - Real.log c)))) := by
    rw [hlogd]
    have hnegneg : -(-(Real.exp (Real.exp K - M)) - Real.log c)
        = Real.exp (Real.exp K - M) + Real.log c := by mach_ring
    rw [hnegneg]
    have hElt : Real.exp (Real.exp K - M) < Real.exp (Real.exp K - M) + Real.log c := by
      have h := add_lt_add_left hlogcpos (Real.exp (Real.exp K - M))
      rwa [add_zero] at h
    have h := log_lt_log hEpos hElt
    rwa [Real.log_exp] at h
  exact core_wrap_bound hexpA_le hd0 hd1 hbig

/-- **Sanity check**: instantiating the general theorem at `A := var`, `P := eml var (const 1)`,
`c := 1+1` reproduces `nonMonotonicWitness_unbounded_below`'s exact conclusion (`eml A (eml P
(eml var (const c)))` unfolds definitionally to `nonMonotonicWitness`) — confirming the
generalization is equivalent to, not merely similar to, the earlier hand-built result. -/
theorem nonMonotonicWitness_unbounded_below_via_general :
    ∀ M : Real, ∃ x, nonMonotonicWitness.eval x < M :=
  eml_unbounded_below_of_wrapped_crossing (A := EMLTree.var)
    (P := EMLTree.eml EMLTree.var (EMLTree.const 1)) (c := 1 + 1)
    (K := Real.log (Real.log (1 + 1) + 1)) one_lt_one_add_one
    (fun d hd0 hd1 => by
      show Real.log (Real.log (1 + 1) + d) ≤ Real.log (Real.log (1 + 1) + 1)
      have hlogcpos : 0 < Real.log (1 + 1) := nonMonotonicWitness_log2_pos
      have hlt : Real.log (1 + 1) + d < Real.log (1 + 1) + 1 :=
        add_lt_add_left hd1 (Real.log (1 + 1))
      have hpos : 0 < Real.log (1 + 1) + d := add_pos hlogcpos hd0
      exact le_of_lt (log_lt_log hpos hlt))

/-- **The combined family closure.** For ANY `A` bounded along the witness path, ANY `P`, ANY
`c > 1`, `c2 > 1`, `S3`: a tree shaped `eml (eml A (eml P (eml var (const c)))) (eml (const c2)
S3)` — the ENTIRE "crossing wrapped exactly twice" family, matching `nonMonotonicWitness`'s own
shape but for arbitrary `A`/`P`/`c` — can never agree with `sin` unless `S3` is positive
somewhere. Direct combination with the existing unbounded-below closure. -/
theorem eml_depth2_witness_of_wrapped_crossing_T1 {A P S3 : EMLTree} {c c2 K : Real}
    (hc : 1 < c) (hc2 : 1 < c2)
    (hAbdd : ∀ d : Real, 0 < d → d < 1 → A.eval (Real.log (Real.log c + d)) ≤ K)
    (hsin : ∀ x, (EMLTree.eml (EMLTree.eml A (EMLTree.eml P (EMLTree.eml EMLTree.var (EMLTree.const c))))
      (EMLTree.eml (EMLTree.const c2) S3)).eval x = Real.sin x) :
    ∃ x0, 0 < S3.eval x0 :=
  eml_depth2_witness_of_const_sibling_unbounded_below_T1 hc2
    (eml_unbounded_below_of_wrapped_crossing hc hAbdd) hsin

end Real
end MachLib
