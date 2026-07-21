import MachLib.EMLSmoothness
import MachLib.Trig
import MachLib.WitnessResidualBoundedNonConstant

/-! # A free witness whenever `T1` is strictly monotonic — generalizing the injectivity trick

`WitnessResidualBoundedNonConstant.lean`'s `boundedNonConstantWitness_ne_shifted_sin_target`
showed one SPECIFIC bounded tree can never satisfy the witness-finding collapsed equation,
using an injectivity-vs-periodicity argument. That argument never actually used anything
specific to the tree — only that it was strictly monotonic. This file lifts it to the same
"free closure" family as `eml_depth2_witness_of_const_sibling_unbounded_T1` (unbounded above)
and `eml_depth2_witness_of_const_sibling_unbounded_below_T1` (unbounded below): ANY strictly
monotonic `T1` closes, unconditionally on `c2` (no `c2 > 1` needed even — this mechanism is
even more general than the two unboundedness ones on that front, since it never inspects
`c2`'s value at all, only that the collapsed target is `2π`-periodic).

**Net effect on the residual.** Combined with all three closures, the witness-finding residual's
surviving open territory narrows to exactly: `T1` bounded in BOTH directions, non-constant,
non-`RightChildrenSimplePositive`, AND not strictly monotonic in either direction. This is now a
fully general characterization (not "no known closure covers this specific tree", but "no known
closure covers ANY tree with these four properties") — matching exactly the shape of
`nonMonotonicWitness` (bounded above, not bounded below, non-monotonic), which is why THAT
specific tree needed the heavier zero-counting machinery and could not be closed for free. -/

namespace MachLib
namespace Real

open EMLTree

/-- **A free witness for `S2` constant, ANY `c2`, whenever `T1` is strictly monotonic.** `T1`
strictly monotonic (either direction) is injective. If `S3` collapsed to `≤ 0` everywhere, the
usual collapse gives `exp(T1.eval x) - c2 = sin x` for ALL `x`; evaluating at `x = 0` and
`x = π` (`sin 0 = sin π = 0`) forces `exp(T1.eval 0) = exp(T1.eval π) = c2`, hence (via `exp`'s
injectivity, itself from `exp_lt`) `T1.eval 0 = T1.eval π` — directly contradicting strict
monotonicity since `0 < π`. No zero-counting, no Pfaffian chain, no target-shift trick — and,
notably, no `c2` constraint at all (unlike the two unboundedness closures, which both need
`c2 > 1` in one direction or the other). -/
theorem eml_depth2_witness_of_const_sibling_strictMono_T1 {T1 S3 : EMLTree} {c2 : Real}
    (hmono : (∀ x y : Real, x < y → T1.eval x < T1.eval y) ∨
             (∀ x y : Real, x < y → T1.eval y < T1.eval x))
    (hsin : ∀ x, (EMLTree.eml T1 (EMLTree.eml (EMLTree.const c2) S3)).eval x = Real.sin x) :
    ∃ x0, 0 < S3.eval x0 := by
  refine Classical.byContradiction (fun hcon => ?_)
  have hallle : ∀ x, S3.eval x ≤ 0 := by
    intro x
    rcases lt_total 0 (S3.eval x) with h | h | h
    · exact absurd ⟨x, h⟩ hcon
    · exact le_of_eq h.symm
    · exact le_of_lt h
  have hcollapse : ∀ x, Real.exp (T1.eval x) - c2 = Real.sin x := by
    intro x
    have hlog0 : Real.log (S3.eval x) = 0 := Real.log_nonpos (hallle x)
    have hNeval : (EMLTree.eml (EMLTree.const c2) S3).eval x = Real.exp c2 := by
      show Real.exp c2 - Real.log (S3.eval x) = Real.exp c2
      rw [hlog0, sub_zero]
    have h1 : Real.exp (T1.eval x) -
        Real.log ((EMLTree.eml (EMLTree.const c2) S3).eval x) = Real.sin x := hsin x
    rwa [hNeval, Real.log_exp] at h1
  have h0 : Real.exp (T1.eval 0) - c2 = 0 := by rw [hcollapse 0, Real.sin_zero]
  have hpi : Real.exp (T1.eval Real.pi) - c2 = 0 := by rw [hcollapse Real.pi, Real.sin_pi]
  have h0' : Real.exp (T1.eval 0) = c2 := by
    have e : Real.exp (T1.eval 0) - c2 + c2 = Real.exp (T1.eval 0) := by mach_ring
    rw [h0, zero_add] at e
    exact e.symm
  have hpi' : Real.exp (T1.eval Real.pi) = c2 := by
    have e : Real.exp (T1.eval Real.pi) - c2 + c2 = Real.exp (T1.eval Real.pi) := by mach_ring
    rw [hpi, zero_add] at e
    exact e.symm
  have heqexp : Real.exp (T1.eval 0) = Real.exp (T1.eval Real.pi) := h0'.trans hpi'.symm
  have heq : T1.eval 0 = T1.eval Real.pi := by
    rcases lt_total (T1.eval 0) (T1.eval Real.pi) with h | h | h
    · have hc := Real.exp_lt h
      rw [heqexp] at hc
      exact absurd hc (lt_irrefl_ax _)
    · exact h
    · have hc := Real.exp_lt h
      rw [← heqexp] at hc
      exact absurd hc (lt_irrefl_ax _)
  rcases hmono with hinc | hdec
  · have h2 := hinc 0 Real.pi Real.pi_pos
    rw [heq] at h2
    exact lt_irrefl_ax _ h2
  · have h2 := hdec 0 Real.pi Real.pi_pos
    rw [heq] at h2
    exact lt_irrefl_ax _ h2

/-- **Sanity check**: this general theorem reproduces the earlier hand-built, tree-specific
closure (`boundedNonConstantWitness_ne_shifted_sin_target`, two rounds ago) directly from the
raw tree-agreement hypothesis, confirming the generalization is equivalent to — not merely
similar to — the original result. -/
theorem boundedNonConstantWitness_closes_via_strictMono {c : Real} (hc : 1 < c)
    (hc1 : Real.log c < 1) {S3 : EMLTree} {c2 : Real}
    (hsin : ∀ x, (EMLTree.eml (boundedNonConstantWitness c)
      (EMLTree.eml (EMLTree.const c2) S3)).eval x = Real.sin x) :
    ∃ x0, 0 < S3.eval x0 :=
  eml_depth2_witness_of_const_sibling_strictMono_T1
    (Or.inr (boundedNonConstantWitness_strictAnti hc hc1)) hsin

end Real
end MachLib
