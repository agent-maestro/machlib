import MachLib.WitnessResidualNonMonotonic
import MachLib.WitnessResidualUnboundedBelow

/-! # Closing the loop: `nonMonotonicWitness` is harmless as a candidate `T1`

`WitnessResidualNonMonotonic.lean` built a bounded-above, non-monotonic EML tree
(`nonMonotonicWitness`), decisively refuting "every bounded, non-`RightChildrenSimplePositive`
tree is monotonic". That same file's closing section then proved this specific tree is NOT
bounded below (`nonMonotonicWitness_unbounded_below`). Combined with the mirror closure theorem
in `WitnessResidualUnboundedBelow.lean` (`eml_depth2_witness_of_const_sibling_unbounded_below_T1`,
which requires `c2 > 1` — exactly the residual's own regime), this means `nonMonotonicWitness`
can NEVER survive as the `T1` of a genuine witness-finding counterexample: whatever `S3` and
`c2 > 1` you pick, a witness `∃ x0, 0 < S3.eval x0` falls out for free. No zero-counting needed.

This does not close the residual in general — it only rules out this ONE tree as a candidate.
But it sharpens the standing conjecture: the only territory that can still resist both closure
mechanisms is `T1` bounded in BOTH directions, and `nonMonotonicWitness` — despite being a
genuine, hard-won non-monotonic counterexample — turns out not to live there. -/

namespace MachLib
namespace Real

/-- **`nonMonotonicWitness` cannot be the `T1` of a real counterexample, for any `c2 > 1`.**
Direct instantiation of the unbounded-below closure at `T1 := nonMonotonicWitness`. -/
theorem nonMonotonicWitness_closes_via_unbounded_below {S3 : EMLTree} {c2 : Real} (hc2 : 1 < c2)
    (hsin : ∀ x, (EMLTree.eml nonMonotonicWitness (EMLTree.eml (EMLTree.const c2) S3)).eval x
      = Real.sin x) :
    ∃ x0, 0 < S3.eval x0 :=
  eml_depth2_witness_of_const_sibling_unbounded_below_T1 hc2 nonMonotonicWitness_unbounded_below
    hsin

end Real
end MachLib
