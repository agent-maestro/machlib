import MachLib.EMLSmoothness
import MachLib.EMLZeroCrossingDomainSplit

/-! # Any tree with a direct crossing as its right child is unbounded above — for ANY left child

`nonMonotonicWitness`'s own inner subtree `B := eml (eml var (const 1)) (eml var (const 2))`
diverges to `+∞` near the crossing point `x0 = log(log 2)` of its right child `D := eml var
(const 2)`. Nothing about that divergence actually used `B`'s specific left child
`eml var (const 1)` — it only used `exp(anything) > 0`. This file generalizes: `eml P D` is
unbounded above for ANY `P` at all, as long as `D`'s crossing (`eml var (const c)`, `c > 1`) is
directly `eml P`'s right child.

**Why this matters for the residual.** Combined with the already-existing
`eml_depth2_witness_of_const_sibling_unbounded_T1` (any `T1` unbounded above closes for free,
any `c2`), this shows the ENTIRE FAMILY of trees shaped `eml P (eml var (const c))` — for ANY
`P` and ANY `c > 1` — can never be the `T1` of a genuine witness-finding counterexample. Not one
hardcoded instance; the whole shape, parametrized. This is the first piece of a bigger structural
question (does EVERY EML tree containing a genuine zero-crossing somewhere have to be unbounded
in SOME direction, at whatever depth the crossing sits?) — this file settles it for crossings
sitting DIRECTLY under the root, leaving crossings buried deeper (like `nonMonotonicWitness`'s,
two levels down) for future work: the mechanism there needs tracking a LOCAL blow-up near a
specific point combined with the outer wrapper's local boundedness there, which is a genuinely
bigger lift (needs some notion of "EML tree continuous/bounded near a point") not attempted
here. -/

namespace MachLib
namespace Real

open EMLTree

/-- **Any tree with a direct crossing as its right child is unbounded above, for ANY left
child.** `eml P (eml var (const c))` for `c > 1`: the right child crosses zero at
`x0 = log(log c)`. For `x` slightly above `x0`, choosing `x := log(log c + d)` for small `d > 0`
makes `D.eval x = d` exactly (same explicit-witness technique as
`nonMonotonicWitness_unbounded_below`); this forces `-log(D.eval x) = -log d`, arbitrarily
large as `d → 0⁺`, and `exp(P.eval x) > 0` ALWAYS (`Real.exp_pos`, regardless of `P`'s shape)
never subtracts enough to stop the blow-up. -/
theorem eml_unbounded_above_of_direct_crossing {P : EMLTree} {c : Real} (hc : 1 < c) :
    ∀ M : Real, ∃ x, M < (EMLTree.eml P (EMLTree.eml EMLTree.var (EMLTree.const c))).eval x := by
  intro M
  have hlogcpos : 0 < Real.log c := log_pos_of_gt_one hc
  have hdpos : 0 < Real.exp (-M) := Real.exp_pos _
  have hsum_pos : 0 < Real.log c + Real.exp (-M) := add_pos hlogcpos hdpos
  refine ⟨Real.log (Real.log c + Real.exp (-M)), ?_⟩
  have hexp_x : Real.exp (Real.log (Real.log c + Real.exp (-M)))
      = Real.log c + Real.exp (-M) := Real.exp_log hsum_pos
  have hDeval : (EMLTree.eml EMLTree.var (EMLTree.const c)).eval
      (Real.log (Real.log c + Real.exp (-M))) = Real.exp (-M) := by
    show Real.exp (Real.log (Real.log c + Real.exp (-M))) - Real.log c = Real.exp (-M)
    rw [hexp_x]
    mach_ring
  show M < Real.exp (P.eval (Real.log (Real.log c + Real.exp (-M))))
      - Real.log ((EMLTree.eml EMLTree.var (EMLTree.const c)).eval
        (Real.log (Real.log c + Real.exp (-M))))
  rw [hDeval, Real.log_exp]
  have hPpos : 0 < Real.exp (P.eval (Real.log (Real.log c + Real.exp (-M)))) := Real.exp_pos _
  have h := add_lt_add_left hPpos M
  have e : Real.exp (P.eval (Real.log (Real.log c + Real.exp (-M)))) - -M
      = M + Real.exp (P.eval (Real.log (Real.log c + Real.exp (-M)))) := by mach_ring
  rw [e]
  rwa [add_zero] at h

/-- **The combined family closure.** For ANY `P`, ANY `c > 1` (the crossing threshold), and ANY
`c2`, `S3`: a tree shaped `eml (eml P (eml var (const c))) (eml (const c2) S3)` can never agree
with `sin` unless `∃x0, 0 < S3.eval x0`. Direct combination of the lemma above with the
already-existing unbounded-above closure — no zero-counting, no restriction on `c2`, and no
restriction on `P` at all. -/
theorem eml_depth2_witness_of_direct_crossing_T1 {P S3 : EMLTree} {c c2 : Real} (hc : 1 < c)
    (hsin : ∀ x, (EMLTree.eml (EMLTree.eml P (EMLTree.eml EMLTree.var (EMLTree.const c)))
      (EMLTree.eml (EMLTree.const c2) S3)).eval x = Real.sin x) :
    ∃ x0, 0 < S3.eval x0 :=
  eml_depth2_witness_of_const_sibling_unbounded_T1
    (eml_unbounded_above_of_direct_crossing hc) hsin

end Real
end MachLib
