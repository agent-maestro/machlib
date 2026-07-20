import MachLib.EMLExplicitBound
import MachLib.MultiVarBucket
import MachLib.SinNotInEML

/-!
# `BoundedZerosBy`, glued across a midpoint — the combinatorial half of a branch-switching bound

Start of an attempt at the "hard" path named in the general-case wall characterization: real
support for `t2 ≤ 0` regions needs a Pfaffian chain that can switch which relation applies across
sub-intervals — confirmed by reading `EMLEncoder.lean`'s `stepCC`/`stepCD` directly (the
reciprocal/log chain relations are only true when the log-argument is strictly positive). That is
a genuinely new construction, not a predicate tweak. This file starts on the PURELY COMBINATORIAL
piece such a strategy would need regardless of how the analytic half is built: given zero-count
bounds on two adjacent sub-intervals, a bound on the whole.

**What's here.** `BoundedZerosBy.glue`: if `f` has at most `K1` zeros on `(a,m)` and at most `K2`
zeros on `(m,b)`, it has at most `K1+K2+1` on `(a,b)` (the `+1` covers `z=m` itself, which neither
open sub-interval counts). Pure list combinatorics — no analysis, no Pfaffian-chain content — via
`length_filter_partition` (`MultiVarBucket.lean`, already built for an unrelated bucketing
argument, reused verbatim here).

**What this is NOT.** Not remotely a working branch-switching bound on its own. The real content
of that strategy — bounding the NUMBER of sign-change sub-intervals a compound `t2` can force (a
zero-count question about `t2` ITSELF, without assuming `t2`'s own validity — genuinely the same
open difficulty this whole arc has circled, recursing one level), and re-deriving each of
`enc_combinedBound`'s several hypotheses (`ChainTagsValid`, `IsTriangular`, `IsCoherentOn`,
`IsAnalyticOnReals`, `LogArgPosOn`, non-degeneracy) FOR EACH sub-interval, for the "reduces to
`eml t1 (const 1)`" tree on the `≤0` pieces — is unstarted. This file is the first, smallest,
most clearly-scoped brick of a genuinely large structure, not a shortcut past it.
-/

namespace MachLib
namespace EMLExplicitBound

open MachLib.Real
open MachLib.MultiVarMod
open MachLib.PfaffianChainMod

/-- A nodup list all of whose elements equal a fixed value has length `≤ 1`. Small standalone
helper for the `z = m` slice of the glue below. -/
theorem length_le_one_of_forall_eq {v : Real} :
    ∀ l : List Real, l.Nodup → (∀ x ∈ l, x = v) → l.length ≤ 1
  | [], _, _ => by simp
  | [_], _, _ => by simp
  | x :: y :: ys, hnd, hmem => by
      exfalso
      have hx : x = v := hmem x (List.mem_cons_self _ _)
      have hy : y = v := hmem y (List.mem_cons_of_mem _ (List.mem_cons_self _ _))
      have hxy : x = y := hx.trans hy.symm
      have hxney : x ≠ y := by
        have := List.nodup_cons.mp hnd
        exact fun h => this.1 (h ▸ List.mem_cons_self _ _)
      exact hxney hxy

/-- **Gluing `BoundedZerosBy` across a midpoint.** Purely combinatorial: any nodup list of zeros
in `(a,b)` splits into those `< m` (bounded by `K1`, via `hK1`), those `= m` (at most one, by
nodup), and those `> m` (bounded by `K2`, via `hK2`). -/
theorem BoundedZerosBy.glue {f : PfaffianFn} {a m b : Real} {K1 K2 : Nat}
    (hK1 : BoundedZerosBy f a m K1) (hK2 : BoundedZerosBy f m b K2) :
    BoundedZerosBy f a b (K1 + K2 + 1) := by
  haveI : DecidableEq Real := fun x y => Classical.propDecidable (x = y)
  intro zeros hnd hz
  have hlo_bound : (zeros.filter (fun z => decide (z < m))).length ≤ K1 := by
    apply hK1 _ (hnd.filter _)
    intro z hzmem
    rw [List.mem_filter] at hzmem
    obtain ⟨hzz, hzlt⟩ := hzmem
    obtain ⟨hza, hzb, hfz⟩ := hz z hzz
    exact ⟨hza, of_decide_eq_true hzlt, hfz⟩
  have hnd_hi : (zeros.filter (fun z => !decide (z < m))).Nodup := hnd.filter _
  have heqm_bound :
      ((zeros.filter (fun z => !decide (z < m))).filter (fun z => decide (z = m))).length ≤ 1 := by
    apply length_le_one_of_forall_eq _ (hnd_hi.filter _)
    intro z hzmem
    rw [List.mem_filter] at hzmem
    exact of_decide_eq_true hzmem.2
  have hgtm_bound : ((zeros.filter (fun z => !decide (z < m))).filter
      (fun z => !decide (z = m))).length ≤ K2 := by
    apply hK2 _ (hnd_hi.filter _)
    intro z hzmem
    rw [List.mem_filter] at hzmem
    obtain ⟨hzhi, hzne⟩ := hzmem
    rw [List.mem_filter] at hzhi
    obtain ⟨hzz, hzge⟩ := hzhi
    obtain ⟨hza, hzb, hfz⟩ := hz z hzz
    have hzgem : ¬ z < m := of_decide_eq_false (by simpa using hzge)
    have hzneqm : z ≠ m := of_decide_eq_false (by simpa using hzne)
    have hzgtm : m < z := by
      rcases lt_total m z with h | h | h
      · exact h
      · exact absurd h.symm hzneqm
      · exact absurd h hzgem
    exact ⟨hzgtm, hzb, hfz⟩
  have hpart_lo : (zeros.filter (fun z => decide (z < m))).length
      + (zeros.filter (fun z => !decide (z < m))).length = zeros.length :=
    length_filter_partition (fun z => decide (z < m)) zeros
  have hpart_hi : ((zeros.filter (fun z => !decide (z < m))).filter (fun z => decide (z = m))).length
      + ((zeros.filter (fun z => !decide (z < m))).filter (fun z => !decide (z = m))).length
      = (zeros.filter (fun z => !decide (z < m))).length :=
    length_filter_partition (fun z => decide (z = m)) (zeros.filter (fun z => !decide (z < m)))
  omega

/-- **The other key fact the branch-switching strategy needs, formalized.** Wherever `t2`'s
value is `≤ 0`, `eml t1 t2` evaluates EXACTLY like `eml t1 (const 1)` — both clamp/compute
`log` to `0` there (`t2 ≤ 0` clamps; `log 1 = 0` is the genuine value), and `eml t1 (const 1)`
is a completely ordinary, always-valid tree (`1 > 0` unconditionally, no clamp involved at all).
This is what would let the "reduce to a validity-free tree on the bad region" half of the
strategy work — PROVIDED the number of `t2 ≤ 0` / `t2 > 0` sub-intervals can itself be bounded
without assuming `t2`'s own validity, which is not attempted here (see file docstring). -/
theorem eml_eval_eq_const_one_of_right_nonpos {t1 t2 : EMLTree} {x : Real}
    (h : t2.eval x ≤ 0) :
    (EMLTree.eml t1 t2).eval x = (EMLTree.eml t1 (EMLTree.const 1)).eval x := by
  show Real.exp (t1.eval x) - Real.log (t2.eval x) = Real.exp (t1.eval x) - Real.log 1
  rw [Real.log_nonpos h, Real.log_one]

end EMLExplicitBound
end MachLib
