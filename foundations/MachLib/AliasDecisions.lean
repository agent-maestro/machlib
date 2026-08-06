import MachLib.KalmanRangeMultiply

/-!
# Alias decisions — four names, two functions, and the ruling is NOT to merge

The corpus carries two functions under two names each:

| function | names | bridged by |
|---|---|---|
| `P·r/(P+r)` | `GaussianConjugacy.postVar` · `KalmanVarianceRecursion.kalmanVarMap` | `kalmanVarMap_eq_postVar` (`rfl`) |
| `P/(P+r)` | `GaussianConjugacy.kGain` · `KalmanEstimateRecursion.kalmanGainMap` | `kalmanGainMap_eq_kGain` (`rfl`) |

Each pair is the **same function with the arguments swapped**, and both bridges close by `rfl`.

## The measurement

| name | files | references | `unfold`/`rw` sites |
|---|---:|---:|---:|
| `postVar` | 7 | **114** | **7** |
| `kalmanVarMap` | 6 | 35 | 0 |
| `kGain` | 2 | 8 | 2 |
| `kalmanGainMap` | 2 | 21 | 1 |

**A merge touches ~150 references and 10 unfolding sites, several of them inside the MMSE chain**
(`posterior_mean_mmse`, `postMean_eq_kalman`, the recursion files) — the flagship claim.

## ▸ THE RULING: do not merge. Cross-reference instead.

**The safety a merge would buy is already bought.** The risk of two names is that something proved
about one fails to apply to the other; **the `rfl` bridges eliminate exactly that** — any result
transfers in a single rewrite.

**What a merge would buy is tidiness. What it would cost is a 150-reference refactor through the
project's flagship proof.** That is a bad trade, and it stays a bad trade until some concrete
proof is actually blocked by the split. **None is.**

### What the real failure mode was, and what fixes it

**The duplication did not arise from a decision — it arose because the definition sites did not
mention each other.** Someone in the probability layer wrote `postVar`; someone in the recursion
layer needed the same map and wrote `kalmanVarMap`, with no way to discover the first. **That is a
proliferation problem, not a duplication problem, and merging does not fix it — cross-referencing
does.**

All four definition sites now name their twin, name the bridge, and say **"do not add a third."**

> **Revisit this ruling if, and only if, a proof is actually blocked by the split.** Tidiness is not
> a reason to refactor a flagship chain.

This file exists so the decision is recorded once and not re-litigated by the next reader who
notices the redundancy. It contains no theorems on purpose.
-/

namespace MachLib
namespace Real

/-- Both alias bridges in one place, so a reader who finds this file can act on it immediately.
Restates `kalmanVarMap_eq_postVar` and `kalmanGainMap_eq_kGain` as a single pair. -/
theorem alias_bridges (r P : Real) :
    kalmanVarMap r P = postVar P r ∧ kalmanGainMap r P = kGain P r :=
  ⟨kalmanVarMap_eq_postVar r P, kalmanGainMap_eq_kGain r P⟩

end Real
end MachLib
