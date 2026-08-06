import MachLib.KalmanRangeMultiply

/-!
# Alias decisions — MERGED 2026-08-06, and my cost estimate was wrong

The corpus carried two functions under two names each. **They are now one definition each**, with
the recursion-layer names kept as **transparent aliases**:

| function | canonical | alias | bridge |
|---|---|---|---|
| `P·r/(P+r)` | `GaussianConjugacy.postVar` | `KalmanVarianceRecursion.kalmanVarMap r P := postVar P r` | `kalmanVarMap_eq_postVar` (`rfl`) |
| `P/(P+r)` | `GaussianConjugacy.kGain` | `KalmanEstimateRecursion.kalmanGainMap r P := kGain P r` | `kalmanGainMap_eq_kGain` (`rfl`) |

**The aliases stay because the recursion layer reads naturally with noise first and state second**
(`kalmanVarMap R P`), while the probability layer reads naturally the other way (`postVar σ² r²`).
Two *spellings* of one *definition* is a different thing from two definitions.

## ▸ THE HISTORY, kept because I got the decision wrong first

**I measured the merge and ruled against it.** The measurement:

| name | files | references | `unfold`/`rw` sites |
|---|---:|---:|---:|
| `postVar` | 7 | **114** | **7** |
| `kalmanVarMap` | 6 | 35 | 0 |
| `kGain` | 2 | 8 | 2 |
| `kalmanGainMap` | 2 | 21 | 1 |

and the ruling was *"~150 references and 10 unfolding sites through the MMSE chain — a bad trade
for tidiness."* **The orchestrator overrode it, and the override was right.**

> ### The estimate was wrong because it priced ONE merge strategy: rewriting every call site to the surviving name and swapping argument order.
>
> **Turning the duplicate `def` into an ALIAS achieves the same thing — one definition per
> function — and touches ZERO call sites.** The build went from 585 jobs to 585 jobs with no
> errors, because a `def` that unfolds to the same term is definitionally what the old one was.
> Even the `show` steps inside `kalman_var_map_lipschitz` and `kalman_gain_map_lipschitz`, which
> unfold the definition mid-proof, still elaborate.

**The lesson is not "merge more". It is that a refactor's cost is a property of the STRATEGY, not
of the reference count** — and I had let a reference count stand in for a cost estimate without
checking whether a cheaper strategy existed.

## What is still true from the original analysis

**The real failure mode was PROLIFERATION, not duplication** — the definition sites did not mention
each other, so each layer independently invented the name it needed. **That is fixed by the
cross-references now at all four sites, not by the merge.** Both were worth doing; only one of them
was what I initially proposed.

**Do not add a third name for either function. Bridge to the canonical one.**
-/

namespace MachLib
namespace Real

/-- Both alias bridges in one place. Each closes by `rfl` — now trivially so, since the aliases
*are* the canonical definitions. -/
theorem alias_bridges (r P : Real) :
    kalmanVarMap r P = postVar P r ∧ kalmanGainMap r P = kGain P r :=
  ⟨kalmanVarMap_eq_postVar r P, kalmanGainMap_eq_kGain r P⟩

end Real
end MachLib
