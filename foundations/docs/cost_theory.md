# The SuperBEST cost theory — the proof-backed core

A reader's front door to MachLib's **machine-checked SuperBEST cost theory**. The blog post
[*The Cost Theory Is Complete*](https://monogate.org/blog/cost-theory-complete) stated the results and
validated them on 187 equations; its Lean side was only *sketched* type signatures. This is the part
that is now actually **proved** — `sorryAx`-free, and on the cleanest axiom footprint in the library.

## 1. What this is

A combinatorial cost model for EML expressions: an expression is a tree of operators (unary like
`exp`/`ln`, binary like `add`/`mul`), each carrying its SuperBEST node-cost; `cost` is the additive
node count. Everything here is pure `Nat` — no Real, no field axioms. `MachLib/CostTheory.lean`.

## 2. The machine-checked results

| Result | Statement | Lean |
|---|---|---|
| **T38 — full decomposition** | `Naive = Actual + PatternBonus + SharingDiscount` (`Cost = Naive − Pattern − Sharing`) | `T38.t38_decomposition` |
| **No-Nesting Penalty (T38-NNP)** | composing operators is purely additive — no interface/depth overhead | `no_nesting_penalty`(`_un`) |
| **O(N) single-sum law (T42)** | a flat sum of `N` equal-cost terms costs `α₀·N + cAdd·(N−1)` = `(α₀+3)·N − 3` | `cost_flatSum`, `cost_flatSum_blog` |
| **O(N²) double-sum law** | a nested `N×N` sum (Hopfield `ΣᵢΣⱼ`) is a proven explicit quadratic in `n` | `cost_doubleSum` |
| **Cost monotonicity (P)** | wrapping a subtree in an operator never lowers cost | `le_cost_un`/`le_cost_bin_left`/`_right` |

**T38 is a theorem, not a tautology.** The two saving mechanisms are defined *independently* by
structural recursion over a body tree with `ref` leaves (the common-subexpression mechanism) whose
operators each carry a compound `nodeCost` *and* a `patSave` (the compound-operator mechanism); the
crux lemma `bNaive_eq` (induction on the body) then proves they account for exactly the naive-vs-actual
gap. A worked example checks by `decide` (`naive 25 = actual 15 + pattern 4 + sharing 6`).

### Axiom footprint

`#print axioms` on every result above shows **only `propext` + `Quot.sound`** (the Lean-core minimum
from `List`/`Nat`) — no MachLib field axioms, no `sorryAx`. The companion well-foundedness keystone
`MachLib/LexProd.lean` (`lexProd_wf`, `natTripleLex_wf`) depends on **no axioms at all** (pure
constructive well-founded induction).

## 3. What this does NOT claim

- The **four structural classes** (C < B < A < D by `exp`/`ln` signature) have a strict *mean*-cost
  ordering — that is an **empirical corpus statistic** over the 187-equation benchmark, not a theorem
  about the cost function, so it is *not* formalised here (it would be dressing up a statistic).
- **T41-ISO** (different scientific fields sharing a minimal DAG topology) reduces, once both sides are
  minimised, to "same shape ⇒ same cost" — but the **minimiser itself is not formalised**, so the
  interesting content (that two *different-looking* formulas minimise to the same DAG) is out of scope.
- The **Quadratic Ceiling Conjecture (T42-QCC)** — no closed-form scientific formula exceeds O(N²) — is
  validated empirically and remains an **open conjecture**.
- This is the cost-*algebra* core. It does not formalise the SuperBEST *routing table* itself (the
  per-operator optimal node counts), which are established by exhaustive search in `eml-cost`.

## 4. Check it yourself

```bash
cd foundations && lake build MachLib.CostTheory MachLib.LexProd

printf 'import MachLib.CostTheory\nimport MachLib.LexProd\nopen MachLib.CostTheory\n#print axioms T38.t38_decomposition\n#print axioms cost_doubleSum\n#print axioms MachLib.LexProd.lexProd_wf\n' > /tmp/chk.lean
lake env lean /tmp/chk.lean    # -> propext/Quot only (CostTheory); no axioms (lexProd_wf); no sorryAx

# library-wide integrity gate (fails red on any non-allowlisted sorryAx):
tools/check.sh
```

## 5. Status

The cost-algebra core of "The Cost Theory Is Complete" is **proof-backed**: T38 (full decomposition),
the No-Nesting Penalty, the O(N) and O(N²) sum laws, and cost monotonicity — all `sorryAx`-free,
propext/Quot-only, integrity-gated. The remaining published claims (four-class ordering, T41-ISO, QCC)
are honestly out of formalisation scope above — they are empirical, minimiser-dependent, or open.
