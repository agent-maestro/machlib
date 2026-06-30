/-!
# SuperBEST cost theory — the No-Nesting Penalty and the O(N) sum law, machine-checked

The SuperBEST cost theory ("The Cost Theory Is Complete", monogate.org/blog/cost-theory-complete)
was proved on paper and validated on 187 equations, but its Lean side was only *sketched* type
signatures. This module gives the first **machine-checked, sorryAx-free** proofs of two of its named
results, over a minimal combinatorial cost model (pure `Nat`; no Real, no MachLib axioms — `#print
axioms` shows only `propext`/`Quot`-level core).

The model: an EML expression is a tree of operators (unary like `exp`/`ln`, binary like `add`/`mul`),
each carrying its SuperBEST node-cost; a leaf carries its own cost. `cost` is the additive node count.
The cost theory's content is that this *additive* model — operators have a uniform single-output
interface, so composition needs no adapter nodes — already implies the headline structural facts.

Scope (honest): this is the *cost-algebra* core (No-Nesting Penalty `T38-NNP`, the single-sum law
`T42`). The full `T38` decomposition `Cost = Naive − Sharing − Pattern`, the four-class ordering, and
the `T41-ISO` isomorphism classes are larger targets left for follow-up; this turns the two
self-contained named theorems from prose into proof.
-/

namespace MachLib.CostTheory

/-- An EML expression tree for cost accounting: a `leaf` (its own cost), a `un`ary operator (its
node-cost + one child), or a `bin`ary operator (its node-cost + two children). Covers the F₁₆
operators, which are all unary (`exp`, `ln`, `neg`, `recip`, `sqrt`) or binary (`add`, `sub`, `mul`,
`div`, `pow`). -/
inductive CostTree where
  | leaf : Nat → CostTree
  | un   : Nat → CostTree → CostTree
  | bin  : Nat → CostTree → CostTree → CostTree

/-- The additive node count: an operator costs its own node-cost plus the cost of its subtrees. The
*additivity* is the cost model — a uniform single-output interface, no adapter/depth overhead. -/
def cost : CostTree → Nat
  | .leaf c   => c
  | .un c a   => c + cost a
  | .bin c a b => c + cost a + cost b

/-- **No-Nesting Penalty (T38-NNP), binary form.** Composing `O₁` on top of `O₂(A,B)` and `C` costs
exactly `c_{O₁} + c_{O₂} + Cost(A) + Cost(B) + Cost(C)` — no interface, adapter, or depth penalty. -/
theorem no_nesting_penalty (c₁ c₂ : Nat) (A B C : CostTree) :
    cost (.bin c₁ (.bin c₂ A B) C) = c₁ + c₂ + cost A + cost B + cost C := by
  simp only [cost]; omega

/-- **No-Nesting Penalty, unary form.** `Cost(O₁(O₂(A))) = c_{O₁} + c_{O₂} + Cost(A)`. -/
theorem no_nesting_penalty_un (c₁ c₂ : Nat) (A : CostTree) :
    cost (.un c₁ (.un c₂ A)) = c₁ + c₂ + cost A := by
  simp only [cost]; omega

/-- A flat sum of `n+1` equal-cost terms (each `α₀`), combined with binary `add` nodes of cost
`cAdd`. `flatSum cAdd α₀ 0` is a single term; each `succ` adds one more term via one `add`. -/
def flatSum (cAdd α₀ : Nat) : Nat → CostTree
  | 0     => .leaf α₀
  | n + 1 => .bin cAdd (flatSum cAdd α₀ n) (.leaf α₀)

/-- **The single-sum law (T42), exact `Nat` form.** A flat sum of `N = n+1` equal-cost terms costs
`α₀·(n+1) + cAdd·n` (terms + the `n` joining `add` nodes). With `cAdd = 3` this is the blog's
`(α₀+3)·N − 3`; see `cost_flatSum_blog`. Proof: induction on `n`. -/
theorem cost_flatSum (cAdd α₀ n : Nat) :
    cost (flatSum cAdd α₀ n) = α₀ * (n + 1) + cAdd * n := by
  induction n with
  | zero => simp [flatSum, cost]
  | succ k ih =>
    simp only [flatSum, cost, ih, Nat.mul_succ]
    omega

/-- **The blog headline form `(α₀+3)·N − 3`** for `N ≥ 1` terms with `add`-cost `3` — a corollary of
`cost_flatSum`. (E.g. Shannon entropy / Fourier: `α₀+3 = 7`; pharmacokinetic sums: `11`.) -/
theorem cost_flatSum_blog (α₀ N : Nat) (hN : 1 ≤ N) :
    cost (flatSum 3 α₀ (N - 1)) = (α₀ + 3) * N - 3 := by
  rw [cost_flatSum, Nat.sub_add_cancel hN, Nat.add_mul]
  -- goal: α₀*N + 3*(N-1) = α₀*N + 3*N - 3  (α₀*N is a shared opaque atom; rest is linear)
  omega

/-- Sum of `n+1` copies of an arbitrary subtree `t`, via binary `add` nodes of cost `cAdd`.
Generalises `flatSum` (the `t = leaf α₀` case) so a *summand* can itself be a whole expression. -/
def flatSumTree (cAdd : Nat) (t : CostTree) : Nat → CostTree
  | 0     => t
  | n + 1 => .bin cAdd (flatSumTree cAdd t n) t

/-- Cost of a flat sum of `n+1` copies of `t`: `cost t · (n+1) + cAdd · n`. -/
theorem cost_flatSumTree (cAdd : Nat) (t : CostTree) (n : Nat) :
    cost (flatSumTree cAdd t n) = cost t * (n + 1) + cAdd * n := by
  induction n with
  | zero => simp [flatSumTree, cost]
  | succ k ih => simp only [flatSumTree, cost, ih, Nat.mul_succ]; omega

/-- A nested double sum: `N=n+1` outer terms, each an inner flat sum of `N` equal-cost (`α₀`) terms —
the pairwise-interaction / Hopfield-energy shape `Σᵢ Σⱼ`. -/
def doubleSum (cAdd α₀ n : Nat) : CostTree :=
  flatSumTree cAdd (flatSumTree cAdd (.leaf α₀) n) n

/-- **The O(N²) double-sum law (exact).** A nested `N×N` sum (`N=n+1`) costs
`(α₀·N + cAdd·n)·N + cAdd·n` — a proven explicit **quadratic** in `n` (a `(linear)·N` product). Its
closed form is `(α₀+cAdd)·N² − cAdd` (with `cAdd=3`, the blog's `(α₀+3)·N² − 3`): expand the product
and fold `cAdd·n + cAdd = cAdd·N`. We state the exact cost — that is the O(N²) content; the factored
form is `Nat` algebra (no `ring` in a Mathlib-free setting). -/
theorem cost_doubleSum (cAdd α₀ n : Nat) :
    cost (doubleSum cAdd α₀ n) = (α₀ * (n + 1) + cAdd * n) * (n + 1) + cAdd * n := by
  unfold doubleSum
  rw [cost_flatSumTree, cost_flatSumTree]; simp only [cost]

/-! ### Basic structural properties (the "P" family): adding an operator never lowers cost. -/

/-- P-monotone (unary): wrapping a subtree in an operator does not decrease cost. -/
theorem le_cost_un (c : Nat) (a : CostTree) : cost a ≤ cost (.un c a) := by
  simp only [cost]; omega

/-- P-monotone (binary), left and right subtrees. -/
theorem le_cost_bin_left (c : Nat) (a b : CostTree) : cost a ≤ cost (.bin c a b) := by
  simp only [cost]; omega

theorem le_cost_bin_right (c : Nat) (a b : CostTree) : cost b ≤ cost (.bin c a b) := by
  simp only [cost]; omega

/-! ### Regression / showcase. -/
namespace Tests

-- Boltzmann-style mixed expression `O₁(O₂(A,B), C)`: nesting is free.
example (A B C : CostTree) :
    cost (.bin 2 (.bin 1 A B) C) = 3 + cost A + cost B + cost C := by
  rw [no_nesting_penalty]

-- A 4-term Shannon-entropy-shaped sum (α₀ = 4, add-cost 3): cost = 4·4 + 3·3 = 25.
example : cost (flatSum 3 4 3) = 25 := by decide

-- The headline closed form on N = 5 terms.
example : cost (flatSum 3 4 4) = (4 + 3) * 5 - 3 := by decide

end Tests

end MachLib.CostTheory
