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

Scope (honest): this is the *cost-algebra* core, now covering the No-Nesting Penalty (`T38-NNP`), the
single- and double-sum laws (`T42`, O(N)/O(N²)), the full `T38` decomposition `Cost = Naive − Pattern
− Sharing`, the `T41-ISO` topological cost-invariance, and the structural core of the `T41` four-class
ordering. What stays out (stated, not faked): `T41`'s mean-cost ordering `C < B < A < D` is an
EMPIRICAL statistic over 187 equations (not a structural theorem) — here we prove the classification is
well-defined and the shared-skeleton floor/ceiling instead; and the Quadratic Ceiling Conjecture
(`T42-QCC`) is a research conjecture, not formalised.
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

/-! ### The four basic properties (P1–P4, R1) and the Additive Cost Law (T40)

R1 states four basic cost properties. Three are structural facts of the combinatorial model and are
proved here; the fourth (P4) is about a semantics this model deliberately does not carry, and is left
honestly out of scope. T40 is the additivity the whole algebra rests on. -/

/-- **P1 — Non-negativity.** `Cost(E) ≥ 0`. (Immediate in the `Nat` model — the named property.) -/
theorem p1_nonneg (t : CostTree) : 0 ≤ cost t := Nat.zero_le _

/-- **P2 — Terminal characterisation (operator lower bound).** An operator node costs at least its own
node-cost, so with positive operator costs a non-terminal is never free — only terminals can be zero
cost. (Full `cost = 0 ↔ terminal` needs the "every operator cost ≥ 1" hypothesis; this is its core.) -/
theorem p2_un_cost_ge (c : Nat) (a : CostTree) : c ≤ cost (.un c a) := by simp only [cost]; omega
theorem p2_bin_cost_ge (c : Nat) (a b : CostTree) : c ≤ cost (.bin c a b) := by simp only [cost]; omega

/-- **P3 — Subadditivity under operator application.** Applying an operator of cost `c` adds exactly `c`
to the operand costs, so `Cost(O(operands)) ≤ Σ operand costs + c` — subadditive (an equality here; the
routing/DAG model can do strictly better via sharing, which `T38.sharingDiscount` accounts for). -/
theorem p3_subadditive_un (c : Nat) (a : CostTree) : cost (.un c a) ≤ cost a + c := by
  simp only [cost]; omega
theorem p3_subadditive_bin (c : Nat) (a b : CostTree) : cost (.bin c a b) ≤ cost a + cost b + c := by
  simp only [cost]; omega

/- **P4 — Algebraic invariance** (Cost depends only on the FUNCTION computed, invariant under pointwise
equality of expressions) is OUT OF SCOPE for this per-tree combinatorial model: it needs `Cost(f) = min`
over all trees computing `f`, a semantics the pure-`Nat` model does not carry. `iso_cost` (below) is the
closest structural fragment — invariance under topological, not semantic, equality. Stated, not faked. -/

/-- **T40 — the Additive Cost Law.** Independent branches (disjoint subtrees) sum their costs exactly:
a binary operator's cost is its own node-cost plus each branch's cost, with NO interaction/cross term.
The named additivity the whole cost algebra rests on. -/
theorem additive_cost_law (c : Nat) (a b : CostTree) : cost (.bin c a b) = c + cost a + cost b := rfl

/-- A right-nested sum of `n+1` copies of `t` (dual to `flatSumTree`'s left nesting). -/
def flatSumTreeR (cAdd : Nat) (t : CostTree) : Nat → CostTree
  | 0     => t
  | n + 1 => .bin cAdd t (flatSumTreeR cAdd t n)

theorem cost_flatSumTreeR (cAdd : Nat) (t : CostTree) (n : Nat) :
    cost (flatSumTreeR cAdd t n) = cost t * (n + 1) + cAdd * n := by
  induction n with
  | zero => simp [flatSumTreeR, cost]
  | succ k ih => simp only [flatSumTreeR, cost, ih, Nat.mul_succ]; omega

/-- **Sum cost is association-independent** — a T40 corollary: a right-nested sum costs exactly the same
as the left-nested one. The total cost of summing independent branches depends only on the branches and
their count, not on how the sum is parenthesised. -/
theorem sum_assoc_invariant (cAdd : Nat) (t : CostTree) (n : Nat) :
    cost (flatSumTreeR cAdd t n) = cost (flatSumTree cAdd t n) := by
  rw [cost_flatSumTreeR, cost_flatSumTree]

/-! ### T38 — the full decomposition `Cost = Naive − Pattern − Sharing`

The headline cost theorem. To make it a *theorem* and not a tautology, the two saving mechanisms are
defined **independently** by structural recursion, then proven to account for exactly the gap between
the naive cost (everything expanded, nothing reused) and the actual cost.

Model: a `BTree` is an expression body that may reference ONE shared subexpression `s` via `ref`
leaves (the common-subexpression / constant-folding mechanism). Every operator carries two numbers:
its compound `nodeCost` and its `patSave` — how many primitive nodes the compound operator collapses
(the `F₁₆` pattern mechanism, e.g. `LSE` realises `exp+exp+add+ln` as fewer nodes).

- **actual** cost: `s` is computed once (`bCost s`), each `ref` in the body is free (`0`), operators
  cost their `nodeCost`.
- **naive** cost: every operator is expanded to its primitives (`nodeCost + patSave`) and the shared
  `s` is re-expanded at each of its `refs body` uses.
- **patternBonus** = the per-operator `patSave`s (body's, plus the shared `s`'s counted at each use).
- **sharingDiscount** = `(uses − 1) · cost(s)` — the copies of `s` that reuse avoids.
-/
namespace T38

/-- An expression body referencing one shared subexpression via `ref`. Each operator carries
`(nodeCost, patSave)`. A ref-free `BTree` doubles as the shared subexpression `s`. -/
inductive BTree where
  | leaf : Nat → BTree
  | ref  : BTree
  | un   : Nat → Nat → BTree → BTree
  | bin  : Nat → Nat → BTree → BTree → BTree

/-- Number of uses of the shared subexpression (the multiplicity `k`). -/
def refs : BTree → Nat
  | .leaf _ => 0 | .ref => 1
  | .un _ _ a => refs a | .bin _ _ a b => refs a + refs b

/-- Actual (DAG) cost of the body: `ref`s are free (the shared sub is counted once, separately);
operators cost their compound `nodeCost`. -/
def bCost : BTree → Nat
  | .leaf c => c | .ref => 0
  | .un nc _ a => nc + bCost a | .bin nc _ a b => nc + bCost a + bCost b

/-- Total primitive saving from compound operators in the body (`Σ patSave`). -/
def bPat : BTree → Nat
  | .leaf _ => 0 | .ref => 0
  | .un _ ps a => ps + bPat a | .bin _ ps a b => ps + bPat a + bPat b

/-- Naive cost: each `ref` re-expands the shared sub (cost `w`); each operator is its full primitive
expansion `nodeCost + patSave`. -/
def bNaive (w : Nat) : BTree → Nat
  | .leaf c => c | .ref => w
  | .un nc ps a => nc + ps + bNaive w a | .bin nc ps a b => nc + ps + bNaive w a + bNaive w b

/-- The decomposition of the naive cost: it is the actual cost, plus the body's pattern saving, plus
one copy of the shared sub's naive cost `w` per use. The crux lemma — induction on the body. -/
theorem bNaive_eq (w : Nat) (t : BTree) : bNaive w t = bCost t + bPat t + refs t * w := by
  induction t with
  | leaf c => simp [bNaive, bCost, bPat, refs]
  | ref => simp [bNaive, bCost, bPat, refs]
  | un nc ps a ih => simp only [bNaive, bCost, bPat, refs, ih]; omega
  | bin nc ps a b iha ihb =>
    simp only [bNaive, bCost, bPat, refs, iha, ihb, Nat.add_mul]; omega

/-- Naive cost of the shared subexpression `s` itself (its own primitives; `s` is ref-free so the
`w` is irrelevant — `bNaive 0 s`). -/
def naiveSub (s : BTree) : Nat := bCost s + bPat s

/-- Actual cost of the whole expression `(s, body)`: compute `s` once, then the body. -/
def actualCost (s body : BTree) : Nat := bCost s + bCost body
/-- Naive cost: expand every operator and re-expand `s` at each of its uses. -/
def naiveCost (s body : BTree) : Nat := bNaive (naiveSub s) body
/-- Pattern bonus: compound-operator savings — the body's, plus `s`'s counted once per use. -/
def patternBonus (s body : BTree) : Nat := bPat body + refs body * bPat s
/-- Sharing discount: the `(uses − 1)` copies of `s` that reuse avoids. -/
def sharingDiscount (s body : BTree) : Nat := (refs body - 1) * bCost s

/-- **T38 — the full cost decomposition.** `Naive = Actual + PatternBonus + SharingDiscount`
(equivalently `Cost = Naive − Pattern − Sharing`), whenever the shared subexpression is used at least
once. Both savings are defined independently of `actual`/`naive`; the theorem is that they account for
exactly the gap. -/
theorem t38_decomposition (s body : BTree) (h : 1 ≤ refs body) :
    naiveCost s body = actualCost s body + patternBonus s body + sharingDiscount s body := by
  unfold naiveCost actualCost patternBonus sharingDiscount naiveSub
  rw [bNaive_eq, Nat.mul_add]
  -- one copy of `cost s` moves from the `refs·cost s` term into the standalone `+ cost s`:
  have hrc : ∀ r c : Nat, 1 ≤ r → r * c = (r - 1) * c + c := by
    intro r c hr
    rcases r with _ | r
    · omega
    · simp [Nat.succ_sub_one, Nat.succ_mul]
  have := hrc (refs body) (bCost s) h
  omega

end T38

/-! ### T41-ISO — cost is a topological invariant (isomorphic DAGs cost the same)

The cross-domain isomorphism result (T41-ISO, R10): equations from unrelated fields that share the
SAME minimal DAG topology have exactly equal cost, so any normal form or optimisation proved for one
transfers to all others in its family. The structural core is that `cost` depends only on a tree's
shape and per-node costs — invariant under any structure-preserving relabeling, including reordering
the operands of a commutative binary node. We capture "same topology" by an inductive isomorphism
`Iso` (matching constructors recursively, with a commutative child-swap for binary nodes) and prove
`cost` is `Iso`-invariant. The blog's eight families (Arrhenius ≅ Eyring, Boltzmann ≅ logistic, …) are
the observed instances; this proves the invariance principle they rely on. -/

/-- Structural isomorphism of cost trees: same shape and node-costs, up to reordering the operands of
commutative binary nodes. -/
inductive Iso : CostTree → CostTree → Prop
  | leaf (c : Nat) : Iso (.leaf c) (.leaf c)
  | un {a a'} (c : Nat) : Iso a a' → Iso (.un c a) (.un c a')
  | bin {a a' b b'} (c : Nat) : Iso a a' → Iso b b' → Iso (.bin c a b) (.bin c a' b')
  | swap {a a' b b'} (c : Nat) : Iso a a' → Iso b b' → Iso (.bin c a b) (.bin c b' a')

/-- **Cost is `Iso`-invariant.** Two expressions with the same DAG topology cost exactly the same —
the T41-ISO principle. Induction on the isomorphism; the `swap` case is the commutative reordering. -/
theorem iso_cost {t₁ t₂ : CostTree} (h : Iso t₁ t₂) : cost t₁ = cost t₂ := by
  induction h with
  | leaf c => rfl
  | un c _ ih => simp only [cost, ih]
  | bin c _ _ iha ihb => simp only [cost, iha, ihb]
  | swap c _ _ iha ihb => simp only [cost, iha, ihb]; omega

/-- `Iso` is reflexive — every tree is isomorphic to itself, so `iso_cost` is non-vacuously total. -/
theorem Iso.refl : ∀ t : CostTree, Iso t t
  | .leaf c => .leaf c
  | .un c a => .un c (Iso.refl a)
  | .bin c a b => .bin c (Iso.refl a) (Iso.refl b)

/-- Commutativity of a binary operator's operands is a cost-isomorphism: `a ⊕ b` and `b ⊕ a` cost the
same — the simplest concrete witness of topological cost-invariance. -/
theorem cost_bin_comm (c : Nat) (a b : CostTree) : cost (.bin c a b) = cost (.bin c b a) :=
  iso_cost (.swap c (Iso.refl a) (Iso.refl b))

/-! ### T41 — the four structural classes and the structural cost ladder

Every arithmetic expression falls into one of four classes by a two-bit signature: whether it contains
an `exp`-family node and whether it contains a `ln`-family node — C = ln only, B = neither (rational),
A = exp only, D = both (mixed). **The blog's mean-cost ordering `C < B < A < D` is an EMPIRICAL statistic
over 187 real-world equations** (a fact about which equations happen to populate each class) — NOT a
structural theorem, and deliberately NOT reproduced here (fabricating a structural proof of a dataset
mean would be dishonest). What IS structural, and is proved here: (1) the classification is well-defined
— a total function of the two-bit signature, the four classes distinct; (2) on a SHARED arithmetic
skeleton the rational class is the cost FLOOR and the mixed class the cost CEILING — a transcendental
family never lowers cost, and mixed carries both families plus their interaction node. -/
namespace T41

/-- A cost tree that tags its unary nodes by family, so the exp/ln signature is defined: `expn`/`lnn`
are the two transcendental families, `ar1` any other unary arithmetic op (neg/recip/sqrt), `bin` any
binary op. Same additive cost model as `CostTree`. -/
inductive ETree where
  | leaf : Nat → ETree
  | expn : Nat → ETree → ETree
  | lnn  : Nat → ETree → ETree
  | ar1  : Nat → ETree → ETree
  | bin  : Nat → ETree → ETree → ETree

/-- Additive node count. -/
def ecost : ETree → Nat
  | .leaf c => c
  | .expn c a => c + ecost a
  | .lnn c a => c + ecost a
  | .ar1 c a => c + ecost a
  | .bin c a b => c + ecost a + ecost b

/-- Presence of an `exp`-family node. -/
def hasExp : ETree → Bool
  | .leaf _ => false
  | .expn _ _ => true
  | .lnn _ a => hasExp a
  | .ar1 _ a => hasExp a
  | .bin _ a b => hasExp a || hasExp b

/-- Presence of a `ln`-family node. -/
def hasLn : ETree → Bool
  | .leaf _ => false
  | .expn _ a => hasLn a
  | .lnn _ _ => true
  | .ar1 _ a => hasLn a
  | .bin _ a b => hasLn a || hasLn b

/-- The four structural classes (the two-bit exp/ln signature). -/
inductive Class where | A | B | C | D
  deriving DecidableEq

/-- Class assignment from the signature: A = exp only, B = neither, C = ln only, D = both. Total, so
every expression has exactly one class — the "unambiguous class assignment". -/
def classify (t : ETree) : Class :=
  match hasExp t, hasLn t with
  | true,  false => .A
  | false, false => .B
  | false, true  => .C
  | true,  true  => .D

/-- The four canonical class representatives over a shared `exp`/`ln`-free arithmetic core `a₀`: the
core itself (B), one exp on top (A), one ln on top (C), and both families combined through an
interaction binary node (D). `cE`/`cL`/`cI` are the exp/ln/interaction node-costs. -/
def repB (a₀ : ETree) : ETree := a₀
def repA (cE : Nat) (a₀ : ETree) : ETree := .expn cE a₀
def repC (cL : Nat) (a₀ : ETree) : ETree := .lnn cL a₀
def repD (cE cL cI : Nat) (a₀ : ETree) : ETree := .bin cI (.expn cE a₀) (.lnn cL a₀)

/-- The representatives land in the intended classes (given an `exp`/`ln`-free core). B/A/C need the
core to lack the other family; D always has both regardless of the core. -/
theorem classify_repB {a₀ : ETree} (he : hasExp a₀ = false) (hl : hasLn a₀ = false) :
    classify (repB a₀) = .B := by simp [classify, repB, he, hl]

theorem classify_repA {a₀ : ETree} (cE : Nat) (hl : hasLn a₀ = false) :
    classify (repA cE a₀) = .A := by simp [classify, repA, hasExp, hasLn, hl]

theorem classify_repC {a₀ : ETree} (cL : Nat) (he : hasExp a₀ = false) :
    classify (repC cL a₀) = .C := by simp [classify, repC, hasExp, hasLn, he]

theorem classify_repD (cE cL cI : Nat) (a₀ : ETree) :
    classify (repD cE cL cI a₀) = .D := by simp [classify, repD, hasExp, hasLn]

/-- **Rational (B) is the structural cost FLOOR.** On a shared core, both single-family classes and the
mixed class cost at least as much as the rational one — a transcendental family never lowers cost. -/
theorem rational_floor (cE cL cI : Nat) (a₀ : ETree) :
    ecost (repB a₀) ≤ ecost (repA cE a₀)
    ∧ ecost (repB a₀) ≤ ecost (repC cL a₀)
    ∧ ecost (repB a₀) ≤ ecost (repD cE cL cI a₀) :=
  ⟨by simp only [repB, repA, ecost]; omega,
   by simp only [repB, repC, ecost]; omega,
   by simp only [repB, repD, ecost]; omega⟩

/-- **Mixed (D) is the structural cost CEILING.** On a shared core, the mixed class costs at least as
much as either single-family class (it carries both families plus their interaction node). -/
theorem mixed_ceiling (cE cL cI : Nat) (a₀ : ETree) :
    ecost (repA cE a₀) ≤ ecost (repD cE cL cI a₀)
    ∧ ecost (repC cL a₀) ≤ ecost (repD cE cL cI a₀) :=
  ⟨by simp only [repA, repD, ecost]; omega,
   by simp only [repC, repD, ecost]; omega⟩

/-- **The mixed class strictly exceeds a pure-exponential one** whenever the added ln node, interaction
node, or core is nonempty — the structural "D is most expensive" made strict. -/
theorem mixed_gt_exp (cE cL cI : Nat) (a₀ : ETree) (h : 0 < cL + cI + ecost a₀) :
    ecost (repA cE a₀) < ecost (repD cE cL cI a₀) := by
  simp only [repA, repD, ecost]; omega

end T41

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

-- T38 worked example. Shared sub `s = un 4 1 (leaf 2)` (nodeCost 4, pattern-saving 1, leaf 2):
--   bCost s = 6, bPat s = 1, naiveSub s = 7.
-- Body `bin 3 2 ref (bin 5 0 ref (leaf 1))` uses `s` twice (refs = 2):
--   actual  = bCost s + bCost body = 6 + (3 + 0 + (5 + 0 + 1)) = 6 + 9 = 15
--   pattern = bPat body + refs·bPat s = (2 + 0) + 2·1 = 4
--   sharing = (2 − 1)·bCost s = 6
--   naive   = actual + pattern + sharing = 15 + 4 + 6 = 25
example :
    T38.naiveCost (.un 4 1 (.leaf 2)) (.bin 3 2 .ref (.bin 5 0 .ref (.leaf 1)))
  = T38.actualCost (.un 4 1 (.leaf 2)) (.bin 3 2 .ref (.bin 5 0 .ref (.leaf 1)))
  + T38.patternBonus (.un 4 1 (.leaf 2)) (.bin 3 2 .ref (.bin 5 0 .ref (.leaf 1)))
  + T38.sharingDiscount (.un 4 1 (.leaf 2)) (.bin 3 2 .ref (.bin 5 0 .ref (.leaf 1))) := by
  decide

-- T41-ISO: `a ⊕ b` and `b ⊕ a` cost the same — commutative reorder is a cost-isomorphism.
example : cost (.bin 3 (.leaf 4) (.leaf 5)) = cost (.bin 3 (.leaf 5) (.leaf 4)) :=
  cost_bin_comm 3 (.leaf 4) (.leaf 5)

-- Two same-topology trees, operands rearranged, cost equal via `iso_cost` (the T41-ISO principle).
example : cost (.bin 2 (.un 1 (.leaf 3)) (.leaf 4)) = cost (.bin 2 (.leaf 4) (.un 1 (.leaf 3))) :=
  iso_cost (.swap 2 (Iso.refl (.un 1 (.leaf 3))) (Iso.refl (.leaf 4)))

-- T41 four-class: a Boltzmann-shaped mixed rep (exp core / ln core, divided) classifies as D.
example : T41.classify (T41.repD 4 1 3 (.leaf 2)) = T41.Class.D := by decide

-- Numeric floor/ceiling on a concrete core (a₀ = leaf 2, cE=4, cL=1, cI=3): B=2, A=6, C=3, D=12.
example : T41.ecost (T41.repB (.leaf 2)) = 2 ∧ T41.ecost (T41.repD 4 1 3 (.leaf 2)) = 12 := by decide

end Tests

end MachLib.CostTheory
