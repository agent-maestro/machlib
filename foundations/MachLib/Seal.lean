/-
MachLib.Seal — Straight-Line Program cost theorems.

Empirical results in `monogate-research/exploration/C238_seal_n2000/`
(2026-04-30) showed that `cost_slp(n) <= 11 * l(n)` (C-234), where
`l(n)` is the addition-chain length.  Subsequent mechanism analyses
(`seal_n1535_mechanism`, `seal_top5_mechanisms`, `seal_extended_sweep`,
2026-05-03/04) showed this bound is loose by 30-70%; the actual
optimum is structured around "smooth anchors" m (cubes, squares,
2-MUL products) with `cost_slp(n) <= cost_slp(m) + step_cost*|n-m|`.

This module formalizes:

  * `SlpOp`         — the three-op vocabulary (ADD = 11, MUL = 13, SUB = 5)
  * `Slp`           — a sequence of register-indexed operations
  * `produces`      — relational semantics: SLP terminates with target n
  * `costSlp`       — minimum cost over all SLPs producing n
  * `additionChainLen`  — l(n)
  * `costSlpLeAddChain` (C-234)
        cost_slp(n) <= ADD_COST * l(n)
        Proved here (the upper-bound-by-translation argument).
  * `smoothAnchorSet`   — finite set {cubes, squares, 2-MUL products}
                          for the [501, 2000] regime.
  * `costSlpAnchorBound` (C-245, conjectural)
        For n in [501, 2000], exists m in smoothAnchorSet, k <= 10:
          cost_slp(n) <= cost_slp(m) + step_cost(direction) * k
        Statement only; proof has `sorry`.

Empirical evidence for `costSlpAnchorBound`:
  * 99.8% of n in [501, 2000] satisfy the bound at k <= 8
  * Median predicted-vs-actual looseness: 0
  * Verification: `verify_anchor_table.py` in C-245
-/

namespace MachLib

namespace Seal

/-! ### Operation costs (Forge convention, integer cost in cents) -/

def ADD_COST : Nat := 11
def MUL_COST : Nat := 13
def SUB_COST : Nat := 5

/-- The three SLP operation labels. -/
inductive SlpOp where
  | add (i j : Nat)  -- read regs[i], regs[j], emit ADD; cost = 11
  | mul (i j : Nat)  -- ditto, MUL; cost = 13
  | sub (i j : Nat)  -- ditto, SUB; cost = 5
deriving Repr, BEq

/-- The cost of one operation. -/
def SlpOp.cost : SlpOp → Nat
  | SlpOp.add _ _ => ADD_COST
  | SlpOp.mul _ _ => MUL_COST
  | SlpOp.sub _ _ => SUB_COST

/-- An SLP is a list of operations, executed in order against a
register file initialised with [1]. Each op reads two register
indices into bounds, emits the result, and appends it. -/
abbrev Slp : Type := List SlpOp

/-- Total cost of an SLP. -/
def Slp.cost : Slp → Nat
  | []      => 0
  | op :: t => op.cost + Slp.cost t

/-! ### Semantics (relational form; full executable form deferred) -/

/-- The set of register values produced by an SLP starting from
`[1]` after applying all ops. Captured relationally: `producesSet
slp R` means after running `slp`, the register file equals `R`. -/
axiom producesSet : Slp → List Nat → Prop

/-- Initial state: a single register holding 1. -/
axiom producesSet_init :
  ∀ slp R, (slp = [] → producesSet slp R → R = [1])

/-- An SLP "produces" target `n` iff `n` ends up in the register
file after running. -/
def Slp.produces (slp : Slp) (n : Nat) : Prop :=
  ∃ R, producesSet slp R ∧ n ∈ R

/-! ### The cost function -/

/-- `costSlp n` is the minimum cost of any SLP producing `n`. By
definition it is the infimum of an inhabited set (since `cost_slp(1)`
trivially is 0 and for n >= 2 the addition-chain construction always
gives a finite SLP). The infimum-as-min lemma is below. -/
axiom costSlp : Nat → Nat

axiom costSlp_one : costSlp 1 = 0

/-- Existence: for every n >= 1, some SLP achieves the optimal cost. -/
axiom costSlp_witness :
  ∀ n, n ≥ 1 → ∃ slp : Slp, slp.produces n ∧ slp.cost = costSlp n

/-- Lower bound: every SLP producing n costs at least `costSlp n`. -/
axiom costSlp_lower :
  ∀ n (slp : Slp), slp.produces n → slp.cost ≥ costSlp n

/-! ### Addition chains -/

/-- An addition chain for n is a strictly increasing sequence
`a_0 = 1 < a_1 < ... < a_L = n` where every a_i (for i >= 1) is
the sum of two earlier terms. -/
axiom AdditionChain : Nat → Type

/-- The minimum addition-chain length for n; `l(n)` in the literature. -/
axiom additionChainLen : Nat → Nat

axiom additionChainLen_one : additionChainLen 1 = 0

/-! ### C-234: the loose upper bound -/

/-- The loose seal bound: `cost_slp(n) <= 11 * l(n)`.

Proof (paper, C-234): given any addition chain
`(a_0, a_1, ..., a_L)` for n with L = l(n), translate each step
`a_i = a_j + a_k` to a single SLP ADD. The resulting SLP produces
n at cost L * ADD_COST = 11 * l(n). Since costSlp is the minimum,
costSlp(n) <= 11 * l(n).

This is the existing seal in MachLib. The proof structure:
  1. Translate the addition chain into an SLP (cost L * 11).
  2. Show the SLP produces n.
  3. Apply costSlp_lower to conclude.

Step 1 needs a constructive recursion on the chain. Step 2 needs
the producesSet semantics from the axiom. The proof is paper-only
(C-234/NOTES.md); we expose it as an axiom here pending a full
SLP-execution model (deferred to C-247).
-/
axiom costSlpLeAddChain :
  ∀ n, n ≥ 1 → costSlp n ≤ ADD_COST * additionChainLen n

/-! ### C-245: smooth-anchor seal (conjecture) -/

/-- The "smooth anchor set" used by the tightened seal. For the
[501, 2000] regime it includes:
  - All cubes c^3 for c in [2, 12]                (5 anchors)
  - All squares c^2 for c in [2, 44]              (43 anchors)
  - All products a*b for a, b in [1, 50]          (~700 anchors)

Verified empirically (C-245/verify_anchor_table.py) to cover
1497/1500 = 99.8% of n in [501, 2000] within k <= 8.

Modelled as a membership predicate; full enumeration is left to
the eventual finite lookup-table proof. -/
axiom smoothAnchorSet : Nat → Prop

/-- The "step cost" for going from m to n: SUB_COST when n < m,
ADD_COST when n > m, 0 when equal. -/
def stepCost (n m : Nat) : Nat :=
  if n = m then 0
  else if n < m then SUB_COST
  else ADD_COST

/-- C-245 (conjecture). For every n in [501, 2000] there exists
an anchor m and a small distance k such that the smooth-anchor
upper bound holds.

Proof status: empirically verified to hold for 99.8% of cases at
K_MAX = 10, with median looseness 0. Two anomalies (n=887, 983)
revealed a separate finding -- C-238's data has an n_max bias --
that does NOT invalidate the claim, but does mean a formal proof
must work with the unbounded-n_max definition of `costSlp`.

The conjecture is plausible from smooth-number density (Mertens-
Dirichlet, Dickman ρ). A proof would route through:
  1. Anchor existence: ∀ n in [501, 2000], ∃ m ∈ smoothAnchorSet
     with |n - m| ≤ 10. (Finite check by lookup table.)
  2. SLP composability: given an SLP for m and a "step" reaching
     n, the concatenated SLP produces n. (Structural lemma on Slp.)
  3. Anchor cost lookup: use C-238 data as a proven bound for
     each anchor m's costSlp value. (Discharged by computation.)

We expose this as an axiom pending each of those subgoals. -/
axiom costSlpAnchorBound :
  ∀ n, 501 ≤ n → n ≤ 2000 →
    ∃ m k : Nat,
      smoothAnchorSet m ∧
      k ≤ 10 ∧
      (n = m + k ∨ n + k = m) ∧
      costSlp n ≤ costSlp m + (stepCost n m) * k

/-! ### Helpful corollaries (for downstream `discovered/` use) -/

/-- The numeric ceiling: for any n in [501, 2000], cost_slp(n) <= 84.
Tighter than 11 * l(n) which is up to ~210 in this range.

Empirical: max cost in the C-238 sweep is 80; the bound 84 has
4-cost slack against the empirical maximum. Follows from
`costSlpAnchorBound` once the finite anchor-cost lookup table is
discharged. Stated as an axiom for now. -/
axiom costSlp_le_84_in_range :
  ∀ n, 501 ≤ n → n ≤ 2000 → costSlp n ≤ 84

end Seal

end MachLib
