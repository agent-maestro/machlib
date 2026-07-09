import MachLib.IterExpDepthNMeasure

/-!
# Explicit arbitrary-depth bound — the nested linearization `rankNested` (arithmetic core)

The chain-2 explicit bound linearized its 3-level lex measure with `rankLex`. The arbitrary-depth
bound needs the same idea for a `NestedNat n` (an `(n+1)`-deep nested `Nat`, the shape of
`chainNMeasureCanon`/`chainNMeasureEI`/`synMeasure`): a **mixed-radix** linearization to a single `Nat`
that is strictly monotone under `nestedOrder`, given per-level upper bounds.

This file is that core (the depth-generic `rankLex`; `rankLex` is its `n = 2` instance in spirit). Pure
`Nat`, no axioms. It is step 1 of the chain-N explicit-bound build
(`monogate-research/roadmap/chainN-explicit-bound-design.md`).

  * `maxRank n A`        — the rank of the bound `A` itself (the max attainable rank under bound `A`).
  * `rankNested n A v`   — the mixed-radix value of `v` in the radix system set by `A`.
  * `rankNested_le_maxRank` — `v ≤ A` (componentwise) ⇒ `rankNested A v ≤ maxRank A`.
  * `rankNested_lt`      — `v' ≤ A` ∧ `nestedOrder n v' v` ⇒ `rankNested A v' < rankNested A v`.
-/

namespace MachLib.ExplicitBound

open MachLib.IterExpDepthN

/-- Componentwise `≤` on `NestedNat n`. -/
def nestedLe : (n : Nat) → NestedNat n → NestedNat n → Prop
  | 0,     a, b => a ≤ b
  | _ + 1, a, b => a.1 ≤ b.1 ∧ nestedLe _ a.2 b.2

/-- The maximal rank attainable under the per-level bound `A` — `A`'s own mixed-radix value. -/
def maxRank : (n : Nat) → NestedNat n → Nat
  | 0,     A => A
  | _ + 1, A => A.1 * (maxRank _ A.2 + 1) + maxRank _ A.2

/-- Mixed-radix linearization of `v : NestedNat n` in the radix system set by the bound `A`: the head
component sits in a "digit" of value `maxRank(tail) + 1`, so the outer coordinate dominates whenever
the value is bounded by `A`. The `NestedNat n → Nat` collapse `nestedOrder` needs. -/
def rankNested : (n : Nat) → NestedNat n → NestedNat n → Nat
  | 0,     _, v => v
  | _ + 1, A, v => v.1 * (maxRank _ A.2 + 1) + rankNested _ A.2 v.2

/-- Under the bound `A`, the rank never exceeds `maxRank A`. -/
theorem rankNested_le_maxRank : ∀ (n : Nat) (A v : NestedNat n),
    nestedLe n v A → rankNested n A v ≤ maxRank n A
  | 0,     A, v, h => h
  | n + 1, A, v, h => by
      obtain ⟨hh, ht⟩ := h
      have ih := rankNested_le_maxRank n A.2 v.2 ht
      show v.1 * (maxRank n A.2 + 1) + rankNested n A.2 v.2
          ≤ A.1 * (maxRank n A.2 + 1) + maxRank n A.2
      have hmul : v.1 * (maxRank n A.2 + 1) ≤ A.1 * (maxRank n A.2 + 1) :=
        Nat.mul_le_mul hh (Nat.le_refl _)
      omega

/-- **Nested lex → Nat linearization.** If `v'` is bounded by `A` componentwise and drops below `v` in
`nestedOrder`, its rank drops strictly. The mixed-radix head/tail cases mirror `rankLex_lt_raw`'s
disjunction; the head case uses `rankNested_le_maxRank` to keep the tail within one digit. -/
theorem rankNested_lt : ∀ (n : Nat) (A v v' : NestedNat n),
    nestedLe n v' A → nestedOrder n v' v → rankNested n A v' < rankNested n A v
  | 0,     A, v, v', _, h => h
  | n + 1, A, v, v', hle, h => by
      obtain ⟨hh', ht'⟩ := hle
      -- nestedOrder (n+1) v' v  =  v'.1 < v.1  ∨  (v'.1 = v.1 ∧ nestedOrder n v'.2 v.2)
      rcases h with hlt | ⟨heq, hinner⟩
      · -- head drops: the tail stays within one digit (maxRank A.2)
        have htmax : rankNested n A.2 v'.2 ≤ maxRank n A.2 := rankNested_le_maxRank n A.2 v'.2 ht'
        show v'.1 * (maxRank n A.2 + 1) + rankNested n A.2 v'.2
            < v.1 * (maxRank n A.2 + 1) + rankNested n A.2 v.2
        have hstep : (v'.1 + 1) * (maxRank n A.2 + 1) ≤ v.1 * (maxRank n A.2 + 1) :=
          Nat.mul_le_mul hlt (Nat.le_refl _)
        have hexp : (v'.1 + 1) * (maxRank n A.2 + 1)
            = v'.1 * (maxRank n A.2 + 1) + (maxRank n A.2 + 1) := Nat.succ_mul _ _
        omega
      · -- head ties, tail drops: recurse
        have ih := rankNested_lt n A.2 v.2 v'.2 ht' hinner
        show v'.1 * (maxRank n A.2 + 1) + rankNested n A.2 v'.2
            < v.1 * (maxRank n A.2 + 1) + rankNested n A.2 v.2
        rw [heq]; omega

end MachLib.ExplicitBound
