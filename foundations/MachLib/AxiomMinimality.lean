import MachLib.Basic

/-!
# Is the `Real` axiom base minimal? — two axioms that are not

The `HighDimensional` audit took the ledger from 295 to 252 pinned axioms by finding **placeholder**
axioms with real referents. The remainder is mostly the *designed* trust boundary: MachLib is
Mathlib-free, so `Real` is axiomatised on purpose, and `Certcom` pins each kernel's round-off
certificate.

That makes a different question the interesting one. **A designed axiom base can still be
redundant**, and a redundant axiom is trust assumed for nothing — it costs exactly as much as a real
one in the ledger and buys nothing. This file asks whether `MachLib.Real`'s base is minimal.

Two answers so far, and the second is not obvious.

## 1. `zero_ne_one_ax` follows from `zero_lt_one_ax` and `lt_irrefl_ax`

If `0 = 1` then `0 < 1` rewrites to `0 < 0`. One line.

## 2. `archimedean` follows from `sup_exists`

**This is the one worth having.** `sup_exists` is full Dedekind completeness — every nonempty
bounded-above predicate has a least upper bound — and a **Dedekind-complete ordered field is
Archimedean**. The argument is classical and short:

> Suppose `ℕ` is bounded above in `ℝ`. It is nonempty, so it has a supremum `s`. Then `s − 1` is not
> an upper bound (or `s ≤ s − 1`), so some `natCast n` exceeds it, so `s < natCast (n+1)` — and
> `natCast (n+1)` is in the set. Contradiction.

`archimedean` is **load-bearing**: `Limits.npow_half_tendsto_zero`, `GeometricDecay.npow_tendsto_zero`
and everything routed through them use it to turn "the terms get small" into "the terms get below
any `ε`". It was pinned as an independent assumption; it is a *theorem*.

## Why this is not a refactor

Nothing below deletes an axiom. Deleting `archimedean` would break every proof that names it, for no
gain — the point is the **ledger**: an axiom that is derivable should be recorded as derivable, so
the trust boundary states what is actually assumed rather than what happens to be declared. The
theorems here are the evidence for that annotation.

`sorryAx`-free. Uses only other `MachLib.Real` axioms — that is the entire claim.
-/

namespace MachLib.Real

/-- `¬ (a < b) → b ≤ a`, from trichotomy. -/
theorem le_of_not_lt' {a b : Real} (h : ¬ a < b) : b ≤ a := by
  rcases lt_total a b with hlt | heq | hgt
  · exact absurd hlt h
  · exact (le_iff_lt_or_eq b a).mpr (Or.inr heq.symm)
  · exact (le_iff_lt_or_eq b a).mpr (Or.inl hgt)

/-- **`0 ≠ 1` is not independent** — it follows from `0 < 1` and irreflexivity. -/
theorem zero_ne_one_derivable : (0 : Real) ≠ 1 := by
  intro h
  have h01 : (0 : Real) < 1 := zero_lt_one_ax
  rw [← h] at h01
  exact lt_irrefl_ax 0 h01

/-- The predicate "is a natural number cast into `Real`". -/
def IsNatCast (y : Real) : Prop := ∃ n : Nat, y = natCast n

private theorem isNatCast_nonempty : ∃ y, IsNatCast y := ⟨natCast 0, ⟨0, rfl⟩⟩

/-- `s − 1 < s`, from `0 < 1`. -/
private theorem sub_one_lt (s : Real) : s - 1 < s := by
  have h := add_lt_add_left zero_lt_one_ax (s - 1)
  rw [add_zero] at h
  have hid : s - 1 + 1 = s := by
    rw [sub_def, add_assoc, add_comm (-(1 : Real)) 1, add_neg, add_zero]
  rwa [hid] at h

private theorem lt_of_le_of_lt' {a b c : Real} (hab : a ≤ b) (hbc : b < c) : a < c := by
  rcases (le_iff_lt_or_eq a b).mp hab with h | h
  · exact lt_trans_ax h hbc
  · rw [h]; exact hbc

private theorem add_le_add_right' {a b : Real} (h : a ≤ b) (c : Real) : a + c ≤ b + c := by
  rcases (le_iff_lt_or_eq a b).mp h with hlt | heq
  · refine (le_iff_lt_or_eq (a + c) (b + c)).mpr (Or.inl ?_)
    rw [add_comm a c, add_comm b c]
    exact add_lt_add_left hlt c
  · rw [heq]; exact (le_iff_lt_or_eq (b + c) (b + c)).mpr (Or.inr rfl)

/-- `a + 1 ≤ s → a ≤ s − 1`. The step that makes `s − 1` an upper bound CONSTRUCTIVELY, which is
what lets this proof avoid `by_contra` — MachLib is Mathlib-free and has neither it nor `by_cases`. -/
private theorem le_sub_one_of_succ_le {a s : Real} (h : a + 1 ≤ s) : a ≤ s - 1 := by
  have h2 := add_le_add_right' h (-(1 : Real))
  have hid : a + 1 + -(1 : Real) = a := by
    rw [add_assoc, add_neg, add_zero]
  rwa [hid, ← sub_def] at h2

/-- **THE RESULT: `archimedean` is derivable from `sup_exists`.**

A Dedekind-complete ordered field is Archimedean. Stated with exactly the axiom's own signature, so
the ledger annotation can point at it directly.

The proof avoids contradiction-by-cases: instead of "`s − 1` is not an upper bound, so extract a
witness", it shows **`s − 1` IS an upper bound** — because `natCast (n+1) ≤ s` gives
`natCast n ≤ s − 1` for every `n` — and that contradicts leastness directly. -/
theorem archimedean_derivable (x : Real) : ∃ n : Nat, x < natCast n := by
  rcases Classical.em (∃ n : Nat, x < natCast n) with hcon | hcon
  · exact hcon
  · exfalso
    have hall : ∀ n : Nat, natCast n ≤ x := fun n =>
      le_of_not_lt' (fun hlt => hcon ⟨n, hlt⟩)
    have hbound : BoundedAbove IsNatCast := by
      refine ⟨x, ?_⟩
      rintro y ⟨n, rfl⟩
      exact hall n
    obtain ⟨s, hub, hleast⟩ := sup_exists IsNatCast isNatCast_nonempty hbound
    -- `s − 1` is an upper bound: every natCast n satisfies natCast n + 1 = natCast (n+1) ≤ s.
    have hub' : ∀ y, IsNatCast y → y ≤ s - 1 := by
      rintro y ⟨n, rfl⟩
      have hsucc : natCast (n + 1) ≤ s := hub (natCast (n + 1)) ⟨n + 1, rfl⟩
      rw [natCast_succ] at hsucc
      exact le_sub_one_of_succ_le hsucc
    exact lt_irrefl_ax s (lt_of_le_of_lt' (hleast (s - 1) hub') (sub_one_lt s))

end MachLib.Real
