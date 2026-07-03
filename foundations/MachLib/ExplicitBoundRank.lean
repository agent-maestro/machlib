import MachLib.ChainExp2Reducer

/-!
# Explicit-bound program — the lex→Nat rank linearization

The Khovanskii finiteness theorems (`chain2_khovanskii_bound_unconditional`,
`chainN_khovanskii_bound_unconditional`) currently produce an EXISTENTIAL zero-count
bound `∃ N, zeros.length ≤ N`. The zero-count `N` the well-founded recursion accumulates
is exactly the number of *reduce* steps taken (each reduce arm returns `⟨N+1, …⟩`; trim
returns `⟨N, …⟩`; the vehicle arm returns `⟨0, …⟩`). Because every reduce step strictly
lowers the well-founded measure `chain2MeasureCanon : Nat × (Nat × Nat)` (a 3-level lex
tuple), the accumulated `N` is bounded by the *rank* of the initial measure — provided we
can linearize the lex order into a single `Nat`.

This file supplies that linearization. `rankLex A B` maps a lex tuple `(d,(a,b))` to a
`Nat` by placing `d` in the highest base-`(A+1)(B+1)` digit; `rankLex_lt` shows it is
strictly monotone under the lex order **given upper bounds `A,B` on the SOURCE tuple's
inner components**. Those bounds come, globally over the whole recursion, from the
polynomial's degrees (reduce/trim never raise the `y₀`-degree, and the inner single-exp
measure is bounded by the `y₀`-degree). Wiring that degree-preservation in, and re-running
the WF induction with `rankLex` bookkeeping instead of `∃ N`, is the remaining work of the
explicit-bound program; this rank lemma is its reusable arithmetic core (the same shape
lifts to the deeper nestings used at depth ≥ 3).

No new axioms — pure `Nat` arithmetic (`omega` + `Nat.succ_mul` + `Nat.mul_le_mul_right`).
-/

namespace MachLib.ExplicitBound

open MachLib.ChainExp2Reducer

/-- Nat rank of a 3-level lex tuple `(d,(a,b))`, given upper bounds `A,B` on the inner two
components. Places `d` in the highest "digit" of base `(A+1)*(B+1)`; the low part
`a*(B+1)+b` stays `< (A+1)*(B+1)` whenever `a≤A ∧ b≤B`, so the outer coordinate dominates. -/
def rankLex (A B : Nat) : Nat × (Nat × Nat) → Nat
  | (d, (a, b)) => d * ((A + 1) * (B + 1)) + a * (B + 1) + b

/-- **Lex→Nat linearization (raw disjunction form).** Strict monotonicity of `rankLex` under
the unfolded 3-level lex order, given SOURCE inner bounds `a ≤ A`, `b ≤ B`. -/
theorem rankLex_lt_raw (A B d a b d' a' b' : Nat)
    (ha : a ≤ A) (hb : b ≤ B)
    (h : d < d' ∨ (d = d' ∧ (a < a' ∨ (a = a' ∧ b < b')))) :
    rankLex A B (d, (a, b)) < rankLex A B (d', (a', b')) := by
  simp only [rankLex]
  have hAexp : (A + 1) * (B + 1) = A * (B + 1) + (B + 1) := Nat.succ_mul A (B + 1)
  have haU : a * (B + 1) ≤ A * (B + 1) := Nat.mul_le_mul_right (B + 1) ha
  have hlowK : a * (B + 1) + b < (A + 1) * (B + 1) := by omega
  rcases h with hd | ⟨hdeq, hrest⟩
  · have hstep : (d + 1) * ((A + 1) * (B + 1)) ≤ d' * ((A + 1) * (B + 1)) :=
      Nat.mul_le_mul_right ((A + 1) * (B + 1)) hd
    have hexp : (d + 1) * ((A + 1) * (B + 1))
        = d * ((A + 1) * (B + 1)) + (A + 1) * (B + 1) := Nat.succ_mul _ _
    omega
  · subst hdeq
    rcases hrest with ha' | ⟨haeq, hb'⟩
    · have hstep : (a + 1) * (B + 1) ≤ a' * (B + 1) := Nat.mul_le_mul_right (B + 1) ha'
      have hexp : (a + 1) * (B + 1) = a * (B + 1) + (B + 1) := Nat.succ_mul _ _
      omega
    · subst haeq; omega

/-- **Lex→Nat linearization** consuming the packaged `nestedLT` order directly (defeq to the
raw disjunction). This is the form the chain-2 / chain-N recursions produce (via
`chain2Reduce_nestedLT_canon`, `chain2_trim_order`, …). -/
theorem rankLex_lt (A B : Nat) (m m' : Nat × (Nat × Nat))
    (ha : m.2.1 ≤ A) (hb : m.2.2 ≤ B) (h : nestedLT m m') :
    rankLex A B m < rankLex A B m' := by
  obtain ⟨d, a, b⟩ := m
  obtain ⟨d', a', b'⟩ := m'
  exact rankLex_lt_raw A B d a b d' a' b' ha hb h

/-- Convenience: `rankLex_lt` in the `+1 ≤` form the reduce arm needs
(`zeros(p) ≤ zeros(reduct) + 1 ≤ rankLex … reduct + 1 ≤ rankLex … p`). -/
theorem rankLex_succ_le (A B : Nat) (m m' : Nat × (Nat × Nat))
    (ha : m.2.1 ≤ A) (hb : m.2.2 ≤ B) (h : nestedLT m m') :
    rankLex A B m + 1 ≤ rankLex A B m' :=
  rankLex_lt A B m m' ha hb h

end MachLib.ExplicitBound
