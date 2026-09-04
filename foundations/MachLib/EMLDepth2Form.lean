import MachLib.EMLDepthTameness

/-!
# The depth-≤2 classification, packaged as a predicate

`depth_le_two_normal_form` (`EMLDepthTameness:5896`) already classifies every depth-≤2 tree:
constant, the identity, or `exp a − log b` with `a` and `b` both in `Depth1Form`. It states that
classification **inline**, about a tree. Depth 1 does not: it has a named predicate `Depth1Form`
together with a one-line wrapper `depth_le_one_form` carrying a tree into it, and that predicate is
what the depth-2 classification itself consumes in its third disjunct.

This file supplies the missing rung of that pattern — `Depth2Form` plus the wrapper — so the depth-3
classification can consume it the same way depth 2 consumes `Depth1Form`.

**Why a predicate rather than the inline statement.** The consumer is a *function*, not a tree: the
depth-3 branch lemmas destructure a node into `exp (a x) − log (b x)` and then need to say "and `a`
is itself a depth-2 shape". There is no tree left at that point to apply `depth_le_two_normal_form`
to. This is exactly why `Depth1Form` exists one level down, and the third disjunct below is where it
is used.

No new mathematics: the wrapper is definitional unfolding, and the proof term is the classification
itself. The content is the packaging, and the packaging is what the next rung is blocked on.
-/

namespace MachLib

open Real

/-- **Normal form at depth ≤ 2, as a predicate on the value function.** Constant, the identity, or
`exp a − log b` with both `a` and `b` in `Depth1Form`. Mirrors `Depth1Form` one level up. -/
def Depth2Form (f : Real → Real) : Prop :=
  (∃ c : Real, ∀ x : Real, 0 < x → f x = c)
  ∨ (∀ x : Real, 0 < x → f x = x)
  ∨ (∃ a b : Real → Real, Depth1Form a ∧ Depth1Form b ∧
      ∀ x : Real, 0 < x → f x = exp (a x) - log (b x))

/-- **Every depth-≤2 tree has `Depth2Form`.** The depth-2 analogue of `depth_le_one_form`; the
classification is `depth_le_two_normal_form`, and this is the wrapper that makes it usable where
only the value function survives. -/
theorem depth_le_two_form (t : EMLTree) (ht : t.depth ≤ 2) : Depth2Form t.eval := by
  -- `depth_le_one_form` needs no unfold because `depth_le_one_classification` already *concludes*
  -- `Depth1Form`. The depth-2 classification states its disjunction inline, so the wrapper has to
  -- open the definition — the one structural difference between the two rungs.
  unfold Depth2Form
  exact depth_le_two_normal_form t ht

/-- **A constant gap below a target for `exp ∘ t`, at depth ≤ 2.**

The depth-2 analogue of `depth_le_one_exp_gap_below` (`EMLDepthTameness:6377`), and the second of
the two inputs `depth_le_three_gap_below` needs (the first is `depth_le_two_form`, above).

**Route: transport, not re-enumeration.** The depth-1 version enumerates all five depth-1 shapes.
This one does not have to. For positive `ν`, `exp (t x) < ν` is exactly `t x < log ν`, so the
*value* gap `depth_le_two_gap_below` already carries the content, and `exp` transports it back:
`t x ≤ log ν − ε₀` gives `exp (t x) ≤ ν · exp (−ε₀)`.

**The gap changes shape under the transport, and that is not a defect.** What comes back is
`ν(1 − exp(−ε₀))` — *proportional* to `ν`, not the value gap `ε₀` itself. A fixed gap below `log ν`
is an exponentially larger gap below `ν` for large `ν`, and a smaller one for small `ν`. Stating it
as `ε₀` would be wrong; stating it proportionally is what the exponential actually gives.

Non-positive `ν` is vacuous: `exp` is positive, so the hypothesis never fires and any `ε` serves. -/
theorem depth_le_two_exp_gap_below (A : EMLTree) (hA : A.depth ≤ 2) (ν : Real) :
    ∃ ε X₀ : Real, 0 < ε ∧ 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → exp (A.eval x) < ν →
      ε ≤ ν - exp (A.eval x) := by
  rcases lt_total 0 ν with hν | hν | hν
  · -- `0 < ν` — the only branch with content.
    obtain ⟨ε₀, X₀, hε₀, hX₀, hg⟩ := depth_le_two_gap_below A hA (log ν)
    have hlt1 : exp (-ε₀) < 1 := by
      have h := exp_lt (neg_neg_of_pos hε₀)
      rw [exp_zero] at h; exact h
    refine ⟨ν - ν * exp (-ε₀), X₀, ?_, hX₀, ?_⟩
    · have h1 : (0 : Real) < 1 - exp (-ε₀) := by
        have u := add_lt_add_left hlt1 (-(exp (-ε₀)))
        have e1 : -(exp (-ε₀)) + exp (-ε₀) = 0 := by mach_ring
        have e2 : -(exp (-ε₀)) + 1 = 1 - exp (-ε₀) := by mach_ring
        rw [e1, e2] at u; exact u
      have h2 : (0 : Real) < ν * (1 - exp (-ε₀)) := mul_pos hν h1
      have e : ν * (1 - exp (-ε₀)) = ν - ν * exp (-ε₀) := by mach_ring
      rw [e] at h2; exact h2
    · intro x hx hlt
      -- `exp (A x) < ν` ⇒ `A x < log ν`, by `log` monotone and `log ∘ exp = id`
      have hAlt : A.eval x < log ν := by
        have h := log_lt_log (exp_pos (A.eval x)) hlt
        rw [log_exp] at h; exact h
      have hgap := hg x hx hAlt
      have hle : A.eval x ≤ log ν - ε₀ := by
        have u := sub_le_sub_left hgap (log ν)
        have e : log ν - (log ν - A.eval x) = A.eval x := by mach_ring
        rw [e] at u; exact u
      have h1 : exp (A.eval x) ≤ exp (log ν - ε₀) := exp_monotone hle
      have h2 : exp (log ν - ε₀) = ν * exp (-ε₀) := by
        have e : log ν - ε₀ = log ν + -ε₀ := by mach_ring
        rw [e, exp_add, exp_log hν]
      rw [h2] at h1
      exact sub_le_sub_left h1 ν
  · -- `ν = 0`: `exp > 0` refutes the hypothesis.
    refine ⟨1, 1, zero_lt_one_ax, le_refl 1, ?_⟩
    intro x _ hlt
    rw [← hν] at hlt
    exact absurd (lt_trans_ax (exp_pos (A.eval x)) hlt) (lt_irrefl_ax 0)
  · -- `ν < 0`: likewise.
    refine ⟨1, 1, zero_lt_one_ax, le_refl 1, ?_⟩
    intro x _ hlt
    have h0 : (0 : Real) < ν := lt_trans_ax (exp_pos (A.eval x)) hlt
    exact absurd (lt_trans_ax h0 hν) (lt_irrefl_ax 0)

/-- **Firing specimen: the gap statement above is not vacuous.**

`depth_le_two_exp_gap_below` concludes an *implication* — `exp (t x) < ν → ε ≤ ν − exp (t x)` — and
an implication whose hypothesis never fires is true for free. Two of the theorem's three branches
are vacuous by design (`ν ≤ 0` cannot exceed a positive `exp`), so the statement would still compile
if the third branch were vacuous too, and every gate would stay green.

This witnesses that it is not: with `t = const 0` and `ν = exp 1` the hypothesis holds at every `x`
(`exp 0 < exp 1`), so the content branch is reached and the `ε` it produces is a real bound. -/
private theorem depth_le_two_exp_gap_below_fires (x : Real) :
    exp ((EMLTree.const 0).eval x) < exp 1 := by
  show exp 0 < exp 1
  exact exp_lt zero_lt_one_ax


end MachLib
