import MachLib.WitnessResidualCrossingUnboundedMirror

/-! # The "positive half" closed: `RightChildrenEverywherePositive` is essentially NECESSARY

Digs into the question left open at the end of the crossing-unboundedness arc: is there anything
"beyond `RightChildrenEverywherePositive`" worth building for the positive/`EMLPfaffianValidOn`-
establishing half of the original tree-depth induction? Working through it directly (not
assuming an answer either way) shows the surprising conclusion: essentially NO — combined with
the crossing-unboundedness results, `RightChildrenEverywherePositive`'s own "every right child
positive EVERYWHERE" requirement turns out to be not just SUFFICIENT (already known) but close to
NECESSARY, for a compound tree built from this grammar to have any chance of being bounded.

**The necessary-condition theorem** (`eml_A_B_bounded_above_sign_definite`): if `eml A B` is
bounded above and `B` is differentiable everywhere, `B` must be SIGN-DEFINITE throughout `ℝ` —
either strictly positive everywhere, or non-positive everywhere. There is no third option. The
proof reduces to the crossing-unboundedness machinery directly: if `B` takes both a non-positive
value (at some `p`) and a positive value (at some `q`), `eml A B` is unbounded regardless of which
of `p, q` comes first (`eml_A_B_unbounded_of_mixed_sign`, wrapping the two directional theorems
from `WitnessResidualCrossingUnboundedMirror.lean`) — contradicting boundedness.

**Why the "non-positive everywhere" disjunct isn't genuinely new territory.** If `B ≤ 0`
everywhere, `log(B)` clamps to `0` EVERYWHERE (`Real.log_nonpos`), so `eml A B` reduces IDENTICALLY
to `exp(A.eval ·)` — the entire `B`-branch becomes dead code (`eml_A_B_eq_exp_A_of_nonpos` below,
a direct three-line confirmation). A tree built this way is not a genuinely NEW construction; it's
a disguised, more complicated way to write a strictly SIMPLER tree that drops `B` entirely — whose
own boundedness is a question about `A` alone, recursively, not about `B` at all.

**The upshot.** At EVERY `eml`-node in a bounded compound tree, the right child must be either (a)
globally positive (exactly `RightChildrenEverywherePositive`'s own condition) or (b) globally
non-positive (which reduces the node away, contributing nothing new). There is no meaningful
"beyond `RightChildrenEverywherePositive`" case within this grammar — not because no one has found
one yet, but because the crossing-unboundedness results, now packaged as a genuine necessary
condition rather than a family of specific-shape refutations, show there is nothing left to find
of that kind. This closes the "positive half" of the original Option D tree-depth induction
question about as definitively as the negative half was closed: not by exhausting shapes, but by
characterizing the constraint directly.

**Honest scope, precisely.** This is a ONE-LEVEL necessary condition (about a single `eml A B`
node's own right child) — turning it into a full statement about an ENTIRE compound tree needs
applying it at every node recursively (structural induction over the tree, checking each level's
own right child against this same dichotomy), which is not carried out here; but the one-level
core — the actual mathematical content the recursion would need at each step — is now a genuine
theorem, not an assumption. Also unaddressed: whether `EMLPfaffianValidOn`'s own INTERVAL-based
(not global) formulation could admit trees bounded only on a restricted range via crossings
entirely OUTSIDE that range — not useful for the residual's own purposes (which needs boundedness
on all of `ℝ`, matching `sin`'s own domain) but a distinct question from what's closed here.

`sorryAx`-free, verified via a genuinely fresh rebuild: same axiom footprint as the
crossing-unboundedness results it's built from — no dependence on `EMLPfaffianValidOn` or
`eml_pfaffian_validon_from_sin_equality`. -/

namespace MachLib
namespace Real

/-- Weakened `eml_A_crossing_B_unbounded_above`: `B(x0) ≤ 0` (not necessarily exactly `0`) is
enough. -/
theorem eml_A_nonpos_pos_unbounded_above (A B : EMLTree) (x0 x1 : Real) (hx0x1 : x0 < x1)
    (hBx0 : B.eval x0 ≤ 0) (hBx1pos : 0 < B.eval x1)
    (hBdiff : ∀ z : Real, x0 ≤ z → z ≤ x1 → ∃ Bd : Real, HasDerivAt B.eval Bd z) (M : Real) :
    ∃ x : Real, M < (EMLTree.eml A B).eval x := by
  rcases lt_total (Real.exp (-(M + 1))) (B.eval x1) with hcase | hcase | hcase
  · have hdiff2 : ∀ z : Real, x0 ≤ z → z ≤ x1 →
        ∃ g' : Real, HasDerivAt (fun w => B.eval w - Real.exp (-(M + 1))) g' z := by
      intro z hz0 hz1
      obtain ⟨Bd, hBd⟩ := hBdiff z hz0 hz1
      refine ⟨Bd - 0, HasDerivAt_sub B.eval (fun _ => Real.exp (-(M + 1))) Bd 0 z hBd
        (HasDerivAt_const _ z)⟩
    have hga : (fun w => B.eval w - Real.exp (-(M + 1))) x0 < 0 := by
      show B.eval x0 - Real.exp (-(M + 1)) < 0
      have h1 : B.eval x0 < Real.exp (-(M + 1)) := lt_of_le_of_lt hBx0 (Real.exp_pos _)
      exact sub_neg_of_lt' h1
    have hgb : 0 < (fun w => B.eval w - Real.exp (-(M + 1))) x1 := by
      show 0 < B.eval x1 - Real.exp (-(M + 1))
      exact sub_pos_of_lt hcase
    obtain ⟨c, hc0, hc1, hBc⟩ := intermediate_value_of_hasDerivAt
      (fun w => B.eval w - Real.exp (-(M + 1))) x0 x1 hx0x1 hdiff2 hga hgb
    have hBceq : B.eval c = Real.exp (-(M + 1)) := by
      have h1 : B.eval c - Real.exp (-(M + 1)) + Real.exp (-(M + 1)) = 0 + Real.exp (-(M + 1)) := by
        rw [hBc]
      have h2 : B.eval c - Real.exp (-(M + 1)) + Real.exp (-(M + 1)) = B.eval c := by mach_ring
      have h3 : (0 : Real) + Real.exp (-(M + 1)) = Real.exp (-(M + 1)) := by mach_ring
      rw [h2, h3] at h1
      exact h1
    refine ⟨c, ?_⟩
    show M < Real.exp (A.eval c) - Real.log (B.eval c)
    rw [hBceq, Real.log_exp]
    have hexpA : (0 : Real) ≤ Real.exp (A.eval c) := le_of_lt (Real.exp_pos _)
    have hstep : M + 1 ≤ Real.exp (A.eval c) - -(M + 1) := by
      have h1 : (0 : Real) - -(M + 1) ≤ Real.exp (A.eval c) - -(M + 1) :=
        sub_le_sub_right hexpA (-(M + 1))
      have h2 : (0 : Real) - -(M + 1) = M + 1 := by mach_ring
      rwa [h2] at h1
    have hlt : M < M + 1 := by
      have h := add_lt_add_left zero_lt_one_ax M
      rwa [add_zero] at h
    exact lt_of_lt_of_le hlt hstep
  · refine ⟨x1, ?_⟩
    show M < Real.exp (A.eval x1) - Real.log (B.eval x1)
    rw [← hcase, Real.log_exp]
    have hexpA : (0 : Real) ≤ Real.exp (A.eval x1) := le_of_lt (Real.exp_pos _)
    have hstep : M + 1 ≤ Real.exp (A.eval x1) - -(M + 1) := by
      have h1 : (0 : Real) - -(M + 1) ≤ Real.exp (A.eval x1) - -(M + 1) :=
        sub_le_sub_right hexpA (-(M + 1))
      have h2 : (0 : Real) - -(M + 1) = M + 1 := by mach_ring
      rwa [h2] at h1
    have hlt : M < M + 1 := by
      have h := add_lt_add_left zero_lt_one_ax M
      rwa [add_zero] at h
    exact lt_of_lt_of_le hlt hstep
  · refine ⟨x1, ?_⟩
    show M < Real.exp (A.eval x1) - Real.log (B.eval x1)
    have hlog_le : Real.log (B.eval x1) ≤ -(M + 1) := by
      have h := log_mono hBx1pos (le_of_lt hcase)
      rwa [Real.log_exp] at h
    have hexpA : (0 : Real) ≤ Real.exp (A.eval x1) := le_of_lt (Real.exp_pos _)
    have hstep1 : Real.exp (A.eval x1) - -(M + 1) ≤ Real.exp (A.eval x1) - Real.log (B.eval x1) :=
      sub_le_sub_left hlog_le _
    have hstep2 : M + 1 ≤ Real.exp (A.eval x1) - -(M + 1) := by
      have h1 : (0 : Real) - -(M + 1) ≤ Real.exp (A.eval x1) - -(M + 1) :=
        sub_le_sub_right hexpA (-(M + 1))
      have h2 : (0 : Real) - -(M + 1) = M + 1 := by mach_ring
      rwa [h2] at h1
    have hlt : M < M + 1 := by
      have h := add_lt_add_left zero_lt_one_ax M
      rwa [add_zero] at h
    exact lt_of_lt_of_le hlt (le_trans hstep2 hstep1)

/-- Weakened mirror: `B(x1) ≤ 0` suffices. -/
theorem eml_A_pos_nonpos_unbounded_above (A B : EMLTree) (x0 x1 : Real) (hx0x1 : x0 < x1)
    (hBx0pos : 0 < B.eval x0) (hBx1 : B.eval x1 ≤ 0)
    (hBdiff : ∀ z : Real, x0 ≤ z → z ≤ x1 → ∃ Bd : Real, HasDerivAt B.eval Bd z) (M : Real) :
    ∃ x : Real, M < (EMLTree.eml A B).eval x := by
  rcases lt_total (Real.exp (-(M + 1))) (B.eval x0) with hcase | hcase | hcase
  · have hdiff2 : ∀ z : Real, x0 ≤ z → z ≤ x1 →
        ∃ h' : Real, HasDerivAt (fun w => Real.exp (-(M + 1)) - B.eval w) h' z := by
      intro z hz0 hz1
      obtain ⟨Bd, hBd⟩ := hBdiff z hz0 hz1
      refine ⟨0 - Bd, HasDerivAt_sub (fun _ => Real.exp (-(M + 1))) B.eval 0 Bd z
        (HasDerivAt_const _ z) hBd⟩
    have hha : (fun w => Real.exp (-(M + 1)) - B.eval w) x0 < 0 := by
      show Real.exp (-(M + 1)) - B.eval x0 < 0
      exact sub_neg_of_lt' hcase
    have hhb : 0 < (fun w => Real.exp (-(M + 1)) - B.eval w) x1 := by
      show 0 < Real.exp (-(M + 1)) - B.eval x1
      have h1 : B.eval x1 < Real.exp (-(M + 1)) := lt_of_le_of_lt hBx1 (Real.exp_pos _)
      exact sub_pos_of_lt h1
    obtain ⟨c, hc0, hc1, hBc⟩ := intermediate_value_of_hasDerivAt
      (fun w => Real.exp (-(M + 1)) - B.eval w) x0 x1 hx0x1 hdiff2 hha hhb
    have hBceq : B.eval c = Real.exp (-(M + 1)) := by
      have h1 : Real.exp (-(M + 1)) - B.eval c + B.eval c = 0 + B.eval c := by rw [hBc]
      have h2 : Real.exp (-(M + 1)) - B.eval c + B.eval c = Real.exp (-(M + 1)) := by mach_ring
      have h3 : (0 : Real) + B.eval c = B.eval c := by mach_ring
      rw [h2, h3] at h1
      exact h1.symm
    refine ⟨c, ?_⟩
    show M < Real.exp (A.eval c) - Real.log (B.eval c)
    rw [hBceq, Real.log_exp]
    have hexpA : (0 : Real) ≤ Real.exp (A.eval c) := le_of_lt (Real.exp_pos _)
    have hstep : M + 1 ≤ Real.exp (A.eval c) - -(M + 1) := by
      have h1 : (0 : Real) - -(M + 1) ≤ Real.exp (A.eval c) - -(M + 1) :=
        sub_le_sub_right hexpA (-(M + 1))
      have h2 : (0 : Real) - -(M + 1) = M + 1 := by mach_ring
      rwa [h2] at h1
    have hlt : M < M + 1 := by
      have h := add_lt_add_left zero_lt_one_ax M
      rwa [add_zero] at h
    exact lt_of_lt_of_le hlt hstep
  · refine ⟨x0, ?_⟩
    show M < Real.exp (A.eval x0) - Real.log (B.eval x0)
    rw [← hcase, Real.log_exp]
    have hexpA : (0 : Real) ≤ Real.exp (A.eval x0) := le_of_lt (Real.exp_pos _)
    have hstep : M + 1 ≤ Real.exp (A.eval x0) - -(M + 1) := by
      have h1 : (0 : Real) - -(M + 1) ≤ Real.exp (A.eval x0) - -(M + 1) :=
        sub_le_sub_right hexpA (-(M + 1))
      have h2 : (0 : Real) - -(M + 1) = M + 1 := by mach_ring
      rwa [h2] at h1
    have hlt : M < M + 1 := by
      have h := add_lt_add_left zero_lt_one_ax M
      rwa [add_zero] at h
    exact lt_of_lt_of_le hlt hstep
  · refine ⟨x0, ?_⟩
    show M < Real.exp (A.eval x0) - Real.log (B.eval x0)
    have hlog_le : Real.log (B.eval x0) ≤ -(M + 1) := by
      have h := log_mono hBx0pos (le_of_lt hcase)
      rwa [Real.log_exp] at h
    have hexpA : (0 : Real) ≤ Real.exp (A.eval x0) := le_of_lt (Real.exp_pos _)
    have hstep1 : Real.exp (A.eval x0) - -(M + 1) ≤ Real.exp (A.eval x0) - Real.log (B.eval x0) :=
      sub_le_sub_left hlog_le _
    have hstep2 : M + 1 ≤ Real.exp (A.eval x0) - -(M + 1) := by
      have h1 : (0 : Real) - -(M + 1) ≤ Real.exp (A.eval x0) - -(M + 1) :=
        sub_le_sub_right hexpA (-(M + 1))
      have h2 : (0 : Real) - -(M + 1) = M + 1 := by mach_ring
      rwa [h2] at h1
    have hlt : M < M + 1 := by
      have h := add_lt_add_left zero_lt_one_ax M
      rwa [add_zero] at h
    exact lt_of_lt_of_le hlt (le_trans hstep2 hstep1)

/-- **The necessary-condition packaging.** Given TWO points with `B` mixed-sign between them
(one `≤0`, one `>0`), regardless of which comes first, `eml A B` is unbounded above. This is the
form a "boundedness ⟹ sign-definite" argument needs: it doesn't know in advance which of its two
witness points is smaller. -/
theorem eml_A_B_unbounded_of_mixed_sign (A B : EMLTree)
    (hBdiff : ∀ z : Real, ∃ Bd : Real, HasDerivAt B.eval Bd z)
    (p q : Real) (hBp : B.eval p ≤ 0) (hBq : 0 < B.eval q) (M : Real) :
    ∃ x : Real, M < (EMLTree.eml A B).eval x := by
  rcases lt_total p q with hpq | hpq | hpq
  · exact eml_A_nonpos_pos_unbounded_above A B p q hpq hBp hBq (fun z _ _ => hBdiff z) M
  · exfalso
    rw [hpq] at hBp
    exact lt_irrefl_ax (B.eval q) (lt_of_le_of_lt hBp hBq)
  · exact eml_A_pos_nonpos_unbounded_above A B q p hpq hBq hBp (fun z _ _ => hBdiff z) M

theorem le_zero_or_pos (x : Real) : x ≤ 0 ∨ 0 < x := by
  rcases lt_total x 0 with h | h | h
  · left; exact le_of_lt h
  · left; exact le_of_eq h
  · right; exact h

/-- **The main closing theorem for the "positive half."** If `eml A B` is bounded ABOVE and `B`
is differentiable everywhere, `B` must be SIGN-DEFINITE throughout `ℝ`: either strictly positive
everywhere, or non-positive everywhere. There is no third option (touching zero anywhere while
being positive anywhere else — regardless of whether `B` ever goes negative — already forces
unboundedness, by `eml_A_B_unbounded_of_mixed_sign`). -/
theorem eml_A_B_bounded_above_sign_definite (A B : EMLTree)
    (hBdiff : ∀ z : Real, ∃ Bd : Real, HasDerivAt B.eval Bd z)
    (M : Real) (hbdd : ∀ x : Real, (EMLTree.eml A B).eval x ≤ M) :
    (∀ x : Real, 0 < B.eval x) ∨ (∀ x : Real, B.eval x ≤ 0) := by
  refine Classical.byContradiction (fun hcon => ?_)
  have hex1 : ∃ p : Real, B.eval p ≤ 0 := by
    refine Classical.byContradiction (fun hcon1 => ?_)
    apply hcon
    left
    intro x
    rcases le_zero_or_pos (B.eval x) with h | h
    · exact absurd ⟨x, h⟩ hcon1
    · exact h
  have hex2 : ∃ q : Real, 0 < B.eval q := by
    refine Classical.byContradiction (fun hcon2 => ?_)
    apply hcon
    right
    intro x
    rcases le_zero_or_pos (B.eval x) with h | h
    · exact h
    · exact absurd ⟨x, h⟩ hcon2
  obtain ⟨p, hp⟩ := hex1
  obtain ⟨q, hq⟩ := hex2
  obtain ⟨x, hx⟩ := eml_A_B_unbounded_of_mixed_sign A B hBdiff p q hp hq M
  exact lt_irrefl_ax M (lt_of_lt_of_le hx (hbdd x))

/-- **The "non-positive everywhere" disjunct is degenerate.** If `B ≤ 0` everywhere, `eml A B`
reduces IDENTICALLY to `exp(A.eval ·)` — the entire `B` branch is dead code, confirming the
`eml_A_B_bounded_above_sign_definite` dichotomy's second case adds no genuinely new tree shape. -/
theorem eml_A_B_eq_exp_A_of_nonpos (A B : EMLTree) (hB : ∀ x : Real, B.eval x ≤ 0) (x : Real) :
    (EMLTree.eml A B).eval x = Real.exp (A.eval x) := by
  show Real.exp (A.eval x) - Real.log (B.eval x) = _
  rw [log_nonpos (hB x), sub_zero]

end Real
end MachLib
