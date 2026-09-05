import MachLib.EMLDecayLadderStep
import MachLib.EMLDepth2Form

/-!
# The `const_left` cell of the depth-4 rung, from the depth-3 decaying floor

`NodeDecayBound 3 3` (`EMLDecayLadderStep`) is the one proposition depth 4 of the decay ladder
rests on: for `A`, `B` of depth ≤ 3, a *positive* node `exp (A x) − log (B x)` is at least
`exp (−C − towerFn 3 x)`. Its `const_left` cell — `A = const c` — used to reduce to
`depth_le_three_gap_below`, which was **refuted** on 2026-09-03 (`depth_le_three_gap_below_refuted`,
`EMLDepth2Form`): a depth-≤3 value *can* approach a constant from below with a vanishing gap.

The replacement is `Depth3ApproachBelow` (`depth3ApproachBelow_holds`, 2026-09-05): the gap
vanishes, but no faster than `exp (−C − exp (exp x))`. This file spends that theorem on the cell
it was written for. With `A = const c` the node is `exp c − log (B x)`, positive exactly when
`B x < exp (exp c)`, and then

    node  =  log (exp (exp c)) − log (B x)  ≥  (exp (exp c) − B x) · exp (−exp c)

by the tangent line `1 + t ≤ exp t` at `t = −node`. The right-hand side is the depth-3 floor times
a constant, so `−log node ≤ (C + exp c) + exp (exp x)` — tower height 2, one below what the rung
asks for, which `towerFn_mono` absorbs.

**What this does and does not move.** One of the four cells of `NodeDecayBound 3 3` is now proved
at depth-3 children. The other three (`var_left`, whose constant-gap input was also refuted;
`bounded_left`; `growing_left`) are not, and `EMLDecayLadderStep`'s route map prices them at
roughly 2 400 lines of new gap analysis. The ledger does not move — a cell is not a rung — and
`EmlGermApproachResearch.md` says why the next move on this ladder is a falsification search, not
another cell.
-/

namespace MachLib

open Real

/-- **`A = const c` at depth-3 children, tower height 2.** If the node `exp c − log (Q x)` is
positive on a ray then it is at least `exp (−C' − exp (exp x))`, with `C' = C + exp c` and `C` the
constant of `depth3ApproachBelow_holds` at the target `exp (exp c)`. -/
theorem depth_four_decay_const_left (c : Real) (Q : EMLTree) (hQ : Q.depth ≤ 3) :
    ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → 0 < log (Q.eval x) →
      0 < exp c - log (Q.eval x) →
        -log (exp c - log (Q.eval x)) ≤ C + EMLTree.towerFn 2 x := by
  obtain ⟨C, X₀, hX₀, hfl⟩ := depth3ApproachBelow_holds Q hQ (exp (exp c))
  refine ⟨C + exp c, X₀, hX₀, ?_⟩
  intro x hx hlogpos hnode
  -- a strictly positive (totalised) log forces a strictly positive argument
  have hQpos : (0 : Real) < Q.eval x := by
    rcases lt_total 0 (Q.eval x) with h | h | h
    · exact h
    · exfalso
      have hz : log (Q.eval x) = 0 := by rw [← h]; exact log_nonpos (le_refl 0)
      rw [hz] at hlogpos
      exact absurd hlogpos (lt_irrefl_ax 0)
    · exfalso
      have hz : log (Q.eval x) = 0 := log_nonpos (le_of_lt h)
      rw [hz] at hlogpos
      exact absurd hlogpos (lt_irrefl_ax 0)
  -- the hypothesis says `log (Q x) < exp c`, i.e. `Q x < exp (exp c)`
  have hlt : log (Q.eval x) < exp c := by
    have u := add_lt_add_left hnode (log (Q.eval x))
    have e1 : log (Q.eval x) + 0 = log (Q.eval x) := by mach_ring
    have e2 : log (Q.eval x) + (exp c - log (Q.eval x)) = exp c := by
      mach_mpoly [log (Q.eval x), exp c]
    rw [e1, e2] at u; exact u
  have hQlt : Q.eval x < exp (exp c) := by
    have w := exp_lt hlt
    rw [exp_log hQpos] at w; exact w
  have hgap := hfl x hx hQlt
  -- tangent line at `−node`: `1 − node ≤ exp (−node) = Q x · exp (−exp c)`
  have h1 := one_add_le_exp (-(exp c - log (Q.eval x)))
  have e1 : exp (-(exp c - log (Q.eval x))) = Q.eval x * exp (-exp c) := by
    have e : -(exp c - log (Q.eval x)) = log (Q.eval x) + -exp c := by
      mach_mpoly [exp c, log (Q.eval x)]
    rw [e, exp_add, exp_log hQpos]
  rw [e1] at h1
  -- so `node ≥ (exp (exp c) − Q x) · exp (−exp c)`
  have h2 : (exp (exp c) - Q.eval x) * exp (-exp c) ≤ exp c - log (Q.eval x) := by
    have hk : exp (exp c) * exp (-exp c) = 1 := by
      have w := exp_neg_self_mul (exp c)
      rw [mul_comm] at w; exact w
    have e2 : (exp (exp c) - Q.eval x) * exp (-exp c)
        = exp (exp c) * exp (-exp c) - Q.eval x * exp (-exp c) := by
      mach_mpoly [exp (exp c), Q.eval x, exp (-exp c)]
    rw [e2, hk]
    have u := add_le_add_wit h1 (le_refl (exp c - log (Q.eval x) - Q.eval x * exp (-exp c)))
    have e3 : 1 + -(exp c - log (Q.eval x)) + (exp c - log (Q.eval x) - Q.eval x * exp (-exp c))
        = 1 - Q.eval x * exp (-exp c) := by
      mach_mpoly [exp c, log (Q.eval x), Q.eval x, exp (-exp c)]
    have e4 : Q.eval x * exp (-exp c) + (exp c - log (Q.eval x) - Q.eval x * exp (-exp c))
        = exp c - log (Q.eval x) := by
      mach_mpoly [exp c, log (Q.eval x), Q.eval x, exp (-exp c)]
    rw [e3, e4] at u; exact u
  -- the depth-3 floor, scaled by the constant, sits below the node
  have h3 := le_trans (mul_le_mul_of_nonneg_right hgap (le_of_lt (exp_pos (-exp c)))) h2
  rw [← exp_add] at h3
  -- take logarithms and rearrange
  have h4 := log_le_log (exp_pos _) h3
  rw [log_exp] at h4
  have hT : EMLTree.towerFn 2 x = exp (exp x) := rfl
  rw [hT]
  have u := neg_le_neg_wit h4
  have e5 : -(-C - exp (exp x) + -exp c) = C + exp c + exp (exp x) := by
    mach_mpoly [C, exp (exp x), exp c]
  rw [e5] at u; exact u

/-- **The same cell at the rung's own tower height.** `NodeDecayBound 3 3` asks for
`C + towerFn 3 x`; one rung of tower is monotone in the height, so the height-2 bound lifts. -/
theorem depth_four_decay_const_left_tower3 (c : Real) (Q : EMLTree) (hQ : Q.depth ≤ 3) :
    ∃ C X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → 0 < log (Q.eval x) →
      0 < exp c - log (Q.eval x) →
        -log (exp c - log (Q.eval x)) ≤ C + EMLTree.towerFn 3 x := by
  obtain ⟨C, X₀, hX₀, h⟩ := depth_four_decay_const_left c Q hQ
  refine ⟨C, X₀, hX₀, fun x hx h1 h2 => ?_⟩
  have hx1 : (1 : Real) ≤ x := le_trans hX₀ hx
  have hmono : EMLTree.towerFn 2 x ≤ EMLTree.towerFn 3 x := towerFn_mono 2 1 hx1
  exact le_trans (h x hx h1 h2) (add_le_add_wit (le_refl C) hmono)

end MachLib
