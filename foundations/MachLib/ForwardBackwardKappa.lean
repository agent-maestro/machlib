import MachLib.BackwardError
import MachLib.ConditionNumber

/-!
# Where the three lenses meet — `forward ≤ κ · backward` for the inner product

The certifier carries three views of the same rounded computation:

* **forward** error (`gexpr_sound`): `|computed − exact| ≤ E`;
* **backward** error (`dot2_backward`): the computed value is the *exact* value of
  perturbed inputs, each within `γ₂ = (1+w)²−1`;
* the **condition number** (`kappa_bound_dominant`): `κ = Σ|tᵢ|/|exact|` measures how a
  backward perturbation amplifies into a forward error.

They were separate files. This joins them on the inner product `a·b + c·d`. From the
*backward* result, the forward error is `|Σ(tᵢ′−tᵢ)| ≤ γ₂·Σ|tᵢ|` (`dot2_fwd_from_bwd`) —
forward error derived from backward error, with no fresh rounding analysis. Then the
*condition number* turns that absolute bound into a genuine *relative* one: when one product
dominates (`κ ≤ 3`, no cancellation), the relative forward error is `≤ 3·γ₂`
(`dot2_fwd_wellcond`). That is Higham's `fwd ≲ κ·bwd` made concrete — the same `γ₂` governs
both the backward perturbation and the forward bound, scaled by the conditioning. `sorryAx`-free.
-/

namespace MachLib.Real

/-- A perturbed term's contribution to the forward error: if `|x′−x| ≤ G·|x|`, the term's
error is `|(x′−x)·y| ≤ G·|x·y|` — the backward perturbation `G` scaled by the term magnitude. -/
theorem pert_term_bound {x x' y G : Real} (h : abs (x' - x) ≤ G * abs x) :
    abs ((x' - x) * y) ≤ G * abs (x * y) := by
  rw [abs_mul, abs_mul]
  refine le_trans (mul_le_mul_of_nonneg_right h (abs_nonneg y)) (le_of_eq ?_)
  mach_mpoly [G, abs x, abs y]

/-- Ring identity (clean names — obtain'd primed vars can't go through `mach_mpoly`'s parser):
the dot of perturbed inputs minus the exact dot is the sum of per-term error contributions. -/
theorem fwd_split_eq (A b C d a c : Real) :
    (A * b + C * d) - (a * b + c * d) = (A - a) * b + (C - c) * d := by
  mach_mpoly [A, b, C, d, a, c]

/-- **Forward error from backward error.** Feeding `dot2_backward` (the computed inner product
is the exact dot of `γ₂`-perturbed inputs) through the triangle inequality gives the forward
error directly: `|r − (a·b + c·d)| ≤ γ₂·(|a·b| + |c·d|)`. No new rounding analysis — the
forward bound is a corollary of backward stability. The right-hand side is `γ₂` times the
*conditioning quantity* `Σ|tᵢ|`, which is exactly the form the condition number consumes. -/
theorem dot2_fwd_from_bwd {w a b c d p1 p2 r : Real} (hw0 : 0 ≤ w)
    (hp1 : RoundsW w p1 (a * b)) (hp2 : RoundsW w p2 (c * d)) (hr : RoundsW w r (p1 + p2)) :
    abs (r - (a * b + c * d))
      ≤ ((1 + w) * (1 + w) - 1) * (abs (a * b) + abs (c * d)) := by
  obtain ⟨a', c', hreq, ha, hc⟩ := dot2_backward hw0 hp1 hp2 hr
  have hsplit : r - (a * b + c * d) = (a' - a) * b + (c' - c) * d := by
    rw [hreq]; exact fwd_split_eq a' b c' d a c
  rw [hsplit]
  refine le_trans (abs_add ((a' - a) * b) ((c' - c) * d)) ?_
  refine le_trans (add_le_add_both (pert_term_bound ha) (pert_term_bound hc)) (le_of_eq ?_)
  mach_mpoly [w, abs (a * b), abs (c * d)]

/-- `γ₂ = (1+w)²−1 ≥ 0` for `w ≥ 0` (it equals `2w + w²`). -/
theorem gamma2_nonneg {w : Real} (hw0 : 0 ≤ w) : 0 ≤ (1 + w) * (1 + w) - 1 := by
  have e : (1 + w) * (1 + w) - 1 = w * (1 + 1) + w * w := by mach_mpoly [w]
  rw [e]
  have h2 : (0 : Real) ≤ 1 + 1 := add_nonneg_ea (le_of_lt one_pos) (le_of_lt one_pos)
  exact add_nonneg_ea (mul_nonneg hw0 h2) (mul_nonneg hw0 hw0)

/-- **The three lenses, one theorem.** For a *well-conditioned* inner product — one product
dominates the other (`2·|c·d| ≤ |a·b|`, so `κ ≤ 3`, no cancellation) — the **relative** forward
error is bounded by `3·γ₂`:

    |r − (a·b + c·d)|  ≤  γ₂ · 3 · |a·b + c·d|.

Backward error supplies the `γ₂` (`dot2_fwd_from_bwd` ← `dot2_backward`); the condition number
supplies the `3` (`kappa_bound_dominant` turns `Σ|tᵢ|` into `≤ 3·|exact|`). This is Higham's
`forward ≲ κ · backward` for the inner product — the same `γ₂` that bounds the backward input
perturbation bounds the forward output error, amplified by exactly the conditioning. -/
theorem dot2_fwd_wellcond {w a b c d p1 p2 r : Real} (hw0 : 0 ≤ w)
    (hp1 : RoundsW w p1 (a * b)) (hp2 : RoundsW w p2 (c * d)) (hr : RoundsW w r (p1 + p2))
    (hdom : (1 + 1) * abs (c * d) ≤ abs (a * b)) :
    abs (r - (a * b + c * d))
      ≤ ((1 + w) * (1 + w) - 1) * ((1 + 1 + 1) * abs (a * b + c * d)) := by
  refine le_trans (dot2_fwd_from_bwd hw0 hp1 hp2 hr) ?_
  exact mul_le_mul_of_nonneg_left (kappa_bound_dominant hdom) (gamma2_nonneg hw0)

end MachLib.Real
