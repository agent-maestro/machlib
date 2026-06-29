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

/-! ## three terms — PID's controller MAC (`Kp·e + Ki·i + Kd·d`) is backward stable -/

/-- Build the 3-term result from the 2-term `bdot_eq` (the 11-atom direct identity overflows
`mach_mpoly`): once the inner sum is `A·b + C·d`, the outer add of the third product and the
final rounding distribute as below. 8 atoms — fits. -/
theorem bdot3_outer_eq (A b C d e f d4 d5 : Real) :
    ((A * b + C * d) + e * f * (1 + d4)) * (1 + d5)
      = (A * (1 + d5)) * b + (C * (1 + d5)) * d + (e * (1 + d4) * (1 + d5)) * f := by
  mach_mpoly [A, b, C, d, e, f, d4, d5]

/-- The accumulated factor on a leading term: `a·(1+d1)(1+d3)` carried through the final add's
`(1+d5)` is the 3-rounding chain `a·∏(1+δ)`. -/
theorem collapse3 (a d1 d3 d5 : Real) :
    (a * (1 + d1) * (1 + d3)) * (1 + d5) = a * prodDelta [d1, d3, d5] := by
  show (a * (1 + d1) * (1 + d3)) * (1 + d5) = a * ((1 + d1) * ((1 + d3) * ((1 + d5) * 1)))
  mach_mpoly [a, d1, d3, d5]

/-- The last term flows through only 2 roundings; pad with a `0` perturbation to length 3 so its
bound is the uniform `γ₃` (`prodDelta [d4,d5,0] = (1+d4)(1+d5)`). -/
theorem collapse3_pad (e d4 d5 : Real) :
    e * (1 + d4) * (1 + d5) = e * prodDelta [d4, d5, (0 : Real)] := by
  show e * (1 + d4) * (1 + d5) = e * ((1 + d4) * ((1 + d5) * ((1 + (0 : Real)) * 1)))
  mach_mpoly [e, d4, d5]

/-- `|t| ≤ w` for every element of a 3-list, from the three element bounds. -/
theorem mem3_bound {w x y z : Real} (hx : abs x ≤ w) (hy : abs y ≤ w) (hz : abs z ≤ w) :
    ∀ t, t ∈ [x, y, z] → abs t ≤ w := by
  intro t ht
  cases ht with
  | head => exact hx
  | tail _ ht2 => cases ht2 with
    | head => exact hy
    | tail _ ht3 => cases ht3 with
      | head => exact hz
      | tail _ ht4 => cases ht4

/-- **Backward stability of the 3-term inner product (PID's MAC).** The computed
`fl(fl(fl(a·b) + fl(c·d)) + fl(e·f))` — the controller law `Kp·e + Ki·i + Kd·d` — is the
*exact* inner product `a'·b + c'·d + e'·f` of inputs each relatively perturbed by `≤ γ₃ =
(1+w)³−1`. The PID controller solves a nearby problem exactly: the computed output is the true
output of slightly-mistuned gains, independent of conditioning. -/
theorem dot3_backward {w a b c d e f p1 p2 p3 q r : Real} (hw0 : 0 ≤ w)
    (hp1 : RoundsW w p1 (a * b)) (hp2 : RoundsW w p2 (c * d)) (hp3 : RoundsW w p3 (e * f))
    (hq : RoundsW w q (p1 + p2)) (hr : RoundsW w r (q + p3)) :
    ∃ a' c' e', r = a' * b + c' * d + e' * f
      ∧ abs (a' - a) ≤ (npow 3 (1 + w) - 1) * abs a
      ∧ abs (c' - c) ≤ (npow 3 (1 + w) - 1) * abs c
      ∧ abs (e' - e) ≤ (npow 3 (1 + w) - 1) * abs e := by
  obtain ⟨δ1, h1l, h1u, e1⟩ := hp1
  obtain ⟨δ2, h2l, h2u, e2⟩ := hp2
  obtain ⟨δ4, h4l, h4u, e4⟩ := hp3
  obtain ⟨δ3, h3l, h3u, eq⟩ := hq
  obtain ⟨δ5, h5l, h5u, er⟩ := hr
  have habs1 := roundsW_delta_abs h1l h1u
  have habs2 := roundsW_delta_abs h2l h2u
  have habs3 := roundsW_delta_abs h3l h3u
  have habs4 := roundsW_delta_abs h4l h4u
  have habs5 := roundsW_delta_abs h5l h5u
  have hz : abs (0 : Real) ≤ w := by rw [abs_zero]; exact hw0
  have hq_eq : q = (a * (1 + δ1) * (1 + δ3)) * b + (c * (1 + δ2) * (1 + δ3)) * d := by
    rw [eq, e1, e2]; exact bdot_eq a b c d δ1 δ2 δ3
  refine ⟨a * prodDelta [δ1, δ3, δ5], c * prodDelta [δ2, δ3, δ5], e * prodDelta [δ4, δ5, (0 : Real)],
          ?_, ?_, ?_, ?_⟩
  · rw [er, hq_eq, e4,
        bdot3_outer_eq (a * (1 + δ1) * (1 + δ3)) b (c * (1 + δ2) * (1 + δ3)) d e f δ4 δ5,
        collapse3 a δ1 δ3 δ5, collapse3 c δ2 δ3 δ5, collapse3_pad e δ4 δ5]
  · exact chain_backward hw0 [δ1, δ3, δ5] (mem3_bound habs1 habs3 habs5)
  · exact chain_backward hw0 [δ2, δ3, δ5] (mem3_bound habs2 habs3 habs5)
  · exact chain_backward hw0 [δ4, δ5, (0 : Real)] (mem3_bound habs4 habs5 hz)

/-- `γ₃ = (1+w)³−1 ≥ 0` for `w ≥ 0`. -/
theorem gamma3_nonneg {w : Real} (hw0 : 0 ≤ w) : 0 ≤ npow 3 (1 + w) - 1 := by
  have e : npow 3 (1 + w) - 1 = w * (1 + 1 + 1) + (w * w * (1 + 1 + 1) + w * w * w) := by
    show (1 + w) * ((1 + w) * ((1 + w) * 1)) - 1 = _
    mach_mpoly [w]
  rw [e]
  have h1 : (0 : Real) ≤ 1 := le_of_lt one_pos
  have h3 : (0 : Real) ≤ 1 + 1 + 1 := add_nonneg_ea (add_nonneg_ea h1 h1) h1
  exact add_nonneg_ea (mul_nonneg hw0 h3)
    (add_nonneg_ea (mul_nonneg (mul_nonneg hw0 hw0) h3) (mul_nonneg (mul_nonneg hw0 hw0) hw0))

/-- Clean-named 3-term split (obtain'd primed vars can't go through `mach_mpoly`). -/
theorem fwd_split3_eq (A b C d E f a c e : Real) :
    (A * b + C * d + E * f) - (a * b + c * d + e * f)
      = (A - a) * b + (C - c) * d + (E - e) * f := by
  mach_mpoly [A, b, C, d, E, f, a, c, e]

/-- **Forward error of PID's MAC, from its backward stability.** `|computed − (ab+cd+ef)| ≤ γ₃·
(|ab|+|cd|+|ef|)`. Same move as `dot2_fwd_from_bwd`, three terms. -/
theorem dot3_fwd_from_bwd {w a b c d e f p1 p2 p3 q r : Real} (hw0 : 0 ≤ w)
    (hp1 : RoundsW w p1 (a * b)) (hp2 : RoundsW w p2 (c * d)) (hp3 : RoundsW w p3 (e * f))
    (hq : RoundsW w q (p1 + p2)) (hr : RoundsW w r (q + p3)) :
    abs (r - (a * b + c * d + e * f))
      ≤ (npow 3 (1 + w) - 1) * (abs (a * b) + abs (c * d) + abs (e * f)) := by
  obtain ⟨a', c', e', hreq, ha, hc, he⟩ := dot3_backward hw0 hp1 hp2 hp3 hq hr
  have hsplit : r - (a * b + c * d + e * f)
      = (a' - a) * b + (c' - c) * d + (e' - e) * f := by
    rw [hreq]; exact fwd_split3_eq a' b c' d e' f a c e
  rw [hsplit]
  refine le_trans (abs_add ((a' - a) * b + (c' - c) * d) ((e' - e) * f)) ?_
  refine le_trans (add_le_add_both (abs_add ((a' - a) * b) ((c' - c) * d)) (le_refl _)) ?_
  refine le_trans (add_le_add_both
    (add_le_add_both (pert_term_bound ha) (pert_term_bound hc)) (pert_term_bound he)) ?_
  exact le_of_eq (by mach_mpoly [npow 3 (1 + w), abs (a * b), abs (c * d), abs (e * f)])

/-- **The three lenses on PID's MAC.** When the proportional term dominates the integral and
derivative terms (`2·(|Ki·i| + |Kd·d|) ≤ |Kp·e|`, so `κ ≤ 3`, no cancellation), the **relative**
forward error of the controller output is `≤ 3·γ₃`. Backward stability (`dot3_backward`) supplies
`γ₃`; the condition number (`kappa_bound_dominant_list`) supplies the `3`. PID is `fwd ≲ κ·bwd`. -/
theorem dot3_fwd_wellcond {w a b c d e f p1 p2 p3 q r : Real} (hw0 : 0 ≤ w)
    (hp1 : RoundsW w p1 (a * b)) (hp2 : RoundsW w p2 (c * d)) (hp3 : RoundsW w p3 (e * f))
    (hq : RoundsW w q (p1 + p2)) (hr : RoundsW w r (q + p3))
    (hdom : (1 + 1) * (abs (c * d) + abs (e * f)) ≤ abs (a * b)) :
    abs (r - (a * b + c * d + e * f))
      ≤ (npow 3 (1 + w) - 1) * ((1 + 1 + 1) * abs (a * b + c * d + e * f)) := by
  refine le_trans (dot3_fwd_from_bwd hw0 hp1 hp2 hp3 hq hr)
    (mul_le_mul_of_nonneg_left ?_ (gamma3_nonneg hw0))
  have hsig : sigmaList [a * b, c * d, e * f] = abs (a * b) + abs (c * d) + abs (e * f) := by
    show abs (a * b) + (abs (c * d) + (abs (e * f) + 0)) = _
    mach_mpoly [abs (a * b), abs (c * d), abs (e * f)]
  have hsum : sumList [a * b, c * d, e * f] = a * b + c * d + e * f := by
    show a * b + (c * d + (e * f + 0)) = _
    mach_mpoly [a, b, c, d, e, f]
  have hdom' : (1 + 1) * sigmaList [c * d, e * f] ≤ abs (a * b) := by
    have hrest : sigmaList [c * d, e * f] = abs (c * d) + abs (e * f) := by
      show abs (c * d) + (abs (e * f) + 0) = _
      mach_mpoly [abs (c * d), abs (e * f)]
    rw [hrest]; exact hdom
  have hk := kappa_bound_dominant_list hdom'
  rw [hsig, hsum] at hk
  exact hk

end MachLib.Real
