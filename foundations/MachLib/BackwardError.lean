import MachLib.Basic
import MachLib.Lemmas
import MachLib.Forge
import MachLib.Ring
import MachLib.MPolyRing
import MachLib.FPModel

/-!
# Backward error — the dual lens

Forward error asks *how far is the computed value from `f(exact)`?* **Backward**
error asks the dual: *the computed value is `f(exact)` for slightly-perturbed
inputs.* For ill-conditioned problems the backward view is often the honest one —
the algorithm is "good" if it solves a nearby problem exactly, even when the
forward error is large (because the problem itself is sensitive).

In the standard model `fl(a∘b) = (a∘b)(1+δ)`, every rounded op is *exactly* the
operation on relatively-perturbed inputs:

* `mul_backward` — `fl(a·b) = a'·b` with `|a'−a| ≤ w·|a|` (perturb one factor);
* `add_backward` — `fl(a+b) = a'+b'` with each input perturbed by `≤ w·|·|`.

This is the seed of the backward-stability theory (Higham): a rounded inner
product is the *exact* inner product of inputs each perturbed by `≤ γ_n`. The
condition number then maps backward error to forward error (`fwd ≲ κ·bwd`) —
joining this lens to the κ-analysis. `sorryAx`-free.
-/

namespace MachLib.Real

/-! fresh-var ring identities (obtain'd `δ` can't go through mach_mpoly's parser). -/
theorem bw_mulcomm (a b d : Real) : (a * b) * (1 + d) = (a * (1 + d)) * b := by
  mach_mpoly [a, b, d]
theorem bw_distrib (a b d : Real) : (a + b) * (1 + d) = a * (1 + d) + b * (1 + d) := by
  mach_mpoly [a, b, d]
theorem bw_pert_eq (a d : Real) : a * (1 + d) - a = a * d := by mach_mpoly [a, d]

/-- `|δ| ≤ w` from a `RoundsW` witness. -/
theorem roundsW_delta_abs {w δ : Real}
    (hδl : -w ≤ δ) (hδu : δ ≤ w) : abs δ ≤ w := by
  apply abs_le_of hδu
  have h := neg_le_neg hδl
  rwa [show -(-w) = w from by mach_ring] at h

/-- The perturbation a single relative `δ` induces: `|a·δ| ≤ w·|a|`. -/
theorem pert_bound {a δ w : Real} (h : abs δ ≤ w) : abs (a * δ) ≤ w * abs a := by
  rw [abs_mul]
  exact le_trans (mul_le_mul_of_nonneg_left h (abs_nonneg a))
                 (le_of_eq (mul_comm (abs a) w))

/-- **Backward error of a rounded product.** The computed product is the *exact*
product of a perturbed first factor. -/
theorem mul_backward {w a b p : Real} (hp : RoundsW w p (a * b)) :
    ∃ a', p = a' * b ∧ abs (a' - a) ≤ w * abs a := by
  obtain ⟨δ, hδl, hδu, hpeq⟩ := hp
  refine ⟨a * (1 + δ), ?_, ?_⟩
  · rw [hpeq]; exact bw_mulcomm a b δ
  · rw [bw_pert_eq a δ]; exact pert_bound (roundsW_delta_abs hδl hδu)

/-- **Backward error of a rounded sum.** The computed sum is the *exact* sum of
both inputs, each relatively perturbed by `≤ w`. -/
theorem add_backward {w a b p : Real} (hp : RoundsW w p (a + b)) :
    ∃ a' b', p = a' + b' ∧ abs (a' - a) ≤ w * abs a ∧ abs (b' - b) ≤ w * abs b := by
  obtain ⟨δ, hδl, hδu, hpeq⟩ := hp
  have hδabs := roundsW_delta_abs hδl hδu
  refine ⟨a * (1 + δ), b * (1 + δ), ?_, ?_, ?_⟩
  · rw [hpeq]; exact bw_distrib a b δ
  · rw [bw_pert_eq a δ]; exact pert_bound hδabs
  · rw [bw_pert_eq b δ]; exact pert_bound hδabs

/-! ## backward-error γₙ — a computed dot product is the exact dot of perturbed inputs -/

theorem bdot_eq (a b c d d1 d2 d3 : Real) :
    (a * b * (1 + d1) + c * d * (1 + d2)) * (1 + d3)
      = (a * (1 + d1) * (1 + d3)) * b + (c * (1 + d2) * (1 + d3)) * d := by
  mach_mpoly [a, b, c, d, d1, d2, d3]
theorem bpert2_eq (a d1 d3 : Real) :
    a * (1 + d1) * (1 + d3) - a = a * (d1 + d3 + d1 * d3) := by mach_mpoly [a, d1, d3]

/-- Two relative roundings compose to `≤ γ₂ = (1+w)²−1`:
`|δ₁+δ₃+δ₁δ₃| ≤ (1+w)(1+w)−1`. -/
theorem two_delta_bound {w δ1 δ3 : Real} (hw0 : 0 ≤ w) (h1 : abs δ1 ≤ w) (h3 : abs δ3 ≤ w) :
    abs (δ1 + δ3 + δ1 * δ3) ≤ (1 + w) * (1 + w) - 1 := by
  have htri : abs (δ1 + δ3 + δ1 * δ3) ≤ (abs δ1 + abs δ3) + abs (δ1 * δ3) :=
    le_trans (abs_add (δ1 + δ3) (δ1 * δ3)) (add_le_add_both (abs_add δ1 δ3) (le_refl _))
  have hprod : abs (δ1 * δ3) ≤ w * w := by
    rw [abs_mul]
    exact le_trans (mul_le_mul_of_nonneg_right h1 (abs_nonneg δ3))
                   (mul_le_mul_of_nonneg_left h3 hw0)
  exact le_trans htri (le_trans (add_le_add_both (add_le_add_both h1 h3) hprod)
    (le_of_eq (show (w + w) + w * w = (1 + w) * (1 + w) - 1 from by mach_mpoly [w])))

/-- **Backward stability of `dot2`** (the γₙ result, n=2). The computed
`fl(a·b + c·d)` is the *exact* dot product `a'·b + c'·d` of inputs each perturbed
relatively by `≤ γ₂ = (1+w)²−1`. The algorithm solves a nearby problem exactly —
the honest statement for an inner product, independent of its conditioning. -/
theorem dot2_backward {w a b c d p1 p2 r : Real} (hw0 : 0 ≤ w)
    (hp1 : RoundsW w p1 (a * b)) (hp2 : RoundsW w p2 (c * d)) (hr : RoundsW w r (p1 + p2)) :
    ∃ a' c', r = a' * b + c' * d
      ∧ abs (a' - a) ≤ ((1 + w) * (1 + w) - 1) * abs a
      ∧ abs (c' - c) ≤ ((1 + w) * (1 + w) - 1) * abs c := by
  obtain ⟨δ1, hδ1l, hδ1u, hpeq1⟩ := hp1
  obtain ⟨δ2, hδ2l, hδ2u, hpeq2⟩ := hp2
  obtain ⟨δ3, hδ3l, hδ3u, hpeq3⟩ := hr
  refine ⟨a * (1 + δ1) * (1 + δ3), c * (1 + δ2) * (1 + δ3), ?_, ?_, ?_⟩
  · rw [hpeq3, hpeq1, hpeq2]; exact bdot_eq a b c d δ1 δ2 δ3
  · rw [bpert2_eq a δ1 δ3, abs_mul]
    exact le_trans
      (mul_le_mul_of_nonneg_left
        (two_delta_bound hw0 (roundsW_delta_abs hδ1l hδ1u) (roundsW_delta_abs hδ3l hδ3u))
        (abs_nonneg a))
      (le_of_eq (mul_comm (abs a) ((1 + w) * (1 + w) - 1)))
  · rw [bpert2_eq c δ2 δ3, abs_mul]
    exact le_trans
      (mul_le_mul_of_nonneg_left
        (two_delta_bound hw0 (roundsW_delta_abs hδ2l hδ2u) (roundsW_delta_abs hδ3l hδ3u))
        (abs_nonneg c))
      (le_of_eq (mul_comm (abs c) ((1 + w) * (1 + w) - 1)))

/-! ## general γₙ — `n` roundings compose to `(1+w)ⁿ − 1` -/

/-- Product of `(1 + δᵢ)` over a list of relative perturbations. -/
noncomputable def prodDelta : List Real → Real
  | []      => 1
  | d :: ds => (1 + d) * prodDelta ds

theorem pdb_ring (w N : Real) : w * N + (N - 1) = (1 + w) * N - 1 := by mach_mpoly [w, N]
theorem pdb_ring2 (N : Real) : (1 : Real) + (N - 1) = N := by mach_mpoly [N]
theorem pdb_split (d P : Real) : (1 + d) * P - 1 = d * P + (P - 1) := by mach_mpoly [d, P]

/-- **General γₙ.** The product of `n` relative roundings (`|δᵢ| ≤ w`) is within
`(1+w)ⁿ − 1` of 1: `|∏(1+δᵢ) − 1| ≤ (1+w)^n − 1`. The `n`-term generalisation of
`two_delta_bound` — the core of `n`-term forward/backward error (Higham's `γₙ`). -/
theorem prod_delta_bound {w : Real} (hw0 : 0 ≤ w) :
    ∀ (ds : List Real), (∀ d, d ∈ ds → abs d ≤ w) →
      abs (prodDelta ds - 1) ≤ npow ds.length (1 + w) - 1
  | [], _ => by
      have h : abs (prodDelta [] - 1) = npow ([] : List Real).length (1 + w) - 1 := by
        simp only [prodDelta, List.length_nil, npow]
        rw [show (1 : Real) - 1 = 0 from by mach_ring, abs_of_nonneg (le_refl (0 : Real))]
      exact le_of_eq h
  | d :: ds, hmem => by
      have hd : abs d ≤ w := hmem d (List.mem_cons_self d ds)
      have ih := prod_delta_bound hw0 ds (fun d' hd' => hmem d' (List.mem_cons_of_mem d hd'))
      have hPmag : abs (prodDelta ds) ≤ npow ds.length (1 + w) := by
        have ht := abs_le_add_err ih
        rwa [show abs (1 : Real) = 1 from abs_of_nonneg (le_of_lt one_pos),
             pdb_ring2 (npow ds.length (1 + w))] at ht
      show abs (prodDelta (d :: ds) - 1) ≤ npow (d :: ds).length (1 + w) - 1
      rw [show prodDelta (d :: ds) = (1 + d) * prodDelta ds from rfl,
          show (d :: ds).length = ds.length + 1 from rfl,
          pdb_split d (prodDelta ds)]
      refine le_trans (abs_add _ _) ?_
      have hdP : abs (d * prodDelta ds) ≤ w * npow ds.length (1 + w) := by
        rw [abs_mul]
        exact le_trans (mul_le_mul_of_nonneg_right hd (abs_nonneg _))
                       (mul_le_mul_of_nonneg_left hPmag hw0)
      refine le_trans (add_le_add_both hdP ih) ?_
      rw [npow_succ]
      exact le_of_eq (pdb_ring w (npow ds.length (1 + w)))

end MachLib.Real
