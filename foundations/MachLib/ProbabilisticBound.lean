import MachLib.OperatorBasisGeneral
import MachLib.Trig

/-!
# Probabilistic rounding error — the √n bound, conditioned on concentration

The certifier's forward-error bounds are WORST-CASE: an `n`-term sum is `≤ (n−1)·u·Σ|xᵢ|`, linear
in `n`, because every rounding is assumed to add adversarially. Higham & Mary (SISC 2019) proved
that under STOCHASTIC rounding the `n` rounding errors are mean-zero and *concentrate*, so the
error is `≈ √n·u·Σ|xᵢ|` with high probability — an asymptotic `√n` improvement. We measured
exactly this on the EML corpus (the error-vs-`n` slope is `0.50`, not `1.0`).

MachLib has no measure theory, so — exactly as `RoundsW` is the *model assumption* for the
deterministic certifier — the **probability is taken as a stated hypothesis**: a Hoeffding/Azuma
concentration bound `|err| ≤ λ·√(Σcⱼ²)·u` on the linearised error `Σⱼ cⱼ·δⱼ` (`δⱼ` the mean-zero
roundings, `cⱼ` the coefficients), which is what Higham–Mary establishes w.h.p. What Lean then
proves is the **deterministic consequence**, and that consequence *is* the reason concentration
buys `√n`: the L²-vs-L¹ gap. The worst-case bound spends the L¹ norm `Σ|cⱼ| ≤ n·B` (`sumAbs_le`,
linear); the probabilistic bound spends the L² norm `√(Σcⱼ²) ≤ √n·B` (`l2_le_sqrt_n`). Same
coefficients, `n` vs `√n`. `sorryAx`-free (rests on the model's `sqrt` axioms, as the certifier's
`√` already does).
-/

namespace MachLib.Real

/-- Sum of squares of the error coefficients — the L² (Euclidean) quantity. -/
noncomputable def sumSq : List Real → Real
  | [] => 0
  | x :: xs => x * x + sumSq xs

/-- Sum of magnitudes — the L¹ (worst-case) conditioning quantity. -/
noncomputable def sumAbs : List Real → Real
  | [] => 0
  | x :: xs => abs x + sumAbs xs

/-- Term count, as a real. -/
noncomputable def nterms : List Real → Real
  | [] => 0
  | _ :: xs => 1 + nterms xs

theorem nterms_nonneg : ∀ cs : List Real, (0 : Real) ≤ nterms cs
  | [] => le_refl 0
  | _ :: xs => by
      show (0 : Real) ≤ 1 + nterms xs
      exact add_nonneg_ea (le_of_lt one_pos) (nterms_nonneg xs)

/-- **L¹ bound (the worst case): `Σ|cⱼ| ≤ n·B`** — linear in the term count. This is the norm the
deterministic certifier spends (`RSum_bound`'s `labs`). -/
theorem sumAbs_le {B : Real} (hB : 0 ≤ B) :
    ∀ {cs : List Real}, (∀ c, c ∈ cs → abs c ≤ B) → sumAbs cs ≤ nterms cs * B
  | [], _ => by
      show (0 : Real) ≤ 0 * B
      rw [show (0 : Real) * B = 0 from by mach_ring]; exact le_refl 0
  | x :: xs, hbd => by
      show abs x + sumAbs xs ≤ (1 + nterms xs) * B
      have hx : abs x ≤ B := hbd x (List.mem_cons_self x xs)
      have hih : sumAbs xs ≤ nterms xs * B :=
        sumAbs_le hB (fun c hc => hbd c (List.mem_cons_of_mem x hc))
      calc abs x + sumAbs xs ≤ B + nterms xs * B := add_le_add_both hx hih
        _ = (1 + nterms xs) * B := by mach_mpoly [nterms xs, B]

/-- **L² bound: `Σcⱼ² ≤ n·B²`.** Each `cⱼ² ≤ B²`. -/
theorem sumSq_le {B : Real} (hB : 0 ≤ B) :
    ∀ {cs : List Real}, (∀ c, c ∈ cs → abs c ≤ B) → sumSq cs ≤ nterms cs * (B * B)
  | [], _ => by
      show (0 : Real) ≤ 0 * (B * B)
      rw [show (0 : Real) * (B * B) = 0 from by mach_ring]; exact le_refl 0
  | x :: xs, hbd => by
      show x * x + sumSq xs ≤ (1 + nterms xs) * (B * B)
      have hx : abs x ≤ B := hbd x (List.mem_cons_self x xs)
      have hxx : x * x ≤ B * B := by
        rw [← abs_of_nonneg (sq_nonneg x), abs_mul]
        exact le_trans (mul_le_mul_of_nonneg_right hx (abs_nonneg x))
                       (mul_le_mul_of_nonneg_left hx hB)
      have hih : sumSq xs ≤ nterms xs * (B * B) :=
        sumSq_le hB (fun c hc => hbd c (List.mem_cons_of_mem x hc))
      calc x * x + sumSq xs ≤ B * B + nterms xs * (B * B) := add_le_add_both hxx hih
        _ = (1 + nterms xs) * (B * B) := by mach_mpoly [nterms xs, B]

/-- **The L²-vs-L¹ gap, in one line: `√(Σcⱼ²) ≤ √n · B`.** This is *why* concentration buys `√n`
— the same coefficients that sum to `n·B` in L¹ have Euclidean norm only `√n·B`. -/
theorem l2_le_sqrt_n {cs : List Real} {B : Real} (hB : 0 ≤ B)
    (hbd : ∀ c, c ∈ cs → abs c ≤ B) :
    sqrt (sumSq cs) ≤ sqrt (nterms cs) * B := by
  apply sqrt_le_of_le_sq (mul_nonneg (sqrt_nonneg _) hB)
  have hsq : (sqrt (nterms cs) * B) * (sqrt (nterms cs) * B) = nterms cs * (B * B) := by
    have e1 : (sqrt (nterms cs) * B) * (sqrt (nterms cs) * B)
            = (sqrt (nterms cs) * sqrt (nterms cs)) * (B * B) := by
      mach_mpoly [sqrt (nterms cs), B]
    rw [e1, sqrt_sq_nonneg (nterms cs) (nterms_nonneg cs)]
  rw [hsq]
  exact sumSq_le hB hbd

/-- **The probabilistic forward-error bound.** *Given* the Higham–Mary concentration hypothesis —
the linearised error is within `λ·√(Σcⱼ²)·u` (what stochastic rounding delivers w.h.p.) — and a
uniform bound `B` on the coefficients, the forward error is `≤ λ·√n·B·u`. The `√n` (vs the
worst-case `n·B·u` from `sumAbs_le`) is exactly the L²-vs-L¹ gap `l2_le_sqrt_n`. The probability
lives entirely in the hypothesis; the improvement is the deterministic theorem. -/
theorem prob_sqrt_n_bound {cs : List Real} {B u lam err : Real}
    (hu : 0 ≤ u) (hlam : 0 ≤ lam) (hB : 0 ≤ B)
    (hbd : ∀ c, c ∈ cs → abs c ≤ B)
    (hconc : abs err ≤ lam * sqrt (sumSq cs) * u) :
    abs err ≤ lam * (sqrt (nterms cs) * B) * u :=
  le_trans hconc
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (l2_le_sqrt_n hB hbd) hlam) hu)

end MachLib.Real
