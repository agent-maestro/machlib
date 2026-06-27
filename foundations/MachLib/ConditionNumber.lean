import MachLib.Basic
import MachLib.Lemmas
import MachLib.Forge
import MachLib.Ring
import MachLib.MPolyRing
import MachLib.FPModel
import MachLib.ErrorAlgebra
import MachLib.ConditionedError

/-!
# The condition number — when the conditioned bound is tight

`ConditionedError` bounds a mixed-sign kernel's error against the *conditioning
quantity* `Σ|tᵢ|`. Whether that is a useful forward-error guarantee is governed
by the **condition number** `κ = Σ|tᵢ| / |exact|`:

* the conditioned bound is `≈ w·Σ|tᵢ|`, so the *relative* error is `≈ w·κ`;
* `κ ≥ 1` always (`Σ|tᵢ| ≥ |exact|`, `exact_le_sigma` = the triangle inequality);
* `κ = 1` **iff the terms share a sign** (`sigma_eq_exact_nonneg`): then
  `Σ|tᵢ| = |exact|` and the conditioned bound *is* the relative bound — the kernel
  is perfectly conditioned;
* `κ → ∞` near cancellation (`exact → 0` with `Σ|tᵢ|` fixed) — the conditioned
  bound stays true but the *relative* guarantee degrades, honestly.

So the well/ill-conditioned boundary is exactly the sign structure of the terms.
This is the characterisation; proving `κ`-bounds for general kernel families
(where signs are data-dependent) is the open research past it.
-/

namespace MachLib.Real

/-- `|x| = −x` for nonpositive `x` (the `abs_of_nonneg` companion). -/
theorem abs_of_nonpos {x : Real} (h : x ≤ 0) : abs x = -x := by
  unfold abs
  by_cases h0 : 0 ≤ x
  · have hx : x = 0 := le_antisymm h h0
    rw [if_pos h0, hx]; mach_ring
  · rw [if_neg h0]

/-- `κ ≥ 1` always: the conditioning quantity dominates the exact value. (Just
the triangle inequality, named for what it means.) -/
theorem exact_le_sigma (t1 t2 : Real) : abs (t1 + t2) ≤ abs t1 + abs t2 := abs_add t1 t2

/-- **`κ = 1` for same-sign terms.** When both terms are nonneg, `Σ|tᵢ| = |exact|`,
so the conditioned bound `((1+w)^d−1)·Σ|tᵢ|` collapses to the relative bound
`((1+w)^d−1)·|exact|` — perfect conditioning. -/
theorem sigma_eq_exact_nonneg {t1 t2 : Real} (h1 : 0 ≤ t1) (h2 : 0 ≤ t2) :
    abs t1 + abs t2 = abs (t1 + t2) := by
  rw [abs_of_nonneg h1, abs_of_nonneg h2, abs_of_nonneg (add_nonneg_ea h1 h2)]

/-- Same, both nonpositive (the other same-sign case). -/
theorem sigma_eq_exact_nonpos {t1 t2 : Real} (h1 : t1 ≤ 0) (h2 : t2 ≤ 0) :
    abs t1 + abs t2 = abs (t1 + t2) := by
  have e1 : abs t1 = -t1 := abs_of_nonpos h1
  have e2 : abs t2 = -t2 := abs_of_nonpos h2
  have e3 : abs (t1 + t2) = -(t1 + t2) := abs_of_nonpos (by
    have h := add_le_add_both h1 h2; rwa [show (0 : Real) + 0 = 0 from by mach_ring] at h)
  rw [e1, e2, e3]; mach_ring

/-- **Well-conditioned ⇒ conditioned bound = relative bound.** For same-sign terms
and any factor `B`, the conditioned target `B·Σ|tᵢ|` equals the relative target
`B·|exact|`. So `prod_diff_fwd`-style bounds on a same-sign dot are genuine
*relative* forward-error guarantees (`κ=1`); only cancellation (`κ>1`) separates
them. -/
theorem cond_is_rel_of_nonneg {t1 t2 B : Real} (h1 : 0 ≤ t1) (h2 : 0 ≤ t2) :
    B * (abs t1 + abs t2) = B * abs (t1 + t2) := by
  rw [sigma_eq_exact_nonneg h1 h2]

/-! ## a κ-bound for a real family: dominant term ⇒ well-conditioned -/

/-- Reverse triangle inequality: `|a| − |b| ≤ |a + b|`. -/
theorem reverse_triangle (a b : Real) : abs a - abs b ≤ abs (a + b) := by
  have h : abs a ≤ abs (a + b) + abs b := by
    have ht := abs_add (a + b) (-b)
    rwa [show (a + b) + (-b) = a from by mach_ring, abs_neg] at ht
  have h2 := sub_le_sub_right h (abs b)
  rwa [show abs (a + b) + abs b - abs b = abs (a + b) from by mach_mpoly [abs (a + b), abs b]] at h2

/-- **κ ≤ 3 for the dominant-term family.** If one term dominates
(`2·|t₂| ≤ |t₁|`), then `Σ|tᵢ| ≤ 3·|exact|` — i.e. `κ = Σ|tᵢ|/|exact| ≤ 3`, so the
conditioned bound is within a factor 3 of a true relative forward-error bound. A
proven condition-number bound for a real kernel class (no cancellation: the
dominant term keeps `|t₁+t₂|` away from 0). -/
theorem kappa_bound_dominant {t1 t2 : Real} (h : (1 + 1) * abs t2 ≤ abs t1) :
    abs t1 + abs t2 ≤ (1 + 1 + 1) * abs (t1 + t2) := by
  have h2 : (0 : Real) ≤ 1 + 1 := le_trans (le_of_lt one_pos) (le_add_of_nonneg_right (le_of_lt one_pos))
  have h3 : (0 : Real) ≤ 1 + 1 + 1 := le_trans h2 (le_add_of_nonneg_right (le_of_lt one_pos))
  have hstep : abs t1 + abs t2 ≤ (1 + 1 + 1) * (abs t1 - abs t2) := by
    have hd : 0 ≤ abs t1 - (1 + 1) * abs t2 := sub_nonneg_of_le h
    have e : (1 + 1 + 1) * (abs t1 - abs t2) - (abs t1 + abs t2)
        = (1 + 1) * (abs t1 - (1 + 1) * abs t2) := by mach_mpoly [abs t1, abs t2]
    have hpos : 0 ≤ (1 + 1 + 1) * (abs t1 - abs t2) - (abs t1 + abs t2) := by
      rw [e]; exact mul_nonneg h2 hd
    exact le_of_sub_nonneg hpos
  exact le_trans hstep (mul_le_mul_of_nonneg_left (reverse_triangle t1 t2) h3)

/-! ## general-N κ — one term dominating the sum of the rest ⇒ κ ≤ 3 -/

/-- Running sum of a list — the exact value `Σtᵢ`. -/
noncomputable def sumList : List Real → Real
  | []      => 0
  | t :: ts => t + sumList ts

/-- Running sum of magnitudes — the conditioning quantity `Σ|tᵢ|`. -/
noncomputable def sigmaList : List Real → Real
  | []      => 0
  | t :: ts => abs t + sigmaList ts

/-- Triangle inequality over a list: `|Σtᵢ| ≤ Σ|tᵢ|` (so `κ = Σ|tᵢ|/|Σtᵢ| ≥ 1`
for any number of terms). -/
theorem abs_sumList_le : ∀ ts : List Real, abs (sumList ts) ≤ sigmaList ts
  | []      => le_of_eq (abs_of_nonneg (le_refl (0 : Real)))
  | t :: ts => by
      show abs (t + sumList ts) ≤ abs t + sigmaList ts
      exact le_trans (abs_add t (sumList ts))
                     (add_le_add_both (le_refl (abs t)) (abs_sumList_le ts))

/-- **κ ≤ 3 for the N-term dominant family.** If the leading term dominates the
*sum of magnitudes of all the others* (`2·Σ|rest| ≤ |t₁|`), then for the whole
list `Σ|tᵢ| ≤ 3·|Σtᵢ|` — i.e. `κ ≤ 3`, regardless of how many small terms there
are. The arbitrary-N generalisation of `kappa_bound_dominant`: one dominant term
keeps the exact sum away from 0 (no cancellation), so the conditioned bound stays
within a factor 3 of a true relative forward-error bound. -/
theorem kappa_bound_dominant_list {t1 : Real} {rest : List Real}
    (h : (1 + 1) * sigmaList rest ≤ abs t1) :
    sigmaList (t1 :: rest) ≤ (1 + 1 + 1) * abs (sumList (t1 :: rest)) := by
  have h2 : (0 : Real) ≤ 1 + 1 :=
    le_trans (le_of_lt one_pos) (le_add_of_nonneg_right (le_of_lt one_pos))
  have h3 : (0 : Real) ≤ 1 + 1 + 1 := le_trans h2 (le_add_of_nonneg_right (le_of_lt one_pos))
  have hR' : abs (sumList rest) ≤ sigmaList rest := abs_sumList_le rest
  have hrev : abs t1 - abs (sumList rest) ≤ abs (t1 + sumList rest) :=
    reverse_triangle t1 (sumList rest)
  have hER : abs t1 - sigmaList rest ≤ abs (t1 + sumList rest) :=
    le_trans (sub_le_sub_left hR' (abs t1)) hrev
  have hstep : abs t1 + sigmaList rest ≤ (1 + 1 + 1) * (abs t1 - sigmaList rest) := by
    have hd : 0 ≤ abs t1 - (1 + 1) * sigmaList rest := sub_nonneg_of_le h
    have e : (1 + 1 + 1) * (abs t1 - sigmaList rest) - (abs t1 + sigmaList rest)
        = (1 + 1) * (abs t1 - (1 + 1) * sigmaList rest) := by mach_mpoly [abs t1, sigmaList rest]
    have hpos : 0 ≤ (1 + 1 + 1) * (abs t1 - sigmaList rest) - (abs t1 + sigmaList rest) := by
      rw [e]; exact mul_nonneg h2 hd
    exact le_of_sub_nonneg hpos
  show abs t1 + sigmaList rest ≤ (1 + 1 + 1) * abs (t1 + sumList rest)
  exact le_trans hstep (mul_le_mul_of_nonneg_left hER h3)

end MachLib.Real
