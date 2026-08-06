import MachLib.AffineContraction
import MachLib.DivisionError
import MachLib.Linarith
import MachLib.GaussianConjugacy

/-!
# Recursive fixed-point error for the Kalman **variance** recursion

`KalmanUpdateFixedPoint` bounds the forward error of ONE scalar Kalman update; `KalmanRecursive`
proves each recursive step is MMSE-optimal. What was missing to call the thing a *filter* rather
than a *measurement update* is the **accumulated** fixed-point error over the recursion — that the
Q16.16 implementation stays faithful to the exact real recursion across `N` steps, not just one.

The variance half of the recursion is the clean, self-contained case: the update

    P ↦ g(P) = P·r / (P + r)          (the posterior-variance map, `r` the measurement noise)

is an **autonomous scalar map** — it depends on neither the estimate `m` nor the measurement `z`, so
there is no coupling to untangle. And it is a **contraction on every `{P ≥ b}`**: writing
`w = 1/(P+r)` gives `g(P) = r − r²·w`, hence

    g(P) − g(P⋆) = r²·(P − P⋆)·w·w⋆ ,   |g(P) − g(P⋆)| = [r² · w · w⋆] · |P − P⋆| ≤ L · |P − P⋆|

with Lipschitz constant `L = r²/(b+r)²` (reciprocal-antitone: `w = 1/(P+r) ≤ 1/(b+r)`). At `b = 0`
this is `L = 1` (nonexpansive — errors accumulate additively, `≤ ε·N`); for any `b > 0` the recursion
strictly contracts (`L < 1`), so the fixed-point error is bounded **uniformly for all `N`**, not
growing.

This drops straight into the pre-existing contraction backbone
(`AffineContraction.local_lipschitz_trajectory_bound`, itself `Iteration.contraction_certificate`
lifted to a concrete map): all this file adds is the one algebraic fact that `g` is `L`-Lipschitz on
`{P ≥ b}`. `sorryAx`-free, zero new axioms.

The **estimate** (`m`) recursion is the coupled follow-on — its per-step error feeds on the variance
error through the gain — and is a separate development; the variance bound proven here is its
prerequisite.
-/

namespace MachLib.Real

/-- The scalar Kalman posterior-**variance** map `g(P) = P·r/(P+r)`. Autonomous (no dependence on
the estimate or the measurement), which is what makes its recursion a clean scalar contraction. -/
-- MERGED 2026-08-06. This was an independent `def` with the same body as
-- `GaussianConjugacy.postVar`; it is now an ALIAS, so the function has ONE definition and the
-- recursion layer keeps the argument order it reads naturally (noise first, state second).
-- All call sites are unchanged -- the alias is definitionally equal, so `kalmanVarMap_eq_postVar`
-- still closes by `rfl`.
noncomputable def kalmanVarMap (r P : Real) : Real := postVar P r

/-- **Contraction core (division-free).** With `w, w⋆` abstract reciprocals of `P+r`, `P⋆+r`
(`(P+r)·w = 1`, `(P⋆+r)·w⋆ = 1`), the difference `P·r·w − P⋆·r·w⋆` equals `(r²·w·w⋆)·(P − P⋆)`, so
its magnitude is `(r²·w·w⋆)·|P − P⋆|`. Given any `L` dominating the (nonnegative) coefficient
`r²·w·w⋆`, this is `≤ L·|P − P⋆|`. Kept abstract in `w, w⋆` so `mach_mpoly` never touches a `1/(·)`
atom — the same discipline as `kalman_fwd_error_abs`. -/
private theorem kalman_var_lip_core (r P Ps w ws L : Real)
    (hw : (P + r) * w = 1) (hws : (Ps + r) * ws = 1)
    (hC0 : 0 ≤ r * r * w * ws) (hCL : r * r * w * ws ≤ L) :
    abs (P * r * w - Ps * r * ws) ≤ L * abs (P - Ps) := by
  -- reciprocal relations, in the form `P·w = 1 − r·w`
  have hPw : P * w = 1 - r * w := by
    have h : P * w + r * w = 1 := by
      rw [show P * w + r * w = (P + r) * w from by mach_mpoly [P, r, w]]; exact hw
    rw [← h]; mach_mpoly [P, r, w]
  have hPsw : Ps * ws = 1 - r * ws := by
    have h : Ps * ws + r * ws = 1 := by
      rw [show Ps * ws + r * ws = (Ps + r) * ws from by mach_mpoly [Ps, r, ws]]; exact hws
    rw [← h]; mach_mpoly [Ps, r, ws]
  -- the reciprocal difference is `(P − P⋆)·w·w⋆`
  have hwmws : ws - w = (P - Ps) * w * ws := by
    rw [show (P - Ps) * w * ws = (P * w) * ws - w * (Ps * ws) from by mach_mpoly [P, Ps, w, ws],
        hPw, hPsw]
    mach_mpoly [r, w, ws]
  -- the key identity: `g(P) − g(P⋆) = (r²·w·w⋆)·(P − P⋆)`
  have hkey : P * r * w - Ps * r * ws = (r * r * w * ws) * (P - Ps) := by
    have e1 : P * r * w = r - r * r * w := by
      rw [show P * r * w = r * (P * w) from by mach_mpoly [P, r, w], hPw]; mach_mpoly [r, w]
    have e2 : Ps * r * ws = r - r * r * ws := by
      rw [show Ps * r * ws = r * (Ps * ws) from by mach_mpoly [Ps, r, ws], hPsw]; mach_mpoly [r, ws]
    rw [e1, e2,
        show (r - r * r * w) - (r - r * r * ws) = r * r * (ws - w) from by mach_mpoly [r, w, ws],
        hwmws]
    mach_mpoly [r, P, Ps, w, ws]
  rw [hkey, abs_mul, abs_of_nonneg hC0]
  exact mul_le_mul_of_nonneg_right hCL (abs_nonneg _)

/-- **The variance map is `r²/(b+r)²`-Lipschitz on `{P ≥ b}`** (`0 < r`, `0 ≤ b`). The concrete
contraction certificate: instantiate the abstract core at `w = 1/(P+r)`, `w⋆ = 1/(P⋆+r)`, discharge
the reciprocal relations by `mul_inv`, and bound the coefficient `r²·w·w⋆ ≤ r²/(b+r)²` by
reciprocal-antitonicity (`div_le_div_pos`). -/
theorem kalman_var_map_lipschitz (r b : Real) (hr : 0 < r) (hb : 0 ≤ b)
    (P Ps : Real) (hP : b ≤ P) (hPs : b ≤ Ps) :
    abs (kalmanVarMap r P - kalmanVarMap r Ps)
      ≤ (r * r * (1 / (b + r)) * (1 / (b + r))) * abs (P - Ps) := by
  have hP0 : 0 ≤ P := le_trans hb hP
  have hPs0 : 0 ≤ Ps := le_trans hb hPs
  have hbr : 0 < b + r := lt_of_lt_of_le hr (le_add_of_nonneg_left hb)
  have hPr : 0 < P + r := lt_of_lt_of_le hr (le_add_of_nonneg_left hP0)
  have hPsr : 0 < Ps + r := lt_of_lt_of_le hr (le_add_of_nonneg_left hPs0)
  have hwrel : (P + r) * (1 / (P + r)) = 1 := mul_inv (P + r) (ne_of_gt hPr)
  have hwsrel : (Ps + r) * (1 / (Ps + r)) = 1 := mul_inv (Ps + r) (ne_of_gt hPsr)
  have hr2 : 0 ≤ r * r := mul_nonneg (le_of_lt hr) (le_of_lt hr)
  have hw0 : 0 ≤ 1 / (P + r) := le_of_lt (one_div_pos_of_pos hPr)
  have hws0 : 0 ≤ 1 / (Ps + r) := le_of_lt (one_div_pos_of_pos hPsr)
  have hC0 : 0 ≤ r * r * (1 / (P + r)) * (1 / (Ps + r)) :=
    mul_nonneg (mul_nonneg hr2 hw0) hws0
  -- reciprocal-antitone bounds: 1/(P+r) ≤ 1/(b+r), 1/(P⋆+r) ≤ 1/(b+r)
  have hwb : 1 / (P + r) ≤ 1 / (b + r) :=
    div_le_div_pos (le_of_lt zero_lt_one_ax) (le_refl 1) hbr (add_le_add_both hP (le_refl r))
  have hwsb : 1 / (Ps + r) ≤ 1 / (b + r) :=
    div_le_div_pos (le_of_lt zero_lt_one_ax) (le_refl 1) hbr (add_le_add_both hPs (le_refl r))
  have hwbnn : 0 ≤ r * r * (1 / (b + r)) := mul_nonneg hr2 (le_of_lt (one_div_pos_of_pos hbr))
  have hA : r * r * (1 / (P + r)) ≤ r * r * (1 / (b + r)) := mul_le_mul_of_nonneg_left hwb hr2
  have hB : r * r * (1 / (P + r)) * (1 / (Ps + r)) ≤ r * r * (1 / (b + r)) * (1 / (Ps + r)) :=
    mul_le_mul_of_nonneg_right hA hws0
  have hC : r * r * (1 / (b + r)) * (1 / (Ps + r)) ≤ r * r * (1 / (b + r)) * (1 / (b + r)) :=
    mul_le_mul_of_nonneg_left hwsb hwbnn
  have hCL : r * r * (1 / (P + r)) * (1 / (Ps + r)) ≤ r * r * (1 / (b + r)) * (1 / (b + r)) :=
    le_trans hB hC
  show abs (P * r / (P + r) - Ps * r / (Ps + r))
      ≤ (r * r * (1 / (b + r)) * (1 / (b + r))) * abs (P - Ps)
  rw [div_def (P * r) (P + r) (ne_of_gt hPr), div_def (Ps * r) (Ps + r) (ne_of_gt hPsr)]
  exact kalman_var_lip_core r P Ps (1 / (P + r)) (1 / (Ps + r))
    (r * r * (1 / (b + r)) * (1 / (b + r))) hwrel hwsrel hC0 hCL

/-- `geom 1 n = n` — the geometric factor collapses to `n` at the nonexpansive constant `L = 1`. -/
theorem geom_one_eq_natCast : ∀ n : Nat, geom 1 n = natCast n
  | 0 => by rw [show geom (1 : Real) 0 = 0 from rfl, natCast_zero]
  | n + 1 => by rw [geom_succ, geom_one_eq_natCast n, natCast_succ]; mach_ring

/-- **Recursive fixed-point error of the Kalman variance recursion.** For the exact real recursion
`Pe(k+1) = g(Pe k)` and the computed recursion `Pc` with per-step round-off `≤ ε`, both orbits
staying in `{P ≥ b}`, and an exact start, the accumulated error obeys

    |Pc n − Pe n| ≤ ε · geom L n ,   (1 − L)·(ε · geom L n) ≤ ε ,   L = r²/(b+r)² .

The second conjunct is the contraction certificate: for `b > 0` (`L < 1`) it caps the error
uniformly for all `n` at `ε/(1−L)`. Instantiates the pre-existing `local_lipschitz_trajectory_bound`
with the variance map's Lipschitz certificate. -/
theorem kalman_variance_recursion_fixed_point
    (r b : Real) (hr : 0 < r) (hb : 0 ≤ b)
    {Pc Pe : Nat → Real} {ε : Real} (hε : 0 ≤ ε)
    (hin : ∀ k, b ≤ Pc k ∧ b ≤ Pe k)
    (h0 : abs (Pc 0 - Pe 0) ≤ 0)
    (hexact : ∀ k, Pe (k + 1) = kalmanVarMap r (Pe k))
    (hstep : ∀ k, abs (Pc (k + 1) - kalmanVarMap r (Pc k)) ≤ ε)
    (n : Nat) :
    abs (Pc n - Pe n) ≤ ε * geom (r * r * (1 / (b + r)) * (1 / (b + r))) n
      ∧ (1 - r * r * (1 / (b + r)) * (1 / (b + r)))
          * (ε * geom (r * r * (1 / (b + r)) * (1 / (b + r))) n) ≤ ε := by
  have hbr : 0 < b + r := lt_of_lt_of_le hr (le_add_of_nonneg_left hb)
  have hL0 : 0 ≤ r * r * (1 / (b + r)) * (1 / (b + r)) :=
    mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt hr) (le_of_lt hr))
      (le_of_lt (one_div_pos_of_pos hbr))) (le_of_lt (one_div_pos_of_pos hbr))
  exact local_lipschitz_trajectory_bound (f := kalmanVarMap r) (D := fun P => b ≤ P)
    hL0 hε (fun x y hx hy => kalman_var_map_lipschitz r b hr hb x y hx hy)
    hin h0 hexact hstep n

/-- **Nonexpansive case (`b = 0`): additive accumulation.** The variance recursion is nonexpansive
(`L = 1`), so the Q16.16 recursion stays within `ε·n` of the exact recursion — the honest
`≈ N·ulp` linear growth, unconditional (needs only both variances `≥ 0`). -/
theorem kalman_variance_recursion_nonexpansive
    (r : Real) (hr : 0 < r)
    {Pc Pe : Nat → Real} {ε : Real} (hε : 0 ≤ ε)
    (hin : ∀ k, 0 ≤ Pc k ∧ 0 ≤ Pe k)
    (h0 : abs (Pc 0 - Pe 0) ≤ 0)
    (hexact : ∀ k, Pe (k + 1) = kalmanVarMap r (Pe k))
    (hstep : ∀ k, abs (Pc (k + 1) - kalmanVarMap r (Pc k)) ≤ ε)
    (n : Nat) :
    abs (Pc n - Pe n) ≤ ε * natCast n := by
  have hL1 : r * r * (1 / (0 + r)) * (1 / (0 + r)) = 1 := by
    have hrinv : r * (1 / r) = 1 := mul_inv r (ne_of_gt hr)
    rw [zero_add, show r * r * (1 / r) * (1 / r) = (r * (1 / r)) * (r * (1 / r))
          from by mach_mpoly [r, 1 / r], hrinv]
    mach_ring
  have hmain := (kalman_variance_recursion_fixed_point r 0 hr (le_refl 0) hε hin h0 hexact hstep n).1
  rw [hL1, geom_one_eq_natCast] at hmain
  exact hmain

end MachLib.Real
