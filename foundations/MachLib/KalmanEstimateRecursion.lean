import MachLib.AffineContraction
import MachLib.KalmanVarianceRecursion

/-!
# Recursive fixed-point error for the Kalman **estimate** recursion (the coupled half)

`KalmanVarianceRecursion` bounds the accumulated error of the autonomous *variance* recursion. The
*estimate* recursion is the coupled half: the update

    m_n = m_{n-1} + K_n·(z_n − m_{n-1}) = (1 − K_n)·m_{n-1} + K_n·z_n

is a **time-varying affine map** whose coefficient `1 − K_n` and offset `K_n·z_n` change every step
(the gain `K_n = P_{n-1}/(P_{n-1}+r)` rides on the evolving variance), and the *computed* and *exact*
orbits follow **different** maps — the computed gain `Kc_n` differs from the exact `Ke_n`. Expanding
the error,

    δm_n = (1 − Kc_n)·δm_{n-1} + (Kc_n − Ke_n)·(z_n − m⋆_{n-1}) + τ_n ,

so `|δm_n| ≤ |1 − Kc_n|·|δm_{n-1}| + |Kc_n − Ke_n|·|z_n − m⋆_{n-1}| + |τ_n|`. Two forcings on top of
the contraction: the **gain error** `Kc_n − Ke_n` (this is where coupling to the variance error lives —
`K` is a Lipschitz function of `P`, so `|Kc − Ke|` is controlled by the variance error `|δP|` plus the
gain's own round-off) and the update **round-off** `τ_n`.

This is exactly `AffineContraction.nearby_maps_trajectory_bound` (two orbits under nearby `L`-Lipschitz
maps), instantiated at `Ac n x = x + Kc n·(z n − x)`, `Ae n x = x + Ke n·(z n − x)`: the computed map is
`|1 − Kc n|`-Lipschitz, the maps agree on the exact orbit to `|Kc n − Ke n|·|z n − m⋆|`, and the
computed orbit follows `Ac` up to the update round-off. The gain-error×innovation bound `ρ` is taken as
a hypothesis — the honest interface, exactly as `kalman_update_1d_fwd_error` takes the reciprocal error
`E_recip` as a hypothesis rather than re-deriving it. `sorryAx`-free, zero new axioms.
-/

namespace MachLib.Real

/-- **Recursive fixed-point error of the Kalman estimate recursion.** For the exact recursion
`me(n+1) = me n + Ke n·(z n − me n)` and the computed recursion `mc` (computed gains `Kc n`, update
round-off `≤ σ`), with the computed gains giving an `≤ L`-contraction (`|1 − Kc n| ≤ L`) and the
gain-error×innovation bounded by `ρ` (`|Kc n − Ke n|·|z n − me n| ≤ ρ`), the accumulated estimate error
obeys `|mc n − me n| ≤ (σ + ρ)·geom L n`, uniformly bounded by `(σ+ρ)/(1−L)` when `L < 1`. `ρ` carries
the coupling to the variance error; `σ` the estimate update's own round-off. -/
theorem kalman_estimate_recursion_fixed_point
    {mc me Kc Ke z : Nat → Real} {L σ ρ : Real}
    (hL0 : 0 ≤ L) (hσ : 0 ≤ σ) (hρ : 0 ≤ ρ)
    (hgainlip : ∀ n, abs (1 - Kc n) ≤ L)
    (hcloseH : ∀ n, abs (Kc n - Ke n) * abs (z n - me n) ≤ ρ)
    (h0 : abs (mc 0 - me 0) ≤ 0)
    (hexact : ∀ n, me (n + 1) = me n + Ke n * (z n - me n))
    (hcomp : ∀ n, abs (mc (n + 1) - (mc n + Kc n * (z n - mc n))) ≤ σ)
    (n : Nat) :
    abs (mc n - me n) ≤ (σ + ρ) * geom L n
      ∧ (1 - L) * ((σ + ρ) * geom L n) ≤ σ + ρ := by
  refine nearby_maps_trajectory_bound (Ac := fun n x => x + Kc n * (z n - x))
    (Ae := fun n x => x + Ke n * (z n - x)) hL0 hσ hρ ?_ ?_ h0 hexact hcomp n
  · -- Ac n is |1 − Kc n|-Lipschitz, hence ≤ L
    intro k x y
    rw [show (x + Kc k * (z k - x)) - (y + Kc k * (z k - y)) = (1 - Kc k) * (x - y)
          from by mach_mpoly [x, y, Kc k, z k], abs_mul]
    exact mul_le_mul_of_nonneg_right (hgainlip k) (abs_nonneg _)
  · -- the maps agree on the exact orbit to |Kc − Ke|·|z − me| ≤ ρ
    intro k
    rw [show (me k + Kc k * (z k - me k)) - (me k + Ke k * (z k - me k))
          = (Kc k - Ke k) * (z k - me k) from by mach_mpoly [me k, Kc k, Ke k, z k], abs_mul]
    exact hcloseH k

/-- **Nonexpansive case (gains in `[0,1]`): additive accumulation.** With every computed gain in
`[0,1]` (so `|1 − Kc n| ≤ 1`), the estimate error accumulates additively at `(σ + ρ)·n` — the honest
`≈ N·(round-off + gain-error·innovation)` linear growth. -/
theorem kalman_estimate_recursion_nonexpansive
    {mc me Kc Ke z : Nat → Real} {σ ρ : Real}
    (hσ : 0 ≤ σ) (hρ : 0 ≤ ρ)
    (hgain01 : ∀ n, 0 ≤ Kc n ∧ Kc n ≤ 1)
    (hcloseH : ∀ n, abs (Kc n - Ke n) * abs (z n - me n) ≤ ρ)
    (h0 : abs (mc 0 - me 0) ≤ 0)
    (hexact : ∀ n, me (n + 1) = me n + Ke n * (z n - me n))
    (hcomp : ∀ n, abs (mc (n + 1) - (mc n + Kc n * (z n - mc n))) ≤ σ)
    (n : Nat) :
    abs (mc n - me n) ≤ (σ + ρ) * natCast n := by
  have hgainlip : ∀ n, abs (1 - Kc n) ≤ 1 := by
    intro n
    have h := hgain01 n
    rw [abs_of_nonneg (sub_nonneg_of_le h.2)]
    exact le_of_sub_nonneg (by rw [show (1 : Real) - (1 - Kc n) = Kc n from by mach_ring]; exact h.1)
  have hmain := (kalman_estimate_recursion_fixed_point (le_of_lt zero_lt_one_ax) hσ hρ
    hgainlip hcloseH h0 hexact hcomp n).1
  rwa [geom_one_eq_natCast] at hmain

/-! ## Making the coupling numeric — the gain error is controlled by the variance error

The estimate bound above takes the gain-error×innovation bound `ρ` as a hypothesis. Here that `ρ` is
*derived*: the gain `K(P) = P/(P+r)` is a Lipschitz function of `P`, so the gain error `|Kc − Ke|` is
bounded by the variance error `|δP|` (times the gain's Lipschitz constant) plus the gain's own round-off.
This closes the variance → gain → estimate coupling — machine-checked, not prose. -/

/-- The scalar Kalman **gain** map `K(P) = P/(P+r)`. (`= kalmanVarMap r P / r`; the variance map is
`r · K`.) -/
-- MERGED 2026-08-06, same as `kalmanVarMap`: an alias, not a second definition.
noncomputable def kalmanGainMap (r P : Real) : Real := kGain P r

/-- Contraction core for the gain map (division-free, coefficient `r` where the variance had `r²`):
`P·w − P⋆·w⋆ = (r·w·w⋆)·(P − P⋆)`. -/
private theorem kalman_gain_lip_core (r P Ps w ws L : Real)
    (hw : (P + r) * w = 1) (hws : (Ps + r) * ws = 1)
    (hC0 : 0 ≤ r * w * ws) (hCL : r * w * ws ≤ L) :
    abs (P * w - Ps * ws) ≤ L * abs (P - Ps) := by
  have hPw : P * w = 1 - r * w := by
    have h : P * w + r * w = 1 := by
      rw [show P * w + r * w = (P + r) * w from by mach_mpoly [P, r, w]]; exact hw
    rw [← h]; mach_mpoly [P, r, w]
  have hPsw : Ps * ws = 1 - r * ws := by
    have h : Ps * ws + r * ws = 1 := by
      rw [show Ps * ws + r * ws = (Ps + r) * ws from by mach_mpoly [Ps, r, ws]]; exact hws
    rw [← h]; mach_mpoly [Ps, r, ws]
  have hwmws : ws - w = (P - Ps) * w * ws := by
    rw [show (P - Ps) * w * ws = (P * w) * ws - w * (Ps * ws) from by mach_mpoly [P, Ps, w, ws],
        hPw, hPsw]
    mach_mpoly [r, w, ws]
  have hkey : P * w - Ps * ws = (r * w * ws) * (P - Ps) := by
    rw [hPw, hPsw,
        show (1 - r * w) - (1 - r * ws) = r * (ws - w) from by mach_mpoly [r, w, ws], hwmws]
    mach_mpoly [r, P, Ps, w, ws]
  rw [hkey, abs_mul, abs_of_nonneg hC0]
  exact mul_le_mul_of_nonneg_right hCL (abs_nonneg _)

/-- **The gain map is `r/(b+r)²`-Lipschitz on `{P ≥ b}`.** (The variance map's `r²/(b+r)²` divided by
`r`, since `g = r·K`.) This is the gain's sensitivity to the variance — how a variance error propagates
into the gain. -/
theorem kalman_gain_map_lipschitz (r b : Real) (hr : 0 < r) (hb : 0 ≤ b)
    (P Ps : Real) (hP : b ≤ P) (hPs : b ≤ Ps) :
    abs (kalmanGainMap r P - kalmanGainMap r Ps)
      ≤ (r * (1 / (b + r)) * (1 / (b + r))) * abs (P - Ps) := by
  have hP0 : 0 ≤ P := le_trans hb hP
  have hPs0 : 0 ≤ Ps := le_trans hb hPs
  have hbr : 0 < b + r := lt_of_lt_of_le hr (le_add_of_nonneg_left hb)
  have hPr : 0 < P + r := lt_of_lt_of_le hr (le_add_of_nonneg_left hP0)
  have hPsr : 0 < Ps + r := lt_of_lt_of_le hr (le_add_of_nonneg_left hPs0)
  have hwrel : (P + r) * (1 / (P + r)) = 1 := mul_inv (P + r) (ne_of_gt hPr)
  have hwsrel : (Ps + r) * (1 / (Ps + r)) = 1 := mul_inv (Ps + r) (ne_of_gt hPsr)
  have hrnn : 0 ≤ r := le_of_lt hr
  have hw0 : 0 ≤ 1 / (P + r) := le_of_lt (one_div_pos_of_pos hPr)
  have hws0 : 0 ≤ 1 / (Ps + r) := le_of_lt (one_div_pos_of_pos hPsr)
  have hC0 : 0 ≤ r * (1 / (P + r)) * (1 / (Ps + r)) := mul_nonneg (mul_nonneg hrnn hw0) hws0
  have hwb : 1 / (P + r) ≤ 1 / (b + r) :=
    div_le_div_pos (le_of_lt zero_lt_one_ax) (le_refl 1) hbr (add_le_add_both hP (le_refl r))
  have hwsb : 1 / (Ps + r) ≤ 1 / (b + r) :=
    div_le_div_pos (le_of_lt zero_lt_one_ax) (le_refl 1) hbr (add_le_add_both hPs (le_refl r))
  have hwbnn : 0 ≤ r * (1 / (b + r)) := mul_nonneg hrnn (le_of_lt (one_div_pos_of_pos hbr))
  have hA : r * (1 / (P + r)) ≤ r * (1 / (b + r)) := mul_le_mul_of_nonneg_left hwb hrnn
  have hB : r * (1 / (P + r)) * (1 / (Ps + r)) ≤ r * (1 / (b + r)) * (1 / (Ps + r)) :=
    mul_le_mul_of_nonneg_right hA hws0
  have hC : r * (1 / (b + r)) * (1 / (Ps + r)) ≤ r * (1 / (b + r)) * (1 / (b + r)) :=
    mul_le_mul_of_nonneg_left hwsb hwbnn
  have hCL : r * (1 / (P + r)) * (1 / (Ps + r)) ≤ r * (1 / (b + r)) * (1 / (b + r)) := le_trans hB hC
  show abs (P / (P + r) - Ps / (Ps + r)) ≤ (r * (1 / (b + r)) * (1 / (b + r))) * abs (P - Ps)
  rw [div_def P (P + r) (ne_of_gt hPr), div_def Ps (Ps + r) (ne_of_gt hPsr)]
  exact kalman_gain_lip_core r P Ps (1 / (P + r)) (1 / (Ps + r))
    (r * (1 / (b + r)) * (1 / (b + r))) hwrel hwsrel hC0 hCL

/-- **The gain error is bounded by the variance error.** With the variance error uniformly `≤ DP`, the
gain round-off `≤ γ` (`|Kc − K(Pc)| ≤ γ`), the exact gain the exact map (`Ke = K(Pe)`), both variances
`≥ b`, and the innovation `≤ Z`, the gain-error×innovation is `≤ (γ + (r/(b+r)²)·DP)·Z` — exactly the
`ρ` the estimate recursion needs, now DERIVED from the variance error. -/
theorem kalman_gain_error_bound (r b : Real) (hr : 0 < r) (hb : 0 ≤ b)
    {Pc Pe Kc Ke z me : Nat → Real} {DP Z gamma : Real}
    (hgamma : 0 ≤ gamma) (hDP : 0 ≤ DP) (hZ : 0 ≤ Z)
    (hPcb : ∀ n, b ≤ Pc n) (hPeb : ∀ n, b ≤ Pe n)
    (hvar : ∀ n, abs (Pc n - Pe n) ≤ DP)
    (hround : ∀ n, abs (Kc n - kalmanGainMap r (Pc n)) ≤ gamma)
    (hKe : ∀ n, Ke n = kalmanGainMap r (Pe n))
    (hinnov : ∀ n, abs (z n - me n) ≤ Z)
    (n : Nat) :
    abs (Kc n - Ke n) * abs (z n - me n)
      ≤ (gamma + (r * (1 / (b + r)) * (1 / (b + r))) * DP) * Z := by
  have hbr : 0 < b + r := lt_of_lt_of_le hr (le_add_of_nonneg_left hb)
  have hgainLip0 : 0 ≤ r * (1 / (b + r)) * (1 / (b + r)) :=
    mul_nonneg (mul_nonneg (le_of_lt hr) (le_of_lt (one_div_pos_of_pos hbr)))
      (le_of_lt (one_div_pos_of_pos hbr))
  have hlipDP : abs (kalmanGainMap r (Pc n) - kalmanGainMap r (Pe n))
      ≤ (r * (1 / (b + r)) * (1 / (b + r))) * DP :=
    le_trans (kalman_gain_map_lipschitz r b hr hb (Pc n) (Pe n) (hPcb n) (hPeb n))
      (mul_le_mul_of_nonneg_left (hvar n) hgainLip0)
  have hKcErr : abs (Kc n - Ke n) ≤ gamma + (r * (1 / (b + r)) * (1 / (b + r))) * DP := by
    rw [hKe n, show Kc n - kalmanGainMap r (Pe n)
          = (Kc n - kalmanGainMap r (Pc n)) + (kalmanGainMap r (Pc n) - kalmanGainMap r (Pe n))
          from by mach_mpoly [Kc n, kalmanGainMap r (Pc n), kalmanGainMap r (Pe n)]]
    exact le_trans (abs_add _ _) (add_le_add_both (hround n) hlipDP)
  have hcoefnn : 0 ≤ gamma + (r * (1 / (b + r)) * (1 / (b + r))) * DP :=
    le_trans hgamma (le_add_of_nonneg_right (mul_nonneg hgainLip0 hDP))
  exact le_trans (mul_le_mul_of_nonneg_right hKcErr (abs_nonneg _))
    (mul_le_mul_of_nonneg_left (hinnov n) hcoefnn)

/-- **The fully-coupled estimate recursion bound.** `ρ` is no longer a hypothesis: the estimate error is
bounded purely in terms of the datapath round-off `σ`, the gain round-off `γ`, the *variance* error `DP`,
the innovation bound `Z`, and the contraction `L`:

    |mc n − me n| ≤ (σ + (γ + (r/(b+r)²)·DP)·Z) · geom L n .

The variance→gain→estimate coupling is now machine-checked end to end — the composition of
`kalman_gain_error_bound` (variance error ⇒ gain error) with `kalman_estimate_recursion_fixed_point`. -/
theorem kalman_estimate_recursion_coupled (r b : Real) (hr : 0 < r) (hb : 0 ≤ b)
    {mc me Kc Ke Pc Pe z : Nat → Real} {L sigma gamma DP Z : Real}
    (hL0 : 0 ≤ L) (hsigma : 0 ≤ sigma) (hgamma : 0 ≤ gamma) (hDP : 0 ≤ DP) (hZ : 0 ≤ Z)
    (hgainlip : ∀ n, abs (1 - Kc n) ≤ L)
    (hPcb : ∀ n, b ≤ Pc n) (hPeb : ∀ n, b ≤ Pe n)
    (hvar : ∀ n, abs (Pc n - Pe n) ≤ DP)
    (hround : ∀ n, abs (Kc n - kalmanGainMap r (Pc n)) ≤ gamma)
    (hKe : ∀ n, Ke n = kalmanGainMap r (Pe n))
    (hinnov : ∀ n, abs (z n - me n) ≤ Z)
    (h0 : abs (mc 0 - me 0) ≤ 0)
    (hexact : ∀ n, me (n + 1) = me n + Ke n * (z n - me n))
    (hcomp : ∀ n, abs (mc (n + 1) - (mc n + Kc n * (z n - mc n))) ≤ sigma)
    (n : Nat) :
    abs (mc n - me n)
      ≤ (sigma + (gamma + (r * (1 / (b + r)) * (1 / (b + r))) * DP) * Z) * geom L n := by
  have hbr : 0 < b + r := lt_of_lt_of_le hr (le_add_of_nonneg_left hb)
  have hgainLip0 : 0 ≤ r * (1 / (b + r)) * (1 / (b + r)) :=
    mul_nonneg (mul_nonneg (le_of_lt hr) (le_of_lt (one_div_pos_of_pos hbr)))
      (le_of_lt (one_div_pos_of_pos hbr))
  have hρnn : 0 ≤ (gamma + (r * (1 / (b + r)) * (1 / (b + r))) * DP) * Z :=
    mul_nonneg (le_trans hgamma (le_add_of_nonneg_right (mul_nonneg hgainLip0 hDP))) hZ
  exact (kalman_estimate_recursion_fixed_point hL0 hsigma hρnn hgainlip
    (fun k => kalman_gain_error_bound r b hr hb hgamma hDP hZ hPcb hPeb hvar hround hKe hinnov k)
    h0 hexact hcomp n).1

end MachLib.Real
