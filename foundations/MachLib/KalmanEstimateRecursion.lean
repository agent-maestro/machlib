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

end MachLib.Real
