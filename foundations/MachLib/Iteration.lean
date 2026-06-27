import MachLib.Basic
import MachLib.Lemmas
import MachLib.Forge
import MachLib.Ring
import MachLib.MPolyRing
import MachLib.FPModel

/-!
# Iteration dynamics — the contraction certificate

`FPModel` and `FixedPoint` bound the round-off error of **one** evaluation. The
engine *iterates* kernels: `x_{n+1} = round(f(x_n))`. This file answers the
question those per-step proofs cannot: does the round-off error stay bounded
over the whole trajectory?

Setup. Let `e n` be the error after `n` steps, with a per-step round-off bound
`ε` and an `L`-Lipschitz map. Then the error obeys the recurrence

    e 0 = 0,    e (k+1) ≤ L · e k + ε

(the triangle inequality: `|round(f(xc)) − f(xe)| ≤ |round(f(xc)) − f(xc)| +
|f(xc) − f(xe)| ≤ ε + L·e k`). The closed solution is `e n ≤ ε · (1+L+…+L^{n-1})`.

The **contraction certificate** (`contraction_certificate`): when `L < 1` the
geometric sum is `≤ 1/(1−L)`, so the whole-trajectory error never exceeds
`ε/(1−L)` — the one-step proof lifts to the entire run *because the map
contracts*. We state the bound division-free as `(1−L)·(ε·geom L n) ≤ ε`, which
is exactly `bound ≤ ε/(1−L)` without dividing (MachLib has no field tactics).

For the PID plant of Leg A, `L = 0.99`, so `1/(1−L) = 100`: the proven per-step
Q16.16 error stays `≤ 100·ε` over the 1000-sample trace. (For an *expansive*
map, `L > 1`, the certificate is vacuous and a trajectory-level invariant is
genuinely needed — see the logistic-map chaos in the research note.)

`sorryAx`-free, Mathlib-free; reuses `FPModel`'s `npow`. Companion: `FixedPoint`
(Leg A, the per-step bound this lifts), `FPModel`.
-/

namespace MachLib.Real

/-! Ring identities over FRESH vars — `mach_mpoly`'s atom parser dislikes
recursion-bound terms (`geom L n`, `npow n L`), so the algebra is factored out
here and applied by instantiation. -/
theorem geom_ring1 (L g : Real) :
    (1 - L) * (1 + L * g) = (1 - L) + L * ((1 - L) * g) := by mach_mpoly [L, g]
theorem geom_ring2 (L p : Real) :
    (1 - L) + L * (1 - p) = 1 - L * p := by mach_mpoly [L, p]
theorem iter_ring (L ε g : Real) :
    L * (ε * g) + ε = ε * (1 + L * g) := by mach_mpoly [L, ε, g]
theorem cc_ring (L ε g : Real) :
    (1 - L) * (ε * g) = ε * ((1 - L) * g) := by mach_mpoly [L, ε, g]

/-- Geometric partial sum `1 + L + L² + … + L^{n-1}`. -/
noncomputable def geom (L : Real) : Nat → Real
  | 0     => 0
  | n + 1 => 1 + L * geom L n

theorem geom_succ (L : Real) (n : Nat) : geom L (n + 1) = 1 + L * geom L n := rfl

/-- `npow` of a nonneg base is nonneg. -/
theorem npow_nonneg {x : Real} (hx : 0 ≤ x) : ∀ n, 0 ≤ npow n x
  | 0     => le_of_lt one_pos
  | n + 1 => by rw [npow_succ]; exact mul_nonneg hx (npow_nonneg hx n)

theorem geom_nonneg {L : Real} (hL : 0 ≤ L) : ∀ n, 0 ≤ geom L n
  | 0     => le_refl 0
  | n + 1 => by
      rw [geom_succ]
      have h := add_le_add_both (le_of_lt one_pos) (mul_nonneg hL (geom_nonneg hL n))
      have e : (0 : Real) + 0 = 0 := by mach_ring
      rw [e] at h; exact h

/-- Telescoping identity: `(1−L)·geom L n = 1 − L^n`. -/
theorem geom_telescope (L : Real) : ∀ n, (1 - L) * geom L n = 1 - npow n L
  | 0     => by
      rw [show geom L 0 = 0 from rfl, show npow 0 L = 1 from rfl]; mach_ring
  | n + 1 => by
      rw [geom_succ, npow_succ, geom_ring1 L (geom L n), geom_telescope L n,
          geom_ring2 L (npow n L)]

/-- The scaled geometric sum is `≤ 1`: i.e. `geom L n ≤ 1/(1−L)`, division-free. -/
theorem geom_scaled_le_one {L : Real} (hL : 0 ≤ L) (n : Nat) :
    (1 - L) * geom L n ≤ 1 := by
  rw [geom_telescope]
  have h := npow_nonneg hL n
  have step : (1 : Real) - npow n L ≤ 1 - 0 := sub_le_sub_left h 1
  have e : (1 : Real) - 0 = 1 := by mach_ring
  rw [e] at step; exact step

/-- **The trajectory error bound.** Any error sequence obeying the contraction
recurrence `e 0 ≤ 0`, `e (k+1) ≤ L·e k + ε` (`L,ε ≥ 0`) satisfies
`e n ≤ ε · geom L n` for all `n`. -/
theorem iterate_error_bound {L ε : Real} (e : Nat → Real)
    (hL : 0 ≤ L) (hε : 0 ≤ ε) (h0 : e 0 ≤ 0)
    (hstep : ∀ k, e (k + 1) ≤ L * e k + ε) :
    ∀ n, e n ≤ ε * geom L n
  | 0     => by
      have hz : ε * geom L 0 = 0 := by rw [show geom L 0 = 0 from rfl]; mach_ring
      rw [hz]; exact h0
  | n + 1 => by
      have ih := iterate_error_bound e hL hε h0 hstep n
      have h1 : L * e n ≤ L * (ε * geom L n) := mul_le_mul_of_nonneg_left ih hL
      have h2 : L * e n + ε ≤ L * (ε * geom L n) + ε := add_le_add_both h1 (le_refl ε)
      have h3 : L * (ε * geom L n) + ε = ε * geom L (n + 1) := by
        rw [geom_succ]; exact iter_ring L ε (geom L n)
      exact le_trans (hstep n) (le_trans h2 (le_of_eq h3))

/-- **Contraction certificate.** Under the contraction recurrence, the
whole-trajectory error is `≤ ε · geom L n`, and that bound satisfies
`(1−L)·bound ≤ ε` — i.e. `bound ≤ ε/(1−L)`, stated without division. When `L<1`
this is a finite trajectory bound for *all* `n`; the per-step proof (Leg A)
lifts to the entire run. (`L = 0.99` ⇒ `bound ≤ 100ε`.) -/
theorem contraction_certificate {L ε : Real} (e : Nat → Real)
    (hL : 0 ≤ L) (hε : 0 ≤ ε) (h0 : e 0 ≤ 0)
    (hstep : ∀ k, e (k + 1) ≤ L * e k + ε) (n : Nat) :
    e n ≤ ε * geom L n ∧ (1 - L) * (ε * geom L n) ≤ ε := by
  refine ⟨iterate_error_bound e hL hε h0 hstep n, ?_⟩
  have hsc : (1 - L) * geom L n ≤ 1 := geom_scaled_le_one hL n
  rw [cc_ring L ε (geom L n)]
  have hmul := mul_le_mul_of_nonneg_left hsc hε
  have e1 : ε * 1 = ε := by mach_ring
  rw [e1] at hmul; exact hmul

end MachLib.Real
