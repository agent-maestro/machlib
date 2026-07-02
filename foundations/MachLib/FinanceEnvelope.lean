import MachLib.Iteration

/-!
# Accumulated rounding error stays inside a certified envelope

`FinanceAmortization` proves the schedule *reconciles* — the balance closes to exactly `$0.00` and
the principal payments sum to exactly the loan (`amortization_reconciles`) — and that each period's
banker's rounding is correct to half a cent (`roundHalfEven_half_ulp`). Those are the *local* and the
*exact* facts. This file adds the missing *global* one: **how far can the rounded trajectory drift
from the exact-arithmetic trajectory over the whole loan, and is that drift bounded?**

The drift obeys a linear recurrence with bounded input. Writing `b_k` for the rounded balance and
`B_k` for the exact-arithmetic balance under the same payment, both follow `x_{k+1} = g·x_k − pmt`
with `g = 1 + r` the per-period growth, except the rounded one carries a per-period rounding
perturbation `ρ_k` (`interest = round(b_k·r)` vs the exact `b_k·r`, `|ρ_k| ≤ c`). Subtracting, the
error `e_k = b_k − B_k` satisfies

    e_0 = 0 ,   e_{k+1} = g·e_k + ρ_k ,   |ρ_k| ≤ c .

Unlike the closed-loop **safety** envelope — a *contraction* (`g < 1`) that settles into a fixed
steady-state box `X = δ/(1−ρ)`, `MachLib.Real.safe_envelope_invariant` — amortization is an
*expansion* (`g > 1`): the error can compound. But only inside an explicit, growing envelope

    cap_k = c · (gᵏ − 1)/(g − 1)      (the geometric sum; kept division-free below).

* `error_within_envelope` — the abstract core, the **expansion dual** of the safety invariant:
  for any real drift `e` with `e_0 = 0` and `|e_{k+1} − g·e_k| ≤ c`, and `g ≥ 1`, one has
  `|e_k| ≤ cap_k` for all `k`.
* `errEnvelope_eq_geomSum`, `geomSum_closed` — `cap_N = c·Σ_{j<N} gʲ` and
  `(g−1)·Σ_{j<N} gʲ = gᴺ − 1`, i.e. the recognizable `c·(gᴺ−1)/(g−1)`, both proven without division.
* `amortization_drift_within_envelope` — the punchline: the rounded schedule `b` never leaves the
  envelope `cap_N` around the exact schedule `B`, for ANY per-period rounding bounded by `c`. With
  `c = ½` cent (banker's rounding, `roundHalfEven_half_ulp`) this is exactly the bound on the
  final-payment adjustment that `amortization_reconciles` leans on — closing the loop between the
  local ½¢ fact and the global reconciliation.

`sorryAx`-free — rests only on the model's ring/order/abs primitives, exactly as the safety envelope
does. (The polynomial identities go through `mach_mpoly`, the complete normaliser, not `mach_ring`.)
-/

namespace MachLib.Real

/-! ## The certified envelope and its ingredients -/

/-- The certified error envelope. `cap 0 = 0`, `cap (k+1) = g·cap k + c`. -/
noncomputable def errEnvelope (g c : Real) : Nat → Real
  | 0 => 0
  | k + 1 => g * errEnvelope g c k + c

theorem errEnvelope_zero (g c : Real) : errEnvelope g c 0 = 0 := rfl
theorem errEnvelope_succ (g c : Real) (k : Nat) :
    errEnvelope g c (k + 1) = g * errEnvelope g c k + c := rfl

/-- Geometric partial sum `Σ_{j<N} gʲ`, defined recursively (no division). -/
noncomputable def geomSum (g : Real) : Nat → Real
  | 0 => 0
  | k + 1 => g * geomSum g k + 1

theorem geomSum_zero (g : Real) : geomSum g 0 = 0 := rfl
theorem geomSum_succ (g : Real) (k : Nat) :
    geomSum g (k + 1) = g * geomSum g k + 1 := rfl

/-- Powers of `g` (self-contained; avoids leaning on the `HPow` instance). -/
noncomputable def gpow (g : Real) : Nat → Real
  | 0 => 1
  | k + 1 => g * gpow g k

theorem gpow_zero (g : Real) : gpow g 0 = 1 := rfl
theorem gpow_succ (g : Real) (k : Nat) : gpow g (k + 1) = g * gpow g k := rfl

/-- Ring helper: `y + (x − y) = x`. -/
theorem add_sub_id (x y : Real) : y + (x - y) = x := by
  rw [sub_def, add_comm x (-y), ← add_assoc, add_neg, zero_add]

/-! ### Ring identities used by the inductions.

Each is stated with its own top-level variables so `mach_mpoly` elaborates the atom list in scope —
`mach_mpoly` reifies its bracket atoms in the outer elaboration context, so a term mentioning an
`induction`-introduced local (e.g. `geomSum g n`) is invisible to it. Proving the identity once, over
plain variables, and `exact`-ing it at the use site side-steps that. -/

/-- `errEnvelope`'s recurrence, after the IH is substituted. -/
theorem envelope_geomSum_step (g c s : Real) :
    g * (c * s) + c = c * (g * s + 1) := by mach_mpoly [g, c, s]

/-- Distribute `(g−1)·(g·s+1)` toward the shape the geometric-sum IH consumes. -/
theorem geomSum_expand_step (g s : Real) :
    (g - 1) * (g * s + 1) = g * ((g - 1) * s) + (g - 1) := by mach_mpoly [g, s]

/-- Collapse `g·(p−1) + (g−1)` to `g·p − 1` after the geometric-sum IH. -/
theorem geomSum_close_step (g p : Real) :
    g * (p - 1) + (g - 1) = g * p - 1 := by mach_mpoly [g, p]

/-- The per-period drift telescopes to exactly the rounding perturbation. -/
theorem drift_step_ring (g bk Bk rk pmt : Real) :
    (g * bk - pmt + rk - (g * Bk - pmt)) - g * (bk - Bk) = rk := by
  mach_mpoly [g, bk, Bk, rk, pmt]

/-! ## The abstract core: |e k| ≤ cap k (expansion dual of `safe_envelope_invariant`) -/

/-- **Accumulated error stays inside the envelope.** A real sequence `e` with `e 0 = 0` whose steps
satisfy `|e_{k+1} − g·e_k| ≤ c` (a bounded per-step perturbation on top of geometric growth `g ≥ 1`)
never leaves the envelope `cap_k = errEnvelope g c k`. This is the expansion counterpart of the
contraction-based `safe_envelope_invariant`: there `g < 1` gives a *fixed* box; here `g ≥ 1` gives a
*growing* one that still bounds the compounded error at every finite horizon. -/
theorem error_within_envelope {e : Nat → Real} {g c : Real}
    (hg : 1 ≤ g) (h0 : e 0 = 0)
    (hstep : ∀ k, abs (e (k + 1) - g * e k) ≤ c) :
    ∀ k, abs (e k) ≤ errEnvelope g c k := by
  have hg0 : (0 : Real) ≤ g := le_trans (le_of_lt zero_lt_one_ax) hg
  intro k
  induction k with
  | zero =>
      rw [h0, errEnvelope_zero, abs_zero]
      exact le_refl _
  | succ n ih =>
      have habs : abs (g * e n) = g * abs (e n) := by
        rw [abs_mul, abs_of_nonneg hg0]
      -- triangle inequality after splitting e(n+1) = g·e n + (e(n+1) − g·e n)
      have hsum : abs (e (n + 1)) ≤ abs (g * e n) + abs (e (n + 1) - g * e n) := by
        have h := abs_add (g * e n) (e (n + 1) - g * e n)
        rw [add_sub_id] at h
        exact h
      -- bound each summand: g·|e n| ≤ g·cap n (ih) and the perturbation ≤ c (hstep)
      have hb1 : abs (g * e n) + abs (e (n + 1) - g * e n) ≤ g * errEnvelope g c n + c := by
        rw [habs]
        exact add_le_add_both (mul_le_mul_of_nonneg_left ih hg0) (hstep n)
      rw [errEnvelope_succ]
      exact le_trans hsum hb1

/-! ## The recognizable closed form (division-free) -/

/-- `cap_N = c · Σ_{j<N} gʲ`. -/
theorem errEnvelope_eq_geomSum (g c : Real) :
    ∀ k, errEnvelope g c k = c * geomSum g k := by
  intro k
  induction k with
  | zero => rw [errEnvelope_zero, geomSum_zero, mul_zero]
  | succ n ih =>
      rw [errEnvelope_succ, geomSum_succ, ih]
      exact envelope_geomSum_step g c (geomSum g n)

/-- `(g − 1) · Σ_{j<N} gʲ = gᴺ − 1` — so `cap_N = c·(gᴺ − 1)/(g − 1)`, division cleared. -/
theorem geomSum_closed (g : Real) :
    ∀ k, (g - 1) * geomSum g k = gpow g k - 1 := by
  intro k
  induction k with
  | zero => rw [geomSum_zero, gpow_zero, mul_zero, sub_def, add_neg]
  | succ n ih =>
      rw [geomSum_succ, gpow_succ, geomSum_expand_step g (geomSum g n), ih]
      exact geomSum_close_step g (gpow g n)

/-! ## The amortization punchline -/

/-- **The rounded schedule never leaves the certified envelope around the exact schedule.** Let `B`
be the exact-arithmetic balance (`B_{k+1} = g·B_k − pmt`) and `b` the rounded balance
(`b_{k+1} = g·b_k − pmt + ρ_k`), both starting at the loan `P`, with each period's rounding
perturbation bounded `|ρ_k| ≤ c`. Then the drift stays inside the envelope:
`|b_k − B_k| ≤ errEnvelope g c k` for all `k`. With `c = ½` cent (banker's rounding,
`roundHalfEven_half_ulp`) this bounds the final-payment adjustment that `amortization_reconciles`
uses to close the balance to exactly `$0.00`. -/
theorem amortization_drift_within_envelope
    {B b rho : Nat → Real} {g pmt P c : Real}
    (hg : 1 ≤ g)
    (hB0 : B 0 = P) (hb0 : b 0 = P)
    (hBrec : ∀ k, B (k + 1) = g * B k - pmt)
    (hbrec : ∀ k, b (k + 1) = g * b k - pmt + rho k)
    (hrho : ∀ k, abs (rho k) ≤ c) :
    ∀ k, abs (b k - B k) ≤ errEnvelope g c k := by
  refine error_within_envelope (e := fun k => b k - B k) hg ?_ ?_
  · show b 0 - B 0 = 0
    rw [hb0, hB0, sub_def, add_neg]
  · intro k
    show abs ((b (k + 1) - B (k + 1)) - g * (b k - B k)) ≤ c
    have hstep : (b (k + 1) - B (k + 1)) - g * (b k - B k) = rho k := by
      rw [hbrec k, hBrec k]
      exact drift_step_ring g (b k) (B k) (rho k) pmt
    rw [hstep]; exact hrho k

end MachLib.Real
