import MachLib.ClosedLoopSafety
import MachLib.FPModel

/-!
# Tracking a two-state loop, and why the obvious measure cannot do it

**The gap this closes.** `foundations/docs/what_is_proven.md` §2 lists four obstacles between the
corpus and an end-to-end join for a PID controller. Three are gone (`SignedFixedPoint`); the
fourth was recorded as "every trajectory lemma is scalar and first-order". That description turned
out to be half wrong in a useful way: **`iterate_affine_bound` is generic over an arbitrary
sequence `s : Nat → Real`** and never required `s` to be the absolute difference of two scalars.
So the missing object is not an iteration lemma. It is a **measure of the vector error that
contracts**, and this file is about which measures can and cannot be that.

**The negative result comes first, because it rules out the obvious attempt.** A PI loop over the
state `(x, i)` — plant `x' = a·x + u`, control `u = Kp·(r − x) + Ki·i`, integrator
`i' = i + (r − x)` — has closed-loop matrix

```
M = [ a − Kp   Ki ]
    [   −1      1 ]
```

and the natural measure to reach for is a weighted maximum of the components,
`‖v‖ = max (|v₁|/w₁) (|v₂|/w₂)`. **No positive weights make that a contraction, for any gains at
all**, and the reason is structural rather than numerical: the triangle inequality can only see
`|M|` entrywise, the integrator row is `[−1, 1]` whose moduli sum to `2` regardless of the design,
so the row-2 requirement is `w₁ + w₂ ≤ L·w₂`, giving `L > 1` whenever `w₁ > 0`. That is
`weighted_max_cannot_contract_integrator` below.

The obstruction is not an artifact of the bound being loose. Measured over five stable designs,
every closed-loop `M` has spectral radius `< 1` while its entrywise-modulus matrix `|M|` has
spectral radius `> 1` (`1.03`–`1.14`). **The negative feedback that stabilises the loop lives in
the sign of that `−1`, and taking moduli is exactly the step that discards it.**

**What does work.** A measure built from two *linear functionals* rather than from the components:
`m u v = max |p·u + q·v| |r·u + s·v|`. It is a seminorm (so subadditive, which is all the error
recursion needs), and when the functionals are chosen as the left eigenvectors of `M` — real and
distinct for the usual over-damped designs — `m ∘ M ≤ ρ(M) · m` with `ρ(M) < 1`. The contraction
is then an arithmetic fact about four constants, supplied by the caller and discharged at the
concrete gains, and no square roots or matrix machinery are needed anywhere.

**Scope, stated plainly.** This file supplies the measure, its subadditivity, and the tracking
theorem that consumes a contraction hypothesis. It does **not** instantiate them at a bit-level
PID datapath, and it does not construct the eigenvectors — a caller with concrete gains does both
by arithmetic. So this removes obstacle (4) as a *missing lemma*; it does not by itself make the
PID join a theorem.
-/

namespace MachLib

namespace Real

/-! ### The negative result -/

/-- **No weighted maximum of the components can contract a loop containing an integrator.**

The integrator row of any PI/PID closed loop is `i' = i + (r − x)`, whose coefficients have
modulus `1` and `1`. A weighted max-norm `max (|v₁|/w₁) (|v₂|/w₂)` can only bound that row by the
sum of the moduli, so a contraction factor `L` would have to satisfy `w₁ + w₂ ≤ L·w₂` — and with
`w₁` strictly positive that forces `L > 1`.

Stated over the requirement rather than over a matrix, so it cannot be dodged by rescaling: it
holds for **every** choice of positive weights and **every** set of gains. -/
theorem weighted_max_cannot_contract_integrator
    {w₁ w₂ L : Real} (hw₁ : 0 < w₁) (hrow : w₁ + w₂ ≤ L * w₂) (hw₂ : 0 < w₂) : 1 < L := by
  -- from `w₁ + w₂ ≤ L·w₂` and `w₁ > 0` we get `w₂ < L·w₂`, hence `1 < L`
  have hlt : w₂ < w₁ + w₂ := by
    have u := add_lt_add_left hw₁ w₂
    have e1 : w₂ + 0 = w₂ := by mach_ring
    have e2 : w₂ + w₁ = w₁ + w₂ := add_comm w₂ w₁
    rw [e1, e2] at u; exact u
  have hstrict : w₂ < L * w₂ := lt_of_lt_of_le hlt hrow
  -- `w₂ = 1 · w₂ < L · w₂` with `w₂ > 0` gives `1 < L`
  have hone : (1 : Real) * w₂ < L * w₂ := by
    rw [one_mul_thm]; exact hstrict
  by_cases hL : 1 < L
  · exact hL
  · exfalso
    have hle : L ≤ 1 := by
      rcases lt_total L 1 with h | h | h
      · exact le_of_lt h
      · rw [h]; exact le_refl 1
      · exact absurd h hL
    have hcon : L * w₂ ≤ 1 * w₂ := mul_le_mul_of_nonneg_right hle (le_of_lt hw₂)
    exact absurd (lt_of_lt_of_le hone hcon) (lt_irrefl_ax _)

/-! ### The measure that does work -/

/-- A seminorm on a two-component state, built from two linear functionals rather than from the
components. Choosing `(p,q)` and `(r,s)` as left eigenvectors of the closed-loop matrix is what
makes it contract; the definition itself does not know that. -/
noncomputable def m2 (p q r s u v : Real) : Real :=
  max (abs (p * u + q * v)) (abs (r * u + s * v))

theorem m2_nonneg (p q r s u v : Real) : 0 ≤ m2 p q r s u v :=
  max_nonneg_left (abs_nonneg _)

/-- **The measure is subadditive.** This is the only property the error recursion needs, and it is
where a measure built from linear functionals differs from one built from the components: the
functionals are applied *before* the absolute value, so cancellation inside them survives. -/
theorem m2_subadd (p q r s u₁ v₁ u₂ v₂ : Real) :
    m2 p q r s (u₁ + u₂) (v₁ + v₂) ≤ m2 p q r s u₁ v₁ + m2 p q r s u₂ v₂ := by
  refine max_le ?_ ?_
  · have esplit : p * (u₁ + u₂) + q * (v₁ + v₂) = (p * u₁ + q * v₁) + (p * u₂ + q * v₂) := by
      mach_mpoly [p, q, u₁, u₂, v₁, v₂]
    rw [esplit]
    refine le_trans (abs_add _ _) ?_
    exact add_le_add_both (le_max_left _ _) (le_max_left _ _)
  · have esplit : r * (u₁ + u₂) + s * (v₁ + v₂) = (r * u₁ + s * v₁) + (r * u₂ + s * v₂) := by
      mach_mpoly [r, s, u₁, u₂, v₁, v₂]
    rw [esplit]
    refine le_trans (abs_add _ _) ?_
    exact add_le_add_both (le_max_right _ _) (le_max_right _ _)

/-- **From left-eigenvector data to the contraction hypothesis.** If `(p,q)` and `(r,s)` are left
eigenvectors of the update matrix with eigenvalues bounded by `L` in modulus, the measure
contracts by `L`. This is the bridge a caller uses: supplying two eigenvectors and two eigenvalue
bounds is arithmetic at concrete gains, where supplying the contraction directly is not.

The proof is one line of algebra per functional — `p·(Au+Bv) + q·(Du+Ev) = λ₁·(p·u + q·v)` — and
that identity is the whole reason the measure sees the cancellation a componentwise one cannot. -/
theorem m2_contract_of_eigen
    {A B D E p q r s lam₁ lam₂ L : Real}
    (h₁u : p * A + q * D = lam₁ * p) (h₁v : p * B + q * E = lam₁ * q)
    (h₂u : r * A + s * D = lam₂ * r) (h₂v : r * B + s * E = lam₂ * s)
    (hl₁ : abs lam₁ ≤ L) (hl₂ : abs lam₂ ≤ L) (u v : Real) :
    m2 p q r s (A * u + B * v) (D * u + E * v) ≤ L * m2 p q r s u v := by
  have hrow₁ : p * (A * u + B * v) + q * (D * u + E * v) = lam₁ * (p * u + q * v) := by
    have e : p * (A * u + B * v) + q * (D * u + E * v)
        = (p * A + q * D) * u + (p * B + q * E) * v := by
      mach_mpoly [p, q, A, B, D, E, u, v]
    rw [e, h₁u, h₁v]
    mach_mpoly [lam₁, p, q, u, v]
  have hrow₂ : r * (A * u + B * v) + s * (D * u + E * v) = lam₂ * (r * u + s * v) := by
    have e : r * (A * u + B * v) + s * (D * u + E * v)
        = (r * A + s * D) * u + (r * B + s * E) * v := by
      mach_mpoly [r, s, A, B, D, E, u, v]
    rw [e, h₂u, h₂v]
    mach_mpoly [lam₂, r, s, u, v]
  refine max_le ?_ ?_
  · rw [hrow₁, abs_mul]
    refine le_trans (mul_le_mul_of_nonneg_right hl₁ (abs_nonneg _)) ?_
    exact mul_le_mul_of_nonneg_left (le_max_left _ _) (le_trans (abs_nonneg lam₁) hl₁)
  · rw [hrow₂, abs_mul]
    refine le_trans (mul_le_mul_of_nonneg_right hl₂ (abs_nonneg _)) ?_
    exact mul_le_mul_of_nonneg_left (le_max_right _ _) (le_trans (abs_nonneg lam₂) hl₂)

/-! ### The tracking theorem -/

/-- **A two-state computed trajectory tracks its exact one, with the error measured by `m2`.**

The shape is deliberately the same as `fxaffine_traj_tracks_exact` one dimension up, and the
proof is a two-line reduction to `iterate_affine_bound` — which was already generic over the
sequence, so no new iteration machinery appears here.

* `hexact` / `hcomp` say both trajectories follow the same affine update, the computed one only
  up to a per-step perturbation `(dx k, di k)`.
* `hcontract` is the eigen-coordinate contraction, supplied by the caller: at concrete gains it is
  an arithmetic fact about four constants. By `weighted_max_cannot_contract_integrator` it cannot
  be obtained from a componentwise measure, which is why it is a hypothesis and not a lemma.
* `hpert` bounds the per-step perturbation in the same measure.

The conclusion carries the transient `Lⁿ · m₀` as well as the steady term, because
`iterate_affine_bound` does not assume the two trajectories start together. -/
theorem two_state_tracks_exact
    {A B C D E F L ε : Real}
    {p q r s : Real}
    {x i xe ie dx di : Nat → Real}
    (hL : 0 ≤ L) (hε : 0 ≤ ε)
    (hexact : ∀ k, xe (k + 1) = A * xe k + B * ie k + C)
    (hexacti : ∀ k, ie (k + 1) = D * xe k + E * ie k + F)
    (hcomp : ∀ k, x (k + 1) = A * x k + B * i k + C + dx k)
    (hcompi : ∀ k, i (k + 1) = D * x k + E * i k + F + di k)
    (hcontract : ∀ u v : Real, m2 p q r s (A * u + B * v) (D * u + E * v) ≤ L * m2 p q r s u v)
    (hpert : ∀ k, m2 p q r s (dx k) (di k) ≤ ε)
    (n : Nat) :
    m2 p q r s (x n - xe n) (i n - ie n)
      ≤ npow n L * m2 p q r s (x 0 - xe 0) (i 0 - ie 0) + ε * geom L n := by
  refine iterate_affine_bound (fun k => m2 p q r s (x k - xe k) (i k - ie k)) hL hε ?_ n
  intro k
  -- the error advances by the same affine map, plus the perturbation
  have ex : x (k + 1) - xe (k + 1)
      = (A * (x k - xe k) + B * (i k - ie k)) + dx k := by
    rw [hcomp k, hexact k]
    mach_mpoly [A, B, C, x k, xe k, i k, ie k, dx k]
  have ei : i (k + 1) - ie (k + 1)
      = (D * (x k - xe k) + E * (i k - ie k)) + di k := by
    rw [hcompi k, hexacti k]
    mach_mpoly [D, E, F, x k, xe k, i k, ie k, di k]
  rw [ex, ei]
  refine le_trans (m2_subadd p q r s _ _ _ _) ?_
  exact add_le_add_both (hcontract (x k - xe k) (i k - ie k)) (hpert k)

/-! ### A specimen — the contraction hypothesis is dischargeable

The vacuity risk in `two_state_tracks_exact` is concentrated in `hcontract`: the recurrence
hypotheses are definitional and a caller supplies them by `rfl`, but a contraction that no matrix
satisfies would make the theorem empty. This corpus has a recorded flagship that was vacuously
true for weeks while every gate passed, so the hypothesis is discharged here at a concrete,
non-diagonal update whose eigenvectors are not the coordinate functionals.

The specimen is `M = [[0, h], [h, 0]]` — eigenvalues `±h`, left eigenvectors `(1,1)` and `(1,−1)`.
It is honest about what it demonstrates: it shows the machinery closes, **not** that it is needed,
because this particular `M` has a modulus matrix that is also a contraction. The regime where a
componentwise measure provably fails is the integrator row of
`weighted_max_cannot_contract_integrator`, and instantiating *that* is arithmetic at concrete
gains, which a caller does. -/
theorem m2_contract_swap_specimen (h : Real) (u v : Real) :
    m2 1 1 1 (-1) (0 * u + h * v) (h * u + 0 * v) ≤ abs h * m2 1 1 1 (-1) u v := by
  refine m2_contract_of_eigen (lam₁ := h) (lam₂ := -h) ?_ ?_ ?_ ?_ (le_refl _) ?_ u v
  · mach_mpoly [h]
  · mach_mpoly [h]
  · mach_mpoly [h]
  · mach_mpoly [h]
  · rw [abs_neg]; exact le_refl _

/-- The tracking theorem, with its contraction hypothesis discharged: only the two recurrences
remain, and a caller supplies those by `rfl` from its own definitions. -/
theorem two_state_tracks_exact_swap_specimen
    {h ε : Real} {x i xe ie dx di : Nat → Real}
    (hε : 0 ≤ ε)
    (hexact : ∀ k, xe (k + 1) = 0 * xe k + h * ie k + 0)
    (hexacti : ∀ k, ie (k + 1) = h * xe k + 0 * ie k + 0)
    (hcomp : ∀ k, x (k + 1) = 0 * x k + h * i k + 0 + dx k)
    (hcompi : ∀ k, i (k + 1) = h * x k + 0 * i k + 0 + di k)
    (hpert : ∀ k, m2 1 1 1 (-1) (dx k) (di k) ≤ ε)
    (n : Nat) :
    m2 1 1 1 (-1) (x n - xe n) (i n - ie n)
      ≤ npow n (abs h) * m2 1 1 1 (-1) (x 0 - xe 0) (i 0 - ie 0) + ε * geom (abs h) n :=
  two_state_tracks_exact (abs_nonneg h) hε hexact hexacti hcomp hcompi
    (m2_contract_swap_specimen h) hpert n

end Real

end MachLib
