import MachLib.Ekf2GainBounded

/-!
# `m·‖K row‖² ≤ P₀₀` — the gain bound that SHRINKS with the prior

**The theorem that makes the composed EKF forward-error bound non-vacuous during acquisition.**

`Ekf2GainBounded` proved the collapse — that `P − K S Kᵀ` *is* the Joseph form — and stated the
consequence in words. This file turns it into the inequality the fold actually consumes, and does it
**without `sqrt` and without division**.

## The vacuity being removed, stated concretely

The composed `ε` instantiates the gain's magnitude as `Mk ≈ ‖P Hᵀ‖ / m` with `m` a lower bound on
`det S`. That factor **grows without limit as `det S → det R`**, which is exactly what convergence
does. So the bound was *worst at the converged steps* — inverted from where the measured error is,
and loose enough during acquisition to be useless.

The physics says the opposite: as `P → 0` the gain `K → 0` too, because `S → R` simultaneously.
Bounding `‖P‖` and `‖S⁻¹‖` **independently** throws that cancellation away. The link is:

```
    K S Kᵀ ⪯ P        (the Joseph collapse, Ekf2GainBounded)
    S ⪰ R             (S = H P Hᵀ + R and H P Hᵀ ⪰ 0)
    R ⪰ m·I           (hypothesis: R's smallest eigenvalue)
  ⟹ m·(k₀₀² + k₀₁²) ≤ P₀₀
```

**Read it as an energy statement:** the gain cannot extract more energy from the innovation than the
prior carries. The right-hand side is `P₀₀`, so the bound **shrinks with `P`** — which is the whole
point, and the reason it is tight precisely where the old one was worst.

## Why no `sqrt` and no division

`‖K‖ ≲ √(‖P‖/λ_min(R))` is the familiar form and it is the wrong one to prove here: MachLib would
need `sqrt` monotonicity and a division, both of which drag hypotheses into a statement that does not
need them. The squared, cleared form `m·(k₀₀² + k₀₁²) ≤ pa` says the same thing. The fold wants
`|k₀₀| ≤ Mk`, and `ekf2_gain_abs_le` supplies exactly that from a caller-chosen `Mk` satisfying
`pa ≤ m·Mk²` — so the square root is taken **once, numerically, by the caller**, and never appears in
a theorem.

**The measured footprint, because "no sqrt" is a claim about DEPENDENCIES and not about spelling:**

| theorem | axioms | sqrt? | division? |
|---|---:|---|---|
| `ekf2_gain_energy_le_prior` | **26** | none | none |
| `ekf2_gain_abs_le` | 29 | none | `divR`, `mul_inv`, `one_div_pos_of_pos` |

The main theorem is clean in both statement *and* dependencies. The helper is not quite: its three
division axioms arrive through `le_of_mul_le_mul_right_pos`, which cancels a positive factor by
multiplying by its inverse. That is stated rather than papered over.

**And `#print axioms` is what caught the first version.** It proved `|k₀₀| ≤ Mk` via
`abs_le_sqrt_of_sq_le` + `sqrt_sq` — two lines, correct, and it pulled **nine** extra axioms
(`sqrt`, `sqrt_nonneg`, `le_sqrt_of_sq_le`, `sqrt_le_of_le_sq`, …) into the footprint of a statement
that mentions no square root. The statement was sqrt-free and the DEPENDENCY was not, which is
exactly the gap a ledger exists to expose. The replacement argues by trichotomy against
`abs k · abs k = k · k` and costs four lines.

## Why `Psd2`'s definition does most of the work

`Psd2 a b d` is literally `∀ x y, 0 ≤ a x² + 2b xy + d y²`. Every quantity in the chain above is that
form **evaluated at a specific point**:

| quantity | is `Psd2 … ` at |
|---|---|
| `(K R Kᵀ)₀₀` | `hR` at `(k₀₀, k₀₁)` |
| `(K H P Hᵀ Kᵀ)₀₀` | `hP` at `((KH)₀₀, (KH)₀₁)` |
| `(I−KH) P (I−KH)ᵀ)₀₀` | `hP` at `(1−(KH)₀₀, −(KH)₀₁)` |
| `m(k₀₀²+k₀₁²) ≤ (K R Kᵀ)₀₀` | `hRm` at `(k₀₀, k₀₁)` |

No congruence lemma is invoked — instantiating the predicate directly is shorter *and* keeps every
step visibly about the same quadratic form.

`sorryAx`-free, zero new axioms.
-/

namespace MachLib.Real

/-- Shifting a quadratic form by `m·I`. Hoisted to top level for two reasons: `mach_mpoly`'s atom
list is elaborated outside the tactic block, so `x`/`y` bound by an `intro` are not in scope there;
and stating it generically keeps the goal SMALL, which is the difference between 11 seconds and a
heartbeat timeout. -/
private theorem psd_shift_id (ra rb rd m x y : Real) :
    ra * (x * x) + (1 + 1) * rb * (x * y) + rd * (y * y)
      = ((ra - m) * (x * x) + (1 + 1) * rb * (x * y) + (rd - m) * (y * y))
        + (m * (x * x) + m * (y * y)) := by
  mach_mpoly [ra, rb, rd, m, x, y]

/-- `p − (A + B) = p − A − B`. Trivial, and deliberately stated on THREE opaque atoms: inlining it
made `mach_ring` chew on the fully-expanded `K S Kᵀ` entries and fail on size alone. -/
private theorem sub_add_eq_sub_sub (p A B : Real) : p - (A + B) = p - A - B := by mach_ring

/-- `R ⪰ m·I` implies `R ⪰ 0`, given `m ≥ 0`. Needed because the Joseph term wants plain PSD. -/
theorem psd2_of_psd2_sub_scalar {ra rb rd m : Real} (hm : 0 ≤ m)
    (hRm : Psd2 (ra - m) rb (rd - m)) : Psd2 ra rb rd := by
  intro x y
  have h := hRm x y
  have hxx : 0 ≤ m * (x * x) := mul_nonneg hm (mul_self_nonneg x)
  have hyy : 0 ≤ m * (y * y) := mul_nonneg hm (mul_self_nonneg y)
  have hid : ra * (x * x) + (1 + 1) * rb * (x * y) + rd * (y * y)
      = ((ra - m) * (x * x) + (1 + 1) * rb * (x * y) + (rd - m) * (y * y))
        + (m * (x * x) + m * (y * y)) := psd_shift_id ra rb rd m x y
  rw [hid]
  exact add_nonneg h (add_nonneg hxx hyy)

/-- **`R ⪰ m·I` bounds the gain row's energy from below by `m·‖k‖²`.**
Just `hRm` evaluated at `(k₀₀, k₀₁)`, rearranged. -/
theorem krkt_ge_m_normsq {k00 k01 ra rb rd m : Real}
    (hRm : Psd2 (ra - m) rb (rd - m)) :
    m * (k00 * k00 + k01 * k01)
      ≤ k00 * k00 * ra + (1 + 1) * (k00 * k01) * rb + k01 * k01 * rd := by
  have h := hRm k00 k01
  have hid : (ra - m) * (k00 * k00) + (1 + 1) * rb * (k00 * k01) + (rd - m) * (k01 * k01)
      = (k00 * k00 * ra + (1 + 1) * (k00 * k01) * rb + k01 * k01 * rd)
        - m * (k00 * k00 + k01 * k01) := by mach_ring
  rw [hid] at h
  exact le_of_sub_nonneg h

set_option maxHeartbeats 4000000 in
/-- **THE GAIN BOUND: `m·(k₀₀² + k₀₁²) ≤ pa`.**

The gain cannot extract more energy from the innovation than the prior carries. Proven from the
gain equation, `P ⪰ 0` and `R ⪰ m·I` — **no inverse, no `sqrt`, no division**.

Every step is `Psd2` instantiated at a point, chained through the Joseph collapse:

```
  m‖k‖²  ≤  (K R Kᵀ)₀₀                       hRm at (k₀₀,k₀₁)
         ≤  (K H P Hᵀ Kᵀ)₀₀ + (K R Kᵀ)₀₀     hP at ((KH)₀₀,(KH)₀₁) is ≥ 0
         =  (K S Kᵀ)₀₀                        S = H P Hᵀ + R
         ≤  pa                                Joseph collapse: pa − (K S Kᵀ)₀₀ is PSD's (0,0)
```
-/
theorem ekf2_gain_energy_le_prior
    (k00 k01 pa pb pd ra rb rd h00 h01 h10 h11 m : Real)
    (hm : 0 ≤ m) (hP : Psd2 pa pb pd) (hRm : Psd2 (ra - m) rb (rd - m))
    (hg00 : k00 * ((h00*h00*pa + (1+1)*(h00*h01)*pb + h01*h01*pd) + ra)
          + k01 * ((h00*h10*pa + (h00*h11 + h01*h10)*pb + h01*h11*pd) + rb)
          = pa * h00 + pb * h01)
    (hg01 : k00 * ((h00*h10*pa + (h00*h11 + h01*h10)*pb + h01*h11*pd) + rb)
          + k01 * ((h10*h10*pa + (1+1)*(h10*h11)*pb + h11*h11*pd) + rd)
          = pa * h10 + pb * h11) :
    m * (k00 * k00 + k01 * k01) ≤ pa := by
  have hR : Psd2 ra rb rd := psd2_of_psd2_sub_scalar hm hRm
  -- (1) the Joseph form's (0,0) entry is nonnegative: congruence of P by (I−KH), plus K R Kᵀ
  have hJ : 0 ≤ ((1 - (k00*h00 + k01*h10)) * (1 - (k00*h00 + k01*h10)) * pa
          + (1+1) * ((1 - (k00*h00 + k01*h10)) * (-(k00*h01 + k01*h11))) * pb
          + (k00*h01 + k01*h11) * (k00*h01 + k01*h11) * pd)
        + (k00*k00*ra + (1+1)*(k00*k01)*rb + k01*k01*rd) := by
    have hp := hP (1 - (k00*h00 + k01*h10)) (-(k00*h01 + k01*h11))
    have hr := hR k00 k01
    have hidp : pa * ((1 - (k00*h00 + k01*h10)) * (1 - (k00*h00 + k01*h10)))
          + (1 + 1) * pb * ((1 - (k00*h00 + k01*h10)) * (-(k00*h01 + k01*h11)))
          + pd * ((-(k00*h01 + k01*h11)) * (-(k00*h01 + k01*h11)))
        = (1 - (k00*h00 + k01*h10)) * (1 - (k00*h00 + k01*h10)) * pa
          + (1+1) * ((1 - (k00*h00 + k01*h10)) * (-(k00*h01 + k01*h11))) * pb
          + (k00*h01 + k01*h11) * (k00*h01 + k01*h11) * pd := by
      -- v4.16.0: `mach_ring` no longer closes this. Its simp phase still normalises both sides, but
      -- the `ac_rfl` closer fails on the post-distribution AC residue (9 atoms, degree 4) that it
      -- used to handle -- 21s spent, then unsolved. `mach_mpoly` with the atoms named closes it in
      -- 6.4s, which is the standing house rule anyway: `mach_ring` is the weak all-`try`
      -- normaliser, `mach_mpoly` is the complete one for identities needing cancellation.
      -- Worth recording for the next stop: this single failure produced THREE errors in the build
      -- log. maxHeartbeats is per-DECLARATION, so exhausting it here made `hidr` below and the
      -- theorem's own `whnf` time out as collateral -- both pass untouched (hidr in 0.5s, on the
      -- DEFAULT budget). Attribute the first failure in a declaration before believing the rest.
      mach_mpoly [pa, pb, pd, k00, k01, h00, h01, h10, h11]
    have hidr : ra * (k00 * k00) + (1 + 1) * rb * (k00 * k01) + rd * (k01 * k01)
        = k00*k00*ra + (1+1)*(k00*k01)*rb + k01*k01*rd := by mach_ring
    rw [hidp] at hp
    rw [hidr] at hr
    exact add_nonneg hp hr
  -- (2) the collapse turns that into (K S Kᵀ)₀₀ ≤ pa
  have hksk : (k00 * ((h00*h00*pa + (1+1)*(h00*h01)*pb + h01*h01*pd) + ra)
        + k01 * ((h00*h10*pa + (h00*h11 + h01*h10)*pb + h01*h11*pd) + rb)) * k00
      + (k00 * ((h00*h10*pa + (h00*h11 + h01*h10)*pb + h01*h11*pd) + rb)
        + k01 * ((h10*h10*pa + (1+1)*(h10*h11)*pb + h11*h11*pd) + rd)) * k01
      ≤ pa := by
    have hj := joseph_eq_p_sub_ksk_a k00 k01 pa pb pd ra rb rd h00 h01 h10 h11 hg00 hg01
    rw [← hj] at hJ
    exact le_of_sub_nonneg (by rw [sub_add_eq_sub_sub]; exact hJ)
  -- (3) drop the H P Hᵀ part, which is ≥ 0, and apply the R lower bound
  have hhph : 0 ≤ (k00*h00 + k01*h10) * (k00*h00 + k01*h10) * pa
      + (1+1) * ((k00*h00 + k01*h10) * (k00*h01 + k01*h11)) * pb
      + (k00*h01 + k01*h11) * (k00*h01 + k01*h11) * pd := by
    have hp := hP (k00*h00 + k01*h10) (k00*h01 + k01*h11)
    have hid : pa * ((k00*h00 + k01*h10) * (k00*h00 + k01*h10))
          + (1 + 1) * pb * ((k00*h00 + k01*h10) * (k00*h01 + k01*h11))
          + pd * ((k00*h01 + k01*h11) * (k00*h01 + k01*h11))
        = (k00*h00 + k01*h10) * (k00*h00 + k01*h10) * pa
          + (1+1) * ((k00*h00 + k01*h10) * (k00*h01 + k01*h11)) * pb
          + (k00*h01 + k01*h11) * (k00*h01 + k01*h11) * pd := by mach_ring
    rwa [hid] at hp
  have hsplit := ksk_split_a k00 k01 pa pb pd ra rb rd h00 h01 h10 h11
  have hkrkt := krkt_ge_m_normsq (k00 := k00) (k01 := k01) hRm
  -- m‖k‖² ≤ KRKᵀ ≤ HPHᵀ-part + KRKᵀ = KSKᵀ ≤ pa
  refine le_trans hkrkt (le_trans ?_ hksk)
  have hform : (k00 * ((h00*h00*pa + (1+1)*(h00*h01)*pb + h01*h01*pd) + ra)
        + k01 * ((h00*h10*pa + (h00*h11 + h01*h10)*pb + h01*h11*pd) + rb)) * k00
      + (k00 * ((h00*h10*pa + (h00*h11 + h01*h10)*pb + h01*h11*pd) + rb)
        + k01 * ((h10*h10*pa + (1+1)*(h10*h11)*pb + h11*h11*pd) + rd)) * k01
      = k00 * (k00 * ((h00*h00*pa + (1+1)*(h00*h01)*pb + h01*h01*pd) + ra)
             + k01 * ((h00*h10*pa + (h00*h11 + h01*h10)*pb + h01*h11*pd) + rb))
      + k01 * (k00 * ((h00*h10*pa + (h00*h11 + h01*h10)*pb + h01*h11*pd) + rb)
             + k01 * ((h10*h10*pa + (1+1)*(h10*h11)*pb + h11*h11*pd) + rd)) := by mach_ring
  rw [hform, hsplit]
  exact le_add_of_nonneg_left hhph

/-- **The interface the fold consumes: `|k₀₀| ≤ Mk`.**

The caller picks `Mk` and discharges `pa ≤ m·Mk²` — one numeric square root, taken *outside* any
theorem. That is deliberate: it keeps `sqrt` out of the statement, and it means the bound the fold
uses is a caller-visible constant rather than an opaque term. -/
theorem ekf2_gain_abs_le {k00 k01 pa m Mk : Real}
    (hMk : 0 ≤ Mk) (hm : 0 < m)
    (hbound : m * (k00 * k00 + k01 * k01) ≤ pa) (hfit : pa ≤ m * (Mk * Mk)) :
    abs k00 ≤ Mk := by
  have hsq : k00 * k00 ≤ Mk * Mk := by
    have h1 : m * (k00 * k00 + k01 * k01) ≤ m * (Mk * Mk) := le_trans hbound hfit
    have h1' : (k00 * k00 + k01 * k01) * m ≤ (Mk * Mk) * m := by
      rw [mul_comm (k00 * k00 + k01 * k01) m, mul_comm (Mk * Mk) m]; exact h1
    exact le_trans (le_add_of_nonneg_right (mul_self_nonneg k01))
      (le_of_mul_le_mul_right_pos h1' hm)
  -- NO `sqrt`, not even in the proof. The first version routed through `abs_le_sqrt_of_sq_le` +
  -- `sqrt_sq`, which is shorter but drags NINE extra axioms (`sqrt`, `divR`, `mul_inv`, …) into the
  -- footprint of a statement that mentions neither. `#print axioms` is what caught it: the
  -- statement was sqrt-free and the DEPENDENCY was not, which is exactly the gap an axiom ledger
  -- exists to expose. Contradiction with `abs_mul_self` costs four lines and keeps the footprint
  -- identical to the main theorem's.
  rcases lt_total Mk (abs k00) with hlt | heq | hgt
  · exfalso
    have hpos : 0 < abs k00 := lt_of_le_of_lt hMk hlt
    have h1 : Mk * Mk ≤ Mk * abs k00 := mul_le_mul_of_nonneg_left (le_of_lt hlt) hMk
    have h2 : Mk * abs k00 < abs k00 * abs k00 := by
      rw [mul_comm Mk (abs k00), mul_comm (abs k00) (abs k00)]
      exact mul_lt_mul_of_pos_left hlt hpos
    have hams : abs k00 * abs k00 = k00 * k00 := by
      rw [← abs_mul, abs_of_nonneg (mul_self_nonneg k00)]
    rw [hams] at h2
    exact lt_irrefl_ax _ (lt_of_le_of_lt hsq (lt_of_le_of_lt h1 h2))
  · exact le_of_eq heq.symm
  · exact le_of_lt hgt

end MachLib.Real
