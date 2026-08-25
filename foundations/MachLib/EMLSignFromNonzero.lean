import MachLib.EMLDepthTameness
import MachLib.GaussianLaplaceRoute

/-!
# Continuous and nonzero on a ray ⟹ constant sign on that ray

`EMLZeroBoundRay` turns a uniform zero bound into **eventual non-vanishing**. This module turns
eventual non-vanishing into **eventual constant sign**, which is what `SignHardCase` asks for.

The mathematics is one line: a continuous function that took both signs would have to cross zero.

## Deliberately generic

The lemma below knows nothing about EML trees, Pfaffian chains, `Fbasis`, or `SignHardCase`. It
takes a bare `f : Real → Real` with two hypotheses on a ray and concludes `EvSign f`. That
separation is the point — it decouples *how* non-vanishing was obtained from *what* it buys, so any
future zero-counting engine can feed it and none of them appear in its statement.

It also isolates the two questions that were entangled when this route was proposed: whether the
bridge is true, and whether a given germ can supply continuity. This file answers only the first.

## `EvSign`'s packaging works in our favour

```
EvSign f := (∃ X₀, 1 ≤ X₀ ∧ ∀ x ≥ X₀, 0 < f x) ∨ (∃ X₀, 1 ≤ X₀ ∧ ∀ x ≥ X₀, f x ≤ 0)
```

The second disjunct is `≤ 0`, not `< 0`, so a strictly-negative conclusion lands in it without
packaging work.

## The orientation wrinkle

`intermediate_value` is stated one way round — `f a < 0` then `0 < f b`. The negative case matches it
directly. The positive case is the mirror image, and rather than assume a mirrored IVT exists, it is
obtained by applying the same theorem to `fun x => -(f x)` via `continuousAt_neg`. Two cases, one
IVT.
-/

namespace MachLib

open Real

private theorem neg_lt_zero_of_pos {a : Real} (h : 0 < a) : -a < 0 := by
  have v := add_lt_add_left h (-a)
  have l : -a + 0 = -a := by mach_ring
  have r : -a + a = 0 := by mach_ring
  rw [l, r] at v; exact v

private theorem zero_lt_neg_of_neg {a : Real} (h : a < 0) : 0 < -a := by
  have v := add_lt_add_left h (-a)
  have l : -a + a = 0 := by mach_ring
  have r : -a + 0 = -a := by mach_ring
  rw [l, r] at v; exact v

private theorem eq_zero_of_neg_eq_zero {a : Real} (h : -a = 0) : a = 0 := by
  have e : a + -a = 0 := by mach_ring
  rw [h] at e
  have e2 : a + 0 = a := by mach_ring
  rw [e2] at e; exact e

/-- **The bridge.** Continuous and nonzero on a ray forces one strict sign on that ray.

Knows nothing about EML, Pfaffian chains, or how the non-vanishing was established. -/
theorem evSign_of_continuous_nonzero_on_ray {f : Real → Real} {R : Real}
    (hR : 1 ≤ R)
    (hne : ∀ x : Real, R ≤ x → f x ≠ 0)
    (hcont : ∀ x : Real, R ≤ x → ContinuousAt f x) :
    EvSign f := by
  rcases lt_total 0 (f R) with hpos | hzero | hneg
  · -- positive at R: it stays positive, or the mirrored IVT finds a zero
    refine Or.inl ⟨R, hR, fun x hx => ?_⟩
    rcases lt_total 0 (f x) with hfx | hfx | hfx
    · exact hfx
    · exact absurd hfx.symm (hne x hx)
    · exfalso
      have hRx : R < x := by
        rcases lt_total R x with h | h | h
        · exact h
        · exact absurd (h ▸ hpos) (fun hp => (ne_of_lt (lt_of_lt_of_le hfx (le_of_lt hp))) rfl)
        · exact absurd (le_of_lt h) (fun hle => (ne_of_lt (lt_of_lt_of_le h hx)) rfl)
      obtain ⟨c, hac, hcb, hc0⟩ :=
        intermediate_value (fun t => -(f t)) R x hRx
          (fun z hz1 hz2 => continuousAt_neg (hcont z hz1))
          (neg_lt_zero_of_pos hpos) (zero_lt_neg_of_neg hfx)
      exact hne c (le_of_lt hac) (eq_zero_of_neg_eq_zero hc0)
  · exact absurd hzero.symm (hne R (le_refl R))
  · -- negative at R: the IVT's own orientation
    refine Or.inr ⟨R, hR, fun x hx => ?_⟩
    rcases lt_total 0 (f x) with hfx | hfx | hfx
    · exfalso
      have hRx : R < x := by
        rcases lt_total R x with h | h | h
        · exact h
        · exact absurd (h ▸ hneg) (fun hn => (ne_of_lt (lt_of_lt_of_le hfx (le_of_lt hn))) rfl)
        · exact absurd (le_of_lt h) (fun _ => (ne_of_lt (lt_of_lt_of_le h hx)) rfl)
      obtain ⟨c, hac, hcb, hc0⟩ :=
        intermediate_value f R x hRx (fun z hz1 hz2 => hcont z hz1) hneg hfx
      exact hne c (le_of_lt hac) hc0
    · exact le_of_eq hfx.symm
    · exact le_of_lt hfx

end MachLib
