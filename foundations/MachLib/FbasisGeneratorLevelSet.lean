import MachLib.FbasisRootUnique
import MachLib.PevRoots
import MachLib.EMLRationalGerm

/-!
# The one-query GENERATOR's level set — finite or cofinite, and GLOBAL

## What this is

`FbasisRootUnique` proves `Fbasis` takes each value at most twice and then says, in as many words:

> This module states the uniqueness only. It does not claim the bounded half — the general germ is
> `bipev N x (Fbasis …)`, a polynomial in `Fbasis` rather than `Fbasis` itself, and that reduction
> is not made here.

The *generator's* half of it is pure assembly of three things already present, and this module makes
it. `fbasis_comp_level_subset` pins `P/Q` to one of two reals fixed independently of `x`; each of
those is the **polynomial** condition `P - uᵢ·Q = 0`; `pev_zero_or_finite_roots` makes a polynomial
identically zero or finitely rooted.

## Why it is worth a module

**It is the first GLOBAL result in this lane.** Everything else here is a ray statement — `EvZeroF`
is `∃ X ≥ 1, ∀ x ≥ X`, and so are `CtxAppliesEv`, `OneQueryDichotomy`, `queryGerm_finite_zeros_on_ray`.
A polynomial is indifferent to whether the region is a ray or a bounded interval, so the collapse
reaches where the asymptotic arguments could not. `EMLZeroListFromBound` names that exact shortfall:
"the other half is the bounded region below `R`".

## What it does NOT give

The generator is the context `hole`. `OneQueryLevelSet` quantifies over every one-hole context, and
for those the equation is `y·B(x) = A(x)` (`one_hole_level_is_affine`), not `y = c`. The two fixed
levels `u₁, u₂` come from `Fbasis` taking each *constant* value at most twice; with a varying right
side there is no such pair, and this argument does not start. That is the degree-1 fragment recorded
in `EMLOneQueryMobius`, and it stays open.

Also worth stating because it nearly went unnoticed: the `Q ≡ 0` branch is real, not a formality.
`pev P x / 0 = 0` by `div_zero`, so the germ collapses to the constant `Fbasis 0 = 1` — the level set
is then all of `ℝ` or empty depending on `c`, and both are legitimate verdicts rather than an edge
case to exclude.
-/

namespace MachLib
open Real

/-- `pev P x / pev Q x = u` off the zeros of `Q` is the polynomial condition `P - u·Q = 0`. -/
private theorem quot_eq_iff_poly {P Q : List Real} {u x : Real} (hQ : pev Q x ≠ 0) :
    pev P x / pev Q x = u ↔ pev (psub P (pscale u Q)) x = 0 := by
  constructor
  · intro h
    rw [pev_psub, pev_pscale]
    have hm : pev P x = u * pev Q x := by
      have e := div_mul_self' (a := pev P x) hQ
      rw [h] at e; exact e.symm
    rw [hm]; mach_ring
  · intro h
    rw [pev_psub, pev_pscale] at h
    have hm : pev P x = u * pev Q x := by
      have e : pev P x = pev P x - u * pev Q x + u * pev Q x := by mach_ring
      rw [h] at e
      have e0 : (0 : Real) + u * pev Q x = u * pev Q x := by mach_ring
      rw [e0] at e; exact e
    rw [hm]
    have ec : u * pev Q x = pev Q x * u := by mach_mpoly [u, pev Q x]
    rw [ec]; exact mul_div_cancel_left' hQ

/-- **The one-query GENERATOR's level set is finite, or everything off a finite set — globally.**

`FbasisRootUnique` states the uniqueness and says in as many words that this collapse "is not made
here". It is the assembly of three things already present: `Fbasis` takes each value at most twice
(`fbasis_comp_level_subset`), so `Fbasis (P/Q) = c` pins `P/Q` to one of two fixed reals; each of
those is the polynomial condition `P - uᵢ·Q = 0`; and `pev_zero_or_finite_roots` makes each
polynomial identically zero or finitely rooted.

Unlike every other result in this lane it is **global** — a polynomial is indifferent to whether
the region is a ray or bounded, which is exactly the reach the ray arguments did not have. -/
theorem fbasis_generator_level_set (P Q : List Real) (c : Real) :
    ∃ E : List Real,
      (∀ x : Real, x ∉ E → Fbasis (pev P x / pev Q x) = c)
      ∨ (∀ x : Real, Fbasis (pev P x / pev Q x) = c → x ∈ E) := by
  classical
  obtain ⟨u₁, u₂, hcarry⟩ := fbasis_comp_level_subset (fun x => pev P x / pev Q x) c
  rcases pev_zero_or_finite_roots Q with hQ0 | ⟨RQ, hRQ⟩
  · -- `Q ≡ 0`, so the quotient is `P/0 = 0` everywhere and the germ is the constant `Fbasis 0 = 1`
    rcases Classical.em (c = 1) with hc | hc
    · refine ⟨[], Or.inl (fun x _ => ?_)⟩
      rw [hQ0 x, div_zero, Fbasis_zero, hc]
    · refine ⟨[], Or.inr (fun x hx => ?_)⟩
      exfalso
      rw [hQ0 x, div_zero, Fbasis_zero] at hx
      exact hc hx.symm
  -- `Q ≢ 0`: its zeros are inside `RQ`, and off them the level set is a polynomial condition
  rcases pev_zero_or_finite_roots (psub P (pscale u₁ Q)) with h1 | ⟨R1, hR1⟩
  · -- `P - u₁·Q ≡ 0`, so the quotient is `u₁` off `RQ`, and the level is attained there iff
    -- `Fbasis u₁ = c`; either way the verdict is one of the two branches.
    rcases Classical.em (Fbasis u₁ = c) with hattain | hmiss
    · refine ⟨RQ, Or.inl (fun x hx => ?_)⟩
      have hQx : pev Q x ≠ 0 := fun h => hx (hRQ x h)
      rw [(quot_eq_iff_poly hQx).mpr (h1 x)]; exact hattain
    · refine ⟨RQ, Or.inr (fun x hx => ?_)⟩
      rcases Classical.em (x ∈ RQ) with hin | hout
      · exact hin
      · exfalso
        have hQx : pev Q x ≠ 0 := fun h => hout (hRQ x h)
        rw [(quot_eq_iff_poly hQx).mpr (h1 x)] at hx
        exact hmiss hx
  rcases pev_zero_or_finite_roots (psub P (pscale u₂ Q)) with h2 | ⟨R2, hR2⟩
  · rcases Classical.em (Fbasis u₂ = c) with hattain | hmiss
    · refine ⟨RQ, Or.inl (fun x hx => ?_)⟩
      have hQx : pev Q x ≠ 0 := fun h => hx (hRQ x h)
      rw [(quot_eq_iff_poly hQx).mpr (h2 x)]; exact hattain
    · refine ⟨RQ, Or.inr (fun x hx => ?_)⟩
      rcases Classical.em (x ∈ RQ) with hin | hout
      · exact hin
      · exfalso
        have hQx : pev Q x ≠ 0 := fun h => hout (hRQ x h)
        rw [(quot_eq_iff_poly hQx).mpr (h2 x)] at hx
        exact hmiss hx
  -- both polynomials are nonzero: the level set is inside `RQ ++ R1 ++ R2`
  refine ⟨RQ ++ (R1 ++ R2), Or.inr (fun x hx => ?_)⟩
  rcases Classical.em (x ∈ RQ) with hin | hout
  · exact List.mem_append_left _ hin
  have hQx : pev Q x ≠ 0 := fun h => hout (hRQ x h)
  refine List.mem_append_right _ ?_
  rcases hcarry x hx with h | h
  · exact List.mem_append_left _ (hR1 x ((quot_eq_iff_poly hQx).mp h))
  · exact List.mem_append_right _ (hR2 x ((quot_eq_iff_poly hQx).mp h))

end MachLib
