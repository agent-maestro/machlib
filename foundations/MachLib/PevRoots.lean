import MachLib.EMLRationalGerm
import MachLib.QuadraticRoots

/-!
# A nonzero polynomial has finitely many roots — algebraically, with no analysis

`pev_dichotomy` gives the *eventual* picture: a coefficient list is eventually zero or eventually
dominates `c·xᵏ`. That controls a tail and says nothing below it, which is exactly the gap that
matters when the countertarget is **global** — `floor` and `mod` do their damage everywhere, not at
infinity.

This file supplies the global fact, and supplies it **algebraically**: no analyticity, no
intermediate value theorem, no zero-counting axiom. The whole content is synthetic division.

## The construction

`deflate r L` is the quotient of `L` by `(x − r)`, computed by Horner from the head:

```
deflate r []        = []
deflate r [_]       = []
deflate r (_ :: cs) = pev cs r :: deflate r cs
```

The dropped head is genuinely dropped — the head of `L` never appears in the quotient, only in the
remainder — so the list gets exactly one shorter, which is what makes the induction terminate. The
identity is the division algorithm with no side condition at all:

```
pev L x = (x − r) · pev (deflate r L) x + pev L r
```

Note it holds for **every** `r`, root or not; `pev L r = 0` is used only at the call site. Stating it
without the hypothesis is what keeps the proof a ring identity rather than a case analysis.

## What comes out

`pev_zero_or_root_list`: every coefficient list either vanishes identically, or has its roots
contained in an explicit finite list. That is the global counterpart of `pev_dichotomy`, and it is
the missing ingredient for a **global** normal form for zero-query terms — where the totalised
divisor must be split into "identically zero, so `div_zero` fires" and "nonzero, so adjoin its
finitely many roots to the exceptional set".

The existential is a `List Real` rather than a `Set` with a finiteness proof: in this corpus a list
*is* the finiteness witness, and it keeps the statement usable by `List.Mem` induction.
-/

namespace MachLib

open Real

/-- Synthetic division of a coefficient list by `(x − r)`. -/
noncomputable def deflate (r : Real) : List Real → List Real
  | []      => []
  | [_]     => []
  | _ :: cs => pev cs r :: deflate r cs

/-- The quotient is exactly one coefficient shorter. -/
theorem deflate_length : ∀ (cs : List Real) (r c : Real),
    (deflate r (c :: cs)).length = cs.length := by
  intro cs
  induction cs with
  | nil => intro _ _; rfl
  | cons d ds ih =>
      intro r _
      show (deflate r (d :: ds)).length + 1 = ds.length + 1
      rw [ih r d]

private theorem deflate_step (c x r D S : Real) :
    c + x * ((x - r) * D + S) = (x - r) * (S + x * D) + (c + r * S) := by
  mach_mpoly [c, x, r, D, S]

private theorem deflate_nil_step (c x r : Real) :
    c + x * 0 = (x - r) * 0 + (c + r * 0) := by
  mach_mpoly [c, x, r]

private theorem deflate_zero_step (x r : Real) : (x - r) * 0 + 0 = 0 := by
  mach_mpoly [x, r]

/-- **The division algorithm, no hypothesis.** `pev L x = (x − r)·q(x) + pev L r` for every `r`. -/
theorem pev_deflate : ∀ (L : List Real) (r x : Real),
    pev L x = (x - r) * pev (deflate r L) x + pev L r := by
  intro L
  induction L with
  | nil =>
      intro r x
      show (0 : Real) = (x - r) * 0 + 0
      exact (deflate_zero_step x r).symm
  | cons c cs ih =>
      intro r x
      cases cs with
      | nil =>
          show c + x * 0 = (x - r) * 0 + (c + r * 0)
          exact deflate_nil_step c x r
      | cons d ds =>
          show c + x * pev (d :: ds) x
              = (x - r) * (pev (d :: ds) r + x * pev (deflate r (d :: ds)) x)
                + (c + r * pev (d :: ds) r)
          rw [ih r x]
          exact deflate_step c x r (pev (deflate r (d :: ds)) x) (pev (d :: ds) r)

private theorem factor_zero (x r D : Real) (h : (x - r) * D + 0 = 0) : (x - r) * D = 0 := by
  have e : (x - r) * D + 0 = (x - r) * D := by mach_mpoly [x, r, D]
  rw [e] at h; exact h

private theorem pev_of_quotient_zero (x r : Real) (h : (x - r) * 0 + 0 = 0) : True := trivial

/-- **A coefficient list vanishes identically, or its roots fit in a finite list.**

The global counterpart of `pev_dichotomy`. Proved by induction on a length budget: either the list
has no root at all (the empty list of roots works, vacuously), or it has one, and dividing by
`(x − r)` produces a strictly shorter list to which the budget applies. If that quotient vanishes
identically so does the original; otherwise its root list, extended by `r`, contains every root.

`Classical.em` is used to ask whether a root exists — a genuinely undecidable question — and adds
nothing to the footprint, which already carries `Classical.choice` through the real substrate. -/
theorem pev_zero_or_root_list : ∀ (n : Nat) (L : List Real), L.length ≤ n →
    (∀ x : Real, pev L x = 0) ∨ ∃ R : List Real, ∀ x : Real, pev L x = 0 → x ∈ R := by
  intro n
  induction n with
  | zero =>
      intro L hL
      cases L with
      | nil => exact Or.inl (fun _ => rfl)
      | cons c cs => exact absurd hL (Nat.not_succ_le_zero cs.length)
  | succ n ih =>
      intro L hL
      cases L with
      | nil => exact Or.inl (fun _ => rfl)
      | cons c cs =>
          rcases Classical.em (∃ r : Real, pev (c :: cs) r = 0) with hyes | hno
          · obtain ⟨r, hr⟩ := hyes
            have hlen : (deflate r (c :: cs)).length ≤ n := by
              rw [deflate_length cs r c]
              exact Nat.le_of_succ_le_succ hL
            rcases ih (deflate r (c :: cs)) hlen with hz | ⟨R, hR⟩
            · refine Or.inl (fun x => ?_)
              have h := pev_deflate (c :: cs) r x
              rw [hz x, hr] at h
              rw [h]
              exact deflate_zero_step x r
            · refine Or.inr ⟨r :: R, fun x hx => ?_⟩
              have h := pev_deflate (c :: cs) r x
              rw [hr, hx] at h
              have hmul : (x - r) * pev (deflate r (c :: cs)) x = 0 :=
                (factor_zero x r (pev (deflate r (c :: cs)) x) h.symm)
              rcases Classical.em (x = r) with hxr | hxr
              · rw [hxr]; exact List.mem_cons_self
              · refine List.mem_cons_of_mem r (hR x ?_)
                rcases Classical.em (pev (deflate r (c :: cs)) x = 0) with hd | hd
                · exact hd
                · exact absurd hmul (mul_ne_zero (QuadraticRoots.sub_ne_zero_of_ne hxr) hd)
          · exact Or.inr ⟨[], fun x hx => absurd ⟨x, hx⟩ hno⟩

/-- The budget-free form: every coefficient list is identically zero or has finitely many roots. -/
theorem pev_zero_or_finite_roots (L : List Real) :
    (∀ x : Real, pev L x = 0) ∨ ∃ R : List Real, ∀ x : Real, pev L x = 0 → x ∈ R :=
  pev_zero_or_root_list L.length L (Nat.le_refl _)

end MachLib
