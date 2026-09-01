/-
# A polynomial identity that holds on an interval holds

`no_rational_logarithm` takes ten hypotheses and **not one of them is eventual**: every one is a
polynomial identity (`PEq`, `Pdvd`, `PNormal`), and `logRat_cross_identity` is pointwise field
algebra with no quantifier at all. So the entire log-junction apparatus is already interval-local.
The one place a tail ever entered was the final lift from "the relation holds" to `PEq`, and the
corpus's only lift, `pnorm_eq_nil_of_evZero`, is stated for a **tail**.

This module supplies the interval twin, which is the exact bridge between the junction machinery and
an interval-local hypothesis.

## Why there is no pigeonhole here

The obvious route is: a finite root list cannot cover an infinite interval, so bound a nodup list of
roots by the list's length. That needs `DecidableEq Real` for `List.erase` and a counting argument
this corpus does not carry — `exact?` finds nothing in core either.

None of it is necessary. `exists_ge_notMem` escapes a finite list by going *above* its upper bound;
a bounded interval forbids that move, so escape **inward** instead. If `r` lies inside `(a,b)`, the
induction runs on the strictly smaller `(r,b)`, and every point of it exceeds `r` — so `y ≠ r` comes
for free from the order, with no counting anywhere.
-/
import MachLib.PolyEvZero
import MachLib.AnalyticFiniteZerosReal
import MachLib.BipevCoeffIdentity


namespace MachLib

/-- **A finite list cannot exhaust an interval.** The interval twin of `exists_ge_notMem`.

The tail version escapes *upward*, past the list's own upper bound. That move is unavailable inside a
bounded interval, and the obvious repair — pigeonhole on a nodup list — needs `DecidableEq Real` and
a counting argument this corpus does not carry. Neither is necessary: escape *inward* instead. If `r`
lies inside `(a,b)` the induction hypothesis runs on the strictly smaller `(r,b)`, and every point
there exceeds `r`, so it differs from `r` for free. -/
theorem exists_in_interval_notMem : ∀ (R : List Real) (a b : Real), a < b →
    ∃ y : Real, a < y ∧ y < b ∧ y ∉ R := by
  intro R
  induction R with
  | nil =>
      intro a b hab
      obtain ⟨m, h1, h2⟩ := exists_between a b hab
      exact ⟨m, h1, h2, by simp⟩
  | cons r rs ih =>
      intro a b hab
      by_cases hin : a < r ∧ r < b
      · obtain ⟨y, h1, h2, h3⟩ := ih r b hin.2
        refine ⟨y, Real.lt_trans_ax hin.1 h1, h2, ?_⟩
        intro hmem
        rcases List.mem_cons.mp hmem with he | ht
        · exact absurd he.symm (Real.ne_of_lt h1)
        · exact h3 ht
      · obtain ⟨y, h1, h2, h3⟩ := ih a b hab
        refine ⟨y, h1, h2, ?_⟩
        intro hmem
        rcases List.mem_cons.mp hmem with he | ht
        · subst he
          exact hin ⟨h1, h2⟩
        · exact h3 ht

/-- **A polynomial vanishing on a non-empty open interval is the zero polynomial.**

The interval twin of `pnorm_eq_nil_of_evZero`, and the same three lines: split on
`pev_zero_or_finite_roots`, then find a point the finite root list misses. It is what makes the whole
log-junction apparatus usable from a LOCAL hypothesis — `no_rational_logarithm` carries no tail and
no growth premise, and `logRat_cross_identity` is pointwise, so this lift was the only place a tail
ever entered. -/
theorem pnorm_nil_of_zero_on_interval {P : List Real} {a b : Real} (hab : a < b)
    (h : ∀ x : Real, a < x → x < b → pev P x = 0) : pnorm P = [] := by
  rcases pev_zero_or_finite_roots P with hall | ⟨R, hR⟩
  · exact pnorm_eq_nil_of_all_zero P hall
  · exfalso
    obtain ⟨y, h1, h2, h3⟩ := exists_in_interval_notMem R a b hab
    exact h3 (hR y (h y h1 h2))

/-- Two polynomials agreeing on an interval are `PEq`. The consumer-facing form. -/
theorem peq_of_eq_on_interval {A B : List Real} {a b : Real} (hab : a < b)
    (h : ∀ x : Real, a < x → x < b → pev A x = pev B x) : PEq A B := by
  refine peq_of_psub_nil ?_
  refine pnorm_nil_of_zero_on_interval (a := a) (b := b) hab ?_
  intro x h1 h2
  rw [pev_psub]
  rw [h x h1 h2]
  mach_ring

end MachLib
