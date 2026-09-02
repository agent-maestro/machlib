/-
# The last four twins: `minimal_grel_identity`'s dependencies, on an interval

`(gj)` left `minimal_grel_identity` untwinned. Its three dependencies now have interval versions —
`gIntervalRel_gdrel` here, `all_gcoeffs_intervalZero_of_shorter'` in `(gi)`, and
`gIntervalRel_cancel_top` here — so that theorem is unblocked.

## Four twins, four times shorter, one reason

Every eventual lemma in this chain opens by merging tails — `three_tails` in `gEvRel_gdrel`,
`two_bounds'` in `gEvRel_gscaleSub` and `gevRel_dropLast`. On an interval every hypothesis already
lives on the same `(a,b)`, so the merge is not simplified, it is **absent**.

That is now four for four, and it is the same fact each time: *"eventually" is an existential over
thresholds that must be intersected; an interval is a fixed pair of endpoints.* The eventual form
pays for a generality this arc never wanted.

The one genuinely new piece is `hasDerivAt_of_agrees_on_interval` — the tail version escapes with a
one-sided `δ = x − X`, and a bounded interval needs a positive number below *both* distances, by
trichotomy.
-/
import MachLib.GermIntervalWitness
import MachLib.GermDeriv
import MachLib.BipevTail

namespace MachLib

open Real

private theorem pos_le_both {p q : Real} (hp : 0 < p) (hq : 0 < q) :
    ∃ d : Real, 0 < d ∧ d ≤ p ∧ d ≤ q := by
  rcases lt_total p q with h | h | h
  · exact ⟨p, hp, le_refl p, le_of_lt h⟩
  · exact ⟨p, hp, le_refl p, le_of_eq h⟩
  · exact ⟨q, hq, le_of_lt h, le_refl q⟩

/-- **The interval twin of `hasDerivAt_of_agrees_on_tail`.** Two-sided `δ`, by trichotomy. -/
theorem hasDerivAt_of_agrees_on_interval {f g : Real → Real} {a b x d : Real}
    (hax : a < x) (hxb : x < b) (hag : ∀ y : Real, a < y → y < b → f y = g y)
    (hf : HasDerivAt f d x) : HasDerivAt g d x := by
  obtain ⟨e, he, hea, heb⟩ := pos_le_both (sub_pos_of_lt hax) (sub_pos_of_lt hxb)
  refine HasDerivAt_congr f g d x ⟨e, he, fun y hy => hag y ?_ ?_⟩ hf
  · have hA : -(y - x) < e := lt_of_le_of_lt (neg_le_abs (y - x)) hy
    have hB : -(y - x) < x - a := lt_of_lt_of_le hA hea
    have hC := add_lt_add_left hB (y - x + a)
    have l : y - x + a + -(y - x) = a := by mach_mpoly [a, x, y]
    have r : y - x + a + (x - a) = y := by mach_mpoly [a, x, y]
    rw [l, r] at hC; exact hC
  · have hA : y - x < e := lt_of_le_of_lt (le_abs_self (y - x)) hy
    have hB : y - x < b - x := lt_of_lt_of_le hA heb
    have hC := add_lt_add_left hB x
    have l : x + (y - x) = y := by mach_mpoly [b, x, y]
    have r : x + (b - x) = b := by mach_mpoly [b, x, y]
    rw [l, r] at hC; exact hC

/-- **The derivative of an interval relation is an interval relation.**

The eventual proof opens with `three_tails`, merging the derivative hypothesis, the
`GDerivAt` hypothesis and the relation's own tail into one. On an interval **all three already live
on `(a,b)`**, so that step disappears entirely — the third time a twin has come out shorter than its
original for the same reason. -/
theorem gIntervalRel_gdrel {u v : Real → Real} {cs es : List (Real → Real)} {a b : Real}
    (hu : ∀ x : Real, a < x → x < b → HasDerivAt u (v x) x)
    (hd : ∀ x : Real, a < x → x < b → GDerivAt x cs es)
    (hrel : GIntervalRel u cs a b) : GIntervalRel u (gdrel v cs es) a b := by
  intro x hax hxb
  have hval := gbipev_hasDerivAt (hu x hax hxb) cs es (hd x hax hxb)
  have hzero : HasDerivAt (fun t => gbipev cs t (u t)) 0 x :=
    hasDerivAt_of_agrees_on_interval (f := fun _ => (0 : Real)) hax hxb
      (fun y hay hyb => (hrel y hay hyb).symm) (HasDerivAt_const 0 x)
  have h := HasDerivAt_unique (fun t => gbipev cs t (u t))
    (gbipev es x (u x) + v x * gydiff cs x (u x)) 0 x hval hzero
  rw [gbipev_gdrel v cs es x (u x)]
  exact h

/-- **Scaled difference of two interval relations.** The eventual proof merges two tails with
`two_bounds'`; here both relations already hold on `(a,b)`, so the merge disappears. Fourth twin in
this arc to come out shorter than its original, for the same reason every time. -/
theorem gIntervalRel_gscaleSub {u : Real → Real} {cs ds : List (Real → Real)}
    (a' b' : Real → Real) {a b : Real} (hlen : cs.length = ds.length)
    (hc : GIntervalRel u cs a b) (hd : GIntervalRel u ds a b) :
    GIntervalRel u (gscaleSub a' b' cs ds) a b := by
  intro x hax hxb
  rw [gbipev_gscaleSub a' b' cs ds x (u x) hlen, hc x hax hxb, hd x hax hxb]
  mach_ring

/-- **The degree drops on an interval, with no division.** Twin of `gcancel_top`: two relations of
equal length, combined against each other's top coefficients, give one that is shorter. -/
theorem gIntervalRel_cancel_top {u : Real → Real} {cs₀ ds₀ : List (Real → Real)}
    {c d : Real → Real} {a b : Real} (hlen : cs₀.length = ds₀.length)
    (hc : GIntervalRel u (cs₀ ++ [c]) a b) (hd : GIntervalRel u (ds₀ ++ [d]) a b) :
    GIntervalRel u (gscaleSub c d cs₀ ds₀) a b := by
  have hall : GIntervalRel u (gscaleSub c d (cs₀ ++ [c]) (ds₀ ++ [d])) a b :=
    gIntervalRel_gscaleSub c d (by simp [hlen]) hc hd
  rw [gscaleSub_concat c d c d cs₀ ds₀ hlen] at hall
  refine gIntervalRel_dropLast hall (fun x _ _ => ?_)
  show c x * d x - d x * c x = 0
  mach_ring

end MachLib
