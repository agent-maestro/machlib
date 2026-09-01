/-
# The witness the hypothesis gate asked for, and the descent's base case

`(gi)` pinned `GIntervalProperRel` as *consumed by `exists_minimal_gIntervalRel`, concluded by
nothing*, with a stated exit condition: the pin comes off when something produces one. It comes off
here, in the same session it went on.

## Read the witness for exactly what it is

`gIntervalProperRel_inhabited` witnesses the **predicate**. It says nothing about whether
`Fbasis ∘ S` carries a proper interval relation — which is the thing this arc exists to *refute*.
Same standing as `pIrred_X`: inhabitance, not applicability. A trivial witness presented as more
would be gaming the gate rather than answering it.

## The base case is a real fact

`no_length_one_gIntervalProperRel` is not plumbing. `gbipev [c] x y = c x` does not mention `y` at
all, so the relation forces `c` to vanish on the interval and contradicts properness outright. That
is where the descent terminates: it can shorten a relation, and length 1 is impossible, so a minimal
proper relation of length ≥ 2 that descends to length 1 is the contradiction the route is aiming at.
-/
import MachLib.GermIntervalMinimal
import MachLib.AnalyticFiniteZerosReal

namespace MachLib

open Real

/-- **`GIntervalProperRel` is inhabited.**

The hypothesis audit flagged it as *consumed by `exists_minimal_gIntervalRel`, concluded by nothing* —
a predicate nothing produces makes every theorem over it vacuously safe.

**Read this for exactly what it is.** It witnesses the PREDICATE, not the arc: it says nothing about
whether `Fbasis ∘ S` carries a proper interval relation, which is the thing this arc exists to
*refute*. Same standing as `pIrred_X` — inhabitance, not applicability.

`gbipev [c₀, c₁] x y = c₀ x + y·c₁ x`, so `u ≡ 0` with `c₀ ≡ 0` satisfies the relation for any `c₁`,
and `c₁ ≡ 1` is not identically zero on a non-empty interval — for which a point is needed, hence
`exists_between`. -/
theorem gIntervalProperRel_inhabited {a b : Real} (hab : a < b) :
    GIntervalProperRel (fun _ => (0 : Real))
      [(fun _ => (0 : Real)), (fun _ => (1 : Real))] a b := by
  refine ⟨?_, [(fun _ => (0 : Real))], (fun _ => (1 : Real)), rfl, ?_⟩
  · intro x _ _
    show (0 : Real) + (0 : Real) * ((1 : Real) + (0 : Real) * 0) = 0
    mach_ring
  · intro hz
    obtain ⟨m, h1, h2⟩ := exists_between a b hab
    exact Real.one_ne_zero (hz m h1 h2)

/-- **A length-1 proper relation is impossible** — the descent's base case, and the reason the
inhabitance witness above has length 2. `gbipev [c] x y = c x`, so the relation forces `c` to vanish
on the interval, contradicting properness directly. -/
theorem no_length_one_gIntervalProperRel {u : Real → Real} {c : Real → Real} {a b : Real}
    (h : GIntervalProperRel u [c] a b) : False := by
  obtain ⟨hrel, cs₀, d, hsplit, hnz⟩ := h
  have hdc : d = c := by
    cases cs₀ with
    | nil => exact ((by simpa using hsplit : c = d)).symm
    | cons h t =>
        exfalso
        have hl := congrArg List.length hsplit
        simp at hl
  refine hnz ?_
  intro x hax hxb
  have hb : c x + u x * 0 = 0 := hrel x hax hxb
  have e : c x + u x * 0 = c x := by mach_ring
  rw [e] at hb
  rw [hdc]
  exact hb

end MachLib
