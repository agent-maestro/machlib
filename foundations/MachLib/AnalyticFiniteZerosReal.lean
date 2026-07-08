import MachLib.AnalyticFiniteZeros
import MachLib.FieldLemmas
import MachLib.Linarith

/-!
# Real analytic-finiteness infrastructure

Constructive helpers built on top of `MachLib.AnalyticFiniteZeros`'s
NON-VACUOUS `RealSetFinite` (bounded-cardinality) predicate and the
`analytic_finite_zeros_compact` axiom. These are the prerequisites the
"full theorem" turned out to need once the earlier `∀ x, s x → True`
placeholder was replaced by a genuine finiteness statement.

1. `exists_between` — any nonempty open interval `(a, b)` contains its
   midpoint `a + (b − a)/2`, strictly between the endpoints.
2. `interval_has_distinct_points` — `(a, b)` contains a `Nodup` list of
   `n` distinct interior points for every `n` (midpoint recursion).
   Concretely: **a nonempty open interval is infinite.**
3. `analytic_zero_on_subinterval_imp_zero` — the **identity theorem**
   (finite-zeros form): if `f` is analytic on `[a, b]` and vanishes on a
   nonempty open sub-interval `(a', b') ⊆ [a, b]`, then `f ≡ 0` on all of
   `(a, b)`. Proof: a nonzero point would force the zero set to be finite
   with some cardinality bound `n` (`analytic_finite_zeros_compact`), but
   `(a', b')` already supplies `n + 1` distinct zeros — contradiction.

These use only the honest analytic axioms (the `rolle`-analog
`analytic_finite_zeros_compact` plus the analytic-closure axioms), NOT the
retired `zero_count_bound_classical`. No Mathlib. No sorryAx.

This is the qualitative tool used to discharge the log-descent `g ≡ 0`
leaf: when the Wronskian vanishes identically, the barrier `q = k·c_D`
piecewise; ruling out the degenerate `k = 0` piece (`q ≡ 0` on a
sub-interval) is exactly this identity theorem applied to the concrete
(analytic) EML barrier. The *uniform* zero count still comes from the
constructive `rolle`-based descent; this axiom only kills the
non-`rolle`-derivable degenerate branch.
-/

namespace MachLib

open MachLib.Real

/-- Division by `1 + 1` is strictly monotone. -/
private theorem div_two_lt_div_two {x y : Real} (h : x < y) :
    x / (1 + 1) < y / (1 + 1) := by
  rw [div_def x (1 + 1) two_ne_zero, div_def y (1 + 1) two_ne_zero]
  exact mul_lt_mul_of_pos_right h (one_div_pos_of_pos two_pos)

/-- Any nonempty open interval `(a, b)` contains its midpoint
`(a + b)/2`, which lies strictly between the endpoints. Using `(a+b)/2`
(rather than `a + (b−a)/2`) keeps the numerator free of `b − a`, so no
rewrite ever self-references `b`. -/
theorem exists_between (a b : Real) (hab : a < b) :
    ∃ m : Real, a < m ∧ m < b := by
  refine ⟨(a + b) / (1 + 1), ?_, ?_⟩
  · -- a = (a+a)/2 < (a+b)/2
    have haa : (a + a) / (1 + 1) = a := by
      rw [show a + a = (1 + 1) * a from by mach_mpoly [a]]
      exact mul_div_cancel_left' two_ne_zero
    have step := div_two_lt_div_two (add_lt_add_left hab a)  -- (a+a)/2 < (a+b)/2
    rwa [haa] at step
  · -- (a+b)/2 < (b+b)/2 = b
    have hbb : (b + b) / (1 + 1) = b := by
      rw [show b + b = (1 + 1) * b from by mach_mpoly [b]]
      exact mul_div_cancel_left' two_ne_zero
    have hcomm : a + b < b + b := by
      have := add_lt_add_left hab b            -- b + a < b + b
      rwa [show b + a = a + b from by mach_mpoly [a, b]] at this
    have step := div_two_lt_div_two hcomm       -- (a+b)/2 < (b+b)/2
    rwa [hbb] at step

/-- A nonempty open interval `(a, b)` contains, for every `n`, a `Nodup`
list of `n` distinct interior points. Built by midpoint recursion:
`n + 1` points = the midpoint `m` (which exceeds every point of a list
built inside `(a, m)`) prepended to `n` points of `(a, m)`. -/
theorem interval_has_distinct_points :
    ∀ (n : Nat) (a b : Real), a < b →
      ∃ l : List Real, l.Nodup ∧ l.length = n ∧ ∀ x ∈ l, Ioo a b x := by
  intro n
  induction n with
  | zero =>
    intro a b _hab
    exact ⟨[], List.nodup_nil, rfl, by intro x hx; exact absurd hx (List.not_mem_nil x)⟩
  | succ k ih =>
    intro a b hab
    obtain ⟨m, ham, hmb⟩ := exists_between a b hab
    obtain ⟨l', hnd', hlen', hmem'⟩ := ih a m ham
    refine ⟨m :: l', ?_, ?_, ?_⟩
    · -- Nodup (m :: l'): m ∉ l' because every element of l' is < m
      rw [List.nodup_cons]
      refine ⟨?_, hnd'⟩
      intro hmemm
      exact absurd (hmem' m hmemm).2 (lt_irrefl_ax m)
    · -- length (m :: l') = k + 1
      rw [List.length_cons, hlen']
    · -- membership: m ∈ (a,b); every x ∈ l' is in (a,m) ⊆ (a,b)
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact ⟨ham, hmb⟩
      · have hxam : Ioo a m x := hmem' x hx'
        exact ⟨hxam.1, lt_of_lt_of_le hxam.2 (le_of_lt hmb)⟩

/-- **Identity theorem (finite-zeros form).** If `f` is analytic on
`[a, b]` and vanishes on a nonempty open sub-interval `(a', b') ⊆ [a, b]`,
then `f ≡ 0` on all of `(a, b)`.

Proof: suppose some `x₀ ∈ (a, b)` had `f x₀ ≠ 0`. Then
`analytic_finite_zeros_compact` bounds the zero set's cardinality by some
`n`. But `interval_has_distinct_points` supplies `n + 1` distinct points
of `(a', b')`, each a zero of `f` inside `[a, b]` — a `Nodup` list of
length `n + 1 > n`, contradicting the bound. -/
theorem analytic_zero_on_subinterval_imp_zero
    (f : Real → Real) (a b a' b' : Real)
    (haa' : a ≤ a') (hb'b : b' ≤ b) (hab' : a' < b') (hab : a < b)
    (hanalytic : IsAnalyticOnReals f (Icc a b))
    (hzero : ∀ x, Ioo a' b' x → f x = 0) :
    ∀ x, Ioo a b x → f x = 0 := by
  intro x0 hx0
  refine Classical.byContradiction (fun hfx0 => ?_)
  have hne : ∃ x : Real, Ioo a b x ∧ f x ≠ 0 := ⟨x0, hx0, hfx0⟩
  obtain ⟨n, hn⟩ := analytic_finite_zeros_compact f a b hab hanalytic hne
  obtain ⟨l, hnd, hlen, hmem⟩ := interval_has_distinct_points (n + 1) a' b' hab'
  have hall : ∀ y ∈ l, Icc a b y ∧ f y = 0 := by
    intro y hy
    have hyab' : Ioo a' b' y := hmem y hy
    exact ⟨⟨le_trans haa' (le_of_lt hyab'.1), le_trans (le_of_lt hyab'.2) hb'b⟩,
           hzero y hyab'⟩
  have hbound := hn l hnd hall
  rw [hlen] at hbound
  exact absurd hbound (Nat.not_succ_le_self n)

/-- **Bounded-zeros adapter.** Repackages `analytic_finite_zeros_compact`
(a `RealSetFinite` bound on the *closed* interval `[a, b]`) into the exact
`∃ M, ∀ Nodup zeros in the OPEN interval (a, b), length ≤ M` shape used by
the Pfaffian descent's `BoundedZeros` / `hDegen` obligation.

This is the direct concrete discharge for an analytic barrier: an EML
function `f`, analytic on `[a, b] ⊆ (0, ∞)` and not identically zero, has
its open-interval zero list bounded by the same cardinality `n`. (The
bound is *non-uniform* in `f` and the interval — the uniform-in-depth
count still comes from the constructive `rolle` descent; this adapter only
handles a leaf where the descent itself cannot proceed.) -/
theorem analytic_open_interval_bounded_zeros
    (f : Real → Real) (a b : Real) (hab : a < b)
    (hanalytic : IsAnalyticOnReals f (Icc a b))
    (hne : ∃ x : Real, Ioo a b x ∧ f x ≠ 0) :
    ∃ M : Nat, ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ f z = 0) → zeros.length ≤ M := by
  obtain ⟨n, hn⟩ := analytic_finite_zeros_compact f a b hab hanalytic hne
  refine ⟨n, fun zeros hnd hz => hn zeros hnd (fun z hzmem => ?_)⟩
  obtain ⟨hza, hzb, hzf⟩ := hz z hzmem
  exact ⟨⟨le_of_lt hza, le_of_lt hzb⟩, hzf⟩

end MachLib
