import MachLib.ClassMinimality
import MachLib.BipevGerm

/-!
# The clearing invariant, and the WLOG it buys

`ClassMinimality` reduced the fourth module to *supply a class, prove it closed under `dropLast` and
under the `gscaleSub` step, and exhibit one proper relation in it*, and named the obstruction:
`minimal_expRel_identity_in` wants its relation to be an `expCoeffs` image, and the minimal member of
a class need not be one.

This module supplies the class and removes that obstruction. The class is

```
ClearsToExp S fs  :=  ∃ D Cs, EvNonvanish D ∧ GEvEq (gscale D fs) (expCoeffs S Cs)
```

— *one* common denominator `D` clears the *whole* coefficient vector to an `expCoeffs` image.

## Why the denominator is needed at all, and why one is enough

`expCoeffs`-ness alone is not closed under the descent. The differentiated relation's coefficients
are `dbipevExp` values, which carry `S'`, and the `S > 0` branch runs at `S = P/Q`, so `S'` is
rational and not a `bipev`. Clearing by a power of `Q` restores `bipev` shape — and because
`gscaleSub` forms products and differences, denominators multiply rather than proliferate, so a
single `D` survives the step. That is the whole reason the invariant is stated with one `D` outside
the list rather than one per entry: per-entry denominators do not survive the later
leading-coefficient reasoning, because `gcancel_top` compares entries against each other.

## `EvNonvanish`, not `¬ EvZeroF`

The denominator must be **non-zero on a tail**, which is strictly stronger than *not eventually
zero*. Germs here are arbitrary `Real → Real` and therefore have zero divisors: two germs neither of
which is eventually zero can have an eventually-zero product, by being supported on interleaved
tails. `GProperRel`'s second clause is `¬ EvZeroF` of the top coefficient, so under the weaker
reading clearing could destroy properness and every leading-coefficient fact with it.

Nothing is lost by asking for the stronger form: the denominators that actually arise are `pev`s of
polynomials, and `pev_dichotomy` says a polynomial is either eventually zero or `EvDom`, the latter
giving non-vanishing on a tail. `evNonvanish_pev` is that step.

## What the WLOG is

`exists_expCoeffs_of_clears` is the point of the module. If `fs` is a proper relation in the class
then `gscale D fs` **is** an `expCoeffs` image, has the **same length**, is still a relation
(`gbipev (gscale D fs) = D · gbipev fs`), and — this is where `EvNonvanish` is spent — is still
proper. Same length means it is still minimal among class members. So a minimal class member can be
*replaced* by an `expCoeffs` image without weakening anything, and
`minimal_expRel_identity_in` gets the shape it asks for.

The obstruction was a scaling lemma, not a new argument.

## The bootstrap, recorded because it is easy to miss

`MinimalityScope.gProperRel_witness` exhibits `[−u, 1]` — a proper relation of length two for *any*
germ — and that is what caps the unrestricted arc at `m = 0`. A restricted `hmin` is only worth
anything if the class excludes it, and `clears_witness_forces_algebraic` says exactly what excluding
it costs: `[−u, 1] ∈ ClearsToExp S` forces `D·u` to be a `bipev` in `e^S`, i.e. `u ∈ R(x)(e^S)`.
For `u = log ∘ S` that is what the **already-closed degree-one theorem refutes**. The `m = 0`
collapse is not an obstacle this class routes around; the degree-one result is what lifts it.
-/

namespace MachLib

open Real

/-! ## Eventual non-vanishing -/

/-- Non-zero on a tail. Strictly stronger than `¬ EvZeroF`, and the gap is load-bearing — see the
module docstring. -/
def EvNonvanish (D : Real → Real) : Prop :=
  ∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x → D x ≠ 0

/-- `EvDom` bounds `|f|` below by `c·xᵏ` with `c > 0`, which on a tail is positive. -/
theorem evNonvanish_of_evDom {f : Real → Real} (h : EvDom f) : EvNonvanish f := by
  obtain ⟨c, k, X, hc, hX, hb⟩ := h
  refine ⟨X, hX, fun x hx hz => ?_⟩
  have hx0 : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax (le_trans hX hx)
  have hp : 0 < c * powNat x k := mul_pos hc (powNat_pos hx0 k)
  have hle : c * powNat x k ≤ abs (f x) := hb x hx
  rw [hz, abs_zero] at hle
  exact (ne_of_lt (lt_of_lt_of_le hp hle)) rfl

/-- **The denominators that arise are fine.** A polynomial that is not eventually zero is eventually
non-vanishing — `pev_dichotomy` has no third case. -/
theorem evNonvanish_pev {L : List Real} (h : ¬ EvZeroF (pev L)) : EvNonvanish (pev L) := by
  rcases pev_dichotomy L with hz | hd
  · exact absurd hz h
  · exact evNonvanish_of_evDom hd

/-- **Clearing cannot create eventual vanishing.** This is the one place `EvNonvanish` is spent, and
it is false for the weaker `¬ EvZeroF` reading. -/
theorem not_evZeroF_mul {D c : Real → Real} (hD : EvNonvanish D) (hc : ¬ EvZeroF c) :
    ¬ EvZeroF (fun x => D x * c x) := by
  intro hz
  obtain ⟨X₁, hX₁, hD'⟩ := hD
  obtain ⟨X₂, hX₂, hz'⟩ := hz
  obtain ⟨X, hX, hle1, hle2⟩ := two_bounds' hX₁ hX₂
  refine hc ⟨X, hX, fun x hx => ?_⟩
  rcases Classical.em (c x = 0) with h | h
  · exact h
  · exact absurd (hz' x (le_trans hle2 hx)) (mul_ne_zero (hD' x (le_trans hle1 hx)) h)

/-! ## Entrywise eventual equality of coefficient lists

Every predicate the descent cares about — `GEvRel`, `GProperRel`, lengths — is invariant under
changing each coefficient on a bounded set. `GEvEq` is that relation, in `GDerivAt`'s shape so the
same `cases` idiom applies. -/

/-- Two coefficient lists agreeing entrywise on a tail. -/
def GEvEq : List (Real → Real) → List (Real → Real) → Prop
  | [],      []      => True
  | c :: cs, d :: ds => EvEqF c d ∧ GEvEq cs ds
  | _,       _       => False

theorem gEvEq_length : ∀ cs ds : List (Real → Real), GEvEq cs ds → cs.length = ds.length := by
  intro cs
  induction cs with
  | nil =>
      intro ds h
      cases ds with
      | nil => rfl
      | cons _ _ => exact absurd h (by intro hh; cases hh)
  | cons c cs ih =>
      intro ds h
      cases ds with
      | nil => exact absurd h (by intro hh; cases hh)
      | cons d ds => exact congrArg (· + 1) (ih ds h.2)

/-- The evaluations agree on a common tail, uniformly in `y`. The induction is where the finitely
many per-entry bounds get merged. -/
theorem gbipev_evEq : ∀ cs ds : List (Real → Real), GEvEq cs ds →
    ∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x → ∀ y : Real, gbipev cs x y = gbipev ds x y := by
  intro cs
  induction cs with
  | nil =>
      intro ds h
      cases ds with
      | nil => exact ⟨1, le_refl 1, fun _ _ _ => rfl⟩
      | cons _ _ => exact absurd h (by intro hh; cases hh)
  | cons c cs ih =>
      intro ds h
      cases ds with
      | nil => exact absurd h (by intro hh; cases hh)
      | cons d ds =>
          obtain ⟨X₁, hX₁, h₁⟩ := h.1
          obtain ⟨X₂, hX₂, h₂⟩ := ih ds h.2
          obtain ⟨X, hX, hle1, hle2⟩ := two_bounds' hX₁ hX₂
          refine ⟨X, hX, fun x hx y => ?_⟩
          show c x + y * gbipev cs x y = d x + y * gbipev ds x y
          rw [h₁ x (le_trans hle1 hx), h₂ x (le_trans hle2 hx) y]

theorem gEvRel_congr_gEvEq {u : Real → Real} {cs ds : List (Real → Real)}
    (he : GEvEq cs ds) (h : GEvRel u cs) : GEvRel u ds := by
  obtain ⟨X₁, hX₁, h₁⟩ := h
  obtain ⟨X₂, hX₂, h₂⟩ := gbipev_evEq cs ds he
  obtain ⟨X, hX, hle1, hle2⟩ := two_bounds' hX₁ hX₂
  refine ⟨X, hX, fun x hx => ?_⟩
  rw [← h₂ x (le_trans hle2 hx) (u x)]
  exact h₁ x (le_trans hle1 hx)

/-- `GEvEq` respects the split at the top, which is how properness transfers. -/
theorem gEvEq_concat_right : ∀ (cs₀ : List (Real → Real)) (c : Real → Real)
    (ds : List (Real → Real)), GEvEq (cs₀ ++ [c]) ds →
      ∃ (ds₀ : List (Real → Real)) (d : Real → Real),
        ds = ds₀ ++ [d] ∧ GEvEq cs₀ ds₀ ∧ EvEqF c d := by
  intro cs₀
  induction cs₀ with
  | nil =>
      intro c ds h
      cases ds with
      | nil => exact absurd h (by intro hh; cases hh)
      | cons d ds =>
          cases ds with
          | nil => exact ⟨[], d, rfl, trivial, h.1⟩
          | cons _ _ => exact absurd h.2 (by intro hh; cases hh)
  | cons a as ih =>
      intro c ds h
      cases ds with
      | nil => exact absurd h (by intro hh; cases hh)
      | cons d ds =>
          obtain ⟨ds₀, dl, hds, hEq, hc⟩ := ih c ds h.2
          exact ⟨d :: ds₀, dl, by rw [hds]; rfl, ⟨h.1, hEq⟩, hc⟩

theorem evZeroF_congr_evEqF {c d : Real → Real} (he : EvEqF c d) (h : EvZeroF d) : EvZeroF c := by
  obtain ⟨X₁, hX₁, h₁⟩ := he
  obtain ⟨X₂, hX₂, h₂⟩ := h
  obtain ⟨X, hX, hle1, hle2⟩ := two_bounds' hX₁ hX₂
  exact ⟨X, hX, fun x hx => by rw [h₁ x (le_trans hle1 hx)]; exact h₂ x (le_trans hle2 hx)⟩

theorem gProperRel_congr_gEvEq {u : Real → Real} {cs ds : List (Real → Real)}
    (he : GEvEq cs ds) (h : GProperRel u cs) : GProperRel u ds := by
  obtain ⟨hrel, cs₀, c, hsplit, hcz⟩ := h
  refine ⟨gEvRel_congr_gEvEq he hrel, ?_⟩
  rw [hsplit] at he
  obtain ⟨ds₀, d, hds, _, hcd⟩ := gEvEq_concat_right cs₀ c ds he
  exact ⟨ds₀, d, hds, fun hdz => hcz (evZeroF_congr_evEqF hcd hdz)⟩

/-! ## Scaling a relation -/

theorem gscale_concat (a : Real → Real) : ∀ (cs : List (Real → Real)) (c : Real → Real),
    gscale a (cs ++ [c]) = gscale a cs ++ [fun x => a x * c x] := by
  intro cs
  induction cs with
  | nil => intro c; rfl
  | cons e es ih =>
      intro c
      show (fun x => a x * e x) :: gscale a (es ++ [c])
          = (fun x => a x * e x) :: (gscale a es ++ [fun x => a x * c x])
      rw [ih c]

theorem gEvRel_gscale {u : Real → Real} {cs : List (Real → Real)} (D : Real → Real)
    (h : GEvRel u cs) : GEvRel u (gscale D cs) := by
  obtain ⟨X, hX, h'⟩ := h
  refine ⟨X, hX, fun x hx => ?_⟩
  rw [gbipev_gscale D cs x (u x), h' x hx]
  mach_ring

/-- **Scaling by a non-vanishing germ preserves properness.** The step the WLOG turns on. -/
theorem gProperRel_gscale {u : Real → Real} {cs : List (Real → Real)} {D : Real → Real}
    (hD : EvNonvanish D) (h : GProperRel u cs) : GProperRel u (gscale D cs) := by
  obtain ⟨hrel, cs₀, c, hsplit, hcz⟩ := h
  refine ⟨gEvRel_gscale D hrel, gscale D cs₀, (fun x => D x * c x), ?_, not_evZeroF_mul hD hcz⟩
  rw [hsplit, gscale_concat D cs₀ c]

/-! ## The class -/

/-- **The admissible class.** `fs` clears, over *one* common eventually non-vanishing denominator,
to an `expCoeffs` image. -/
def ClearsToExp (S : Real → Real) (fs : List (Real → Real)) : Prop :=
  ∃ (D : Real → Real) (Cs : List (List (List Real))),
    EvNonvanish D ∧ GEvEq (gscale D fs) (expCoeffs S Cs)

theorem gEvEq_gscale_one : ∀ cs : List (Real → Real), GEvEq (gscale (fun _ => 1) cs) cs := by
  intro cs
  induction cs with
  | nil => trivial
  | cons c cs ih =>
      refine ⟨⟨1, le_refl 1, fun x _ => ?_⟩, ih⟩
      show (1 : Real) * c x = c x
      mach_ring

/-- **The witness.** Every `expCoeffs` image is in the class, with `D = 1` — this is what
`exists_minimal_hmin` needs, and it costs nothing. -/
theorem clearsToExp_expCoeffs (S : Real → Real) (Cs : List (List (List Real))) :
    ClearsToExp S (expCoeffs S Cs) :=
  ⟨fun _ => 1, Cs, ⟨1, le_refl 1, fun _ _ h => zero_ne_one_ax h.symm⟩,
    gEvEq_gscale_one (expCoeffs S Cs)⟩

private theorem expCoeffs_split {S : Real → Real} {Cs : List (List (List Real))}
    {ds₀ : List (Real → Real)} {d : Real → Real} (h : expCoeffs S Cs = ds₀ ++ [d]) :
    ∃ Cs₀ : List (List (List Real)), ds₀ = expCoeffs S Cs₀ := by
  have hne : Cs ≠ [] := by
    intro hz
    rw [hz] at h
    simp [expCoeffs] at h
  refine ⟨Cs.dropLast, ?_⟩
  have hsplit : Cs = Cs.dropLast ++ [Cs.getLast hne] := (List.dropLast_concat_getLast hne).symm
  rw [hsplit, expCoeffs_concat] at h
  have hd : (expCoeffs S Cs.dropLast
      ++ [fun x => bipev (Cs.getLast hne) x (exp (S x))]).dropLast = (ds₀ ++ [d]).dropLast := by
    rw [h]
  rw [List.dropLast_concat, List.dropLast_concat] at hd
  exact hd.symm

/-- **The `hdrop` obligation.** The class is closed under dropping the top coefficient — same
denominator, one fewer numerator. -/
theorem clearsToExp_dropLast {S : Real → Real} {fs : List (Real → Real)} {c : Real → Real}
    (h : ClearsToExp S (fs ++ [c])) : ClearsToExp S fs := by
  obtain ⟨D, Cs, hD, he⟩ := h
  rw [gscale_concat D fs c] at he
  obtain ⟨ds₀, d, hds, hEq, _⟩ :=
    gEvEq_concat_right (gscale D fs) (fun x => D x * c x) (expCoeffs S Cs) he
  obtain ⟨Cs₀, hCs₀⟩ := expCoeffs_split hds
  exact ⟨D, Cs₀, hD, hCs₀ ▸ hEq⟩

/-! ## The WLOG -/

/-- **A proper member of the class may be replaced by an `expCoeffs` image of the same length.**

This is what `ClassMinimality` called the genuinely hard direction. It is a scaling lemma: `gscale D`
carries `fs` *into* the `expCoeffs` images, preserves the relation, preserves properness because `D`
is non-vanishing, and preserves length — so a member minimal among class members stays minimal. -/
theorem exists_expCoeffs_of_clears {S u : Real → Real} {fs : List (Real → Real)}
    (hcl : ClearsToExp S fs) (hprop : GProperRel u fs) :
    ∃ Cs : List (List (List Real)),
      GProperRel u (expCoeffs S Cs) ∧ (expCoeffs S Cs).length = fs.length := by
  obtain ⟨D, Cs, hD, he⟩ := hcl
  refine ⟨Cs, gProperRel_congr_gEvEq he (gProperRel_gscale hD hprop), ?_⟩
  rw [← gEvEq_length _ _ he, gscale_length]

/-! ## The bootstrap

Why the restricted `hmin` is not vacuous. -/

/-- **What excluding the trivial witness costs.** `MinimalityScope.gProperRel_witness` puts
`[−u, 1]` in reach of every germ; if it were in the class, `hmin` would again force length two. It is
in the class exactly when `u` is a `bipev` in `e^S` over a non-vanishing denominator — which for
`u = log ∘ S` is what `positive_branch_impossible` already refutes. -/
theorem clears_witness_forces_algebraic {S u : Real → Real}
    (h : ClearsToExp S [fun x => 0 - u x, fun _ => 1]) :
    ∃ (D : Real → Real) (C : List (List Real)),
      EvNonvanish D ∧ EvEqF (fun x => D x * (0 - u x)) (fun x => bipev C x (exp (S x))) := by
  obtain ⟨D, Cs, hD, he⟩ := h
  cases Cs with
  | nil => exact absurd he (by intro hh; cases hh)
  | cons C Cs => exact ⟨D, C, hD, he.1⟩

end MachLib
