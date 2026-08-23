import MachLib.BipevNonzeroCoeff

/-!
# Relations with germ coefficients

`EvRel` carries `List (List Real)` — coefficients that are *polynomials in `x`*, evaluated by `pev`.
The `S > 0` branch needs the same descent with coefficients in `R(x)(e^S)`, which are not polynomials
in `x`.

Reading the four descent proofs shows **none of them inspects `pev`**. They use a coefficient only
through "is / is not eventually zero" and through `bipev`'s cons step. So the whole layer restates
over an arbitrary germ coefficient, and the polynomial version is recovered by
`gbipev_map_pev : gbipev (Ls.map pev) = bipev Ls`.

## The monic problem, and why it is not one

Sizing this layer flagged one thing as a genuine design decision rather than a transcription: the
descent argument differentiates a relation and needs the top coefficient's derivative to vanish,
which classically means dividing by the leading coefficient — legitimate in a field, unavailable
here without carrying a nonvanishing witness with every germ.

**It is avoidable.** For a relation `R = Σ cⱼ Yʲ = 0` of degree `d`, the combination

```
c_d · R'  −  c_d' · R
```

has `Yᵈ` coefficient `c_d·c_d' − c_d'·c_d = 0` and vanishes wherever `R` and `R'` do. The degree
drops with no division anywhere, so germ coefficients need no nonvanishing witness and this layer is
pure transcription after all. `gcancel_top` below is that combination's shape lemma.

## What is deliberately *not* here

The inner variable `u` is arbitrary. Nothing in this module knows it is `exp ∘ S`, and nothing knows
about `q`, `pnorm` or divisibility. That is the same discipline as `BipevDescent`, which needed
neither properness nor minimality of the relation it descends.
-/

namespace MachLib

open Real

/-- `Σⱼ cⱼ(x)·yʲ` for germ coefficients — the same little-endian Horner shape as `bipev`. -/
noncomputable def gbipev : List (Real → Real) → Real → Real → Real
  | [],      _, _ => 0
  | c :: cs, x, y => c x + y * gbipev cs x y

/-- The relation `Σⱼ cⱼ(x)·u(x)ʲ = 0` holds on a tail. -/
def GEvRel (u : Real → Real) (cs : List (Real → Real)) : Prop :=
  ∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x → gbipev cs x (u x) = 0

/-- Genuinely of its stated degree: it holds, and its leading coefficient is not eventually zero. -/
def GProperRel (u : Real → Real) (cs : List (Real → Real)) : Prop :=
  GEvRel u cs ∧ ∃ (cs₀ : List (Real → Real)) (c : Real → Real),
    cs = cs₀ ++ [c] ∧ ¬ EvZeroF c

/-! ## The polynomial layer is the special case -/

/-- `gbipev` over `pev`-images is `bipev`. The bridge in the only direction needed: a polynomial
relation *is* a germ relation. -/
theorem gbipev_map_pev : ∀ (Ls : List (List Real)) (x y : Real),
    gbipev (Ls.map pev) x y = bipev Ls x y := by
  intro Ls
  induction Ls with
  | nil => intro x y; rfl
  | cons L Ls ih =>
      intro x y
      show pev L x + y * gbipev (Ls.map pev) x y = pev L x + y * bipev Ls x y
      rw [ih x y]

theorem gEvRel_of_evRel {S : Real → Real} {Ls : List (List Real)} (h : EvRel S Ls) :
    GEvRel (fun x => exp (S x)) (Ls.map pev) := by
  obtain ⟨X, hX, hr⟩ := h
  exact ⟨X, hX, fun x hx => by rw [gbipev_map_pev Ls x (exp (S x))]; exact hr x hx⟩

/-! ## Splitting at the top -/

theorem gbipev_concat : ∀ (cs : List (Real → Real)) (c : Real → Real) (x y : Real),
    gbipev (cs ++ [c]) x y = gbipev cs x y + powNat y cs.length * c x := by
  intro cs
  induction cs with
  | nil =>
      intro c x y
      show c x + y * 0 = 0 + powNat y 0 * c x
      show c x + y * 0 = 0 + 1 * c x
      mach_ring
  | cons a as ih =>
      intro c x y
      show a x + y * gbipev (as ++ [c]) x y
          = a x + y * gbipev as x y + (y * powNat y as.length) * c x
      rw [ih c x y]
      mach_ring

/-- **The top term is killed.** -/
theorem gbipev_drop_top {cs : List (Real → Real)} {c : Real → Real} {x y : Real}
    (hc : c x = 0) : gbipev (cs ++ [c]) x y = gbipev cs x y := by
  rw [gbipev_concat cs c x y, hc]
  mach_ring

/-- A relation whose final coefficient is eventually zero truncates to a relation. -/
theorem gevRel_dropLast {u : Real → Real} {cs₀ : List (Real → Real)} {c : Real → Real}
    (hrel : GEvRel u (cs₀ ++ [c])) (hc : EvZeroF c) : GEvRel u cs₀ := by
  obtain ⟨X₁, hX₁, h₁⟩ := hrel
  obtain ⟨X₂, hX₂, h₂⟩ := hc
  obtain ⟨X, hX, hle1, hle2⟩ := two_bounds' hX₁ hX₂
  refine ⟨X, hX, fun x hx => ?_⟩
  have hb := h₁ x (le_trans hle1 hx)
  rw [gbipev_drop_top (cs := cs₀) (h₂ x (le_trans hle2 hx))] at hb
  exact hb

/-! ## Minimality and the descent -/

/-- **A relation of minimal degree exists**, given any proper relation at all. -/
theorem exists_minimal_grel {u : Real → Real} {cs : List (Real → Real)} (h : GProperRel u cs) :
    ∃ ms : List (Real → Real), GProperRel u ms ∧
      ∀ ns : List (Real → Real), GProperRel u ns → ms.length ≤ ns.length :=
  exists_minimal_length' (GProperRel u) h

/-- **Every coefficient of a too-short relation is eventually zero.** Budget induction from the
right, exactly as in `BipevDescent`. -/
theorem all_gcoeffs_evZero_of_shorter {u : Real → Real} {ms : List (Real → Real)}
    (hmin : ∀ ns : List (Real → Real), GProperRel u ns → ms.length ≤ ns.length) :
    ∀ (n : Nat) (es : List (Real → Real)), es.length ≤ n → GEvRel u es → es.length < ms.length →
      ∀ c : Real → Real, c ∈ es → EvZeroF c := by
  intro n
  induction n with
  | zero =>
      intro es hlen _ _ c hc
      cases es with
      | nil => exact absurd hc (by simp)
      | cons _ _ => simp at hlen
  | succ n ih =>
      intro es hlen hrel hlt c hc
      cases hes : es with
      | nil => rw [hes] at hc; exact absurd hc (by simp)
      | cons _ _ =>
          have hne : es ≠ [] := by rw [hes]; simp
          obtain ⟨es₀, c₀, hsplit⟩ : ∃ es₀ c₀, es = es₀ ++ [c₀] :=
            ⟨es.dropLast, es.getLast hne, (List.dropLast_concat_getLast hne).symm⟩
          have hc₀ : EvZeroF c₀ := by
            rcases Classical.em (EvZeroF c₀) with h | h
            · exact h
            · exfalso
              have := hmin es ⟨hrel, es₀, c₀, hsplit, h⟩
              omega
          have hrel₀ : GEvRel u es₀ := by
            rw [hsplit] at hrel
            exact gevRel_dropLast hrel hc₀
          have hlen₀ : es₀.length + 1 = es.length := by rw [hsplit]; simp
          have hIH := ih es₀ (by omega) hrel₀ (by omega)
          rw [hsplit] at hc
          rcases List.mem_append.mp hc with hm | hm
          · exact hIH c hm
          · have : c = c₀ := by simpa using hm
            rw [this]; exact hc₀

/-- The budget-free form. -/
theorem all_gcoeffs_evZero_of_shorter' {u : Real → Real} {ms es : List (Real → Real)}
    (hmin : ∀ ns : List (Real → Real), GProperRel u ns → ms.length ≤ ns.length)
    (hrel : GEvRel u es) (hlt : es.length < ms.length) :
    ∀ c : Real → Real, c ∈ es → EvZeroF c :=
  all_gcoeffs_evZero_of_shorter hmin es.length es (Nat.le_refl _) hrel hlt

/-! ## The division-free degree drop

`a·(second relation) − b·(first relation)` is a relation for any germs `a`, `b`. Taking `a` and `b`
to be the two *top* coefficients makes the top entry `c·d − d·c`, identically zero, so the degree
drops — and nothing was divided by anything.

This is what replaces monic normalisation. The classical argument divides the relation by its
leading coefficient, which needs that coefficient to be invertible; here the same effect is obtained
by multiplying, which needs nothing at all. -/

/-- `a·ds − b·cs`, coefficientwise. Off-length tails are dropped; every lemma below carries the
length hypothesis rather than relying on that. -/
noncomputable def gscaleSub (a b : Real → Real) :
    List (Real → Real) → List (Real → Real) → List (Real → Real)
  | c :: cs, d :: ds => (fun x => a x * d x - b x * c x) :: gscaleSub a b cs ds
  | _,       _       => []

theorem gbipev_gscaleSub (a b : Real → Real) : ∀ (cs ds : List (Real → Real)) (x y : Real),
    cs.length = ds.length →
    gbipev (gscaleSub a b cs ds) x y = a x * gbipev ds x y - b x * gbipev cs x y := by
  intro cs
  induction cs with
  | nil =>
      intro ds x y hlen
      cases ds with
      | nil => show (0 : Real) = a x * 0 - b x * 0; mach_ring
      | cons _ _ => simp at hlen
  | cons c cs ih =>
      intro ds x y hlen
      cases ds with
      | nil => simp at hlen
      | cons d ds =>
          show (a x * d x - b x * c x) + y * gbipev (gscaleSub a b cs ds) x y
              = a x * (d x + y * gbipev ds x y) - b x * (c x + y * gbipev cs x y)
          rw [ih ds x y (by simpa using hlen)]
          -- `mach_ring` leaves a pure AC residual across the two `gbipev` atoms
          mach_mpoly [a x, b x, c x, d x, y, gbipev cs x y, gbipev ds x y]

theorem gscaleSub_concat (a b c d : Real → Real) :
    ∀ (cs₀ ds₀ : List (Real → Real)), cs₀.length = ds₀.length →
      gscaleSub a b (cs₀ ++ [c]) (ds₀ ++ [d])
        = gscaleSub a b cs₀ ds₀ ++ [fun x => a x * d x - b x * c x] := by
  intro cs₀
  induction cs₀ with
  | nil =>
      intro ds₀ hlen
      cases ds₀ with
      | nil => rfl
      | cons _ _ => simp at hlen
  | cons e cs ih =>
      intro ds₀ hlen
      cases ds₀ with
      | nil => simp at hlen
      | cons f ds =>
          show (fun x => a x * f x - b x * e x) :: gscaleSub a b (cs ++ [c]) (ds ++ [d])
              = (fun x => a x * f x - b x * e x) :: (gscaleSub a b cs ds ++ [_])
          rw [ih ds (by simpa using hlen)]

/-- A germ-scaled difference of two relations is a relation. -/
theorem gEvRel_gscaleSub {u : Real → Real} {cs ds : List (Real → Real)} (a b : Real → Real)
    (hlen : cs.length = ds.length) (hc : GEvRel u cs) (hd : GEvRel u ds) :
    GEvRel u (gscaleSub a b cs ds) := by
  obtain ⟨X₁, hX₁, h₁⟩ := hc
  obtain ⟨X₂, hX₂, h₂⟩ := hd
  obtain ⟨X, hX, hle1, hle2⟩ := two_bounds' hX₁ hX₂
  refine ⟨X, hX, fun x hx => ?_⟩
  rw [gbipev_gscaleSub a b cs ds x (u x) hlen, h₁ x (le_trans hle1 hx),
      h₂ x (le_trans hle2 hx)]
  mach_ring

/-- **The degree drops, with no division.** Two relations of equal length, combined against each
other's top coefficients, give a relation that is one shorter. -/
theorem gcancel_top {u : Real → Real} {cs₀ ds₀ : List (Real → Real)} {c d : Real → Real}
    (hlen : cs₀.length = ds₀.length)
    (hc : GEvRel u (cs₀ ++ [c])) (hd : GEvRel u (ds₀ ++ [d])) :
    GEvRel u (gscaleSub c d cs₀ ds₀) := by
  have hall : GEvRel u (gscaleSub c d (cs₀ ++ [c]) (ds₀ ++ [d])) :=
    gEvRel_gscaleSub c d (by simp [hlen]) hc hd
  rw [gscaleSub_concat c d c d cs₀ ds₀ hlen] at hall
  refine gevRel_dropLast hall ⟨1, le_refl 1, fun x _ => ?_⟩
  show c x * d x - d x * c x = 0
  mach_ring

end MachLib
