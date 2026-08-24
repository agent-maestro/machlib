import MachLib.GermRelation

/-!
# Differentiating a germ-coefficient relation

The remaining structural piece of the `S > 0` branch's step 1. `GermRelation` gave the descent over
arbitrary germ coefficients; this gives the derivative, which is what feeds `gcancel_top`.

```
d/dx  Σⱼ cⱼ(x)·u(x)ʲ  =  Σⱼ cⱼ'(x)·u(x)ʲ  +  u'(x)·Σⱼ j·cⱼ(x)·u(x)^(j−1)
```

## `gydiff` is a value; `gyd` is the list, and neither carries an index

The second sum is the *formal `y`-derivative*, and the obvious move is to build it as a coefficient
list mirroring `pderiv` — an auxiliary recursion carrying the degree as a `Nat`, plus `natMul`
arithmetic to relate `k+1` to `k`.

The **index** is what is avoidable, not the list. The Horner shape gives the value directly,

```
∂/∂y [c₀ + y·C(y)]  =  C(y) + y·C'(y)
```

so `gydiff (c :: cs) x y = gbipev cs x y + y · gydiff cs x y`, and the derivative theorem below
proves in that form with no index anywhere. `gcancel_top` does consume coefficient *lists*, so the
list `gyd` is still needed — but the same identity builds it as one shift and one addition
(`gyd (c :: cs) = gadd cs (0 :: gyd cs)`), again with no index and no `natMul`.

So this is a partial instance of the arc's recurring pattern, and worth stating as partial: the list
was genuinely required, and only the index bookkeeping fell away.

## The coefficient-derivative hypothesis

`GDerivAt x cs es` is structural rather than index-based, for the same reason: the proof is an
induction over the two lists in lockstep, and an index-based statement would have to be re-derived
into that shape at every step.
-/

namespace MachLib

open Real

/-- The formal `y`-derivative's **value**: `Σⱼ j·cⱼ(x)·y^(j−1)`. -/
noncomputable def gydiff : List (Real → Real) → Real → Real → Real
  | [],      _, _ => 0
  | _ :: cs, x, y => gbipev cs x y + y * gydiff cs x y

/-- `es` is the coefficientwise derivative of `cs` at `x`. Structural, so it inducts in lockstep
with `gbipev`. -/
def GDerivAt (x : Real) : List (Real → Real) → List (Real → Real) → Prop
  | [],      []      => True
  | c :: cs, e :: es => HasDerivAt c (e x) x ∧ GDerivAt x cs es
  | _,       _       => False

theorem gDerivAt_length : ∀ (x : Real) (cs es : List (Real → Real)),
    GDerivAt x cs es → cs.length = es.length := by
  intro x cs
  induction cs with
  | nil => intro es h; cases es with
    | nil => rfl
    | cons _ _ => exact absurd h (by intro hh; cases hh)
  | cons c cs ih =>
      intro es h
      cases es with
      | nil => exact absurd h (by intro hh; cases hh)
      | cons e es => exact congrArg (· + 1) (ih es h.2)

/-! ## The product-and-chain rule, at every degree at once -/

/-- **The derivative of a germ-coefficient polynomial in `u`.** -/
theorem gbipev_hasDerivAt {u : Real → Real} {v x : Real} (hu : HasDerivAt u v x) :
    ∀ cs es : List (Real → Real), GDerivAt x cs es →
      HasDerivAt (fun t => gbipev cs t (u t))
        (gbipev es x (u x) + v * gydiff cs x (u x)) x := by
  intro cs
  induction cs with
  | nil =>
      intro es h
      cases es with
      | nil =>
          have h0 : (0 : Real) = gbipev ([] : List (Real → Real)) x (u x)
              + v * gydiff ([] : List (Real → Real)) x (u x) := by
            show (0 : Real) = 0 + v * 0
            mach_ring
          exact h0 ▸ HasDerivAt_const 0 x
      | cons _ _ => exact absurd h (by intro hh; cases hh)
  | cons c cs ih =>
      intro es h
      cases es with
      | nil => exact absurd h (by intro hh; cases hh)
      | cons e es =>
          obtain ⟨hc, hrest⟩ := h
          have hG := ih es hrest
          -- product rule on `u · (the tail's value)`, then the sum rule against `c`
          have hprod := HasDerivAt_mul u (fun t => gbipev cs t (u t)) v
            (gbipev es x (u x) + v * gydiff cs x (u x)) x hu hG
          have hsum := HasDerivAt_add c (fun t => u t * gbipev cs t (u t)) (e x)
            (v * gbipev cs x (u x) + u x * (gbipev es x (u x) + v * gydiff cs x (u x))) x hc hprod
          have heq : e x + (v * gbipev cs x (u x)
                + u x * (gbipev es x (u x) + v * gydiff cs x (u x)))
              = gbipev (e :: es) x (u x) + v * gydiff (c :: cs) x (u x) := by
            show _ = (e x + u x * gbipev es x (u x))
                + v * (gbipev cs x (u x) + u x * gydiff cs x (u x))
            mach_mpoly [e x, v, u x, gbipev cs x (u x), gbipev es x (u x), gydiff cs x (u x)]
          exact heq ▸ hsum

/-! ## The differentiated relation, as a list

`gcancel_top` consumes relations as coefficient *lists*, so the derivative value above has to be
packaged back into one. `gdrel v cs es = gadd es (gscale v (gyd cs))`, where `gyd` is the formal
`y`-derivative built by one shift and one addition — no running index, and it preserves length
(the top entry is the trailing zero), which is exactly what `gcancel_top`'s equal-length hypothesis
wants. -/

noncomputable def gadd : List (Real → Real) → List (Real → Real) → List (Real → Real)
  | [],      ds      => ds
  | c :: cs, []      => c :: cs
  | c :: cs, d :: ds => (fun x => c x + d x) :: gadd cs ds

noncomputable def gscale (a : Real → Real) : List (Real → Real) → List (Real → Real)
  | []      => []
  | c :: cs => (fun x => a x * c x) :: gscale a cs

/-- The formal `y`-derivative as a list: `gyd (c :: cs) = cs + y·gyd cs`, the Horner identity
`∂/∂y [c₀ + y·C] = C + y·C'` read as list arithmetic. -/
noncomputable def gyd : List (Real → Real) → List (Real → Real)
  | []      => []
  | _ :: cs => gadd cs ((fun _ => (0 : Real)) :: gyd cs)

/-- The differentiated relation's coefficient list. -/
noncomputable def gdrel (v : Real → Real) (cs es : List (Real → Real)) : List (Real → Real) :=
  gadd es (gscale v (gyd cs))

theorem gbipev_gadd : ∀ (a b : List (Real → Real)) (x y : Real),
    gbipev (gadd a b) x y = gbipev a x y + gbipev b x y := by
  intro a
  induction a with
  | nil => intro b x y; show gbipev b x y = 0 + gbipev b x y; mach_ring
  | cons c cs ih =>
      intro b x y
      cases b with
      | nil => show gbipev (c :: cs) x y = gbipev (c :: cs) x y + 0; mach_ring
      | cons d ds =>
          show (c x + d x) + y * gbipev (gadd cs ds) x y
              = (c x + y * gbipev cs x y) + (d x + y * gbipev ds x y)
          rw [ih ds x y]
          mach_mpoly [c x, d x, y, gbipev cs x y, gbipev ds x y]

theorem gbipev_gscale (a : Real → Real) : ∀ (cs : List (Real → Real)) (x y : Real),
    gbipev (gscale a cs) x y = a x * gbipev cs x y := by
  intro cs
  induction cs with
  | nil => intro x y; show (0 : Real) = a x * 0; mach_ring
  | cons c cs ih =>
      intro x y
      show a x * c x + y * gbipev (gscale a cs) x y = a x * (c x + y * gbipev cs x y)
      rw [ih x y]
      mach_mpoly [a x, c x, y, gbipev cs x y]

theorem gbipev_gyd : ∀ (cs : List (Real → Real)) (x y : Real),
    gbipev (gyd cs) x y = gydiff cs x y := by
  intro cs
  induction cs with
  | nil => intro x y; rfl
  | cons c cs ih =>
      intro x y
      show gbipev (gadd cs ((fun _ => (0 : Real)) :: gyd cs)) x y
          = gbipev cs x y + y * gydiff cs x y
      rw [gbipev_gadd cs ((fun _ => (0 : Real)) :: gyd cs) x y]
      show gbipev cs x y + (0 + y * gbipev (gyd cs) x y) = _
      rw [ih x y]
      mach_ring

/-! ## Lengths — one-sided, because `omega` treats `Nat.max` as opaque -/

theorem gadd_length_of_le : ∀ (a b : List (Real → Real)), a.length ≤ b.length →
    (gadd a b).length = b.length := by
  intro a
  induction a with
  | nil => intro b _; rfl
  | cons c cs ih =>
      intro b hlen
      cases b with
      | nil => simp at hlen
      | cons d ds =>
          show (gadd cs ds).length + 1 = ds.length + 1
          rw [ih ds (by simpa using hlen)]

theorem gscale_length (a : Real → Real) : ∀ cs : List (Real → Real),
    (gscale a cs).length = cs.length := by
  intro cs
  induction cs with
  | nil => rfl
  | cons _ cs ih => show (gscale a cs).length + 1 = cs.length + 1; rw [ih]

theorem gyd_length : ∀ cs : List (Real → Real), (gyd cs).length = cs.length := by
  intro cs
  induction cs with
  | nil => rfl
  | cons _ cs ih =>
      show (gadd cs ((fun _ => (0 : Real)) :: gyd cs)).length = cs.length + 1
      rw [gadd_length_of_le cs ((fun _ => (0 : Real)) :: gyd cs) (by simp [ih])]
      show (gyd cs).length + 1 = cs.length + 1
      rw [ih]

theorem gdrel_length {v : Real → Real} {cs es : List (Real → Real)}
    (h : cs.length = es.length) : (gdrel v cs es).length = cs.length := by
  show (gadd es (gscale v (gyd cs))).length = cs.length
  rw [gadd_length_of_le es (gscale v (gyd cs)) (by rw [gscale_length, gyd_length]; omega),
      gscale_length, gyd_length]

theorem gbipev_gdrel (v : Real → Real) (cs es : List (Real → Real)) (x y : Real) :
    gbipev (gdrel v cs es) x y = gbipev es x y + v x * gydiff cs x y := by
  show gbipev (gadd es (gscale v (gyd cs))) x y = _
  rw [gbipev_gadd, gbipev_gscale, gbipev_gyd]

/-! ## Differentiating the relation

A relation vanishes on a tail, so its derivative vanishes strictly inside — the same
`hasDerivAt_of_agrees_on_tail` move as `dbipevExp_eq_zero_of_relation_on_tail`, with `u` arbitrary
and the coefficients arbitrary differentiable germs. -/

/-- **The derivative of a relation is a relation**, of the same length. -/
theorem gEvRel_gdrel {u v : Real → Real} {cs es : List (Real → Real)}
    (hu : ∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x → HasDerivAt u (v x) x)
    (hd : ∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x → GDerivAt x cs es)
    (hrel : GEvRel u cs) : GEvRel u (gdrel v cs es) := by
  obtain ⟨X₁, hX₁, hu'⟩ := hu
  obtain ⟨X₂, hX₂, hd'⟩ := hd
  obtain ⟨X₃, hX₃, hr⟩ := hrel
  obtain ⟨X, hX, h1, h2, h3⟩ := three_tails hX₁ hX₂ hX₃
  refine ⟨X + 1, le_trans hX (le_of_lt (self_lt_succ X)), fun x hx => ?_⟩
  have hXx : X < x := lt_of_lt_of_le (self_lt_succ X) hx
  -- the relation's derivative, computed
  have hval := gbipev_hasDerivAt (hu' x (le_trans h1 (le_of_lt hXx))) cs es
    (hd' x (le_trans h2 (le_of_lt hXx)))
  -- and the same derivative, read off the constant zero it agrees with on the tail
  have hzero : HasDerivAt (fun t => gbipev cs t (u t)) 0 x :=
    hasDerivAt_of_agrees_on_tail (f := fun _ => (0 : Real)) hXx
      (fun y hy => (hr y (le_trans h3 (le_of_lt hy))).symm) (HasDerivAt_const 0 x)
  have := HasDerivAt_unique (fun t => gbipev cs t (u t))
    (gbipev es x (u x) + v x * gydiff cs x (u x)) 0 x hval hzero
  rw [gbipev_gdrel v cs es x (u x)]
  exact this

end MachLib
