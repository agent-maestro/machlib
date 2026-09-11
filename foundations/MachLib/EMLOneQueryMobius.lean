import MachLib.EMLOneQueryNormalForm

/-!
# A one-query context is MÖBIUS in the query value

## The fact

`FCtx` is a full rational-expression tree — `add`, `sub`, `mul`, `div`, nested arbitrarily — so
nothing about its syntax bounds the degree of anything. `ctxFrac` already gives it a rational normal
form `C.eval x y · D(x,y) = N(x,y)` with `N`, `D` bivariate polynomials (`ctxFrac_eval`), and for a
general context those have arbitrary degree in `y`.

Under `FCtx.holes C = 1` they are **affine in `y`**:

```
oneQueryCtx_mobius :  holes C = 1 →
    C.eval x y · (d₀(x) + y·d₁(x))  =  n₀(x) + y·n₁(x)
```

One occurrence of `y` cannot be squared. That is the entire argument, and it is invisible in the
recursion until the degrees are tracked, because `bimul` at a binary node multiplies *four*
components and only the hole-count says which of them can carry `y`.

## Why it is worth having

`OneQueryLevelSet` — the open row — asks whether `{x : T(x) = c}` is finite or co-finite for a
one-query `T`. Through the global normal form `T(x) = C(x, F(P(x)/Q(x)))`, that is an equation in
the query value `u = F(P(x)/Q(x))`. **Möbius makes it LINEAR in `u`:** `T(x) = c` rearranges to

```
u · (c·d₁ − n₁)(x)  =  (n₀ − c·d₀)(x)
```

— one polynomial coefficient against one polynomial constant term, which is exactly the shape
`zero_query_level_set` solves one level down with `pev_zero_or_finite_roots`. Without the degree
bound the same rearrangement is a polynomial in `u` of unknown degree and the level-0 template does
not transfer.

## What this does NOT do, stated so nobody reads it as more

It does not prove `OneQueryLevelSet`, and the gap is not the algebra above. Two things remain:

1. **The side conditions, and the gap is RAY-vs-GLOBAL, not missing machinery.** `ctxFrac_eval`,
   and so this theorem, hold where `DivDenomsOK C x y` and `bipev (ctxFrac C).2 x y ≠ 0`. Those
   exist: `divClamp_denom_and_divDenomsOK` (`EMLCtxDivClamp`) supplies both at `y = F(P/Q)`, which
   is how `oneQueryDichotomy_holds` discharges its row. But it supplies them on a **ray** —
   `∃ X, 1 ≤ X ∧ ∀ x ≥ X` — and `OneQueryLevelSet` is **global**. Only the ray form exists.

   That is not a formality to grind out. The ray form works because a dominant term eventually
   wins; a global form needs the zero set counted on a bounded interval, which is compactness or
   analyticity, and this base deliberately has neither. It is the same fault line
   `EMLOneQueryGlobal.lean` opens with — the level-1 normal form was eventual, and "both live where
   an eventual statement cannot look" — and the one `EMLZeroListFromBound.lean` names outright:
   the ray form is what today's `divClamp` work produces, while a level-set theorem consumes the
   global form.
2. **The residue — and it is a strictly SMALLER residue than the corpus records.**
   `one_hole_level_is_affine` below turns `C(x, y) = c` into `y·B(x) = A(x)` for polynomials `A`,
   `B` built from the Möbius coefficients. Off the degenerate locus that says `F(P/Q) = A/B`, an
   analytic statement about `exp + log` composed with a rational function. Not proved here.

   **What is new is the degree.** `FbasisRootUnique`'s closing note says the lift from the
   generator to the general one-query germ "needs linear independence of the **powers** of
   `Fbasis ∘ u` over rational germs — which is `BoundedGermTranscendence`, itself an OPEN
   obligation." That is right for an arbitrary context. For a ONE-HOLE context it is too strong:
   `ctxFrac_ydeg` caps the degree in `y` at one, so only `y⁰` and `y¹` ever occur and no
   independence of higher powers is required.

   So `OneQueryLevelSet` does not need `BoundedGermTranscendence`. It needs its **degree-1
   fragment**, which is a weaker statement, and the two open rows are related more tightly than
   either records. Whether the fragment is easier is not claimed — only that it is smaller.

So: the *linearisation* is discharged; the finiteness is not. Stated this way because the
temptation, having made the equation linear, is to call the row reduced.
-/

namespace MachLib

/-- `biadd` takes the longer of the two. -/
theorem biadd_length : ∀ A B : List (List Real),
    (biadd A B).length = max A.length B.length
  | [],      M       => by simp [biadd]
  | _ :: _,  []      => by simp [biadd]
  | A :: As, B :: Bs => by
      show (padd A B :: biadd As Bs).length = _
      simp [List.length_cons, biadd_length As Bs]

/-- `biscale` preserves length. -/
theorem biscale_length : ∀ (a : List Real) (M : List (List Real)),
    (biscale a M).length = M.length
  | _, []      => rfl
  | a, _ :: Ms => by
      show (_ :: biscale a Ms).length = _
      simp [biscale_length a Ms]

/-- `bimul` by a nonempty right factor: degrees ADD, in the `deg = length - 1` convention.
`[]` on the left is the zero bipoly and stays zero. -/
theorem bimul_length_le : ∀ (A B : List (List Real)), B ≠ [] →
    (bimul A B).length ≤ A.length + B.length - 1
  | [],      _, _  => by simp [bimul]
  | A :: As, B, hB => by
      have hB1 : 1 ≤ B.length := by
        cases B with
        | nil => exact absurd rfl hB
        | cons _ _ => simp
      have ih := bimul_length_le As B hB
      show (biadd (biscale A B) ([] :: bimul As B)).length ≤ _
      rw [biadd_length, biscale_length]
      simp [List.length_cons]
      omega

/-- A nonempty left factor keeps `bimul` nonempty — so `ctxFrac` never degenerates to the empty
list, which the degree bound below needs at every node. -/
theorem bimul_ne_nil : ∀ (A B : List (List Real)), A ≠ [] → bimul A B ≠ []
  | [],      _, h => absurd rfl h
  | A :: As, B, _ => by
      show biadd (biscale A B) ([] :: bimul As B) ≠ []
      intro hz
      have := congrArg List.length hz
      rw [biadd_length, biscale_length] at this
      simp [List.length_cons] at this

theorem bisub_length (A B : List (List Real)) :
    (bisub A B).length = max A.length B.length := by
  show (biadd A (biscale [0 - 1] B)).length = _
  rw [biadd_length, biscale_length]

private theorem len_pos_of_ne_nil {a : Type} : ∀ {L : List a}, L ≠ [] → 1 ≤ L.length
  | [],     h => absurd rfl h
  | _ :: _, _ => Nat.succ_le_succ (Nat.zero_le _)

private theorem biadd_ne_nil_left (A B : List (List Real)) (h : A ≠ []) : biadd A B ≠ [] := by
  intro hz
  have e : max A.length B.length = 0 := by
    have := congrArg List.length hz
    rw [biadd_length] at this
    exact this
  have := len_pos_of_ne_nil h
  omega

/-- Degrees add, in the bound form the induction actually uses. -/
private theorem bimul_bound {A B : List (List Real)} {p q : Nat}
    (hA : A.length ≤ p) (hB : B.length ≤ q) (hBne : B ≠ []) :
    (bimul A B).length ≤ p + q - 1 := by
  have u := bimul_length_le A B hBne
  have := len_pos_of_ne_nil hBne
  omega

/-- **One hole ⟹ affine in the hole.** Carried as one statement because the three parts are
mutually needed at every binary node: a length bound is worthless without nonemptiness (a `bimul`
with an empty left factor collapses to `[]`, whose degree claim says nothing), and the one-hole
bound leans on the hole-FREE bound at whichever child does not carry the hole.

`length` is `degree + 1` in the `bipev` convention, so `≤ 2` is "affine in `y`". -/
theorem ctxFrac_ydeg : ∀ C : FCtx,
    ((ctxFrac C).1 ≠ [] ∧ (ctxFrac C).2 ≠ [])
    ∧ (FCtx.holes C = 0 → (ctxFrac C).1.length ≤ 1 ∧ (ctxFrac C).2.length ≤ 1)
    ∧ (FCtx.holes C = 1 → (ctxFrac C).1.length ≤ 2 ∧ (ctxFrac C).2.length ≤ 2) := by
  intro C
  induction C with
  | hole =>
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · show ([[], [1]] : List (List Real)) ≠ []; exact List.cons_ne_nil _ _
      · show ([[1]] : List (List Real)) ≠ []; exact List.cons_ne_nil _ _
      · intro h; exact absurd h (by show (1 : Nat) ≠ 0; omega)
      · intro _; exact ⟨by show (2 : Nat) ≤ 2; omega, by show (1 : Nat) ≤ 2; omega⟩
  | const c =>
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · show ([[c]] : List (List Real)) ≠ []; exact List.cons_ne_nil _ _
      · show ([[1]] : List (List Real)) ≠ []; exact List.cons_ne_nil _ _
      · intro _; exact ⟨by show (1 : Nat) ≤ 1; omega, by show (1 : Nat) ≤ 1; omega⟩
      · intro h; exact absurd h (by show (0 : Nat) ≠ 1; omega)
  | var =>
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · show ([[0, 1]] : List (List Real)) ≠ []; exact List.cons_ne_nil _ _
      · show ([[1]] : List (List Real)) ≠ []; exact List.cons_ne_nil _ _
      · intro _; exact ⟨by show (1 : Nat) ≤ 1; omega, by show (1 : Nat) ≤ 1; omega⟩
      · intro h; exact absurd h (by show (0 : Nat) ≠ 1; omega)
  | add a b iha ihb =>
      obtain ⟨⟨haN, haD⟩, ha0, ha1⟩ := iha
      obtain ⟨⟨hbN, hbD⟩, hb0, hb1⟩ := ihb
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · show biadd (bimul (ctxFrac a).1 (ctxFrac b).2) (bimul (ctxFrac b).1 (ctxFrac a).2) ≠ []
        exact biadd_ne_nil_left _ _ (bimul_ne_nil _ _ haN)
      · show bimul (ctxFrac a).2 (ctxFrac b).2 ≠ []
        exact bimul_ne_nil _ _ haD
      · intro h
        have hsum : FCtx.holes a + FCtx.holes b = 0 := h
        obtain ⟨pa, qa⟩ := ha0 (by omega)
        obtain ⟨pb, qb⟩ := hb0 (by omega)
        refine ⟨?_, ?_⟩
        · show (biadd (bimul (ctxFrac a).1 (ctxFrac b).2) (bimul (ctxFrac b).1 (ctxFrac a).2)).length ≤ 1
          rw [biadd_length]
          have u1 := bimul_bound pa qb hbD
          have u2 := bimul_bound pb qa haD
          omega
        · show (bimul (ctxFrac a).2 (ctxFrac b).2).length ≤ 1
          have u3 := bimul_bound qa qb hbD
          omega
      · intro h
        have hsum : FCtx.holes a + FCtx.holes b = 1 := h
        -- The asymmetry IS the content: exactly one child carries the hole, and the bound only
        -- closes because the OTHER is held at 1. Weakening both to 2 gives 2 + 2 - 1 = 3, and the
        -- Möbius claim dies with it.
        rcases (by omega : FCtx.holes a = 0 ∧ FCtx.holes b = 1
                        ∨ FCtx.holes a = 1 ∧ FCtx.holes b = 0) with ⟨x, y⟩ | ⟨x, y⟩
        · obtain ⟨pa, qa⟩ := ha0 x
          obtain ⟨pb, qb⟩ := hb1 y
          refine ⟨?_, ?_⟩
          · show (biadd (bimul (ctxFrac a).1 (ctxFrac b).2) (bimul (ctxFrac b).1 (ctxFrac a).2)).length ≤ 2
            rw [biadd_length]
            have u1 := bimul_bound pa qb hbD
            have u2 := bimul_bound pb qa haD
            omega
          · show (bimul (ctxFrac a).2 (ctxFrac b).2).length ≤ 2
            have u3 := bimul_bound qa qb hbD
            omega
        · obtain ⟨pa, qa⟩ := ha1 x
          obtain ⟨pb, qb⟩ := hb0 y
          refine ⟨?_, ?_⟩
          · show (biadd (bimul (ctxFrac a).1 (ctxFrac b).2) (bimul (ctxFrac b).1 (ctxFrac a).2)).length ≤ 2
            rw [biadd_length]
            have u1 := bimul_bound pa qb hbD
            have u2 := bimul_bound pb qa haD
            omega
          · show (bimul (ctxFrac a).2 (ctxFrac b).2).length ≤ 2
            have u3 := bimul_bound qa qb hbD
            omega
  | sub a b iha ihb =>
      obtain ⟨⟨haN, haD⟩, ha0, ha1⟩ := iha
      obtain ⟨⟨hbN, hbD⟩, hb0, hb1⟩ := ihb
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · show bisub (bimul (ctxFrac a).1 (ctxFrac b).2) (bimul (ctxFrac b).1 (ctxFrac a).2) ≠ []
        exact biadd_ne_nil_left _ _ (bimul_ne_nil _ _ haN)
      · show bimul (ctxFrac a).2 (ctxFrac b).2 ≠ []
        exact bimul_ne_nil _ _ haD
      · intro h
        have hsum : FCtx.holes a + FCtx.holes b = 0 := h
        obtain ⟨pa, qa⟩ := ha0 (by omega)
        obtain ⟨pb, qb⟩ := hb0 (by omega)
        refine ⟨?_, ?_⟩
        · show (bisub (bimul (ctxFrac a).1 (ctxFrac b).2) (bimul (ctxFrac b).1 (ctxFrac a).2)).length ≤ 1
          rw [bisub_length]
          have u1 := bimul_bound pa qb hbD
          have u2 := bimul_bound pb qa haD
          omega
        · show (bimul (ctxFrac a).2 (ctxFrac b).2).length ≤ 1
          have u3 := bimul_bound qa qb hbD
          omega
      · intro h
        have hsum : FCtx.holes a + FCtx.holes b = 1 := h
        -- The asymmetry IS the content: exactly one child carries the hole, and the bound only
        -- closes because the OTHER is held at 1. Weakening both to 2 gives 2 + 2 - 1 = 3, and the
        -- Möbius claim dies with it.
        rcases (by omega : FCtx.holes a = 0 ∧ FCtx.holes b = 1
                        ∨ FCtx.holes a = 1 ∧ FCtx.holes b = 0) with ⟨x, y⟩ | ⟨x, y⟩
        · obtain ⟨pa, qa⟩ := ha0 x
          obtain ⟨pb, qb⟩ := hb1 y
          refine ⟨?_, ?_⟩
          · show (bisub (bimul (ctxFrac a).1 (ctxFrac b).2) (bimul (ctxFrac b).1 (ctxFrac a).2)).length ≤ 2
            rw [bisub_length]
            have u1 := bimul_bound pa qb hbD
            have u2 := bimul_bound pb qa haD
            omega
          · show (bimul (ctxFrac a).2 (ctxFrac b).2).length ≤ 2
            have u3 := bimul_bound qa qb hbD
            omega
        · obtain ⟨pa, qa⟩ := ha1 x
          obtain ⟨pb, qb⟩ := hb0 y
          refine ⟨?_, ?_⟩
          · show (bisub (bimul (ctxFrac a).1 (ctxFrac b).2) (bimul (ctxFrac b).1 (ctxFrac a).2)).length ≤ 2
            rw [bisub_length]
            have u1 := bimul_bound pa qb hbD
            have u2 := bimul_bound pb qa haD
            omega
          · show (bimul (ctxFrac a).2 (ctxFrac b).2).length ≤ 2
            have u3 := bimul_bound qa qb hbD
            omega
  | mul a b iha ihb =>
      obtain ⟨⟨haN, haD⟩, ha0, ha1⟩ := iha
      obtain ⟨⟨hbN, hbD⟩, hb0, hb1⟩ := ihb
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · show bimul (ctxFrac a).1 (ctxFrac b).1 ≠ []
        exact bimul_ne_nil _ _ haN
      · show bimul (ctxFrac a).2 (ctxFrac b).2 ≠ []
        exact bimul_ne_nil _ _ haD
      · intro h
        have hsum : FCtx.holes a + FCtx.holes b = 0 := h
        obtain ⟨pa, qa⟩ := ha0 (by omega)
        obtain ⟨pb, qb⟩ := hb0 (by omega)
        refine ⟨?_, ?_⟩
        · show (bimul (ctxFrac a).1 (ctxFrac b).1).length ≤ 1
          have u1 := bimul_bound pa pb hbN
          omega
        · show (bimul (ctxFrac a).2 (ctxFrac b).2).length ≤ 1
          have u3 := bimul_bound qa qb hbD
          omega
      · intro h
        have hsum : FCtx.holes a + FCtx.holes b = 1 := h
        -- The asymmetry IS the content: exactly one child carries the hole, and the bound only
        -- closes because the OTHER is held at 1. Weakening both to 2 gives 2 + 2 - 1 = 3, and the
        -- Möbius claim dies with it.
        rcases (by omega : FCtx.holes a = 0 ∧ FCtx.holes b = 1
                        ∨ FCtx.holes a = 1 ∧ FCtx.holes b = 0) with ⟨x, y⟩ | ⟨x, y⟩
        · obtain ⟨pa, qa⟩ := ha0 x
          obtain ⟨pb, qb⟩ := hb1 y
          refine ⟨?_, ?_⟩
          · show (bimul (ctxFrac a).1 (ctxFrac b).1).length ≤ 2
            have u1 := bimul_bound pa pb hbN
            omega
          · show (bimul (ctxFrac a).2 (ctxFrac b).2).length ≤ 2
            have u3 := bimul_bound qa qb hbD
            omega
        · obtain ⟨pa, qa⟩ := ha1 x
          obtain ⟨pb, qb⟩ := hb0 y
          refine ⟨?_, ?_⟩
          · show (bimul (ctxFrac a).1 (ctxFrac b).1).length ≤ 2
            have u1 := bimul_bound pa pb hbN
            omega
          · show (bimul (ctxFrac a).2 (ctxFrac b).2).length ≤ 2
            have u3 := bimul_bound qa qb hbD
            omega
  | div a b iha ihb =>
      obtain ⟨⟨haN, haD⟩, ha0, ha1⟩ := iha
      obtain ⟨⟨hbN, hbD⟩, hb0, hb1⟩ := ihb
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · show bimul (ctxFrac a).1 (ctxFrac b).2 ≠ []
        exact bimul_ne_nil _ _ haN
      · show bimul (ctxFrac a).2 (ctxFrac b).1 ≠ []
        exact bimul_ne_nil _ _ haD
      · intro h
        have hsum : FCtx.holes a + FCtx.holes b = 0 := h
        obtain ⟨pa, qa⟩ := ha0 (by omega)
        obtain ⟨pb, qb⟩ := hb0 (by omega)
        refine ⟨?_, ?_⟩
        · show (bimul (ctxFrac a).1 (ctxFrac b).2).length ≤ 1
          have u1 := bimul_bound pa qb hbD
          omega
        · show (bimul (ctxFrac a).2 (ctxFrac b).1).length ≤ 1
          have u3 := bimul_bound qa pb hbN
          omega
      · intro h
        have hsum : FCtx.holes a + FCtx.holes b = 1 := h
        -- The asymmetry IS the content: exactly one child carries the hole, and the bound only
        -- closes because the OTHER is held at 1. Weakening both to 2 gives 2 + 2 - 1 = 3, and the
        -- Möbius claim dies with it.
        rcases (by omega : FCtx.holes a = 0 ∧ FCtx.holes b = 1
                        ∨ FCtx.holes a = 1 ∧ FCtx.holes b = 0) with ⟨x, y⟩ | ⟨x, y⟩
        · obtain ⟨pa, qa⟩ := ha0 x
          obtain ⟨pb, qb⟩ := hb1 y
          refine ⟨?_, ?_⟩
          · show (bimul (ctxFrac a).1 (ctxFrac b).2).length ≤ 2
            have u1 := bimul_bound pa qb hbD
            omega
          · show (bimul (ctxFrac a).2 (ctxFrac b).1).length ≤ 2
            have u3 := bimul_bound qa pb hbN
            omega
        · obtain ⟨pa, qa⟩ := ha1 x
          obtain ⟨pb, qb⟩ := hb0 y
          refine ⟨?_, ?_⟩
          · show (bimul (ctxFrac a).1 (ctxFrac b).2).length ≤ 2
            have u1 := bimul_bound pa qb hbD
            omega
          · show (bimul (ctxFrac a).2 (ctxFrac b).1).length ≤ 2
            have u3 := bimul_bound qa pb hbN
            omega

/-- A bipoly of `length ≤ 2` IS an affine function of `y`, with its two coefficients exhibited. -/
theorem bipev_affine : ∀ (B : List (List Real)), B ≠ [] → B.length ≤ 2 →
    ∃ c1 c0 : List Real, ∀ x y : Real, bipev B x y = pev c0 x + y * pev c1 x
  | [],            h, _ => absurd rfl h
  | [L0],          _, _ => ⟨[], L0, fun x y => by
      show pev L0 x + y * 0 = pev L0 x + y * pev [] x
      show pev L0 x + y * 0 = pev L0 x + y * 0
      rfl⟩
  | [L0, L1],      _, _ => ⟨L1, L0, fun x y => by
      show pev L0 x + y * (pev L1 x + y * 0) = pev L0 x + y * pev L1 x
      mach_ring⟩
  | _ :: _ :: _ :: _, _, h => by simp [List.length_cons] at h

/-- **The Möbius normal form for a one-query context.**

`C.eval x y = (n₁(x)·y + n₀(x)) / (d₁(x)·y + d₀(x))`, stated multiplied out so it needs no
nonvanishing beyond what `ctxFrac_eval` already asks.

This is what makes the level-set question tractable: solving `C.eval x (F w) = c` for the query
value `F w` is solving a LINEAR equation, not an equation of unknown degree. `FCtx` is a full
rational-expression tree, so nothing about its syntax suggests degree 1 — the bound comes entirely
from `holes C = 1`, and one occurrence of `y` cannot be squared. -/
theorem oneQueryCtx_mobius (C : FCtx) (h : FCtx.holes C = 1) :
    ∃ n1 n0 d1 d0 : List Real, ∀ x y : Real, DivDenomsOK C x y →
      bipev (ctxFrac C).2 x y ≠ 0 →
        C.eval x y * (pev d0 x + y * pev d1 x) = pev n0 x + y * pev n1 x := by
  obtain ⟨⟨hNne, hDne⟩, _, hlen⟩ := ctxFrac_ydeg C
  obtain ⟨hN2, hD2⟩ := hlen h
  obtain ⟨n1, n0, hn⟩ := bipev_affine (ctxFrac C).1 hNne hN2
  obtain ⟨d1, d0, hd⟩ := bipev_affine (ctxFrac C).2 hDne hD2
  refine ⟨n1, n0, d1, d0, fun x y hok hne => ?_⟩
  have e := ctxFrac_eval C x y hok hne
  rw [hd x y, hn x y] at e
  exact e

/-- The level equation for a ONE-HOLE context is affine in the query value: no power of
`Fbasis` above the first ever appears. -/
theorem one_hole_level_is_affine (C : FCtx) (hC : FCtx.holes C = 1) (c : Real) :
    ∃ n1 n0 d1 d0 : List Real, ∀ x y : Real, DivDenomsOK C x y →
      bipev (ctxFrac C).2 x y ≠ 0 → FCtx.eval C x y = c →
        y * (pev n1 x - c * pev d1 x) = c * pev d0 x - pev n0 x := by
  obtain ⟨n1, n0, d1, d0, hm⟩ := oneQueryCtx_mobius C hC
  refine ⟨n1, n0, d1, d0, fun x y hok hne hEq => ?_⟩
  have h := hm x y hok hne
  rw [hEq] at h
  -- c * (d0 + y*d1) = n0 + y*n1  ⟹  y*(n1 - c*d1) = c*d0 - n0
  have e : c * (pev d0 x + y * pev d1 x) - (pev n0 x + y * pev n1 x)
         = (c * pev d0 x - pev n0 x) - y * (pev n1 x - c * pev d1 x) := by
    mach_mpoly [c, pev d0 x, pev d1 x, pev n0 x, pev n1 x, y]
  have hz : (c * pev d0 x - pev n0 x) - y * (pev n1 x - c * pev d1 x) = 0 := by
    rw [← e, h]; mach_ring
  have e2 : c * pev d0 x - pev n0 x
          = ((c * pev d0 x - pev n0 x) - y * (pev n1 x - c * pev d1 x))
            + y * (pev n1 x - c * pev d1 x) := by
    mach_mpoly [c, pev d0 x, pev d1 x, pev n0 x, pev n1 x, y]
  rw [e2, hz]; mach_ring

end MachLib
