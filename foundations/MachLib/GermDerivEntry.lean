import MachLib.GermDeriv

/-!
# Reading `gdrel`'s entries

The last bookkeeping between `GermDeriv` and the identity the `S > 0` branch needs. `gcancel_top`
produces a shorter relation; minimality then says all of its coefficients vanish eventually, and the
one that carries the content is the *top* one. Getting at it means knowing what `gdrel` holds at an
index:

```
(gdrel v cs es)[j]  =  eⱼ + v·(j+1)·c_(j+1)          for j+1 < cs.length
(gdrel v cs es)[n]  =  eₙ                             for cs.length = n+1
```

The second is the trailing zero of `gyd` doing its job: the formal `y`-derivative of a degree-`n`
polynomial has degree `n−1`, and `gyd` records that as a zero in the top slot rather than by
shortening the list — which is what keeps `gdrel_length` equal to `cs.length`, and hence what lets
`gcancel_top` apply at all.

## Values, not functions

Every entry lemma concludes `∃ b, … = some b ∧ ∀ x, b x = …` rather than naming the function
literally. Two coefficient germs that agree everywhere are equal only by `funext`, and the caller
needs the *values* — the identity being extracted is a pointwise equation on a tail. So the
existential form is both cheaper and closer to what is consumed. This is the same shape as
`dcoeffs_getElem`, and the fourth shape lemma in this arc written before the theorem that needs it.
-/

namespace MachLib

open Real

/-! ## Entries of the list operations -/

theorem gadd_getElem : ∀ (a b : List (Real → Real)) (j : Nat) (p q : Real → Real),
    a[j]? = some p → b[j]? = some q → (gadd a b)[j]? = some (fun x => p x + q x) := by
  intro a
  induction a with
  | nil => intro b j p q hp _; simp at hp
  | cons c cs ih =>
      intro b j p q hp hq
      cases b with
      | nil => simp at hq
      | cons d ds =>
          cases j with
          | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at hp hq
              show (gadd (c :: cs) (d :: ds))[0]? = _
              simp only [gadd, List.getElem?_cons_zero, hp, hq]
          | succ k =>
              simp only [List.getElem?_cons_succ] at hp hq
              show (gadd (c :: cs) (d :: ds))[k + 1]? = _
              simp only [gadd, List.getElem?_cons_succ]
              exact ih ds k p q hp hq

theorem gadd_getElem_left_none : ∀ (a b : List (Real → Real)) (j : Nat),
    a.length ≤ j → (gadd a b)[j]? = b[j]? := by
  intro a
  induction a with
  | nil => intro b j _; rfl
  | cons c cs ih =>
      intro b j hlen
      cases j with
      | zero => simp at hlen
      | succ k =>
          cases b with
          | nil =>
              show (c :: cs)[k + 1]? = ([] : List (Real → Real))[k + 1]?
              rw [List.getElem?_eq_none (by simpa using hlen)]
              rfl
          | cons d ds =>
              show (gadd (c :: cs) (d :: ds))[k + 1]? = (d :: ds)[k + 1]?
              simp only [gadd, List.getElem?_cons_succ]
              exact ih ds k (by simpa using hlen)

theorem gscale_getElem (v : Real → Real) : ∀ (cs : List (Real → Real)) (j : Nat) (p : Real → Real),
    cs[j]? = some p → (gscale v cs)[j]? = some (fun x => v x * p x) := by
  intro cs
  induction cs with
  | nil => intro j p hp; simp at hp
  | cons c cs ih =>
      intro j p hp
      cases j with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hp
          show (gscale v (c :: cs))[0]? = _
          simp only [gscale, List.getElem?_cons_zero, hp]
      | succ k =>
          simp only [List.getElem?_cons_succ] at hp
          show (gscale v (c :: cs))[k + 1]? = _
          simp only [gscale, List.getElem?_cons_succ]
          exact ih k p hp

theorem gscaleSub_getElem (a b : Real → Real) :
    ∀ (cs ds : List (Real → Real)) (j : Nat) (p q : Real → Real),
      cs[j]? = some p → ds[j]? = some q →
      (gscaleSub a b cs ds)[j]? = some (fun x => a x * q x - b x * p x) := by
  intro cs
  induction cs with
  | nil => intro ds j p q hp _; simp at hp
  | cons c cs ih =>
      intro ds j p q hp hq
      cases ds with
      | nil => simp at hq
      | cons d ds =>
          cases j with
          | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at hp hq
              show (gscaleSub a b (c :: cs) (d :: ds))[0]? = _
              simp only [gscaleSub, List.getElem?_cons_zero, hp, hq]
          | succ k =>
              simp only [List.getElem?_cons_succ] at hp hq
              show (gscaleSub a b (c :: cs) (d :: ds))[k + 1]? = _
              simp only [gscaleSub, List.getElem?_cons_succ]
              exact ih ds k p q hp hq

/-! ## Entries of the formal `y`-derivative -/

/-- `(gyd cs)[j] = (j+1)·c_(j+1)`. -/
theorem gyd_getElem : ∀ (cs : List (Real → Real)) (j : Nat) (a : Real → Real),
    cs[j + 1]? = some a →
      ∃ b : Real → Real, (gyd cs)[j]? = some b ∧ ∀ x, b x = natMul (j + 1) 1 * a x := by
  intro cs
  induction cs with
  | nil => intro j a ha; simp at ha
  | cons c cs ih =>
      intro j a ha
      simp only [List.getElem?_cons_succ] at ha
      cases j with
      | zero =>
          refine ⟨fun x => a x + (fun _ => (0 : Real)) x, ?_, fun x => ?_⟩
          · show (gadd cs ((fun _ => (0 : Real)) :: gyd cs))[0]? = _
            exact gadd_getElem cs _ 0 a (fun _ => (0 : Real)) ha (by simp)
          · show a x + 0 = natMul 1 1 * a x
            show a x + 0 = (1 + natMul 0 1) * a x
            show a x + 0 = (1 + 0) * a x
            mach_ring
      | succ k =>
          obtain ⟨b', hb', hval⟩ := ih k a ha
          refine ⟨fun x => a x + b' x, ?_, fun x => ?_⟩
          · show (gadd cs ((fun _ => (0 : Real)) :: gyd cs))[k + 1]? = _
            refine gadd_getElem cs _ (k + 1) a b' ha ?_
            simpa using hb'
          · show a x + b' x = natMul (k + 2) 1 * a x
            rw [hval x]
            show a x + natMul (k + 1) 1 * a x = (1 + natMul (k + 1) 1) * a x
            mach_mpoly [a x, natMul (k + 1) 1]

/-- The trailing zero: the top slot of `gyd` is empty, which is what keeps the length equal. -/
theorem gyd_getElem_top : ∀ (cs : List (Real → Real)) (n : Nat), cs.length = n + 1 →
    ∃ b : Real → Real, (gyd cs)[n]? = some b ∧ ∀ x, b x = 0 := by
  intro cs
  induction cs with
  | nil => intro n hn; simp at hn
  | cons c cs ih =>
      intro n hn
      have hcs : cs.length = n := by simpa using hn
      have hstep : (gyd (c :: cs))[n]? = ((fun _ => (0 : Real)) :: gyd cs)[n]? := by
        show (gadd cs ((fun _ => (0 : Real)) :: gyd cs))[n]? = _
        exact gadd_getElem_left_none cs _ n (by omega)
      cases n with
      | zero => exact ⟨fun _ => (0 : Real), by rw [hstep]; simp, fun _ => rfl⟩
      | succ m =>
          obtain ⟨b, hb, hval⟩ := ih m hcs
          exact ⟨b, by rw [hstep]; simpa using hb, hval⟩

/-! ## Entries of the differentiated relation -/

/-- **The interior entry**: `eⱼ + v·(j+1)·c_(j+1)`. -/
theorem gdrel_getElem {v : Real → Real} {cs es : List (Real → Real)} {j : Nat} {e a : Real → Real}
    (he : es[j]? = some e) (ha : cs[j + 1]? = some a) :
    ∃ b : Real → Real, (gdrel v cs es)[j]? = some b ∧
      ∀ x, b x = e x + v x * (natMul (j + 1) 1 * a x) := by
  obtain ⟨w, hw, hwval⟩ := gyd_getElem cs j a ha
  refine ⟨fun x => e x + (fun t => v t * w t) x, ?_, fun x => ?_⟩
  · show (gadd es (gscale v (gyd cs)))[j]? = _
    exact gadd_getElem es _ j e _ he (gscale_getElem v (gyd cs) j w hw)
  · show e x + v x * w x = _
    rw [hwval x]

/-- **The top entry**: `eₙ`, because `gyd`'s top slot is zero. -/
theorem gdrel_getElem_top {v : Real → Real} {cs es : List (Real → Real)} {n : Nat} {e : Real → Real}
    (he : es[n]? = some e) (hn : cs.length = n + 1) :
    ∃ b : Real → Real, (gdrel v cs es)[n]? = some b ∧ ∀ x, b x = e x := by
  obtain ⟨w, hw, hwval⟩ := gyd_getElem_top cs n hn
  refine ⟨fun x => e x + (fun t => v t * w t) x, ?_, fun x => ?_⟩
  · show (gadd es (gscale v (gyd cs)))[n]? = _
    exact gadd_getElem es _ n e _ he (gscale_getElem v (gyd cs) n w hw)
  · show e x + v x * w x = e x
    rw [hwval x]
    mach_ring

/-! ## The identity

Everything assembled. The minimal relation and its derivative combine by `gcancel_top` into a
relation one shorter; minimality kills all of its coefficients; and the one at the top carries

```
c_d·(c_(d−1)' + v·d·c_d)  −  c_d'·c_(d−1)  ≈  0
```

which rearranges to `d·v·c_d² = c_d'·c_(d−1) − c_d·c_(d−1)'`. With `v = L'` and the coefficients in
`R(x)[E]` that is the `S > 0` branch's target identity, and **no division appears anywhere in
reaching it**. -/

theorem gscaleSub_length (a b : Real → Real) : ∀ cs ds : List (Real → Real),
    cs.length = ds.length → (gscaleSub a b cs ds).length = cs.length := by
  intro cs
  induction cs with
  | nil => intro ds _; rfl
  | cons c cs ih =>
      intro ds hlen
      cases ds with
      | nil => simp at hlen
      | cons d ds =>
          show (gscaleSub a b cs ds).length + 1 = cs.length + 1
          rw [ih ds (by simpa using hlen)]

private theorem evZeroF_congr {f g : Real → Real} (h : EvZeroF f) (he : ∀ x, f x = g x) :
    EvZeroF g := by
  obtain ⟨X, hX, hf⟩ := h
  exact ⟨X, hX, fun x hx => (he x) ▸ hf x hx⟩

private theorem split_last {α : Type} : ∀ (l : List α) (n : Nat), l.length = n + 1 →
    ∃ (l₀ : List α) (a : α), l = l₀ ++ [a] ∧ l₀.length = n := by
  intro l n hn
  have hne : l ≠ [] := by intro h; rw [h] at hn; simp at hn
  exact ⟨l.dropLast, l.getLast hne, (List.dropLast_concat_getLast hne).symm, by
    rw [List.length_dropLast, hn]; omega⟩

/-- **The identity a minimal germ-coefficient relation forces on its top two coefficients.** -/
theorem minimal_grel_identity {u v : Real → Real} {cs es cs₀ es₀ : List (Real → Real)}
    {cd ed cd1 ed1 : Real → Real} {m : Nat}
    (hu : ∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x → HasDerivAt u (v x) x)
    (hdd : ∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x → GDerivAt x cs es)
    (hmin : ∀ ns : List (Real → Real), GProperRel u ns → cs.length ≤ ns.length)
    (hrel : GEvRel u cs)
    (hcs : cs = cs₀ ++ [cd]) (hes : es = es₀ ++ [ed])
    (hlen0 : cs₀.length = m + 1) (hlenes : es₀.length = m + 1)
    (hcd1 : cs₀[m]? = some cd1) (hed1 : es₀[m]? = some ed1) :
    EvZeroF (fun x => cd x * (ed1 x + v x * (natMul (m + 1) 1 * cd x)) - ed x * cd1 x) := by
  -- shapes
  have hlen : cs.length = m + 2 := by rw [hcs]; simp [hlen0]
  have hlenE : es.length = m + 2 := by rw [hes]; simp [hlenes]
  have hcsIdx : cs[m + 1]? = some cd := by
    rw [hcs, List.getElem?_append_right (by omega), hlen0]; simp
  have hesTop : es[m + 1]? = some ed := by
    rw [hes, List.getElem?_append_right (by omega), hlenes]; simp
  have hesIdx : es[m]? = some ed1 := by
    rw [hes, List.getElem?_append_left (by omega)]; exact hed1
  -- the derivative is a relation of the same length, and splits
  have hdrel : GEvRel u (gdrel v cs es) := gEvRel_gdrel hu hdd hrel
  have hdlen : (gdrel v cs es).length = m + 2 := by
    rw [gdrel_length (by rw [hlen, hlenE]), hlen]
  obtain ⟨ds₀, dtop, hsplit, hds0⟩ := split_last (gdrel v cs es) (m + 1) hdlen
  -- the two entries the identity needs
  obtain ⟨bt, hbt, hbtval⟩ := gdrel_getElem_top (v := v) hesTop hlen
  have hdtop : dtop = bt := by
    have : (gdrel v cs es)[m + 1]? = some dtop := by
      rw [hsplit, List.getElem?_append_right (by omega), hds0]; simp
    rw [this] at hbt; exact Option.some_inj.mp hbt
  obtain ⟨b', hb', hb'val⟩ := gdrel_getElem (v := v) hesIdx hcsIdx
  have hds0Idx : ds₀[m]? = some b' := by
    rw [← hb', hsplit, List.getElem?_append_left (by omega)]
  -- cancel the top, then let minimality kill every remaining coefficient
  have hgs : GEvRel u (gscaleSub cd dtop cs₀ ds₀) :=
    gcancel_top (by rw [hlen0, hds0]) (hcs ▸ hrel) (hsplit ▸ hdrel)
  have hgslen : (gscaleSub cd dtop cs₀ ds₀).length = m + 1 := by
    rw [gscaleSub_length cd dtop cs₀ ds₀ (by rw [hlen0, hds0]), hlen0]
  have hentry := gscaleSub_getElem cd dtop cs₀ ds₀ m cd1 b' hcd1 hds0Idx
  have hall := all_gcoeffs_evZero_of_shorter' hmin hgs (by omega)
  refine evZeroF_congr (hall _ (List.mem_of_getElem? hentry)) (fun x => ?_)
  show cd x * b' x - dtop x * cd1 x = _
  rw [hb'val x, hdtop, hbtval x]

end MachLib
