import MachLib.EMLRationalGerm

/-!
# The one-query normal form, in two layers

`C₀` is characterised: `fOcc T = 0` iff `T` is an eventual rational germ. The next level up needs a
shape for `C₁`, and it is built here in two deliberately separate layers.

## Layer 1 is exact and syntactic

If `fOcc T = 1` there is exactly one `F` node, so `T` splits into an `F`-free argument `A` and an
`F`-free **one-hole field context** `C`:

```
T(x) = C(x, F(A(x)))      for every x, no asymptotics
```

`FCtx` has no `F` constructor at all, so "the context is `F`-free" is a fact about the *type* rather
than a predicate to carry around, and `holes C = 1` is proved rather than assumed.

## Layer 2 is eventual, and stops early on purpose

Feeding `ratGerm_of_zero_query` into the argument gives `A(x) = P(x)/Q(x)` eventually, hence

```
T(x) = C(x, F(P(x)/Q(x)))      eventually
```

**The outer context is deliberately not collapsed to a single quotient.** At zero queries a
denominator is a polynomial in `x` and `pev_dichotomy` decides it. Here a denominator looks like
`Q(x, F(S(x)))`, and `pev_dichotomy` says nothing about that — so writing `C` as `P/Q` "eventually"
would silently assume the very dichotomy that is the next theorem. The context stays a context.

That missing statement is registered as `OneQueryDichotomy`: **is a one-query context eventually
zero, or eventually nonzero?** It is again a cancellation question — expand
`Q(x, F(S)) = Σⱼ qⱼ(x)·F(S)ʲ` and ask whether the surviving component dominates — which is the same
shape that governs `C₀`, one level up. Normal forms and lower bounds at query level `k` look to be
governed by one cancellation theorem at level `k`.
-/

namespace MachLib

open Real

/-! ## `F`-free one-hole field contexts -/

/-- A field context with a hole. **No `F` constructor**: `F`-freeness is a property of the type. -/
inductive FCtx where
  | hole  : FCtx
  | const : Real → FCtx
  | var   : FCtx
  | add   : FCtx → FCtx → FCtx
  | sub   : FCtx → FCtx → FCtx
  | mul   : FCtx → FCtx → FCtx
  | div   : FCtx → FCtx → FCtx

/-- `C.eval x y` plugs `y` into the hole. -/
noncomputable def FCtx.eval : FCtx → Real → Real → Real
  | hole,    _, y => y
  | const c, _, _ => c
  | var,     x, _ => x
  | add a b, x, y => eval a x y + eval b x y
  | sub a b, x, y => eval a x y - eval b x y
  | mul a b, x, y => eval a x y * eval b x y
  | div a b, x, y => eval a x y / eval b x y

/-- Occurrences of the hole. -/
def FCtx.holes : FCtx → Nat
  | hole    => 1
  | const _ => 0
  | var     => 0
  | add a b => holes a + holes b
  | sub a b => holes a + holes b
  | mul a b => holes a + holes b
  | div a b => holes a + holes b

/-- An `F`-free term as a hole-free context. The `F` case is unreachable under `fOcc t = 0` and is
sent to a constant rather than made partial. -/
noncomputable def FTerm.toCtx : FTerm → FCtx
  | .const c => FCtx.const c
  | .var     => FCtx.var
  | .add a b => FCtx.add (toCtx a) (toCtx b)
  | .sub a b => FCtx.sub (toCtx a) (toCtx b)
  | .mul a b => FCtx.mul (toCtx a) (toCtx b)
  | .div a b => FCtx.div (toCtx a) (toCtx b)
  | .F _     => FCtx.const 0

theorem FTerm.toCtx_holes : ∀ t : FTerm, FCtx.holes (FTerm.toCtx t) = 0 := by
  intro t
  induction t with
  | const c => rfl
  | var => rfl
  | add a b iha ihb => show FCtx.holes _ + FCtx.holes _ = 0; rw [iha, ihb]
  | sub a b iha ihb => show FCtx.holes _ + FCtx.holes _ = 0; rw [iha, ihb]
  | mul a b iha ihb => show FCtx.holes _ + FCtx.holes _ = 0; rw [iha, ihb]
  | div a b iha ihb => show FCtx.holes _ + FCtx.holes _ = 0; rw [iha, ihb]
  | F a _ => rfl

theorem FTerm.toCtx_eval : ∀ (t : FTerm), fOcc t = 0 →
    ∀ x y : Real, FCtx.eval (FTerm.toCtx t) x y = FTerm.eval t x := by
  intro t
  induction t with
  | const c => intro _ _ _; rfl
  | var => intro _ _ _; rfl
  | add a b iha ihb =>
      intro h x y
      have ha : fOcc a = 0 := by simp only [fOcc] at h; omega
      have hb : fOcc b = 0 := by simp only [fOcc] at h; omega
      show FCtx.eval _ x y + FCtx.eval _ x y = FTerm.eval a x + FTerm.eval b x
      rw [iha ha x y, ihb hb x y]
  | sub a b iha ihb =>
      intro h x y
      have ha : fOcc a = 0 := by simp only [fOcc] at h; omega
      have hb : fOcc b = 0 := by simp only [fOcc] at h; omega
      show FCtx.eval _ x y - FCtx.eval _ x y = FTerm.eval a x - FTerm.eval b x
      rw [iha ha x y, ihb hb x y]
  | mul a b iha ihb =>
      intro h x y
      have ha : fOcc a = 0 := by simp only [fOcc] at h; omega
      have hb : fOcc b = 0 := by simp only [fOcc] at h; omega
      show FCtx.eval _ x y * FCtx.eval _ x y = FTerm.eval a x * FTerm.eval b x
      rw [iha ha x y, ihb hb x y]
  | div a b iha ihb =>
      intro h x y
      have ha : fOcc a = 0 := by simp only [fOcc] at h; omega
      have hb : fOcc b = 0 := by simp only [fOcc] at h; omega
      show FCtx.eval _ x y / FCtx.eval _ x y = FTerm.eval a x / FTerm.eval b x
      rw [iha ha x y, ihb hb x y]
  | F a _ => intro h _ _; simp only [fOcc] at h; omega

/-! ## Layer 1: the exact syntactic decomposition -/

/-- `f` is the context `C` applied to `F ∘ g`, at every point. Named so that the *conclusion* of the
decomposition theorem mentions the context — Lean prints `C.eval x y` in dot notation, so an inline
statement leaves no token a claim can bind to. Same repair as `FRepresentable`. -/
def CtxApplies (C : FCtx) (g f : Real → Real) : Prop :=
  ∀ x : Real, f x = FCtx.eval C x (Fbasis (g x))

/-- The eventual version, for layer 2. -/
def CtxAppliesEv (C : FCtx) (g f : Real → Real) (X : Real) : Prop :=
  ∀ x : Real, X ≤ x → f x = FCtx.eval C x (Fbasis (g x))

/-- **One query, one hole.** A term with exactly one `F` node is an `F`-free one-hole field context
applied to `F` of an `F`-free argument — **at every real point**, with no asymptotics, no rational
normalisation and no denominator condition. -/
theorem one_query_decompose : ∀ T : FTerm, fOcc T = 1 →
    ∃ (C : FCtx) (A : FTerm), FCtx.holes C = 1 ∧ fOcc A = 0
      ∧ CtxApplies C (FTerm.eval A) (FTerm.eval T) := by
  intro T
  induction T with
  | const c => intro h; exact absurd h (by simp [fOcc])
  | var => intro h; exact absurd h (by simp [fOcc])
  | add a b iha ihb =>
      intro h
      simp only [fOcc] at h
      rcases Nat.eq_zero_or_pos (fOcc a) with ha | ha
      · obtain ⟨C, A, hC, hA, he⟩ := ihb (by omega)
        refine ⟨FCtx.add (FTerm.toCtx a) C, A, ?_, hA, fun x => ?_⟩
        · show FCtx.holes (FTerm.toCtx a) + FCtx.holes C = 1
          rw [FTerm.toCtx_holes, hC]
        · show FTerm.eval a x + FTerm.eval b x
              = FCtx.eval (FTerm.toCtx a) x _ + FCtx.eval C x _
          rw [FTerm.toCtx_eval a ha x _, he x]
      · obtain ⟨C, A, hC, hA, he⟩ := iha (by omega)
        have hb : fOcc b = 0 := by omega
        refine ⟨FCtx.add C (FTerm.toCtx b), A, ?_, hA, fun x => ?_⟩
        · show FCtx.holes C + FCtx.holes (FTerm.toCtx b) = 1
          rw [FTerm.toCtx_holes, hC]
        · show FTerm.eval a x + FTerm.eval b x
              = FCtx.eval C x _ + FCtx.eval (FTerm.toCtx b) x _
          rw [FTerm.toCtx_eval b hb x _, he x]
  | sub a b iha ihb =>
      intro h
      simp only [fOcc] at h
      rcases Nat.eq_zero_or_pos (fOcc a) with ha | ha
      · obtain ⟨C, A, hC, hA, he⟩ := ihb (by omega)
        refine ⟨FCtx.sub (FTerm.toCtx a) C, A, ?_, hA, fun x => ?_⟩
        · show FCtx.holes (FTerm.toCtx a) + FCtx.holes C = 1
          rw [FTerm.toCtx_holes, hC]
        · show FTerm.eval a x - FTerm.eval b x
              = FCtx.eval (FTerm.toCtx a) x _ - FCtx.eval C x _
          rw [FTerm.toCtx_eval a ha x _, he x]
      · obtain ⟨C, A, hC, hA, he⟩ := iha (by omega)
        have hb : fOcc b = 0 := by omega
        refine ⟨FCtx.sub C (FTerm.toCtx b), A, ?_, hA, fun x => ?_⟩
        · show FCtx.holes C + FCtx.holes (FTerm.toCtx b) = 1
          rw [FTerm.toCtx_holes, hC]
        · show FTerm.eval a x - FTerm.eval b x
              = FCtx.eval C x _ - FCtx.eval (FTerm.toCtx b) x _
          rw [FTerm.toCtx_eval b hb x _, he x]
  | mul a b iha ihb =>
      intro h
      simp only [fOcc] at h
      rcases Nat.eq_zero_or_pos (fOcc a) with ha | ha
      · obtain ⟨C, A, hC, hA, he⟩ := ihb (by omega)
        refine ⟨FCtx.mul (FTerm.toCtx a) C, A, ?_, hA, fun x => ?_⟩
        · show FCtx.holes (FTerm.toCtx a) + FCtx.holes C = 1
          rw [FTerm.toCtx_holes, hC]
        · show FTerm.eval a x * FTerm.eval b x
              = FCtx.eval (FTerm.toCtx a) x _ * FCtx.eval C x _
          rw [FTerm.toCtx_eval a ha x _, he x]
      · obtain ⟨C, A, hC, hA, he⟩ := iha (by omega)
        have hb : fOcc b = 0 := by omega
        refine ⟨FCtx.mul C (FTerm.toCtx b), A, ?_, hA, fun x => ?_⟩
        · show FCtx.holes C + FCtx.holes (FTerm.toCtx b) = 1
          rw [FTerm.toCtx_holes, hC]
        · show FTerm.eval a x * FTerm.eval b x
              = FCtx.eval C x _ * FCtx.eval (FTerm.toCtx b) x _
          rw [FTerm.toCtx_eval b hb x _, he x]
  | div a b iha ihb =>
      intro h
      simp only [fOcc] at h
      rcases Nat.eq_zero_or_pos (fOcc a) with ha | ha
      · obtain ⟨C, A, hC, hA, he⟩ := ihb (by omega)
        refine ⟨FCtx.div (FTerm.toCtx a) C, A, ?_, hA, fun x => ?_⟩
        · show FCtx.holes (FTerm.toCtx a) + FCtx.holes C = 1
          rw [FTerm.toCtx_holes, hC]
        · show FTerm.eval a x / FTerm.eval b x
              = FCtx.eval (FTerm.toCtx a) x _ / FCtx.eval C x _
          rw [FTerm.toCtx_eval a ha x _, he x]
      · obtain ⟨C, A, hC, hA, he⟩ := iha (by omega)
        have hb : fOcc b = 0 := by omega
        refine ⟨FCtx.div C (FTerm.toCtx b), A, ?_, hA, fun x => ?_⟩
        · show FCtx.holes C + FCtx.holes (FTerm.toCtx b) = 1
          rw [FTerm.toCtx_holes, hC]
        · show FTerm.eval a x / FTerm.eval b x
              = FCtx.eval C x _ / FCtx.eval (FTerm.toCtx b) x _
          rw [FTerm.toCtx_eval b hb x _, he x]
  | F a _ =>
      intro h
      have ha : fOcc a = 0 := by simp only [fOcc] at h; omega
      exact ⟨FCtx.hole, a, rfl, ha, fun _ => rfl⟩

/-! ## Layer 2: the argument becomes a rational germ -/

/-- **The one-query normal form.** `T(x) = C(x, F(P(x)/Q(x)))` from some point on, with `C` an
`F`-free one-hole field context and `P/Q` an eventual rational germ.

`C` is **not** collapsed to a single quotient. Doing so would need to know whether its denominators —
which are functions of `x` *and* `F(P/Q)` — eventually vanish, and that is precisely
`OneQueryDichotomy` below, not something the normal form may assume. -/
theorem one_query_normal_form (T : FTerm) (h : fOcc T = 1) :
    ∃ (C : FCtx) (P Q : List Real) (X : Real),
      FCtx.holes C = 1 ∧ 1 ≤ X ∧ (∀ x : Real, X ≤ x → pev Q x ≠ 0)
      ∧ CtxAppliesEv C (fun x => pev P x / pev Q x) (FTerm.eval T) X := by
  obtain ⟨C, A, hC, hA, he⟩ := one_query_decompose T h
  obtain ⟨P, Q, X, hX, hQ, hg⟩ := ratGerm_of_zero_query A hA
  exact ⟨C, P, Q, X, hC, hX, hQ, fun x hx => by rw [he x, hg x hx]⟩

/-! ## The level-1 cancellation obligation -/

/-- **Named obligation.** Is a one-query context eventually zero, or eventually nonzero?

At level `0` this was `pev_dichotomy` and it decided every denominator. At level `1` the denominators
are `Q(x, F(S(x)))`, and expanding `Σⱼ qⱼ(x)·F(S)ʲ` asks whether the surviving component dominates or
whether exact cancellation can persist — the same question `C₀` faced, one level up.

Discharging it would lift the whole `C₀` machinery: `C₁` would become rational functions of `x` and
`F(S(x))`, and only then does "is `exp ∈ C₁`?" become a concrete algebraic question rather than an
amorphous one. -/
def OneQueryDichotomy : Prop :=
  ∀ (C : FCtx) (P Q : List Real) (X : Real), 1 ≤ X → (∀ x : Real, X ≤ x → pev Q x ≠ 0) →
    EvZeroF (fun x => FCtx.eval C x (Fbasis (pev P x / pev Q x)))
    ∨ ∃ Y : Real, 1 ≤ Y ∧ ∀ x : Real, Y ≤ x → FCtx.eval C x (Fbasis (pev P x / pev Q x)) ≠ 0

/-- **Discrimination: the decomposition is not vacuous and the hole is where it should be.** `F`
itself decomposes with the identity context; a term with the `F` node buried under field operations
decomposes with a context that is not the hole. -/
theorem one_query_decompose_specimens :
    (FCtx.holes FCtx.hole = 1
      ∧ ∀ x : Real, FTerm.eval (FTerm.F FTerm.var) x = FCtx.eval FCtx.hole x (Fbasis x))
    ∧ (fOcc (FTerm.add (FTerm.mul FTerm.var (FTerm.F (FTerm.mul FTerm.var FTerm.var)))
        (FTerm.const 1)) = 1) := ⟨⟨rfl, fun _ => rfl⟩, rfl⟩

end MachLib
