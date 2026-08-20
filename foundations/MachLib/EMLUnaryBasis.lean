import MachLib.EMLDepthTameness

/-!
# A unary decoder for `exp` and `log`

The EML node is binary: `eml a b ↦ exp(a) − log(b)`. This module records that a *single unary*
function built from it already carries both primitives, on `(0, ∞)`.

Take

```
    F(x) = eml(x, 1/x) = exp x − log (1/x) = exp x + log x
```

and form the **multiplicative finite difference**

```
    Δₙ F(x) = F(n·x) − F(x) − log n
```

The logarithm cancels *exactly*, because `log` turns dilation into translation:
`log(n·x) = log n + log x`, and the `− log n` removes what is left. So `Δₙ F(x) = exp(n x) − exp x`,
a pure exponential difference — the logarithmic component has been annihilated by a discrete
operator rather than by an estimate.

Two scales then recover everything. With `y = exp x`:

```
    Δ₂F = y² − y        Δ₃F = y³ − y        Δ₃F / Δ₂F − 1 = y
```

and `log x = F(x) − exp x`. So `F`, dilation by `2` and `3`, and field operations suffice to
reconstruct both `exp` and `log` on the positive reals.

**Why more than one scale.** On the domain that matters — `x > 0`, hence `y = exp x > 1` — the
polynomial `Pₙ(y) = yⁿ − y` has `Pₙ′(y) = n·y^(n−1) − 1 > 0` and is **injective**, so a single scale
already *determines* `y`. What it does not give is a *rational* formula: inverting `yⁿ − y = t` is
algebraic of degree `n`. Determinacy and rational recoverability are different properties, and only
the second is at issue here.

**One scale is not rationally sufficient; some two-scale pairs are.** `(2,3)` works because
`y³ − y = (y² − y)(y + 1)`. `(2,4)` also works, by a *different* elimination: `P₄/P₂ = 1 + y + y²`,
and subtracting `P₂ = y² − y` leaves `2y + 1`. Whether *every* pair of distinct scales works is
**open**; the criterion is a clean algebra question about when `ℝ(Pₘ, Pₙ) = ℝ(y)`, and it is
independent of EML.

**Scope.** Stated for the *functions*, on `(0, ∞)`. Nothing here claims `F` is cheap as a tree: its
right child computes `1/x`, and `d(1/x) = 4` is recorded elsewhere, so `F` itself is not a low-depth
object. Whether `F` is a genuine *basis* — every EML node recoverable from unary `F` data — is a
separate question and is not addressed here.
-/

namespace MachLib

open Real

/-- `F(x) = exp x + log x`, the value of `eml(x, 1/x)` on `(0, ∞)`. -/
noncomputable def Fbasis (x : Real) : Real := exp x + log x

/-- `a / b = c` from `a = b · c`. -/
private theorem div_of_eq_mul {a b c : Real} (hb : b ≠ 0) (h : a = b * c) : a / b = c := by
  rw [div_def a b hb, h]
  have e : b * c * (1 / b) = c * (b * (1 / b)) := by mach_mpoly [b, c, (1 : Real) / b]
  rw [e, mul_inv b hb]; mach_ring

/-- **The dilation difference annihilates the logarithm.**

`Δₙ F(x) = exp (n x) − exp x`, exactly — no error term, no ray, no hypothesis beyond positivity.
This is the whole mechanism: `log` is a cocycle for dilation, so a dilation difference kills it. -/
theorem dilation_diff (n x : Real) (hn : 0 < n) (hx : 0 < x) :
    Fbasis (n * x) - Fbasis x - log n = exp (n * x) - exp x := by
  unfold Fbasis
  rw [log_mul hn hx]
  mach_mpoly [exp (n * x), exp x, log n, log x]

/-- **`log` is recovered from `F` and `exp`.** Immediate, and recorded because it is half the
decoder. -/
theorem decoder_log (x : Real) : Fbasis x - exp x = log x := by
  unfold Fbasis; mach_mpoly [exp x, log x]

/-- **`exp` is recovered from `F` at three scales, rationally.**

```
    (F(3x) − F(x) − log 3) / (F(2x) − F(x) − log 2)  −  1  =  exp x
```

The denominator is nonzero because `x > 0` forces `exp x > 1`. -/
theorem decoder_exp (x : Real) (hx : 0 < x) :
    (Fbasis ((1 + 1 + 1) * x) - Fbasis x - log (1 + 1 + 1))
      / (Fbasis ((1 + 1) * x) - Fbasis x - log (1 + 1)) - 1 = exp x := by
  have h2p : (0 : Real) < 1 + 1 := add_pos zero_lt_one_ax zero_lt_one_ax
  have h3p : (0 : Real) < 1 + 1 + 1 := add_pos h2p zero_lt_one_ax
  rw [dilation_diff (1 + 1 + 1) x h3p hx, dilation_diff (1 + 1) x h2p hx]
  have e2 : exp ((1 + 1) * x) = exp x * exp x := by
    have hx2 : (1 + 1) * x = x + x := by mach_ring
    rw [hx2, exp_add]
  have e3 : exp ((1 + 1 + 1) * x) = exp x * exp x * exp x := by
    have hx3 : (1 + 1 + 1) * x = x + x + x := by mach_ring
    rw [hx3, exp_add, exp_add]
  rw [e2, e3]
  have hy : 1 < exp x := one_lt_exp hx
  have hy0 : (0 : Real) < exp x := lt_trans_ax zero_lt_one_ax hy
  have hy1 : (0 : Real) < exp x - 1 := by
    have v := add_lt_add_left hy (-1 : Real)
    have l : (-1 : Real) + 1 = 0 := by mach_ring
    have r : (-1 : Real) + exp x = exp x - 1 := by mach_ring
    rw [l, r] at v; exact v
  have hne : exp x * exp x - exp x ≠ 0 := by
    refine ne_of_gt ?_
    have hp : (0 : Real) < exp x * (exp x - 1) := mul_pos hy0 hy1
    have e : exp x * (exp x - 1) = exp x * exp x - exp x := by mach_mpoly [exp x]
    rw [e] at hp; exact hp
  have hfac : exp x * exp x * exp x - exp x
      = (exp x * exp x - exp x) * (exp x + 1) := by mach_mpoly [exp x]
  rw [div_of_eq_mul hne hfac]
  mach_ring

/-- **The decoder, both halves.** From the values of `F` at `x`, `2x` and `3x` alone, both
primitives are recovered on `(0, ∞)`. -/
theorem unary_decoder (x : Real) (hx : 0 < x) :
    ((Fbasis ((1 + 1 + 1) * x) - Fbasis x - log (1 + 1 + 1))
        / (Fbasis ((1 + 1) * x) - Fbasis x - log (1 + 1)) - 1 = exp x)
    ∧ (Fbasis x - ((Fbasis ((1 + 1 + 1) * x) - Fbasis x - log (1 + 1 + 1))
        / (Fbasis ((1 + 1) * x) - Fbasis x - log (1 + 1)) - 1) = log x) := by
  have he := decoder_exp x hx
  exact ⟨he, by rw [he]; exact decoder_log x⟩


/-! ## The shallow dilation calculus

`Δₙ f(x) = f(n x) − f(x)`. Applied to the five closed forms of depth `≤ 1`
(`depth_le_one_classification`) it produces a **rigid signature**:

| form | `Δₙ` |
| --- | --- |
| `α` | `0` |
| `x` | `(n − 1)·x` |
| `c − log x` | `−log n` |
| `exp x − d` | `exp(n x) − exp x` |
| `exp x − log x` | `exp(n x) − exp x − log n` |

Five syntactic classes, five distinct shapes — and the separation is *exact*, not asymptotic. Note
that `α` and `c − log x` both give something constant in `x`, but the first gives `0` for every `n`
while the second gives `−log n ≠ 0` as soon as `n > 1`. So a single non-trivial scale already tells
them apart.

**This is a different species of invariant from everything else in the corpus.** Every depth
argument so far has the shape *syntax ⟹ growth envelope*, and concludes by comparing magnitudes.
This one has the shape *syntax ⟹ exact annihilation identity*, and concludes by comparing algebraic
form. Whether it yields exclusions is open; that it is a different mechanism is not.

**And it has a proved blind spot** — see `dilation_blind_to_translation` below. -/

/-- **The dilation calculus at depth ≤ 1.** Five forms in, five shapes out. -/
theorem dilation_depth_le_one (t : EMLTree) (ht : t.depth ≤ 1) (n : Real) (hn : 0 < n) :
    (∀ x : Real, 0 < x → t.eval (n * x) - t.eval x = 0)
    ∨ (∀ x : Real, 0 < x → t.eval (n * x) - t.eval x = (n - 1) * x)
    ∨ (∀ x : Real, 0 < x → t.eval (n * x) - t.eval x = -log n)
    ∨ (∀ x : Real, 0 < x → t.eval (n * x) - t.eval x = exp (n * x) - exp x)
    ∨ (∀ x : Real, 0 < x → t.eval (n * x) - t.eval x = exp (n * x) - exp x - log n) := by
  rcases depth_le_one_classification t ht with ⟨α, hα⟩ | hv | ⟨c, _, hc⟩ | ⟨d, hd⟩ | hcl
  · refine Or.inl ?_
    intro x hx
    rw [hα (n * x) (mul_pos hn hx), hα x hx]; mach_ring
  · refine Or.inr (Or.inl ?_)
    intro x hx
    rw [hv (n * x) (mul_pos hn hx), hv x hx]; mach_mpoly [n, x]
  · refine Or.inr (Or.inr (Or.inl ?_))
    intro x hx
    rw [hc (n * x) (mul_pos hn hx), hc x hx, log_mul hn hx]
    mach_mpoly [c, log n, log x]
  · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
    intro x hx
    rw [hd (n * x) (mul_pos hn hx), hd x hx]
    mach_mpoly [exp (n * x), exp x, d]
  · refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
    intro x hx
    rw [hcl (n * x) (mul_pos hn hx), hcl x hx, log_mul hn hx]
    mach_mpoly [exp (n * x), exp x, log n, log x]

/-- **The dilation operator is blind to translation.**

`Δₙ (x + c) = (n − 1)·x`, with **no dependence on `c` whatsoever**. So the new instrument cannot
distinguish `x + c` from `x`, and in particular cannot settle the negative-translation obligation
`NegativeTranslationGrowingLeft` — the very thing it might have been hoped to reach.

Recorded as a theorem rather than a remark because a tool's blind spot should be proved, not
suspected: dilation and the mirror band are different research threads and this says so formally. -/
theorem dilation_blind_to_translation (c n x : Real) :
    ((n * x) + c) - (x + c) = (n - 1) * x := by
  mach_mpoly [n, x, c]



/-! ## `L_F` — an explicit language over the single function `F`

"Basis" needs a type before it can be a theorem, so here is the object the claim is about.

`L_F` is constants, the variable, the four field operations, and one unary symbol `F`. Nothing else
— in particular **no conditional and no sign test**, which is what makes the totalised branch a real
obstruction rather than a bookkeeping detail. -/

/-- Terms over `F`: constants, `x`, field operations, and `u ↦ F(u)`. -/
inductive FTerm where
  | const : Real → FTerm
  | var   : FTerm
  | add   : FTerm → FTerm → FTerm
  | sub   : FTerm → FTerm → FTerm
  | mul   : FTerm → FTerm → FTerm
  | div   : FTerm → FTerm → FTerm
  | F     : FTerm → FTerm

namespace FTerm

/-- Evaluation. `F` is the one non-field symbol, and it means `Fbasis`. -/
noncomputable def eval : FTerm → Real → Real
  | const c, _ => c
  | var,     x => x
  | add a b, x => eval a x + eval b x
  | sub a b, x => eval a x - eval b x
  | mul a b, x => eval a x * eval b x
  | div a b, x => eval a x / eval b x
  | F a,     x => Fbasis (eval a x)

/-- The exponential decoder, **as a term of the language**. -/
noncomputable def EF (u : FTerm) : FTerm :=
  sub (div (sub (sub (F (mul (const (1 + 1 + 1)) u)) (F u)) (const (log (1 + 1 + 1))))
           (sub (sub (F (mul (const (1 + 1)) u)) (F u)) (const (log (1 + 1)))))
      (const 1)

/-- The logarithm decoder, as a term. -/
noncomputable def LF (u : FTerm) : FTerm := sub (F u) (EF u)

/-- `EF u` computes `exp` of whatever `u` computes, wherever that is positive. -/
theorem EF_eval (u : FTerm) (x : Real) (h : 0 < eval u x) :
    eval (EF u) x = exp (eval u x) := by
  show (Fbasis ((1 + 1 + 1) * eval u x) - Fbasis (eval u x) - log (1 + 1 + 1))
      / (Fbasis ((1 + 1) * eval u x) - Fbasis (eval u x) - log (1 + 1)) - 1
      = exp (eval u x)
  exact decoder_exp (eval u x) h

/-- `LF u` computes `log` of whatever `u` computes, wherever that is positive. -/
theorem LF_eval (u : FTerm) (x : Real) (h : 0 < eval u x) :
    eval (LF u) x = log (eval u x) := by
  show Fbasis (eval u x) - eval (EF u) x = log (eval u x)
  rw [EF_eval u x h]
  exact decoder_log (eval u x)

end FTerm

/-- **The positive-internal fragment.** Every `eml` node in `t` has *both children* strictly
positive throughout `D`.

Stated structurally rather than as "the function is positive", because that is what the decoder
actually needs: `EF` requires the left child positive and `LF` the right, at each node. -/
def PositiveInternal (D : Real → Prop) : EMLTree → Prop
  | .const _ => True
  | .var     => True
  | .eml a b => PositiveInternal D a ∧ PositiveInternal D b
                ∧ (∀ x : Real, D x → 0 < a.eval x) ∧ (∀ x : Real, D x → 0 < b.eval x)

/-- **The positive-fragment unary basis theorem.**

Every EML tree whose internal arguments stay positive on `D` is computed on `D` by a term of `L_F` —
that is, by constants, `x`, field operations, and the single unary function `F`.

The induction is one line at each node: `eml a b ↦ EF(â) − LF(b̂)`. -/
theorem positive_fragment_F_representable (D : Real → Prop) :
    ∀ t : EMLTree, PositiveInternal D t →
      ∃ T : FTerm, ∀ x : Real, D x → FTerm.eval T x = t.eval x := by
  intro t
  induction t with
  | const c => intro _; exact ⟨FTerm.const c, fun _ _ => rfl⟩
  | var => intro _; exact ⟨FTerm.var, fun _ _ => rfl⟩
  | eml a b iha ihb =>
      intro h
      obtain ⟨hpa, hpb, hposa, hposb⟩ := h
      obtain ⟨Ta, hTa⟩ := iha hpa
      obtain ⟨Tb, hTb⟩ := ihb hpb
      refine ⟨FTerm.sub (FTerm.EF Ta) (FTerm.LF Tb), ?_⟩
      intro x hx
      have hA : 0 < FTerm.eval Ta x := by rw [hTa x hx]; exact hposa x hx
      have hB : 0 < FTerm.eval Tb x := by rw [hTb x hx]; exact hposb x hx
      show FTerm.eval (FTerm.EF Ta) x - FTerm.eval (FTerm.LF Tb) x
          = exp (a.eval x) - log (b.eval x)
      rw [FTerm.EF_eval Ta x hA, FTerm.LF_eval Tb x hB, hTa x hx, hTb x hx]



/-! ## Weakening positivity: the two children are not symmetric

The fragment above requires *both* children of every node positive. Probing the two requirements
separately shows they are not the same kind of constraint. -/

/-- The exponential decoder after a shift: `exp u = exp(−C)·exp(u + C)`. -/
noncomputable def FTerm.EFshift (C : Real) (u : FTerm) : FTerm :=
  FTerm.mul (FTerm.const (exp (-C))) (FTerm.EF (FTerm.add u (FTerm.const C)))

/-- **The left child needs only a known lower bound, not positivity.**

`exp` is perfectly well defined for negative arguments; it was the *decoder* that wanted positivity,
and a shift removes that. So obstruction (A) is a limitation of the instrument and is repairable. -/
theorem FTerm.EFshift_eval (C : Real) (u : FTerm) (x : Real) (h : 0 < FTerm.eval u x + C) :
    FTerm.eval (FTerm.EFshift C u) x = exp (FTerm.eval u x) := by
  show exp (-C) * FTerm.eval (FTerm.EF (FTerm.add u (FTerm.const C))) x = exp (FTerm.eval u x)
  have hval : FTerm.eval (FTerm.add u (FTerm.const C)) x = FTerm.eval u x + C := rfl
  rw [FTerm.EF_eval _ x (by rw [hval]; exact h), hval, ← exp_add]
  have e : -C + (FTerm.eval u x + C) = FTerm.eval u x := by mach_mpoly [C, FTerm.eval u x]
  rw [e]

/-! ### The right child is different — and the difference is *evidence*, not a theorem

For the right child there is no shift to apply. The node computes `log₀(B x)`, which is `log (B x)`
where `B x > 0` and `0` where `B x ≤ 0` — a genuinely piecewise operation — and `L_F` has constants,
`x`, four field operations and `F`, with **no conditional and no sign test**.

**That is evidence of an obstruction, and it is deliberately not claimed as a non-representability
result.** Two reasons. Absence of an explicit conditional does not prove a piecewise function
undefinable: compositional languages can synthesise branch-like behaviour indirectly. And `F` itself
descends from a totalised construction, so some branch information may already be latent in the
primitive. Turning this into an impossibility theorem would require an invariant that every `L_F`
term satisfies and `log₀` violates — continuity or analyticity across the sign change is the obvious
candidate. None is offered here, so obstruction (B) stands as a hypothesis.

Obstruction (C), a child that *changes* sign, is (B) made unavoidable on any domain where the
crossing occurs. But on a domain where the sign is **stable**, the branch can be chosen once by the
translator rather than at runtime — which is the next section, and which turns out to close. -/

/-! ## Global versus eventual representation

The positive fragment is a *global* statement. The interesting weakening is not to drop positivity
but to replace it by **sign stability**: on a domain where each internal argument keeps one sign, the
*translator* can pick the branch once, and the emitted term is ordinary and branch-free. No runtime
selector is needed, so the obstruction above does not apply.

The trichotomy is kept **strict** on purpose. "Eventually non-negative" is not the same as
"eventually positive or identically zero", and `EF`/`LF` consume strict positivity — smoothing that
distinction is exactly how a false lemma would enter. -/

/-- On `D`, a function is strictly positive, strictly negative, or identically zero. -/
def SignStable (D : Real → Prop) (f : Real → Real) : Prop :=
  (∀ x : Real, D x → 0 < f x) ∨ (∀ x : Real, D x → f x < 0) ∨ (∀ x : Real, D x → f x = 0)

/-- Every `eml` node's two children are sign-stable on `D`. -/
def StableInternalSigns (D : Real → Prop) : EMLTree → Prop
  | .const _ => True
  | .var     => True
  | .eml a b => StableInternalSigns D a ∧ StableInternalSigns D b
                ∧ SignStable D a.eval ∧ SignStable D b.eval

/-- `exp a = 1 / exp (−a)`. The route for a left child that is stably *negative*. -/
private theorem exp_eq_inv_exp_neg (a : Real) : exp a = 1 / exp (-a) := by
  refine (div_of_eq_mul (ne_of_gt (exp_pos (-a))) ?_).symm
  rw [← exp_add]
  have e : -a + a = 0 := by mach_ring
  rw [e, exp_zero]

/-- **Stable internal signs suffice.** Every EML tree whose internal arguments keep one sign on `D`
is computed on `D` by a branch-free term of `L_F`.

Six cases at each node, and the totalisation collapses two of them:

| left child | term | right child | term |
| --- | --- | --- | --- |
| `> 0` | `EF â` | `> 0` | `LF b̂` |
| `< 0` | `1 / EF(−â)` | `< 0` | `0` |
| `= 0` | `1` | `= 0` | `0` |

The right child's two non-positive cases give the same term because `log₀` is `0` on both — there is
nothing to decode, which is the totalisation *helping* for once. -/
theorem stable_signs_F_representable (D : Real → Prop) :
    ∀ t : EMLTree, StableInternalSigns D t →
      ∃ T : FTerm, ∀ x : Real, D x → FTerm.eval T x = t.eval x := by
  intro t
  induction t with
  | const c => intro _; exact ⟨FTerm.const c, fun _ _ => rfl⟩
  | var => intro _; exact ⟨FTerm.var, fun _ _ => rfl⟩
  | eml a b iha ihb =>
      intro h
      obtain ⟨hpa, hpb, hsa, hsb⟩ := h
      obtain ⟨Ta, hTa⟩ := iha hpa
      obtain ⟨Tb, hTb⟩ := ihb hpb
      -- the left half: three sign cases, three terms
      obtain ⟨LT, hLT⟩ : ∃ LT : FTerm, ∀ x : Real, D x → FTerm.eval LT x = exp (a.eval x) := by
        rcases hsa with hp | hn | hz
        · exact ⟨FTerm.EF Ta, fun x hx => by
            rw [FTerm.EF_eval Ta x (by rw [hTa x hx]; exact hp x hx), hTa x hx]⟩
        · refine ⟨FTerm.div (FTerm.const 1) (FTerm.EF (FTerm.sub (FTerm.const 0) Ta)), ?_⟩
          intro x hx
          have hneg : FTerm.eval (FTerm.sub (FTerm.const 0) Ta) x = -(a.eval x) := by
            show (0 : Real) - FTerm.eval Ta x = -(a.eval x)
            rw [hTa x hx]; mach_ring
          have hpos : 0 < FTerm.eval (FTerm.sub (FTerm.const 0) Ta) x := by
            rw [hneg]
            have v := add_lt_add_left (hn x hx) (-(a.eval x))
            have l : -(a.eval x) + a.eval x = 0 := by mach_ring
            have r : -(a.eval x) + 0 = -(a.eval x) := by mach_ring
            rw [l, r] at v; exact v
          show (1 : Real) / FTerm.eval (FTerm.EF (FTerm.sub (FTerm.const 0) Ta)) x = exp (a.eval x)
          rw [FTerm.EF_eval _ x hpos, hneg, ← exp_eq_inv_exp_neg]
        · exact ⟨FTerm.const 1, fun x hx => by rw [hz x hx, exp_zero]; rfl⟩
      -- the right half: positive decodes, both non-positive cases are `0`
      obtain ⟨RT, hRT⟩ : ∃ RT : FTerm, ∀ x : Real, D x → FTerm.eval RT x = log (b.eval x) := by
        rcases hsb with hp | hn | hz
        · exact ⟨FTerm.LF Tb, fun x hx => by
            rw [FTerm.LF_eval Tb x (by rw [hTb x hx]; exact hp x hx), hTb x hx]⟩
        · exact ⟨FTerm.const 0, fun x hx => by
            show (0 : Real) = log (b.eval x)
            rw [log_nonpos (le_of_lt (hn x hx))]⟩
        · exact ⟨FTerm.const 0, fun x hx => by
            show (0 : Real) = log (b.eval x)
            rw [hz x hx, log_nonpos (le_refl 0)]⟩
      exact ⟨FTerm.sub LT RT, fun x hx => by
        show FTerm.eval LT x - FTerm.eval RT x = exp (a.eval x) - log (b.eval x)
        rw [hLT x hx, hRT x hx]⟩



/-! ## What `EvSign` actually supplies, and what it does not

`EvSign f` is `(eventually 0 < f) ∨ (eventually f ≤ 0)`. Comparing it to what the translation
consumes, child by child, locates the gap exactly:

- **Right child: `EvSign` is enough, on the nose.** `log₀` is `0` on *both* non-positive cases, so
  the two collapse and `f x ≤ 0` suffices. No strictness is needed.
- **Left child: `EvSign` is not enough.** `exp` needs `a > 0` for `EF`, or `a < 0` *strictly* for
  `1/EF(−a)` — at a point where `a = 0` the denominator `exp(2·0) − exp(0)` vanishes — or a lower
  bound for `EFshift`. `f x ≤ 0` distinguishes none of these.

So the missing statement is precisely: **a term that is eventually non-positive is eventually
*strictly* negative, or eventually zero.** That is strictly stronger than `EvSign` and is not
implied by it. Whether it holds for EML terms is open, and it is a sharper question than
`SignHardCase` because it asks for a trichotomy where `SignHardCase` delivers a dichotomy.

The refinement below weakens the right-hand hypothesis accordingly, so the remaining gap is
localised in one place instead of two. -/

/-- The right child's requirement, in `EvSign`'s exact shape: positive, or non-positive. -/
def SignStableRight (D : Real → Prop) (f : Real → Real) : Prop :=
  (∀ x : Real, D x → 0 < f x) ∨ (∀ x : Real, D x → f x ≤ 0)

/-- Left children sign-stable (strict trichotomy); right children merely `EvSign`-stable. -/
def StableSignsRefined (D : Real → Prop) : EMLTree → Prop
  | .const _ => True
  | .var     => True
  | .eml a b => StableSignsRefined D a ∧ StableSignsRefined D b
                ∧ SignStable D a.eval ∧ SignStableRight D b.eval

/-- **The refined stable-sign theorem.** The right-hand hypothesis is now exactly what `EvSign`
delivers; only the left-hand one asks for more. -/
theorem stable_signs_refined_F_representable (D : Real → Prop) :
    ∀ t : EMLTree, StableSignsRefined D t →
      ∃ T : FTerm, ∀ x : Real, D x → FTerm.eval T x = t.eval x := by
  intro t
  induction t with
  | const c => intro _; exact ⟨FTerm.const c, fun _ _ => rfl⟩
  | var => intro _; exact ⟨FTerm.var, fun _ _ => rfl⟩
  | eml a b iha ihb =>
      intro h
      obtain ⟨hpa, hpb, hsa, hsb⟩ := h
      obtain ⟨Ta, hTa⟩ := iha hpa
      obtain ⟨Tb, hTb⟩ := ihb hpb
      obtain ⟨LT, hLT⟩ : ∃ LT : FTerm, ∀ x : Real, D x → FTerm.eval LT x = exp (a.eval x) := by
        rcases hsa with hp | hn | hz
        · exact ⟨FTerm.EF Ta, fun x hx => by
            rw [FTerm.EF_eval Ta x (by rw [hTa x hx]; exact hp x hx), hTa x hx]⟩
        · refine ⟨FTerm.div (FTerm.const 1) (FTerm.EF (FTerm.sub (FTerm.const 0) Ta)), ?_⟩
          intro x hx
          have hneg : FTerm.eval (FTerm.sub (FTerm.const 0) Ta) x = -(a.eval x) := by
            show (0 : Real) - FTerm.eval Ta x = -(a.eval x)
            rw [hTa x hx]; mach_ring
          have hpos : 0 < FTerm.eval (FTerm.sub (FTerm.const 0) Ta) x := by
            rw [hneg]
            have v := add_lt_add_left (hn x hx) (-(a.eval x))
            have l : -(a.eval x) + a.eval x = 0 := by mach_ring
            have r : -(a.eval x) + 0 = -(a.eval x) := by mach_ring
            rw [l, r] at v; exact v
          show (1 : Real) / FTerm.eval (FTerm.EF (FTerm.sub (FTerm.const 0) Ta)) x = exp (a.eval x)
          rw [FTerm.EF_eval _ x hpos, hneg, ← exp_eq_inv_exp_neg]
        · exact ⟨FTerm.const 1, fun x hx => by rw [hz x hx, exp_zero]; rfl⟩
      obtain ⟨RT, hRT⟩ : ∃ RT : FTerm, ∀ x : Real, D x → FTerm.eval RT x = log (b.eval x) := by
        rcases hsb with hp | hnp
        · exact ⟨FTerm.LF Tb, fun x hx => by
            rw [FTerm.LF_eval Tb x (by rw [hTb x hx]; exact hp x hx), hTb x hx]⟩
        · -- both non-positive cases at once: `log₀` is `0` on all of them
          exact ⟨FTerm.const 0, fun x hx => by
            show (0 : Real) = log (b.eval x)
            rw [log_nonpos (hnp x hx)]⟩
      exact ⟨FTerm.sub LT RT, fun x hx => by
        show FTerm.eval LT x - FTerm.eval RT x = exp (a.eval x) - log (b.eval x)
        rw [hLT x hx, hRT x hx]⟩


end MachLib
