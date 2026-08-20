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
theorem div_of_eq_mul {a b c : Real} (hb : b ≠ 0) (h : a = b * c) : a / b = c := by
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

/-- **`f` is computed on `D` by a term of `L_F`.** The property the basis theorems conclude.

Named rather than written out at each theorem so that the *conclusion* mentions the language: a
statement that merely exhibits some function agreeing with `f` says nothing, and the whole content
is that the witness is an `FTerm`. -/
def FRepresentable (D : Real → Prop) (f : Real → Real) : Prop :=
  ∃ T : FTerm, ∀ x : Real, D x → FTerm.eval T x = f x

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
      FRepresentable D t.eval := by
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

**⚠ REFUTED at the end of this file** (`F_unary_basis`, `log_totalised_F_representable`). Read the
paragraph below as the record of a wrong guess that was at least labelled as a guess. The second of
the two reasons given for not claiming it is exactly the reason it is false: `F` *is* a totalised
construction, and `F u − exp u = log₀ u` extracts the branch, unconditionally.

That is evidence of an obstruction, and it is deliberately not claimed as a non-representability
result. Two reasons. Absence of an explicit conditional does not prove a piecewise function
undefinable: compositional languages can synthesise branch-like behaviour indirectly. And `F` itself
descends from a totalised construction, so some branch information may already be latent in the
primitive. Turning this into an impossibility theorem would require an invariant that every `L_F`
term satisfies and `log₀` violates — continuity or analyticity across the sign change is the obvious
candidate. None is offered here, so obstruction (B) stands as a hypothesis.

Obstruction (C), a child that *changes* sign, is (B) made unavoidable on any domain where the
crossing occurs. But on a domain where the sign is **stable**, the branch can be chosen once by the
translator rather than at runtime — which is the next section, and which turns out to close. -/

/-! ## Global versus eventual representation

**⚠ SUBSUMED.** Everything from here to `F_unary_basis` assumes something about signs, and none of
it is needed — the global theorem at the end of the file has no hypothesis at all. It is kept as the
record of the search, and because the intermediate constructions (`EFshift`, `EFupper`) are what
eventually suggested the unconditional one.

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

/-! ## `EvSign` is enough after all — the gap was in the instrument

An earlier version of this file claimed the *left* child needed strictly more than `EvSign`, on the
grounds that none of the three routes then available covers `a x ≤ 0`: `EF` wants `a > 0`,
`1/EF(−a)` wants `a < 0` **strictly** (at `a = 0` the denominator `exp(2·0) − exp(0)` vanishes), and
`EFshift` wants a lower bound.

**That was a gap in the instrument, not in the hypothesis.** There is a fourth route:

`exp a = exp C / exp (C − a)`, available whenever `a < C`

so an *upper* bound decodes exactly as well as a lower one. The left child therefore needs only that
`a` be bounded on **one** side — and `EvSign`'s two branches supply precisely that: `0 < a` bounds it
below by `0`, and `a ≤ 0` bounds it above by `1`.

So both children need the *same* hypothesis, and it is exactly `EvSign`'s shape. No extra
stabilization statement is required, and in particular the strict trichotomy asked for earlier is
not needed. -/

/-- The exponential decoder from an *upper* bound: `exp u = exp C / exp (C − u)`. -/
noncomputable def FTerm.EFupper (C : Real) (u : FTerm) : FTerm :=
  FTerm.div (FTerm.const (exp C)) (FTerm.EF (FTerm.sub (FTerm.const C) u))

/-- **An upper bound decodes `exp` as well as a lower one.**

`EFshift` reflects the argument up past `0` by translation; this reflects it *down* past `0` by
division. Between them, one-sided boundedness in either direction is enough, which is what makes
`EvSign` sufficient. -/
theorem FTerm.EFupper_eval (C : Real) (u : FTerm) (x : Real) (h : FTerm.eval u x < C) :
    FTerm.eval (FTerm.EFupper C u) x = exp (FTerm.eval u x) := by
  have hval : FTerm.eval (FTerm.sub (FTerm.const C) u) x = C - FTerm.eval u x := rfl
  show exp C / FTerm.eval (FTerm.EF (FTerm.sub (FTerm.const C) u)) x = exp (FTerm.eval u x)
  rw [FTerm.EF_eval _ x (by rw [hval]; exact sub_pos_of_lt h), hval]
  refine div_of_eq_mul (ne_of_gt (exp_pos _)) ?_
  rw [← exp_add]
  have e : C - FTerm.eval u x + FTerm.eval u x = C := by mach_ring
  rw [e]

/-- Eventual sign stability on `D`: strictly positive throughout, or non-positive throughout.
This is `EvSign`'s shape with the ray replaced by an arbitrary domain, and it is what **both**
children need. -/
def EvStable (D : Real → Prop) (f : Real → Real) : Prop :=
  (∀ x : Real, D x → 0 < f x) ∨ (∀ x : Real, D x → f x ≤ 0)

/-- Historical name. This was introduced as the *right* child's condition, before `EFupper` showed
the left child needs the same thing; kept so the record of that step survives. -/
abbrev SignStableRight (D : Real → Prop) (f : Real → Real) : Prop := EvStable D f

/-- Every `eml` node's two children are `EvStable` on `D`. -/
def EvStableInternal (D : Real → Prop) : EMLTree → Prop
  | .const _ => True
  | .var     => True
  | .eml a b => EvStableInternal D a ∧ EvStableInternal D b
                ∧ EvStable D a.eval ∧ EvStable D b.eval

/-- **One node**, given both children already represented and both `EvStable`. Factored out because
the global and the eventual theorems below differ only in how they obtain the sign hypotheses.

Four cases, and each side collapses two of them:

| left child | term | right child | term |
| --- | --- | --- | --- |
| `> 0` | `EF â` | `> 0` | `LF b̂` |
| `≤ 0` | `exp 1 / EF(1 − â)` | `≤ 0` | `0` |

On the right, `log₀` is `0` on the whole non-positive branch. On the left, `EFupper` needs only
`a < 1`, which `a ≤ 0` gives. -/
private theorem node_step {D : Real → Prop} {a b : EMLTree} {Ta Tb : FTerm}
    (hTa : ∀ x : Real, D x → FTerm.eval Ta x = a.eval x)
    (hTb : ∀ x : Real, D x → FTerm.eval Tb x = b.eval x)
    (hsa : EvStable D a.eval) (hsb : EvStable D b.eval) :
    FRepresentable D (EMLTree.eml a b).eval := by
  obtain ⟨LT, hLT⟩ : ∃ LT : FTerm, ∀ x : Real, D x → FTerm.eval LT x = exp (a.eval x) := by
    rcases hsa with hp | hnp
    · exact ⟨FTerm.EF Ta, fun x hx => by
        rw [FTerm.EF_eval Ta x (by rw [hTa x hx]; exact hp x hx), hTa x hx]⟩
    · refine ⟨FTerm.EFupper 1 Ta, fun x hx => ?_⟩
      have hlt : FTerm.eval Ta x < 1 := by
        rw [hTa x hx]; exact lt_of_le_of_lt (hnp x hx) zero_lt_one_ax
      rw [FTerm.EFupper_eval 1 Ta x hlt, hTa x hx]
  obtain ⟨RT, hRT⟩ : ∃ RT : FTerm, ∀ x : Real, D x → FTerm.eval RT x = log (b.eval x) := by
    rcases hsb with hp | hnp
    · exact ⟨FTerm.LF Tb, fun x hx => by
        rw [FTerm.LF_eval Tb x (by rw [hTb x hx]; exact hp x hx), hTb x hx]⟩
    · exact ⟨FTerm.const 0, fun x hx => by
        show (0 : Real) = log (b.eval x)
        rw [log_nonpos (hnp x hx)]⟩
  exact ⟨FTerm.sub LT RT, fun x hx => by
    show FTerm.eval LT x - FTerm.eval RT x = exp (a.eval x) - log (b.eval x)
    rw [hLT x hx, hRT x hx]⟩

/-- **The unary basis theorem.** Every EML tree whose internal arguments are eventually
sign-definite on `D` — positive throughout, or non-positive throughout, nothing finer — is computed
on `D` by a **branch-free** term of `L_F`.

No runtime selector is needed: the *translator* chooses the branch once, per node, from the
hypothesis. `L_F` has no conditional and does not acquire one. -/
theorem evStable_F_representable (D : Real → Prop) :
    ∀ t : EMLTree, EvStableInternal D t →
      FRepresentable D t.eval := by
  intro t
  induction t with
  | const c => intro _; exact ⟨FTerm.const c, fun _ _ => rfl⟩
  | var => intro _; exact ⟨FTerm.var, fun _ _ => rfl⟩
  | eml a b iha ihb =>
      intro h
      obtain ⟨hpa, hpb, hsa, hsb⟩ := h
      obtain ⟨Ta, hTa⟩ := iha hpa
      obtain ⟨Tb, hTb⟩ := ihb hpb
      exact node_step hTa hTb hsa hsb

/-! ### The strict-trichotomy versions are corollaries

`SignStable`'s three cases and `StableSignsRefined`'s mixed pair both imply `EvStable`, so the
theorems stated earlier in this development now follow from the one above rather than repeating its
induction. -/

/-- A strict trichotomy implies the two-way split. -/
private theorem evStable_of_signStable {D : Real → Prop} {f : Real → Real}
    (h : SignStable D f) : EvStable D f := by
  rcases h with hp | hn | hz
  · exact Or.inl hp
  · exact Or.inr (fun x hx => le_of_lt (hn x hx))
  · exact Or.inr (fun x hx => le_of_eq (hz x hx))

private theorem evStableInternal_of_stableInternalSigns {D : Real → Prop} :
    ∀ t : EMLTree, StableInternalSigns D t → EvStableInternal D t := by
  intro t
  induction t with
  | const c => intro _; exact True.intro
  | var => intro _; exact True.intro
  | eml a b iha ihb =>
      intro h
      obtain ⟨hpa, hpb, hsa, hsb⟩ := h
      exact ⟨iha hpa, ihb hpb, evStable_of_signStable hsa, evStable_of_signStable hsb⟩

/-- **Stable internal signs suffice** — now a corollary of `evStable_F_representable`. -/
theorem stable_signs_F_representable (D : Real → Prop) :
    ∀ t : EMLTree, StableInternalSigns D t →
      FRepresentable D t.eval :=
  fun t h => evStable_F_representable D t (evStableInternal_of_stableInternalSigns t h)

/-- Left children sign-stable (strict trichotomy); right children merely `EvStable`. The
intermediate step from when the two children were believed to differ. -/
def StableSignsRefined (D : Real → Prop) : EMLTree → Prop
  | .const _ => True
  | .var     => True
  | .eml a b => StableSignsRefined D a ∧ StableSignsRefined D b
                ∧ SignStable D a.eval ∧ EvStable D b.eval

private theorem evStableInternal_of_refined {D : Real → Prop} :
    ∀ t : EMLTree, StableSignsRefined D t → EvStableInternal D t := by
  intro t
  induction t with
  | const c => intro _; exact True.intro
  | var => intro _; exact True.intro
  | eml a b iha ihb =>
      intro h
      obtain ⟨hpa, hpb, hsa, hsb⟩ := h
      exact ⟨iha hpa, ihb hpb, evStable_of_signStable hsa, hsb⟩

/-- **The refined stable-sign theorem** — also a corollary now. -/
theorem stable_signs_refined_F_representable (D : Real → Prop) :
    ∀ t : EMLTree, StableSignsRefined D t →
      FRepresentable D t.eval :=
  fun t h => evStable_F_representable D t (evStableInternal_of_refined t h)

/-! ## Eventual representation: from `EvSign` to a single ray

`EvSign` gives each node its *own* ray. Finitely many nodes, so the rays join, and the whole tree is
represented on the common one. -/

private theorem le_total' (a b : Real) : a ≤ b ∨ b ≤ a := by
  rcases lt_total a b with h | h | h
  · exact Or.inl (le_of_lt h)
  · exact Or.inl (le_of_eq h)
  · exact Or.inr (le_of_lt h)

/-- Two rays with base `≥ 1` have a common refinement with base `≥ 1`. -/
private theorem ray_join {X₁ X₂ : Real} (h₁ : 1 ≤ X₁) (h₂ : 1 ≤ X₂) :
    ∃ X : Real, 1 ≤ X ∧ X₁ ≤ X ∧ X₂ ≤ X := by
  rcases le_total' X₁ X₂ with h | h
  · exact ⟨X₂, h₂, h, le_refl X₂⟩
  · exact ⟨X₁, h₁, le_refl X₁, h⟩

/-- `EvSign` is `EvStable` on a ray. -/
private theorem evStable_of_evSign {f : Real → Real} (h : EvSign f) :
    ∃ X : Real, 1 ≤ X ∧ EvStable (fun x => X ≤ x) f := by
  rcases h with ⟨X, hX1, hp⟩ | ⟨X, hX1, hn⟩
  · exact ⟨X, hX1, Or.inl (fun x hx => hp x hx)⟩
  · exact ⟨X, hX1, Or.inr (fun x hx => hn x hx)⟩

/-- Sign stability survives shrinking the ray. -/
private theorem evStable_mono {X Y : Real} (hXY : X ≤ Y) {f : Real → Real}
    (h : EvStable (fun x => X ≤ x) f) : EvStable (fun x => Y ≤ x) f := by
  rcases h with hp | hn
  · exact Or.inl (fun x hx => hp x (le_trans hXY hx))
  · exact Or.inr (fun x hx => hn x (le_trans hXY hx))

/-- **The induction skeleton, once.** Any subtree-closed predicate that supplies eventual
sign-definiteness for the two children of every node yields eventual `L_F` representability on a
single ray.

Stated over a predicate rather than proved twice because the two instances below — one conditional
on `SignHardCase`, one unconditional at depth ≤ 3 — differ only in where the sign hypotheses come
from. -/
theorem eventual_F_representable_of_pred (P : EMLTree → Prop)
    (hsub : ∀ a b : EMLTree, P (EMLTree.eml a b) → P a ∧ P b)
    (hsign : ∀ a b : EMLTree, P (EMLTree.eml a b) → EvSign a.eval ∧ EvSign b.eval) :
    ∀ t : EMLTree, P t →
      ∃ X₀ : Real, 1 ≤ X₀ ∧ FRepresentable (fun x : Real => X₀ ≤ x) t.eval := by
  intro t
  induction t with
  | const c => intro _; exact ⟨1, le_refl 1, FTerm.const c, fun _ _ => rfl⟩
  | var => intro _; exact ⟨1, le_refl 1, FTerm.var, fun _ _ => rfl⟩
  | eml a b iha ihb =>
      intro hP
      obtain ⟨hPa, hPb⟩ := hsub a b hP
      obtain ⟨hga, hgb⟩ := hsign a b hP
      obtain ⟨Xa, hXa1, Ta, hTa⟩ := iha hPa
      obtain ⟨Xb, hXb1, Tb, hTb⟩ := ihb hPb
      obtain ⟨Ya, hYa1, hsa⟩ := evStable_of_evSign hga
      obtain ⟨Yb, hYb1, hsb⟩ := evStable_of_evSign hgb
      obtain ⟨R1, hR11, hR1a, hR1b⟩ := ray_join hXa1 hYa1
      obtain ⟨R2, hR21, hR2a, hR2b⟩ := ray_join hXb1 hYb1
      obtain ⟨X₀, hX01, hX0a, hX0b⟩ := ray_join hR11 hR21
      refine ⟨X₀, hX01, ?_⟩
      exact node_step
        (fun x hx => hTa x (le_trans (le_trans hR1a hX0a) hx))
        (fun x hx => hTb x (le_trans (le_trans hR2a hX0b) hx))
        (evStable_mono (le_trans hR1b hX0a) hsa)
        (evStable_mono (le_trans hR2b hX0b) hsb)

/-- **Every EML tree of depth ≤ 3 is eventually computed by a term of `L_F`. Unconditionally.**

The node itself never needs a sign; only its two children do. So `evSign_depth_le_two`, which is
unconditional, covers the children of every node in a depth-≤3 tree — one level deeper than the
sign theorem itself reaches. -/
theorem eventual_F_representable_depth_le_three (t : EMLTree) (ht : t.depth ≤ 3) :
    ∃ X₀ : Real, 1 ≤ X₀ ∧ FRepresentable (fun x : Real => X₀ ≤ x) t.eval := by
  refine eventual_F_representable_of_pred (fun s => s.depth ≤ 3) ?_ ?_ t ht
  · intro a b h
    simp only [EMLTree.depth] at h
    have hl := Nat.le_max_left a.depth b.depth
    have hr := Nat.le_max_right a.depth b.depth
    exact ⟨by omega, by omega⟩
  · intro a b h
    simp only [EMLTree.depth] at h
    have hl := Nat.le_max_left a.depth b.depth
    have hr := Nat.le_max_right a.depth b.depth
    exact ⟨evSign_depth_le_two a (by omega), evSign_depth_le_two b (by omega)⟩

/-- **`SignHardCase` implies every EML tree is eventually computed by a term of `L_F`.**

The conditional half of the same statement, at every depth. `evSign_of_hard` supplies the two
sign hypotheses at each node; nothing else is required of the hypothesis, and in particular no
strict trichotomy. -/
theorem eventual_F_representable_of_hard (h : SignHardCase) (t : EMLTree) :
    ∃ X₀ : Real, 1 ≤ X₀ ∧ FRepresentable (fun x : Real => X₀ ≤ x) t.eval :=
  eventual_F_representable_of_pred (fun _ => True)
    (fun _ _ _ => ⟨True.intro, True.intro⟩)
    (fun a b _ => ⟨evSign_of_hard h a, evSign_of_hard h b⟩)
    t True.intro

/-- **Discrimination specimen: `log` itself is eventually a term of `L_F`, with no hypothesis.**

`logTree var` has depth exactly 3, so the theorem above applies to it and nothing else is assumed.
Recorded because a depth bound that covered only trivial trees would prove nothing — this is a
tree whose value is not itself an `L_F` primitive. -/
theorem log_eventually_F_representable :
    ∃ X₀ : Real, 1 ≤ X₀ ∧ FRepresentable (fun x : Real => X₀ ≤ x) log := by
  obtain ⟨X₀, hX1, T, hT⟩ :=
    eventual_F_representable_depth_le_three (logTree EMLTree.var) (by decide)
  refine ⟨X₀, hX1, T, fun x hx => ?_⟩
  rw [hT x hx, logTree_eval]
  rfl

/-! ## The global theorem: `F` is a unary basis for EML, with no hypothesis at all

Everything above buys representability by *assuming* something about signs. That was the wrong shape
of effort, and two facts already in this file close the question outright.

**`decoder_log` has no hypothesis.** `F u − exp u = log₀ u` for every real `u`, the totalised branch
included — because `F` is itself built from the totalised `log`, so the branch information is latent
in the primitive rather than lost. This is precisely the escape flagged when obstruction (B) was
raised, and it is the one that works.

**`EF` needs its argument positive, but the argument is ours to choose.** Both `u + u² + 1` and
`u² + 1` are positive for *every* real `u`, and

```
exp u = exp(u + u² + 1) / exp(u² + 1)
```

so `exp` is decoded everywhere with no case split. `log₀` then follows from `F` and `exp`.

Obstructions (A), (B) and (C) are therefore all **refuted**, and every sign hypothesis in this file
is unnecessary. The development above is kept because it records the search, not because any of it
is needed. -/

/-- `0 < c` and `0 < c · z` give `0 < z`. Written over variables only — no numeral ever reaches the
normaliser. -/
private theorem pos_of_scaled_pos {c z : Real} (hc : 0 < c) (h : 0 < c * z) : 0 < z := by
  rcases lt_total 0 z with hz | hz | hz
  · exact hz
  · exfalso
    have e : c * z = 0 := by rw [← hz]; mach_ring
    rw [e] at h; exact absurd h (lt_irrefl_ax 0)
  · exfalso
    have v := add_lt_add_left hz (-z)
    have l : -z + z = 0 := by mach_ring
    have r : -z + 0 = -z := by mach_ring
    rw [l, r] at v
    have hsum := add_pos h (mul_pos hc v)
    have ez : c * z + c * -z = 0 := by mach_ring
    rw [ez] at hsum; exact absurd hsum (lt_irrefl_ax 0)

/-- `u² + u + 1 > 0` for every real `u` — `4(u² + u + 1) = (2u + 1)² + 3`. The shift that makes the
decoder unconditional. -/
theorem quad_pos (u : Real) : 0 < u * u + u + 1 := by
  have h3 : (0 : Real) < 1 + 1 + 1 := add_pos (add_pos zero_lt_one_ax zero_lt_one_ax) zero_lt_one_ax
  have h4 : (0 : Real) < 1 + 1 + 1 + 1 := add_pos h3 zero_lt_one_ax
  have hsum : (0 : Real) < (u + u + 1) * (u + u + 1) + (1 + 1 + 1) :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) h3
  have e : (u + u + 1) * (u + u + 1) + (1 + 1 + 1) = (1 + 1 + 1 + 1) * (u * u + u + 1) := by
    mach_mpoly [u]
  rw [e] at hsum
  exact pos_of_scaled_pos h4 hsum

/-- **The unconditional exponential decoder**: `exp u = EF(u + u² + 1) / EF(u² + 1)`.

Both arguments are positive for every real `u`, so `EF` applies at each of them with no hypothesis,
and the quotient of the two exponentials is `exp u`. -/
noncomputable def FTerm.EFall (u : FTerm) : FTerm :=
  FTerm.div (FTerm.EF (FTerm.add (FTerm.add u (FTerm.mul u u)) (FTerm.const 1)))
            (FTerm.EF (FTerm.add (FTerm.mul u u) (FTerm.const 1)))

theorem FTerm.EFall_eval (u : FTerm) (x : Real) :
    FTerm.eval (FTerm.EFall u) x = exp (FTerm.eval u x) := by
  have hnum : FTerm.eval (FTerm.add (FTerm.add u (FTerm.mul u u)) (FTerm.const 1)) x
      = FTerm.eval u x + FTerm.eval u x * FTerm.eval u x + 1 := rfl
  have hden : FTerm.eval (FTerm.add (FTerm.mul u u) (FTerm.const 1)) x
      = FTerm.eval u x * FTerm.eval u x + 1 := rfl
  have hdp : 0 < FTerm.eval u x * FTerm.eval u x + 1 :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) zero_lt_one_ax
  have hnp : 0 < FTerm.eval u x + FTerm.eval u x * FTerm.eval u x + 1 := by
    have hq := quad_pos (FTerm.eval u x)
    have e : FTerm.eval u x * FTerm.eval u x + FTerm.eval u x + 1
        = FTerm.eval u x + FTerm.eval u x * FTerm.eval u x + 1 := by mach_ring
    rw [e] at hq; exact hq
  show FTerm.eval (FTerm.EF (FTerm.add (FTerm.add u (FTerm.mul u u)) (FTerm.const 1))) x
      / FTerm.eval (FTerm.EF (FTerm.add (FTerm.mul u u) (FTerm.const 1))) x = exp (FTerm.eval u x)
  rw [FTerm.EF_eval _ x (by rw [hnum]; exact hnp), FTerm.EF_eval _ x (by rw [hden]; exact hdp),
      hnum, hden]
  refine div_of_eq_mul (ne_of_gt (exp_pos _)) ?_
  rw [← exp_add]
  have e : FTerm.eval u x * FTerm.eval u x + 1 + FTerm.eval u x
      = FTerm.eval u x + FTerm.eval u x * FTerm.eval u x + 1 := by mach_ring
  rw [e]

/-- **The unconditional logarithm decoder**: `log₀ u = F u − exp u`, everywhere, totalised branch
included. -/
noncomputable def FTerm.LFall (u : FTerm) : FTerm := FTerm.sub (FTerm.F u) (FTerm.EFall u)

theorem FTerm.LFall_eval (u : FTerm) (x : Real) :
    FTerm.eval (FTerm.LFall u) x = log (FTerm.eval u x) := by
  show Fbasis (FTerm.eval u x) - FTerm.eval (FTerm.EFall u) x = log (FTerm.eval u x)
  rw [FTerm.EFall_eval u x]
  exact decoder_log (FTerm.eval u x)

/-- **The compiler**, `EML → L_F`, as an explicit function rather than an existence proof. One
clause per constructor, and the `eml` node becomes `EFall â − LFall b̂`.

Named because the equivalence-of-classes theorem needs to say things *about* the emitted term — in
particular that its divisions never vanish — which an `∃` buried in an induction cannot support. -/
noncomputable def toFTerm : EMLTree → FTerm
  | .const c => FTerm.const c
  | .var     => FTerm.var
  | .eml a b => FTerm.sub (FTerm.EFall (toFTerm a)) (FTerm.LFall (toFTerm b))

theorem toFTerm_eval : ∀ (t : EMLTree) (x : Real), FTerm.eval (toFTerm t) x = t.eval x := by
  intro t
  induction t with
  | const c => intro _; rfl
  | var => intro _; rfl
  | eml a b iha ihb =>
      intro x
      show FTerm.eval (FTerm.EFall (toFTerm a)) x - FTerm.eval (FTerm.LFall (toFTerm b)) x
          = exp (a.eval x) - log (b.eval x)
      rw [FTerm.EFall_eval _ x, FTerm.LFall_eval _ x, iha x, ihb x]

/-- `f` is computed on **all** of `Real` by a term of `L_F`. -/
def FRepresentableGlobally (f : Real → Real) : Prop :=
  ∃ T : FTerm, ∀ x : Real, FTerm.eval T x = f x

/-- **`F` is a unary basis for EML.** Every EML tree is computed at *every real point* by a term of
`L_F` — constants, the variable, the four field operations, and the single unary symbol
`F(x) = exp x + log x`.

No domain, no ray, no sign hypothesis, no positivity, and no runtime selector: `L_F` still has no
conditional. One function generates both primitives of the grammar, and the totalisation comes along
for free because `F` carries it. -/
theorem F_unary_basis : ∀ t : EMLTree, FRepresentableGlobally t.eval :=
  fun t => ⟨toFTerm t, toFTerm_eval t⟩

/-- Every domain at once: the global theorem restricted anywhere. Every hypothesis-carrying
representability theorem in this file is this corollary with an unused hypothesis. -/
theorem F_representable_everywhere (D : Real → Prop) (t : EMLTree) : FRepresentable D t.eval := by
  obtain ⟨T, hT⟩ := F_unary_basis t
  exact ⟨T, fun x _ => hT x⟩

/-- **Discrimination: the basis is not vacuous.** `log₀` itself — the totalised primitive, `0` on
`x ≤ 0` and `log x` on `x > 0` — is a term of `L_F` at every real point, sign change included.
That is exactly what obstruction (B) said could not be done. -/
theorem log_totalised_F_representable : FRepresentableGlobally log :=
  ⟨FTerm.LFall FTerm.var, fun x => FTerm.LFall_eval FTerm.var x⟩

/-- And `exp`, for the same reason. -/
theorem exp_F_representable : FRepresentableGlobally exp :=
  ⟨FTerm.EFall FTerm.var, fun x => FTerm.EFall_eval FTerm.var x⟩

/-! ## Where this leaves the question

| statement | status |
| --- | --- |
| every EML tree is an `L_F` term, globally, no hypothesis | **proved** (`F_unary_basis`) |
| `log₀` is an `L_F` term across its own sign change | **proved** — obstruction (B) refuted |
| obstructions (A) and (C) | refuted by the same construction |
| the sign-stability development above | subsumed; kept as the record of the search |

What is *not* answered, and is now the interesting question: **`F` is a basis — is it a minimal
one?** `EFall` spends three `F` evaluations per `exp` and four per `log₀`, and the dilation identity
that makes the decoder work needs at least two scales (one is not rationally sufficient). Whether
three is necessary, and whether some other single function does better, is open.

Nothing here says `L_F` is a *small* language, only that it is a complete one. -/

end MachLib
