import MachLib.EMLBasisLogArgPos
import MachLib.EMLFTranscendence
import MachLib.EMLRationalGerm

/-!
# The query germ as an `L_F` term, and its explicit zero bound

`oneQueryDichotomy_of_uniformBoundsFrom` (`EMLZeroBoundRay`) reduces `OneQueryDichotomy` to a
ray-relative uniform zero bound for the germ

```
x ↦ bipev N x (Fbasis (pev P x / pev Q x))
```

and `fterm_encBound_bounds` (`EMLBasisLogArgPos`) supplies such a bound for **any `L_F` term** whose
divisions are safe and whose `F`-arguments are positive. What was missing between them is the germ
itself as an `FTerm`. This module builds it.

## It is one `F`, and everything else is field operations

The germ is a bivariate polynomial in `x` and `Fbasis u`, with `u = pev P x / pev Q x` a ratio of
polynomials. In `L_F` that is: Horner in the coefficients (`add`/`mul`/`const`/`var`), one `div`, and
`F` applied to a **single** argument.

**But `fOcc (queryTerm N P Q) = N.length`, not `1`** — Horner writes `u` once per coefficient level,
so the *occurrence* count is the degree. I claimed `1` here on first writing and it is false; the
germ is one-query in the sense of **one distinct `F`-argument**, which is a different statement.
`EMLOneQueryGlobal` exists precisely to stop that conflation, and `queryTerm_fOcc` below pins the
actual number so the claim cannot drift back.

The side conditions fall out of that shape rather than being imposed:

* `DivSafe` reduces to `pev Q x ≠ 0`, because the single `div` is the only one in the term;
* `FArgsPos` reduces to `0 < pev P x / pev Q x`, because the single `F` is the only one.

Both are then discharged, at each point, from hypotheses the antecedent already carries or that
`ratGerm_eventual_sign` supplies on a ray.

## Scope

The **positive branch only**. `ratGerm_eventual_sign` splits a rational germ three ways, and the other
two need different machinery rather than more of this: where `u < 0` eventually the totalised
`Fbasis u = exp u` kills the log level (no `LogArgPos` obligation, but also no `FTree` route — that is
`ExpRationalKhovanskii`'s territory), and where `u` is eventually zero the germ collapses to a
polynomial in `x`. Neither is attempted here, and the module does not pretend the branch it does is
the whole statement.
-/

namespace MachLib

open Real

/-! ## Polynomials and bivariate polynomials as terms -/

/-! ### A note on `pevTerm`

`pevTerm` and `pevTerm_eval` are **not** defined here: `EMLRationalGerm` already has both, with
the identical Horner definition, proved for the identical reason (*"`pev` is Horner, which is field
operations on constants and the variable, so it **is** an `F`-free term"*). I wrote them again before
Lean rejected the duplicate name.

That is the second duplication this session, and both were caught the same way — **by picking the
name the corpus had already picked.** A construction given its obvious name collides audibly; given a
creative one it ships silently beside its twin. Worth preferring the obvious name for that reason
alone.

What is genuinely new below is the two side-condition lemmas (`DivSafe`, `FArgsPos`), which nothing
had needed before `EMLBasisLogArgPos` introduced the second predicate. -/

/-- No divisions and no `F`, so both side conditions are vacuous on a polynomial term. -/
theorem pevTerm_divSafe : ∀ (L : List Real) (x : Real), DivSafe (pevTerm L) x
  | [], _ => True.intro
  | _ :: cs, x => ⟨True.intro, True.intro, pevTerm_divSafe cs x⟩

theorem pevTerm_fArgsPos : ∀ (L : List Real) (S : RealSet), FArgsPos (pevTerm L) S
  | [], _ => True.intro
  | _ :: cs, S => ⟨True.intro, True.intro, pevTerm_fArgsPos cs S⟩

/-- A bivariate polynomial as a term, with the second variable supplied as a term. -/
noncomputable def bipevTerm : List (List Real) → FTerm → FTerm
  | [],      _ => .const 0
  | L :: Ls, u => .add (pevTerm L) (.mul u (bipevTerm Ls u))

theorem bipevTerm_eval : ∀ (N : List (List Real)) (u : FTerm) (x : Real),
    FTerm.eval (bipevTerm N u) x = bipev N x (FTerm.eval u x)
  | [], _, _ => rfl
  | L :: Ls, u, x => by
      show FTerm.eval (pevTerm L) x + FTerm.eval u x * FTerm.eval (bipevTerm Ls u) x
          = pev L x + FTerm.eval u x * bipev Ls x (FTerm.eval u x)
      rw [pevTerm_eval L x, bipevTerm_eval Ls u x]

/-- The coefficients contribute nothing; whatever `u` needs is all that is left. -/
theorem bipevTerm_divSafe : ∀ (N : List (List Real)) (u : FTerm) (x : Real),
    DivSafe u x → DivSafe (bipevTerm N u) x
  | [], _, _, _ => True.intro
  | L :: Ls, u, x, hu => ⟨pevTerm_divSafe L x, hu, bipevTerm_divSafe Ls u x hu⟩

theorem bipevTerm_fArgsPos : ∀ (N : List (List Real)) (u : FTerm) (S : RealSet),
    FArgsPos u S → FArgsPos (bipevTerm N u) S
  | [], _, _, _ => True.intro
  | L :: Ls, u, S, hu => ⟨pevTerm_fArgsPos L S, hu, bipevTerm_fArgsPos Ls u S hu⟩

/-! ## The germ -/

/-- **The query germ as an `L_F` term.** One `F`, one `div`, and Horner. -/
noncomputable def queryTerm (N : List (List Real)) (P Q : List Real) : FTerm :=
  bipevTerm N (.F (.div (pevTerm P) (pevTerm Q)))

theorem queryTerm_eval (N : List (List Real)) (P Q : List Real) (x : Real) :
    FTerm.eval (queryTerm N P Q) x = bipev N x (Fbasis (pev P x / pev Q x)) := by
  rw [queryTerm, bipevTerm_eval]
  show bipev N x (Fbasis (FTerm.eval (pevTerm P) x / FTerm.eval (pevTerm Q) x)) = _
  rw [pevTerm_eval P x, pevTerm_eval Q x]

/-- `DivSafe` collapses to the denominator being nonzero — the term has exactly one division. -/
theorem queryTerm_divSafe (N : List (List Real)) (P Q : List Real) (x : Real)
    (hQ : pev Q x ≠ 0) : DivSafe (queryTerm N P Q) x := by
  refine bipevTerm_divSafe N _ x ?_
  refine ⟨pevTerm_divSafe P x, pevTerm_divSafe Q x, ?_⟩
  rw [pevTerm_eval Q x]; exact hQ

/-- `FArgsPos` collapses to positivity of `P/Q` — the term has exactly one `F`. -/
theorem queryTerm_fArgsPos (N : List (List Real)) (P Q : List Real) (S : RealSet)
    (hpos : ∀ x : Real, S x → 0 < pev P x / pev Q x) : FArgsPos (queryTerm N P Q) S := by
  refine bipevTerm_fArgsPos N _ S ⟨⟨pevTerm_fArgsPos P S, pevTerm_fArgsPos Q S⟩, ?_⟩
  intro x hx
  show (0 : Real) < FTerm.eval (pevTerm P) x / FTerm.eval (pevTerm Q) x
  rw [pevTerm_eval P x, pevTerm_eval Q x]
  exact hpos x hx

/-! ## The bound, on the positive branch -/

/-- **The query germ's zeros are bounded by a `Nat` built from `N`, `P`, `Q` alone.** No `a`, no `b`
— which is exactly what `oneQueryDichotomy_of_uniformBoundsFrom` needs, and what an `∃K`-per-interval
statement could not give.

The two hypotheses are the two the germ's shape leaves: the denominator nonzero, and `P/Q` positive.
On the branch where `ratGerm_eventual_sign` puts `pev P / pev Q` eventually positive, both hold on a
ray, and every interval inside that ray inherits this bound with the same constant. -/
theorem queryTerm_zero_bound (N : List (List Real)) (P Q : List Real) (a b : Real) (hab : a < b)
    (hQ : ∀ x : Real, Icc a b x → pev Q x ≠ 0)
    (hpos : ∀ x : Real, Icc a b x → 0 < pev P x / pev Q x)
    (hne : ∃ z : Real, a < z ∧ z < b ∧ bipev N z (Fbasis (pev P z / pev Q z)) ≠ 0) :
    ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ bipev N z (Fbasis (pev P z / pev Q z)) = 0) →
      zeros.length ≤ encBound (toEML (queryTerm N P Q)) := by
  have hd : ∀ x : Real, Icc a b x → DivSafe (queryTerm N P Q) x :=
    fun x hx => queryTerm_divSafe N P Q x (hQ x hx)
  have hf : FArgsPos (queryTerm N P Q) (Icc a b) := queryTerm_fArgsPos N P Q (Icc a b) hpos
  have hne' : ∃ z : Real, a < z ∧ z < b ∧ FTerm.eval (queryTerm N P Q) z ≠ 0 := by
    obtain ⟨z, h1, h2, h0⟩ := hne
    exact ⟨z, h1, h2, by rw [queryTerm_eval]; exact h0⟩
  intro zeros hnd hz
  refine fterm_encBound_bounds (queryTerm N P Q) a b hab hd hf hne' zeros hnd ?_
  intro z hzmem
  obtain ⟨h1, h2, h0⟩ := hz z hzmem
  exact ⟨h1, h2, by rw [queryTerm_eval]; exact h0⟩

/-- **The occurrence count is the degree, not one.** Horner repeats `u` at every coefficient level.
Stated because the docstring above once said `1`: the germ has a single `F`-*argument*, and that is
not the same as a single `F`-*occurrence*. -/
theorem bipevTerm_fOcc : ∀ (N : List (List Real)) (u : FTerm),
    fOcc (bipevTerm N u) = N.length * fOcc u
  | [], u => by show 0 = 0 * fOcc u; rw [Nat.zero_mul]
  | L :: Ls, u => by
      show fOcc (pevTerm L) + (fOcc u + fOcc (bipevTerm Ls u)) = (Ls.length + 1) * fOcc u
      rw [fOcc_pevTerm L, bipevTerm_fOcc Ls u]
      have e : (Ls.length + 1) * fOcc u = fOcc u + Ls.length * fOcc u := by
        rw [Nat.succ_mul]; omega
      omega

theorem queryTerm_fOcc (N : List (List Real)) (P Q : List Real) :
    fOcc (queryTerm N P Q) = N.length := by
  rw [queryTerm, bipevTerm_fOcc]
  show N.length * (1 + (fOcc (pevTerm P) + fOcc (pevTerm Q))) = N.length
  rw [fOcc_pevTerm P, fOcc_pevTerm Q]
  omega

end MachLib
