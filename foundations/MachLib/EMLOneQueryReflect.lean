import MachLib.EMLOneQueryGlobal
import MachLib.EMLCtxDivClamp

/-!
# Reflection, the second tail, and what `OneQueryLevelSet` actually needs

## The gap this closes, and the one it does not

Every result in the query-cost lane is stated on a **ray** — `EvZeroF` is `∃ X ≥ 1, ∀ x ≥ X`,
`CtxAppliesEv` likewise, `OneQueryDichotomy` likewise. So the corpus had machinery for `x → +∞` and
**nothing whatever for `x → -∞`**, while `OneQueryLevelSet` quantifies over all of `ℝ`. That was
recorded as a "ray versus global" gap, as though the missing piece were finiteness on the middle.

It is cheaper than that on one side and harder on the other.

**Cheaper:** `FTerm` is closed under `x ↦ -x`, and `fOcc` counts `F` nodes, so substituting
`0 - var` for `var` costs no queries. `reflect` makes every ray theorem a theorem about the other
tail, for free. The corpus never needed new `-∞` analysis; it needed a syntactic involution.

**Harder:** with both tails in hand the level set is everything-or-nothing near `+∞` and near `-∞`,
and **that still does not exclude `sign`.** Take `c = 1`: on the positive tail `sign x = 1`, so the
"everything" branch holds; on the negative tail `sign (-x) = -1`, so the "nothing" branch holds.
Both at once. An eventual statement cannot see a function that is eventually constant on each side
with *different constants*, and `sign` is exactly that. This is the same trap `EMLOneQueryGlobal`
warns about one level down, wearing a two-sided costume.

## So the residue is rigidity, not counting

```
one_query_level_set_ray        :  on a ray, the level set is everything or nothing   [PROVED here]
one_query_level_set_two_sided  :  the same at both tails, via `reflect`              [PROVED here]
oneQueryLevelSet_of_residues   :  OneQueryLevelSet  ⟸  rigidity ∧ bounded-finiteness [PROVED here]
```

`OneQueryTailRigidity` — agreeing with a constant on a tail forces agreement off a finite set — is
an **identity/continuation** statement. With it `sign` dies at once: `T = 1` on the positive tail
would force `T = 1` off a finite set, contradicting `T = -1` on the negative tail. Naming it
correctly matters, because "finitely many zeros on a compact" was being treated as the obstruction
and it is the *easy* half: `OneQueryBoundedLevelFinite` rests on
`analytic_finite_zeros_compact`, which is already trusted **and** already witnessed.

Nothing here discharges the ledger row. The reduction is stated as an implication so it cannot be
mistaken for one.
-/

namespace MachLib

open Real

/-- Substitute `-x` for the variable. Every constructor is carried through unchanged except
`var`, which becomes `0 - var`. -/
noncomputable def FTerm.reflect : FTerm → FTerm
  | .const c => .const c
  | .var     => .sub (.const 0) .var
  | .add a b => .add (reflect a) (reflect b)
  | .sub a b => .sub (reflect a) (reflect b)
  | .mul a b => .mul (reflect a) (reflect b)
  | .div a b => .div (reflect a) (reflect b)
  | .F a     => .F (reflect a)

/-- Reflection costs no queries: `fOcc` counts `F` nodes, and `var ↦ 0 - var` introduces none. -/
theorem fOcc_reflect : ∀ T : FTerm, fOcc T.reflect = fOcc T
  | .const _ => rfl
  | .var     => rfl
  | .add a b => by show fOcc a.reflect + fOcc b.reflect = _; rw [fOcc_reflect a, fOcc_reflect b]; rfl
  | .sub a b => by show fOcc a.reflect + fOcc b.reflect = _; rw [fOcc_reflect a, fOcc_reflect b]; rfl
  | .mul a b => by show fOcc a.reflect + fOcc b.reflect = _; rw [fOcc_reflect a, fOcc_reflect b]; rfl
  | .div a b => by show fOcc a.reflect + fOcc b.reflect = _; rw [fOcc_reflect a, fOcc_reflect b]; rfl
  | .F a     => by show 1 + fOcc a.reflect = _; rw [fOcc_reflect a]; rfl

/-- And it does what it says: the reflected term evaluates the original at `-x`. -/
theorem eval_reflect : ∀ (T : FTerm) (x : Real), T.reflect.eval x = T.eval (0 - x)
  | .const _, _ => rfl
  | .var,     x => by show (0 : Real) - x = 0 - x; rfl
  | .add a b, x => by show a.reflect.eval x + b.reflect.eval x = _; rw [eval_reflect a, eval_reflect b]; rfl
  | .sub a b, x => by show a.reflect.eval x - b.reflect.eval x = _; rw [eval_reflect a, eval_reflect b]; rfl
  | .mul a b, x => by show a.reflect.eval x * b.reflect.eval x = _; rw [eval_reflect a, eval_reflect b]; rfl
  | .div a b, x => by show a.reflect.eval x / b.reflect.eval x = _; rw [eval_reflect a, eval_reflect b]; rfl
  | .F a,     x => by show Fbasis (a.reflect.eval x) = _; rw [eval_reflect a]; rfl

private theorem le_tr {a b c : Real} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  rcases (le_iff_lt_or_eq a b).mp h1 with p | p
  · rcases (le_iff_lt_or_eq b c).mp h2 with q | q
    · exact le_of_lt (lt_trans_ax p q)
    · exact le_of_lt (q ▸ p)
  · exact p ▸ h2

/-- Two thresholds, one ray. -/
private theorem two_bnd {A B : Real} (hA : 1 ≤ A) (hB : 1 ≤ B) :
    ∃ X : Real, 1 ≤ X ∧ A ≤ X ∧ B ≤ X := by
  rcases lt_total A B with h | h | h
  · exact ⟨B, hB, le_of_lt h, le_refl B⟩
  · exact ⟨B, hB, le_of_eq h, le_refl B⟩
  · exact ⟨A, hA, le_refl A, le_of_lt h⟩

/-- **The level set of a one-query term is, on a ray, everything or nothing.**

NOT the open obligation `OneQueryLevelSet`, which is GLOBAL. This is the eventual statement, and
`OneQueryDichotomy` -- already discharged -- supplies it once the level is folded into the context:
`T x = c` is `(C - c)(x, F(P/Q)) = 0`, and `sub C (const c)` still has exactly one hole, so the
dichotomy applies verbatim. The work is threshold bookkeeping, not mathematics. -/
theorem one_query_level_set_ray (T : FTerm) (h : fOcc T = 1) (c : Real) :
    ∃ X : Real, 1 ≤ X ∧ ((∀ x : Real, X ≤ x → T.eval x = c)
                        ∨ (∀ x : Real, X ≤ x → T.eval x ≠ c)) := by
  obtain ⟨C, P, Q, X, hC, hX, hQ, happ⟩ := one_query_normal_form T h
  have hC' : FCtx.holes (FCtx.sub C (FCtx.const c)) = 1 := by
    show FCtx.holes C + 0 = 1; omega
  have hval : ∀ x : Real, X ≤ x →
      FCtx.eval (FCtx.sub C (FCtx.const c)) x (Fbasis (pev P x / pev Q x)) = T.eval x - c := by
    intro x hx
    show FCtx.eval C x (Fbasis (pev P x / pev Q x)) - c = T.eval x - c
    rw [← happ x hx]
  rcases oneQueryDichotomy_holds (FCtx.sub C (FCtx.const c)) P Q X hX hQ with hz | ⟨Y, hY, hne⟩
  · obtain ⟨Z, hZ, hzero⟩ := hz
    obtain ⟨W, hW, hXW, hZW⟩ := two_bnd hX hZ
    refine ⟨W, hW, Or.inl (fun x hx => ?_)⟩
    have hz0 : FCtx.eval (FCtx.sub C (FCtx.const c)) x (Fbasis (pev P x / pev Q x)) = 0 :=
      hzero x (le_tr hZW hx)
    rw [hval x (le_tr hXW hx)] at hz0
    have e : T.eval x = T.eval x - c + c := by mach_ring
    rw [e, hz0]; mach_ring
  · obtain ⟨W, hW, hXW, hYW⟩ := two_bnd hX hY
    refine ⟨W, hW, Or.inr (fun x hx hEq => ?_)⟩
    refine hne x (le_tr hYW hx) ?_
    rw [hval x (le_tr hXW hx), hEq]; mach_ring

/-- **Both tails at once.** The level set is everything-or-nothing near `+∞` AND near `-∞`.

This is what `reflect` buys. Every result in this lane is stated on a ray `x ≥ X`, so the corpus had
nothing to say about `x → -∞` at all; reflection converts one into the other at no cost, because
`fOcc` counts `F` nodes and `var ↦ 0 - var` introduces none. -/
theorem one_query_level_set_two_sided (T : FTerm) (h : fOcc T = 1) (c : Real) :
    ∃ X : Real, 1 ≤ X
      ∧ ((∀ x : Real, X ≤ x → T.eval x = c) ∨ (∀ x : Real, X ≤ x → T.eval x ≠ c))
      ∧ ((∀ x : Real, X ≤ x → T.eval (0 - x) = c)
         ∨ (∀ x : Real, X ≤ x → T.eval (0 - x) ≠ c)) := by
  obtain ⟨A, hA, hpos⟩ := one_query_level_set_ray T h c
  have hr : fOcc T.reflect = 1 := by rw [fOcc_reflect T]; exact h
  obtain ⟨B, hB, hneg⟩ := one_query_level_set_ray T.reflect hr c
  obtain ⟨X, hX, hAX, hBX⟩ := two_bnd hA hB
  refine ⟨X, hX, ?_, ?_⟩
  · rcases hpos with hall | hnone
    · exact Or.inl (fun x hx => hall x (le_tr hAX hx))
    · exact Or.inr (fun x hx => hnone x (le_tr hAX hx))
  · rcases hneg with hall | hnone
    · exact Or.inl (fun x hx => by
        have := hall x (le_tr hBX hx); rw [eval_reflect T x] at this; exact this)
    · exact Or.inr (fun x hx => by
        have := hnone x (le_tr hBX hx); rw [eval_reflect T x] at this; exact this)

/-! ## What is actually left, named

The two-sided dichotomy above does **not** exclude `sign`, and it is worth being exact about why,
because it is the same trap the module header warns of one level down. Take `c = 1`: on the positive
tail `sign x = 1`, so the `= c` branch holds; on the negative tail `sign (-x) = -1`, so the `≠ c`
branch holds. Both are satisfied at once. An eventual statement cannot see a function that is
eventually constant on each side with *different* constants, and that is precisely what `sign` is.

So the gap between `one_query_level_set_two_sided` and `OneQueryLevelSet` is **not** a finiteness
theorem, which is how it has been described. It is a **rigidity** theorem: agreeing with a constant
on a tail must force agreement off a finite set. With that, `sign` dies immediately — `T = 1` on the
positive tail would force `T = 1` almost everywhere, contradicting `T = -1` on the negative one.

Two residues, and only the first is the interesting one. -/

/-- **Residue 1 — rigidity.** A one-query term agreeing with a constant on either tail agrees with
it off a finite set. This is an identity/continuation statement, not a counting one. -/
def OneQueryTailRigidity : Prop :=
  ∀ T : FTerm, fOcc T = 1 → ∀ c X : Real, 1 ≤ X →
    ((∀ x : Real, X ≤ x → T.eval x = c) ∨ (∀ x : Real, X ≤ x → T.eval (0 - x) = c)) →
    ∃ E : List Real, ∀ x : Real, x ∉ E → T.eval x = c

/-- **Residue 2 — finiteness on a bounded interval.** The cheap half: `analytic_finite_zeros_compact`
is already trusted AND witnessed, so this is assembly rather than discovery. -/
def OneQueryBoundedLevelFinite : Prop :=
  ∀ T : FTerm, fOcc T = 1 → ∀ c X : Real, 1 ≤ X →
    ∃ E : List Real, ∀ x : Real, 0 - X ≤ x → x ≤ X → T.eval x = c → x ∈ E

/-- **The residue, as one proposition**, so it can carry a ledger row of its own. Splitting it
across two hypotheses would leave the reduction untrackable: the obligations ledger requires a
`reduced` row to name a residue that is itself a tracked row, which is what stops a reduction from
quietly discharging anything. -/
def OneQueryLevelSetResidue : Prop :=
  OneQueryTailRigidity ∧ OneQueryBoundedLevelFinite

/-- **The reduction.** `OneQueryLevelSet` follows from the residue and nothing else.

Stated as an implication on purpose: a reduction recorded as an implication cannot be mistaken for a
discharge, which is the failure mode the obligations ledger exists to prevent. -/
theorem oneQueryLevelSet_of_residue (hRes : OneQueryLevelSetResidue) : OneQueryLevelSet := by
  obtain ⟨hR, hB⟩ := hRes
  intro T h c
  obtain ⟨X, hX, hpos, hneg⟩ := one_query_level_set_two_sided T h c
  rcases hpos with hall | hposnone
  · obtain ⟨E, hE⟩ := hR T h c X hX (Or.inl hall)
    exact ⟨E, Or.inl hE⟩
  rcases hneg with hall | hnegnone
  · obtain ⟨E, hE⟩ := hR T h c X hX (Or.inr hall)
    exact ⟨E, Or.inl hE⟩
  -- both tails miss the level, so the level set is trapped in [-X, X]
  obtain ⟨E, hE⟩ := hB T h c X hX
  refine ⟨E, Or.inr (fun x hx => ?_)⟩
  rcases lt_total x (0 - X) with hlo | hlo | hlo
  · -- x < -X : then X ≤ 0 - x, and the negative tail says the level is missed there
    exfalso
    refine hnegnone (0 - x) ?_ ?_
    · have u := add_lt_add_left hlo (0 - x + X)
      have e1 : 0 - x + X + x = X := by mach_ring
      have e2 : 0 - x + X + (0 - X) = 0 - x := by mach_ring
      rw [e1, e2] at u; exact le_of_lt u
    · have e : 0 - (0 - x) = x := by mach_ring
      rw [e]; exact hx
  · refine hE x (le_of_eq hlo.symm) ?_ hx
    rcases lt_total (0 - X) X with hu | hu | hu
    · exact le_of_lt (hlo ▸ hu)
    · exact le_of_eq (hlo ▸ hu)
    · exfalso
      -- `X < 0 - X` with `1 ≤ X` is impossible: it forces `X + X < 0 < X`.
      have hXpos : (0 : Real) < X := lt_of_lt_of_le zero_lt_one_ax hX
      have u := add_lt_add_left hu X
      have e : X + (0 - X) = 0 := by mach_ring
      rw [e] at u
      have v := add_lt_add_left hXpos X
      have e2 : X + 0 = X := by mach_ring
      rw [e2] at v
      exact lt_irrefl_ax X (lt_trans_ax (lt_trans_ax v u) hXpos)
  · rcases lt_total X x with hhi | hhi | hhi
    · exact absurd (hposnone x (le_of_lt hhi) hx) (fun k => k)
    · exact absurd (hposnone x (le_of_eq hhi) hx) (fun k => k)
    · exact hE x (le_of_lt hlo) (le_of_lt hhi) hx

end MachLib