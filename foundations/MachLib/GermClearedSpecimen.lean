import MachLib.GermClearedDescent

/-!
# A firing specimen: `q = x`, `S = 1/x`, `u = log(1/x)`

Every theorem in this arc is conditional on a pole hypothesis set that, until now, **nobody had ever
instantiated**. That is not a cosmetic gap. Two of those hypotheses turned out to be *unsatisfiable*,
so every theorem carrying them was vacuously true and proved nothing:

* `∀ r, DerivCoprime q r` — false at `r = 0`, since `pnsum 0 _ = []` and every polynomial divides the
  zero polynomial. Fixed by weakening to `r + 1` (proof-neutral: no consumer ever used index `0`).
* `∀ r, PNormal (pnsum r (pderiv q))` — false at **every** `r ≥ 1`, since `pderiv` is
  length-preserving (`pderiv_length`) and therefore always leaves a trailing zero. Fixed by
  *deleting* it: it fed exactly one `euclid_lemma` call, and `euclid_lemma'` shows the normality side
  condition was never needed, because `Pdvd` already sees only `pnorm`.

This module closes that gap the only way it can be closed — by exhibiting germs that satisfy the
surviving hypothesis set. `q = x`, `P = 1`, `Q = x`, so `S = 1/x` and the germ is `log(1/x)`, which
is the canonical covered case for the branch.

**Read this as the gate on the whole arc.** If a future edit makes some hypothesis unsatisfiable
again, this file stops compiling — which is exactly what did not happen for the two defects above.
-/

namespace MachLib

open Real

/-! ## `x` is irreducible -/

private theorem pNormal_X : PNormal ([0, 1] : List Real) := by
  intro c hc
  have h1 : (1 : Real) = c := by simpa using hc
  rw [← h1]
  exact fun h => zero_ne_one_ax h.symm

/-- **`x` is irreducible.** `PEq` is `pnorm`-equality and both sides are canonical, so the
factorisation is a literal list equation and `pmul_length` closes it: `2 = a + b − 1` with
`a, b ≥ 1` forces one factor constant. -/
theorem pIrred_X : PIrred ([0, 1] : List Real) := by
  refine ⟨pNormal_X, by simp, ?_⟩
  intro X Y hXn hYn hXne hYne hPEq
  have h2 : pnorm (pmul X Y) = pmul X Y := pnorm_eq_self _ (pmul_normal hXn hYn hXne hYne)
  have h1 : pnorm ([0, 1] : List Real) = [0, 1] := pnorm_eq_self _ pNormal_X
  have heq : pmul X Y = ([0, 1] : List Real) := by rw [← h2, ← hPEq, h1]
  have hlen : X.length + Y.length - 1 = 2 := by
    rw [← pmul_length X Y hXne hYne, heq]; rfl
  have hX1 : 1 ≤ X.length := by
    cases X with
    | nil => exact absurd rfl hXne
    | cons _ _ => simp
  have hY1 : 1 ≤ Y.length := by
    cases Y with
    | nil => exact absurd rfl hYne
    | cons _ _ => simp
  omega

/-! ## `DerivCoprime` for `x`

`pderiv [0,1] = [1+0, 0]` — the trailing zero that made the old `hcharN` unsatisfiable. Under
`pnorm` it is the constant `1`, so the whole family reduces to `q ∤ (r+1)·1`, which
`not_Pdvd_pnsum_one'` already proves from irreducibility alone. -/

private theorem pderiv_X_eq : pderiv ([0, 1] : List Real) = [1 + 0, 0] := rfl

private theorem peq_pderiv_X : PEq (pderiv ([0, 1] : List Real)) [1] := by
  rw [pderiv_X_eq]
  have e : (1 : Real) + 0 = 1 := by mach_ring
  rw [e]
  show pconsN (1 : Real) (pnorm [(0 : Real)]) = pnorm [(1 : Real)]
  rw [pnorm_nil_zero]
  rfl

/-- **`x ∤ (r+1)·x'` for every `r`.** `pderiv [0,1] = [1+0, 0]` — the trailing zero that made the old
`hcharN` unsatisfiable — normalises to the constant `1`, so this reduces to `q ∤ (r+1)·1`, which
`not_Pdvd_pnsum_one'` proves from irreducibility alone. -/
theorem derivCoprime_X : ∀ r : Nat, DerivCoprime ([0, 1] : List Real) (r + 1) := by
  intro r h
  exact not_Pdvd_pnsum_one' pIrred_X (n := r + 1) (by omega)
    (Pdvd_of_peq (peq_pnsum (r + 1) peq_pderiv_X).symm h)

/-! ## The remaining hypotheses -/

theorem pev_X (x : Real) : pev ([0, 1] : List Real) x = x := by
  show (0 : Real) + x * (1 + x * 0) = x
  mach_ring

theorem pev_one (x : Real) : pev ([1] : List Real) x = 1 := by
  show (1 : Real) + x * 0 = 1
  mach_ring

private theorem not_evZeroF_pev_one : ¬ EvZeroF (pev ([1] : List Real)) := by
  intro ⟨X, hX, h⟩
  have hz := h X (le_refl X)
  rw [pev_one] at hz
  exact zero_ne_one_ax hz.symm

private theorem pnorm_one_ne_nil : pnorm ([1] : List Real) ≠ [] :=
  pnorm_ne_nil_of_not_evZero not_evZeroF_pev_one

private theorem pNormal_one : PNormal ([1] : List Real) := by
  intro c hc
  have h1 : (1 : Real) = c := by simpa using hc
  rw [← h1]
  exact fun h => zero_ne_one_ax h.symm

theorem not_evZeroF_pev_X : ¬ EvZeroF (pev ([0, 1] : List Real)) := by
  intro ⟨X, hX, h⟩
  have hz : X = 0 := by rw [← pev_X X]; exact h X (le_refl X)
  have hpos : (0 : Real) < X := lt_of_lt_of_le zero_lt_one_ax hX
  rw [hz] at hpos
  exact (ne_of_lt hpos) rfl

theorem pos_inv_X : ∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x →
    0 < pev ([1] : List Real) x * (1 / pev ([0, 1] : List Real) x) := by
  refine ⟨1, le_refl 1, fun x hx => ?_⟩
  have hx0 : (0 : Real) < x := lt_of_lt_of_le zero_lt_one_ax hx
  rw [pev_one, pev_X]
  have h := one_div_pos_of_pos hx0
  have e : (1 : Real) * (1 / x) = 1 / x := by mach_ring
  rw [e]; exact h

/-! ## The specimen fires -/

/-- **`log(1/x)` satisfies no proper relation in the class.** Every hypothesis of
`no_proper_cleared_relation` is discharged at `q = x`, `P = 1`, `Q = x`; nothing is assumed.

This is the artifact that makes the arc non-vacuous. -/
theorem no_proper_cleared_relation_inv_x
    {fs : List (Real → Real)}
    (hcl : ClearsToExp (fun y => pev [1] y * (1 / pev [0, 1] y)) fs)
    (hprop : GProperRel (fun y => Real.log (pev [1] y * (1 / pev [0, 1] y))) fs) :
    False :=
  no_proper_cleared_relation pIrred_X derivCoprime_X
    (not_Pdvd_const pIrred_X pnorm_one_ne_nil (by simp))
    pNormal_one pNormal_X (by simp) Pdvd_refl not_evZeroF_pev_X pos_inv_X
    (fun r => not_Pdvd_pnsum_one' pIrred_X (by omega))
    hcl hprop

/-! ## The same pole data witnesses the neighbouring capstones

A theorem concluding `False` is *meant* to have an unsatisfiable hypothesis set — that is what an
impossibility statement is. So "is it vacuous?" is the wrong question for these; the right one is
whether everything **except** the relation-existence hypothesis can be discharged. If it cannot, the
theorem says "these side conditions never hold" rather than "no relation exists for this germ", and
that is the failure `positive_branch_impossible` had.

`proper_relation_impossible` and `germ_relation_impossible` take exactly the pole data discharged
above, so the same `q = x`, `P = 1`, `Q = x` witnesses both. `ProperRel S Ls` is a polynomial
relation in `exp (S x)` with a non-vanishing top coefficient, so what these say, concretely, is that
**`exp (1/x)` is transcendental over `ℝ(x)`** — now with nothing assumed about the pole. -/

/-- **`exp (1/x)` satisfies no proper polynomial relation over `ℝ(x)`.** Every pole hypothesis
discharged; only the relation itself is assumed. -/
theorem proper_relation_impossible_inv_x {Ls : List (List Real)}
    (hrel : ProperRel (fun y => pev [1] y * (1 / pev [0, 1] y)) Ls) : False :=
  proper_relation_impossible pIrred_X derivCoprime_X
    (not_Pdvd_const pIrred_X pnorm_one_ne_nil (by simp))
    pNormal_one pNormal_X (by simp) Pdvd_refl not_evZeroF_pev_X hrel

/-- The same, for any germ eventually equal to `1/x`. -/
theorem germ_relation_impossible_inv_x {S : Real → Real} {Ls : List (List Real)}
    (hagree : EvEqF S (fun y => pev [1] y * (1 / pev [0, 1] y)))
    (hrel : ProperRel S Ls) : False :=
  germ_relation_impossible pIrred_X derivCoprime_X
    (not_Pdvd_const pIrred_X pnorm_one_ne_nil (by simp))
    pNormal_one pNormal_X (by simp) Pdvd_refl not_evZeroF_pev_X hagree hrel

end MachLib
