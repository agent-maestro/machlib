import MachLib.BipevComposition

/-!
# The lower coefficient is nonzero

`minimal_relation_impossible` consumes a hypothesis it does not produce: some coefficient strictly
below the top is not eventually zero. This module discharges it, and the argument turns out not to
need minimality at all — **properness alone suffices.**

If every lower coefficient were eventually zero then on the common tail
`bipev (Ls₀ ++ [v]) x t = 0 + t^m · pev v x`, and `t = exp(S x)` is positive, so `pev v x = 0` on
that tail. That contradicts properness directly.

The commit that closed the composition predicted a different proof — divide the relation by `e^S`
and appeal to minimality for a shorter one. That works too, but it is strictly more machinery for a
strictly weaker statement: this version never mentions `hmin`. **Third time in this arc that the
predicted tool was heavier than the needed one.**

## Two shape lemmas

`common_tail` intersects finitely many tails, one per coefficient — an induction over the list, not
a limit argument. `bipev_eq_zero_of_coeffs` says a bipolynomial with all-zero coefficients is zero
at every `y`, which is the `pev`-level fact `bipev`'s definition makes a two-line induction.
-/

namespace MachLib

open Real

/-- `a·b = 0` with `a ≠ 0` forces `b = 0`. Proved here rather than imported: the corpus's copies
live in `KhovanskiiReduction` and `SingleExpKhovanskii`, and importing either would pull the whole
Khovanskii development in for four lines. -/
private theorem factor_cancel {a b : Real} (ha : a ≠ 0) (hab : a * b = 0) : b = 0 := by
  have hkey : a * b * (1 / a) = b := by
    rw [mul_comm a b, mul_assoc, mul_inv a ha, mul_one_ax]
  rw [hab, zero_mul] at hkey
  exact hkey.symm

/-- **Finitely many tails intersect.** One bound per coefficient, combined pairwise. -/
theorem common_tail : ∀ Ls : List (List Real), (∀ A : List Real, A ∈ Ls → EvZeroF (pev A)) →
    ∃ X : Real, 1 ≤ X ∧ ∀ A : List Real, A ∈ Ls → ∀ x : Real, X ≤ x → pev A x = 0 := by
  intro Ls
  induction Ls with
  | nil =>
      intro _
      exact ⟨1, le_refl 1, fun A hA => absurd hA (by simp)⟩
  | cons A As ih =>
      intro hall
      obtain ⟨XA, hXA, hA⟩ := hall A (List.mem_cons_self ..)
      obtain ⟨XS, hXS, hS⟩ := ih (fun B hB => hall B (List.mem_cons_of_mem A hB))
      obtain ⟨X, hX, hXa, hXs⟩ := two_bounds' hXA hXS
      refine ⟨X, hX, fun B hB x hx => ?_⟩
      rcases List.mem_cons.mp hB with hb | hb
      · rw [hb]; exact hA x (le_trans hXa hx)
      · exact hS B hb x (le_trans hXs hx)

/-- **All coefficients zero at `x` makes the bipolynomial zero at every `y`.** -/
theorem bipev_eq_zero_of_coeffs : ∀ (Ls : List (List Real)) (x y : Real),
    (∀ A : List Real, A ∈ Ls → pev A x = 0) → bipev Ls x y = 0 := by
  intro Ls
  induction Ls with
  | nil => intro x y _; rfl
  | cons A As ih =>
      intro x y hall
      show pev A x + y * bipev As x y = 0
      rw [hall A (List.mem_cons_self ..),
          ih x y (fun B hB => hall B (List.mem_cons_of_mem A hB))]
      show (0 : Real) + y * 0 = 0
      mach_ring

/-- **A proper relation has a nonzero coefficient below the top.** No minimality needed. -/
theorem exists_nonzero_lower_coeff {S : Real → Real} {Ls₀ : List (List Real)} {v : List Real}
    (hrel : EvRel S (Ls₀ ++ [v])) (hv : ¬ EvZeroF (pev v)) :
    ∃ (j : Nat) (u : List Real), Ls₀[j]? = some u ∧ ¬ EvZeroF (pev u) := by
  refine Classical.byContradiction (fun hcon => ?_)
  -- every lower coefficient is eventually zero, or the existential would hold
  have hall : ∀ A : List Real, A ∈ Ls₀ → EvZeroF (pev A) := by
    intro A hA
    refine Classical.byContradiction (fun hAz => ?_)
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hA
    exact hcon ⟨i, A, hi, hAz⟩
  obtain ⟨X₁, hX₁, h1⟩ := hrel
  obtain ⟨X₂, hX₂, h2⟩ := common_tail Ls₀ hall
  obtain ⟨X, hX, hXa, hXb⟩ := two_bounds' hX₁ hX₂
  refine hv ⟨X, hX, fun x hx => ?_⟩
  have hb := h1 x (le_trans hXa hx)
  rw [bipev_concat Ls₀ v x (exp (S x))] at hb
  rw [bipev_eq_zero_of_coeffs Ls₀ x (exp (S x)) (fun A hA => h2 A hA x (le_trans hXb hx)),
      zero_add] at hb
  exact factor_cancel (ne_of_gt (powNat_pos (exp_pos (S x)) Ls₀.length)) hb

/-! ## The top-level theorem

Every hypothesis of `minimal_relation_impossible` is now either structural (about `q`, `P`, `Q`) or
produced here. What is left is `ProperRel` itself — the assumption that a relation exists at all,
which is exactly what the theorem refutes. -/

/-- **No proper relation exists.** For `S = P/Q` with an irreducible `q` dividing `Q` but not `P`,
there is no eventually-holding polynomial relation `Σ pⱼ·exp(S x)ʲ = 0` with a leading coefficient
that is not eventually zero. -/
theorem proper_relation_impossible {P Q q : List Real}
    (hq : PIrred q)
    (hchar : ∀ r : Nat, DerivCoprime q r)
    (hcharN : ∀ r : Nat, PNormal (pnsum r (pderiv q)))
    (hPd : ¬ Pdvd q P) (hPn : PNormal P)
    (hQn : PNormal Q) (hQne : Q ≠ []) (hQd : Pdvd q Q)
    (hQz : ¬ EvZeroF (pev Q))
    {Ls : List (List Real)}
    (hrel : ProperRel (fun y => pev P y * (1 / pev Q y)) Ls) :
    False := by
  obtain ⟨Ms, ⟨hMrel, Ls₀, v, hMs, hv⟩, hmin⟩ := exists_minimal_rel hrel
  obtain ⟨j, u, hu, huz⟩ := exists_nonzero_lower_coeff (hMs ▸ hMrel) hv
  exact minimal_relation_impossible hq hchar hcharN hPd hPn hQn hQne hQd hQz
    hmin hMrel hMs hv hu huz

end MachLib
