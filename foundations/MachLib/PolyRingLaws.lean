import MachLib.PolyMulDegree

/-!
# Syntactic ring laws — because `pev` cannot be used to prove them

Everything downstream of division (Bézout, gcd, divisibility, `ord_q`) needs the ring laws as
**coefficient identities**, not as facts about the functions the coefficients denote. The reason is
the model argument recorded in `PolyMulDegree`: `algebraFootprint` is the theory of fields, fields
have finite models, and over `𝔽₂` the polynomial `X² + X` vanishes identically without being zero.
So `(∀ x, pev L x = 0) → pnorm L = []` is refutable in a model of the allowed axioms, and no ring
law may be obtained by proving it for `pev` and transporting back.

What makes that bearable is that these lists are *close* to canonical already: two coefficient lists
of the same length with propositionally equal entries **are** equal, so each law below is one
induction plus one `mach_ring` per coefficient. The laws that need care are the ones where the
lengths differ — `padd` pads, `pmul [c] M` leaves a trailing `[0]` — and those are exactly the
places `pnorm` or a nonemptiness hypothesis appears.

The target these assemble into is the division identity in coefficient form,
`pnorm A = pnorm (padd (pmul Q B) R)`, which `pdivmod_spec` currently gives only through `pev`.
The quotient is kept on the **left** of `pmul` throughout, because `pmul` recurses on its first
argument and left-distributivity is therefore the cheap direction.
-/

namespace MachLib

open Real

attribute [local instance] Classical.propDecidable

/-! ## `padd` is commutative, and rearranges -/

theorem padd_comm : ∀ X Y : List Real, padd X Y = padd Y X := by
  intro X
  induction X with
  | nil => intro Y; cases Y with
    | nil => rfl
    | cons b bs => rfl
  | cons a as ih =>
      intro Y
      cases Y with
      | nil => rfl
      | cons b bs =>
          show (a + b) :: padd as bs = (b + a) :: padd bs as
          rw [add_comm a b, ih bs]

theorem padd_left_comm (X Y Z : List Real) :
    padd X (padd Y Z) = padd Y (padd X Z) := by
  rw [← padd_assoc, padd_comm X Y, padd_assoc]

/-- The four-term rearrangement the product distributivity proof runs on. -/
theorem padd_middle_four (A B C D : List Real) :
    padd (padd A B) (padd C D) = padd (padd A C) (padd B D) := by
  rw [padd_assoc, padd_left_comm B C D, ← padd_assoc]

/-- Two shifted summands merge — `0 :: —` distributes over `padd`. -/
theorem padd_zero_cons (U V : List Real) :
    padd ((0 : Real) :: U) ((0 : Real) :: V) = (0 : Real) :: padd U V := by
  show ((0 : Real) + 0) :: padd U V = (0 : Real) :: padd U V
  rw [add_zero]

/-! ## `pscale` -/

/-- Scaling by a sum splits. Note this is scaling by `c + d`, not `pscale c` applied to a sum. -/
theorem pscale_add_left : ∀ (c d : Real) (M : List Real),
    pscale (c + d) M = padd (pscale c M) (pscale d M) := by
  intro c d M
  induction M with
  | nil => rfl
  | cons m ms ih =>
      show ((c + d) * m) :: pscale (c + d) ms = (c * m + d * m) :: padd (pscale c ms) (pscale d ms)
      have hm : (c + d) * m = c * m + d * m := by mach_ring
      rw [hm, ih]

/-- A zero scaling is absorbed by anything at least as long. The coefficients differ syntactically
(`0·m + x` versus `x`) but are propositionally equal, which for a list identity is enough. -/
theorem pscale_zero_padd : ∀ (M X : List Real), M.length ≤ X.length →
    padd (pscale 0 M) X = X := by
  intro M
  induction M with
  | nil => intro X _; rfl
  | cons m ms ih =>
      intro X h
      cases X with
      | nil => exact absurd h (by simp)
      | cons x xs =>
          show (0 * m + x) :: padd (pscale 0 ms) xs = x :: xs
          have hz : (0 : Real) * m + x = x := by mach_ring
          rw [hz, ih xs (by simpa using h)]

/-! ## `pmul` distributes on the left -/

theorem pmul_padd_left : ∀ (X Y M : List Real),
    pmul (padd X Y) M = padd (pmul X M) (pmul Y M) := by
  intro X
  induction X with
  | nil => intro Y M; rfl
  | cons a as ih =>
      intro Y M
      cases Y with
      | nil =>
          show pmul (a :: as) M = padd (pmul (a :: as) M) (pmul ([] : List Real) M)
          rw [show pmul ([] : List Real) M = [] from rfl, padd_nil_right]
      | cons b bs =>
          show padd (pscale (a + b) M) ((0 : Real) :: pmul (padd as bs) M)
              = padd (padd (pscale a M) ((0 : Real) :: pmul as M))
                     (padd (pscale b M) ((0 : Real) :: pmul bs M))
          rw [pscale_add_left, ih bs, ← padd_zero_cons (pmul as M) (pmul bs M),
              padd_middle_four]

/-! ## Monomials

`pmul [c] M` is `pscale c M` with a trailing `[0]` that `padd_zero_singleton` removes, so the
monomial cases need `M ≠ []` — the one place these laws are not unconditional. -/

theorem pmul_singleton (c : Real) (M : List Real) (hM : M ≠ []) :
    pmul [c] M = pscale c M := by
  have hne : pscale c M ≠ [] := by
    intro h
    have hl := pscale_length c M
    rw [h] at hl
    cases M with
    | nil => exact hM rfl
    | cons _ _ => simp at hl
  show padd (pscale c M) [(0 : Real)] = pscale c M
  exact padd_zero_singleton _ hne

/-- **A shifted monomial multiplies as a shifted scaling.** This is the identity that turns the
division step's quotient contribution into the list the step actually subtracted. -/
theorem pmul_pshift_singleton : ∀ (k : Nat) (c : Real) (M : List Real), M ≠ [] →
    pmul (pshift k [c]) M = pshift k (pscale c M) := by
  intro k
  induction k with
  | zero => intro c M hM; exact pmul_singleton c M hM
  | succ n ih =>
      intro c M hM
      have hlen : M.length ≤ ((0 : Real) :: pshift n (pscale c M)).length := by
        show M.length ≤ (pshift n (pscale c M)).length + 1
        rw [pshift_length, pscale_length]
        omega
      show padd (pscale 0 M) ((0 : Real) :: pmul (pshift n [c]) M)
          = (0 : Real) :: pshift n (pscale c M)
      rw [ih c M hM]
      exact pscale_zero_padd _ _ hlen

end MachLib
