import MachLib.PolyDivIdentity

/-!
# Divisibility, on coefficients

`Pdvd q A` says some `M` makes `q·M` share a normal form with `A`. It is stated on coefficients
rather than through `pev` for the reason recorded in `PolyMulDegree`: the transport back from `pev`
is refutable over `𝔽₂`, so there is no functional definition available to this layer.

## Two design choices, both load-bearing

**The witness is required canonical.** `Pdvd` carries `PNormal M`, not merely `∃ M`. That is what
makes the degree bound free: with `q` and `M` both canonical and nonempty, `pmul_normal` says
`pmul q M` is *already* canonical, so `pnorm` does nothing and `pmul_length` reads the degree off
directly. Without it, every degree argument would first have to normalise the witness, which needs
the congruence below.

**`pmul` is not associative on the nose.** `pmul (pmul [x] Y) Z` and `pmul [x] (pmul Y Z)` differ by
a run of trailing zeros — concretely `padd (pscale 0 Z) [0]` versus `[0]`, which are equal lists only
when `Z` has length one. So associativity, and hence transitivity of divisibility, is a statement
**up to `pnorm`**, and that forces the congruence.

## The congruence, and why it is cheap this time

`pnorm (pmul L M) = pnorm (pmul (pnorm L) M)` looks like it should be as awkward as its `padd`
counterpart was. It is not, because that counterpart already exists: `pmul` recurses on its first
argument's head into a `padd`, so stripping a trailing zero from the first argument is exactly one
application of `pnorm_padd_congr` plus the induction hypothesis. The hard work was done once, in
`PolyDivIdentity`, and is reused rather than repeated.
-/

namespace MachLib

open Real

attribute [local instance] Classical.propDecidable

/-! ## Zero lists -/

theorem pscale_zero_replicate : ∀ M : List Real,
    pscale 0 M = List.replicate M.length (0 : Real) := by
  intro M
  induction M with
  | nil => rfl
  | cons m ms ih =>
      show (0 * m) :: pscale 0 ms = List.replicate (ms.length + 1) (0 : Real)
      have hz : (0 : Real) * m = 0 := by mach_ring
      rw [hz, ih]; rfl

/-- Multiplying by the zero polynomial gives a run of zeros — not `[]`, which is why `pnorm`
appears in every divisibility statement. -/
theorem pmul_nil_right : ∀ q : List Real,
    pmul q [] = List.replicate q.length (0 : Real) := by
  intro q
  induction q with
  | nil => rfl
  | cons a as ih =>
      show padd (pscale a ([] : List Real)) ((0 : Real) :: pmul as []) = _
      show (0 : Real) :: pmul as [] = List.replicate (as.length + 1) (0 : Real)
      rw [ih]; rfl

theorem pnorm_replicate_zero : ∀ n : Nat, pnorm (List.replicate n (0 : Real)) = [] := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
      show pconsN (0 : Real) (pnorm (List.replicate k (0 : Real))) = []
      rw [ih]
      show (if (0 : Real) = 0 then [] else [(0 : Real)]) = []
      rw [if_pos rfl]

/-! ## `pnorm` congruence for `pmul`'s first argument -/

theorem pnorm_pmul_concat_zero : ∀ (L M : List Real),
    pnorm (pmul (L ++ [0]) M) = pnorm (pmul L M) := by
  intro L
  induction L with
  | nil =>
      intro M
      show pnorm (padd (pscale 0 M) ((0 : Real) :: pmul ([] : List Real) M)) = pnorm []
      show pnorm (padd (pscale 0 M) [(0 : Real)]) = pnorm []
      have h := pnorm_padd_concat_zero (pscale 0 M) []
      rw [List.nil_append, padd_nil_right] at h
      rw [h, pscale_zero_replicate, pnorm_replicate_zero]
      rfl
  | cons l ls ih =>
      intro M
      show pnorm (padd (pscale l M) ((0 : Real) :: pmul (ls ++ [0]) M))
          = pnorm (padd (pscale l M) ((0 : Real) :: pmul ls M))
      refine pnorm_padd_congr _ ?_
      show pconsN (0 : Real) (pnorm (pmul (ls ++ [0]) M))
          = pconsN (0 : Real) (pnorm (pmul ls M))
      rw [ih M]

theorem pnorm_pmul_replicate : ∀ (n : Nat) (L M : List Real),
    pnorm (pmul (L ++ List.replicate n 0) M) = pnorm (pmul L M) := by
  intro n
  induction n with
  | zero => intro L M; simp
  | succ k ih =>
      intro L M
      have hsplit : L ++ List.replicate (k + 1) (0 : Real) = (L ++ List.replicate k 0) ++ [0] := by
        rw [List.append_assoc]
        congr 1
        rw [List.replicate_succ']
      rw [hsplit, pnorm_pmul_concat_zero, ih L M]

/-- **`pmul` sees only the normal form of its left argument.** -/
theorem pnorm_pmul_left (L M : List Real) :
    pnorm (pmul L M) = pnorm (pmul (pnorm L) M) := by
  obtain ⟨n, hn⟩ := pnorm_decomp L
  have h := pnorm_pmul_replicate n (pnorm L) M
  rw [← hn] at h
  exact h

theorem pnorm_pmul_congr {L L' : List Real} (M : List Real) (h : pnorm L = pnorm L') :
    pnorm (pmul L M) = pnorm (pmul L' M) := by
  rw [pnorm_pmul_left L M, pnorm_pmul_left L' M, h]

/-! ## The unit -/

theorem pmul_one_right : ∀ L : List Real, pmul L [1] = L := by
  intro L
  induction L with
  | nil => rfl
  | cons a as ih =>
      cases as with
      | nil =>
          show padd (pscale a [(1 : Real)]) [(0 : Real)] = [a]
          show ((a * 1) + 0) :: padd ([] : List Real) [] = [a]
          have h : a * 1 + 0 = a := by mach_ring
          rw [h]; rfl
      | cons d ds =>
          show padd (pscale a [(1 : Real)]) ((0 : Real) :: pmul (d :: ds) [1]) = a :: d :: ds
          rw [ih]
          show ((a * 1) + 0) :: padd ([] : List Real) (d :: ds) = a :: d :: ds
          have h : a * 1 + 0 = a := by mach_ring
          rw [h]; rfl

/-! ## Divisibility -/

/-- `q ∣ A`, on coefficients, with a **canonical** witness — see the module docstring for why the
canonicity is not decoration. -/
def Pdvd (q A : List Real) : Prop :=
  ∃ M : List Real, PNormal M ∧ pnorm A = pnorm (pmul q M)

theorem Pdvd_refl {A : List Real} : Pdvd A A := by
  refine ⟨[1], ?_, ?_⟩
  · intro c hc
    have h1 : (1 : Real) = c := by simpa using hc
    rw [← h1]; exact one_ne_zero
  · rw [pmul_one_right]

/-- **Divisors are short.** With both sides canonical no normalisation intervenes, so `pmul_length`
gives the degree bound directly — the reason `Pdvd` carries a canonical witness. -/
theorem Pdvd_length {q A : List Real} (hq : PNormal q) (hqne : q ≠ [])
    (hAne : pnorm A ≠ []) (h : Pdvd q A) : q.length ≤ (pnorm A).length := by
  obtain ⟨M, hMn, hM⟩ := h
  have hMne : M ≠ [] := by
    intro hMnil
    rw [hMnil] at hM
    have hz : pnorm (pmul q ([] : List Real)) = [] := by
      rw [pmul_nil_right, pnorm_replicate_zero]
    rw [hz] at hM
    exact hAne hM
  have hcanon : pnorm (pmul q M) = pmul q M :=
    pnorm_eq_self _ (pmul_normal hq hMn hqne hMne)
  rw [hM, hcanon, pmul_length q M hqne hMne]
  have hMlen : 1 ≤ M.length := by
    cases M with
    | nil => exact absurd rfl hMne
    | cons _ _ => exact Nat.succ_le_succ (Nat.zero_le _)
  omega

end MachLib
