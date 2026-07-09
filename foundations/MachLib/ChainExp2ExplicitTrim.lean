import MachLib.ChainExp2ExplicitBound
import MachLib.ChainExp2Trim

/-!
# Explicit chain-2 bound — the TRIM-side degree bound

`ChainExp2ExplicitBound.lean` proved the REDUCE-side degree-preservation facts the explicit bound
needs (`cdegY0_lcY1_reduce_le`, `degreeX_chain2Reduce_le`, `degreeY0_chain2Reduce_le`). The `rankLex A B`
linearizer (`ExplicitBoundRank.lean`) turns the nested-lex measure into a `Nat` given global bounds
`A ≥ cdegY0(lcY₁ q)` and `B ≥ (x-degree component)` over every `q` the WF recursion reaches.

The chain-2 recursion (`chain2_khovanskii_bound_unconditional`) has two descending arms:
  * **reduce** (`chain2Reduce …`) — bounds done in `ChainExp2ExplicitBound.lean`.
  * **trim** (`dropLeadingYAt ⟨1⟩ p`) — this file. `dropLeadingYAt i p = reconstructY i (yCoeffsAt i p).dropLast 0`,
    so its degrees are governed by `reconstructY` over a *sub-list* of `p`'s `y_i`-coefficients.

This file closes the trim's **B-bound** — `degreeX (dropLeadingYAt i p) ≤ degreeX p` — the trim analog of
`degreeX_chain2Reduce_le`, via a `degreeX`-non-raising tower over the `yCoeffsAt` list operations
(mirroring the existing `yCoeffsAt_entries_degreeY_zero` tower) plus `reconstructY`.

**Remaining for the full explicit chain-2 bound** (scoped):
  * Bridge: `singleExpMeasureCanon(lcY₁ q).2 ≤ degreeX q` (measure x-component ≤ poly x-degree) ⇒ global `B := degreeX p₀`.
  * A-bound trim analog (the ONE hard obligation, `ExplicitBoundRank.lean:48-52`): after reduces grow `degreeY₀`
    (`degreeY0_chain2Reduce_le`, +1/step), a `degreeY₁`-dropping trim still exposes an `lcY₁` whose `cdegY0`
    is bounded by a degree functional of the ORIGINAL `p` — the exponential-in-`degreeY₁` accounting ⇒ global `A`.
  * Thread the `(A,B)` invariant + `rankLex_succ_le` through the WF induction (replacing `∃ N`).

No new axioms — pure structural `Nat`/`degreeX` facts.
-/

namespace MachLib.ChainExp2Explicit

open MachLib.MultiPolyMod MachLib.MultiPolyMod.MultiPoly
open MachLib.MultiPolyReconstruct MachLib.ChainExp2Trim
open MachLib.ChainExp2CanonMeasure MachLib.PolynomialCanonical

/-! ### `reconstructY` degree core -/

/-- `degreeX ((varYⁱ)ᵏ) = 0` — the chain (`y_i`) variable is x-free, so any power of it is too. -/
theorem degreeX_pow_varY_zero {n : Nat} (i : Fin n) (k : Nat) :
    degreeX (pow (varY i) k) = 0 := by
  induction k with
  | zero => rfl
  | succ m ih =>
    show degreeX (varY i) + degreeX (pow (varY i) m) = 0
    rw [degreeX_varY, ih]

/-- **`reconstructY` never raises `degreeX` past its coefficients.** If every coefficient has
`degreeX ≤ D`, so does `reconstructY i coeffs k` — each term `c · (varYⁱ)ᵏ` has `degreeX = degreeX c`,
and `add` takes the max. -/
theorem degreeX_reconstructY_le {n : Nat} (i : Fin n) (D : Nat) :
    ∀ (coeffs : List (MultiPoly n)) (k : Nat),
      (∀ c ∈ coeffs, degreeX c ≤ D) → degreeX (reconstructY i coeffs k) ≤ D
  | [], _, _ => by rw [reconstructY_nil]; exact Nat.zero_le _
  | c :: cs, k, h => by
      rw [reconstructY_cons]
      show Nat.max (degreeX (mul c (pow (varY i) k))) (degreeX (reconstructY i cs (k + 1))) ≤ D
      refine Nat.max_le.mpr ⟨?_, ?_⟩
      · show degreeX c + degreeX (pow (varY i) k) ≤ D
        rw [degreeX_pow_varY_zero]
        have hc := h c (List.mem_cons_self c cs)
        omega
      · exact degreeX_reconstructY_le i D cs (k + 1)
          (fun c' hc' => h c' (List.mem_cons_of_mem c hc'))

/-! ### `degreeX`-non-raising tower over the `yCoeffsAt` list operations -/

/-- `listAddN` entries stay under a common `degreeX` bound `D`. -/
theorem listAddN_entries_degreeX_le {n : Nat} (l1 l2 : List (MultiPoly n)) (D : Nat)
    (h1 : ∀ c ∈ l1, degreeX c ≤ D) (h2 : ∀ c ∈ l2, degreeX c ≤ D) :
    ∀ c ∈ listAddN l1 l2, degreeX c ≤ D := by
  induction l1 generalizing l2 with
  | nil => intro c hc; rw [listAddN_nil_left] at hc; exact h2 c hc
  | cons p ps ih =>
    cases l2 with
    | nil => intro c hc; rw [listAddN_cons_nil] at hc; exact h1 c hc
    | cons q qs =>
      intro c hc; rw [listAddN_cons_cons] at hc
      cases hc with
      | head =>
        exact Nat.max_le.mpr ⟨h1 p (List.mem_cons_self _ _), h2 q (List.mem_cons_self _ _)⟩
      | tail _ hc' =>
        exact ih qs (fun c hc => h1 c (List.mem_cons_of_mem _ hc))
                 (fun c hc => h2 c (List.mem_cons_of_mem _ hc)) c hc'

/-- `listSubN` entries stay under a common `degreeX` bound `D`. -/
theorem listSubN_entries_degreeX_le {n : Nat} (l1 l2 : List (MultiPoly n)) (D : Nat)
    (h1 : ∀ c ∈ l1, degreeX c ≤ D) (h2 : ∀ c ∈ l2, degreeX c ≤ D) :
    ∀ c ∈ listSubN l1 l2, degreeX c ≤ D := by
  induction l1 generalizing l2 with
  | nil =>
    induction l2 with
    | nil => intro c hc; exact absurd hc (List.not_mem_nil _)
    | cons q qs ihq =>
      intro c hc
      change c ∈ (sub (const 0) q :: listSubN [] qs) at hc
      cases hc with
      | head =>
        exact Nat.max_le.mpr ⟨Nat.zero_le _, h2 q (List.mem_cons_self _ _)⟩
      | tail _ hc' => exact ihq (fun c hc => h2 c (List.mem_cons_of_mem _ hc)) c hc'
  | cons p ps ih =>
    cases l2 with
    | nil => intro c hc; change c ∈ (p :: ps) at hc; exact h1 c hc
    | cons q qs =>
      intro c hc; change c ∈ (sub p q :: listSubN ps qs) at hc
      cases hc with
      | head =>
        exact Nat.max_le.mpr ⟨h1 p (List.mem_cons_self _ _), h2 q (List.mem_cons_self _ _)⟩
      | tail _ hc' =>
        exact ih qs (fun c hc => h1 c (List.mem_cons_of_mem _ hc))
                 (fun c hc => h2 c (List.mem_cons_of_mem _ hc)) c hc'

/-- `listScaleN p l` entries: `degreeX ≤ Dp + D` where `Dp ≥ degreeX p` and `D` bounds `l`. -/
theorem listScaleN_entries_degreeX_le {n : Nat} (p : MultiPoly n) (Dp : Nat) (hp : degreeX p ≤ Dp)
    (l : List (MultiPoly n)) (D : Nat) (hl : ∀ c ∈ l, degreeX c ≤ D) :
    ∀ c ∈ listScaleN p l, degreeX c ≤ Dp + D := by
  induction l with
  | nil => intro c hc; rw [listScaleN_nil] at hc; exact absurd hc (List.not_mem_nil _)
  | cons q qs ih =>
    intro c hc; rw [listScaleN_cons] at hc
    cases hc with
    | head =>
      show degreeX p + degreeX q ≤ Dp + D
      exact Nat.add_le_add hp (hl q (List.mem_cons_self _ _))
    | tail _ hc' => exact ih (fun c hc => hl c (List.mem_cons_of_mem _ hc)) c hc'

/-- `listMulN l1 l2` entries: `degreeX ≤ D1 + D2`. -/
theorem listMulN_entries_degreeX_le {n : Nat} (l1 l2 : List (MultiPoly n)) (D1 D2 : Nat)
    (h1 : ∀ c ∈ l1, degreeX c ≤ D1) (h2 : ∀ c ∈ l2, degreeX c ≤ D2) :
    ∀ c ∈ listMulN l1 l2, degreeX c ≤ D1 + D2 := by
  induction l1 with
  | nil => intro c hc; rw [listMulN_nil] at hc; exact absurd hc (List.not_mem_nil _)
  | cons p ps ih =>
    intro c hc; rw [listMulN_cons] at hc
    refine listAddN_entries_degreeX_le (listScaleN p l2) (const 0 :: listMulN ps l2) (D1 + D2)
      ?_ ?_ c hc
    · exact listScaleN_entries_degreeX_le p D1 (h1 p (List.mem_cons_self _ _)) l2 D2 h2
    · intro c' hc'
      cases hc' with
      | head => exact Nat.zero_le _
      | tail _ hc'' => exact ih (fun c hc => h1 c (List.mem_cons_of_mem _ hc)) c' hc''

/-- **Every `yCoeffsAt i p` entry has `degreeX ≤ degreeX p`.** Structural induction over `p`, threading the
tower above through `listAddN`/`listSubN`/`listMulN` (mirror of `yCoeffsAt_entries_degreeY_zero`). -/
theorem yCoeffsAt_entries_degreeX_le {n : Nat} (i : Fin n) (p : MultiPoly n) :
    ∀ c ∈ yCoeffsAt i p, degreeX c ≤ degreeX p := by
  induction p with
  | const a =>
    intro c hc; change c ∈ [const a] at hc
    rw [List.mem_singleton] at hc; subst hc; exact Nat.le_refl _
  | varX =>
    intro c hc; change c ∈ [varX] at hc
    rw [List.mem_singleton] at hc; subst hc; exact Nat.le_refl _
  | varY j =>
    intro c hc
    by_cases hji : j = i
    · have he : yCoeffsAt i (varY j) = [const 0, const 1] := by
        show (if j = i then _ else _) = _; rw [if_pos hji]
      rw [he] at hc
      rcases List.mem_cons.mp hc with rfl | hc2
      · exact Nat.zero_le _
      · rw [List.mem_singleton] at hc2; subst hc2; exact Nat.zero_le _
    · have he : yCoeffsAt i (varY j) = [varY j] := by
        show (if j = i then _ else _) = _; rw [if_neg hji]
      rw [he, List.mem_singleton] at hc; subst hc; exact Nat.le_refl _
  | add p q ihp ihq =>
    intro c hc
    exact listAddN_entries_degreeX_le (yCoeffsAt i p) (yCoeffsAt i q) (Nat.max (degreeX p) (degreeX q))
      (fun c hc => Nat.le_trans (ihp c hc) (Nat.le_max_left _ _))
      (fun c hc => Nat.le_trans (ihq c hc) (Nat.le_max_right _ _)) c hc
  | sub p q ihp ihq =>
    intro c hc
    exact listSubN_entries_degreeX_le (yCoeffsAt i p) (yCoeffsAt i q) (Nat.max (degreeX p) (degreeX q))
      (fun c hc => Nat.le_trans (ihp c hc) (Nat.le_max_left _ _))
      (fun c hc => Nat.le_trans (ihq c hc) (Nat.le_max_right _ _)) c hc
  | mul p q ihp ihq =>
    intro c hc
    exact listMulN_entries_degreeX_le (yCoeffsAt i p) (yCoeffsAt i q) (degreeX p) (degreeX q)
      ihp ihq c hc

/-! ### The trim B-bound -/

/-- **`degreeX` non-increase under the trim (B-bound).** `dropLeadingYAt i p = reconstructY` over a
sub-list (`dropLast`) of `p`'s `y_i`-coefficients, each of `degreeX ≤ degreeX p`, so the reconstruction
does not exceed `degreeX p`. The trim analog of `degreeX_chain2Reduce_le`. -/
theorem degreeX_dropLeadingYAt_le {n : Nat} (i : Fin n) (p : MultiPoly n) :
    degreeX (dropLeadingYAt i p) ≤ degreeX p := by
  show degreeX (reconstructY i (yCoeffsAt i p).dropLast 0) ≤ degreeX p
  exact degreeX_reconstructY_le i (degreeX p) (yCoeffsAt i p).dropLast 0
    (fun c hc => yCoeffsAt_entries_degreeX_le i p c (List.dropLast_subset _ hc))

/-! ### The measure↔degreeX bridge (two of three pieces)

The measure's x-component is `singleExpMeasureCanon(lcY₁ q).2 =
polyTrueDegreeStrict (polyCoeffs (multiPolyToPolyForLex (canonLcY0 (lcY₁ q))))`. The bridge
`… ≤ degreeX q + C` factors into three pieces; two land here cleanly (the third — a `listMulR`
convolution-length bound — is the remaining chunk, scoped below):

  (1) `polyTrueDegreeStrict L ≤ L.length + 1`                 [Poly strict-degree ≤ coeff count]
  (2) `degreeX (canonLcY0 (lcY₁ q)) ≤ degreeX q`             [MultiPoly side, reuses the tower above]
  (3) `length (polyCoeffs (multiPolyToPolyForLex m)) ≤ degreeX m + 1`   ← OPEN: needs
      `length_listAddR = max`, `length_listMulR = m+n−1` (tight convolution length, Nat-subtraction
      edge cases). With (3): b(q) ≤ degreeX q + 2, so `B := degreeX p₀ + 2` closes the B-bound. -/

/-- Every list is a `dropWhile` superset of itself: membership survives `dropWhile`. -/
private theorem mem_of_mem_dropWhile {α : Type} (p : α → Bool) :
    ∀ (l : List α) (a : α), a ∈ l.dropWhile p → a ∈ l
  | [], _, h => h
  | b :: bs, a, h => by
      rw [List.dropWhile_cons] at h
      by_cases hpb : p b = true
      · rw [if_pos hpb] at h
        exact List.mem_cons_of_mem _ (mem_of_mem_dropWhile p bs a h)
      · rw [if_neg hpb] at h; exact h

/-- **Bridge piece (1).** The strict polynomial degree never exceeds the coefficient count (`+1`):
`polyTrueDegree L ≤ L.length` (nothing is nonzero past the end), and `strict = trueDegree + 1` or `0`. -/
theorem polyTrueDegreeStrict_le_length (L : List Real) :
    polyTrueDegreeStrict L ≤ L.length + 1 := by
  unfold polyTrueDegreeStrict
  split
  · exact Nat.zero_le _
  · have h := polyTrueDegree_le_of_bounded L L.length (polyDegreeBoundedBy_at_length L)
    omega

/-- **Bridge piece (2).** `canonLcY0 m` is either a `yCoeffsAt ⟨0⟩ m` entry (via the `reverse`/`dropWhile`
of that list) or `const 0`, so its `degreeX` is bounded by `degreeX m` — using the trim-side tower. -/
theorem degreeX_canonLcY0_le (m : MultiPoly 2) :
    degreeX (canonLcY0 m) ≤ degreeX m := by
  show degreeX (((yCoeffsAt (⟨0, by omega⟩ : Fin 2) m).reverse.dropWhile coeffCanonZeroB).headD
                  (const 0)) ≤ degreeX m
  cases hl : (yCoeffsAt (⟨0, by omega⟩ : Fin 2) m).reverse.dropWhile coeffCanonZeroB with
  | nil => exact Nat.zero_le _
  | cons a rest =>
    show degreeX a ≤ degreeX m
    have ha_dw : a ∈ (yCoeffsAt (⟨0, by omega⟩ : Fin 2) m).reverse.dropWhile coeffCanonZeroB := by
      rw [hl]; exact List.mem_cons_self _ _
    have ha_rev := mem_of_mem_dropWhile coeffCanonZeroB _ a ha_dw
    exact yCoeffsAt_entries_degreeX_le _ m a (List.mem_reverse.mp ha_rev)

/-- **Bridge piece (2), composed to `lcY₁`.** `degreeX (canonLcY0 (lcY₁ q)) ≤ degreeX q`, via piece (2)
and `degreeX_leadingCoeffY_le`. The MultiPoly-side half of the measure↔degreeX bridge. -/
theorem degreeX_canonLcY0_lcY1_le (q : MultiPoly 2) :
    degreeX (canonLcY0 (leadingCoeffY (⟨1, by omega⟩ : Fin 2) q)) ≤ degreeX q :=
  Nat.le_trans (degreeX_canonLcY0_le _)
    (degreeX_leadingCoeffY_le (⟨1, by omega⟩ : Fin 2) q)

/-! ### Bridge piece (3) — the coeff-list-length tower + the closed bridge

`length (polyCoeffs (multiPolyToPolyForLex m)) ≤ degreeX m + 1`. The Poly-conversion sends `add→max`,
`mul→convolution`, so we need `listAddR`/`listSubR` length `= max` and the TIGHT `listMulR` length
`= m+n−1` (nonempty). `polyCoeffs_nonempty` supplies the nonemptiness. -/

open MachLib.PfaffianChainMod.PfaffianFn   -- multiPolyToPolyForLex

-- Mathlib-free `Nat.max` helpers (built from the `Nat.max`-based primitives; `split_ifs`/`Nat.max_def`
-- match the general `max`, not `Nat.max`, so they don't fire on these goals).
private theorem mymax_eq_right {a b : Nat} (h : a ≤ b) : Nat.max a b = b :=
  Nat.le_antisymm (Nat.max_le.mpr ⟨h, Nat.le_refl b⟩) (Nat.le_max_right a b)
private theorem mymax_eq_left {a b : Nat} (h : b ≤ a) : Nat.max a b = a :=
  Nat.le_antisymm (Nat.max_le.mpr ⟨Nat.le_refl a, h⟩) (Nat.le_max_left a b)
private theorem max_succ (a b : Nat) : Nat.max a b + 1 = Nat.max (a + 1) (b + 1) := by
  rcases Nat.le_total a b with h | h
  · rw [mymax_eq_right h, mymax_eq_right (Nat.succ_le_succ h)]
  · rw [mymax_eq_left h, mymax_eq_left (Nat.succ_le_succ h)]
private theorem zeromax (n : Nat) : Nat.max 0 n = n := mymax_eq_right (Nat.zero_le n)
private theorem maxzero (n : Nat) : Nat.max n 0 = n := mymax_eq_left (Nat.zero_le n)

theorem length_listScaleR (r : Real) : ∀ l : List Real, (listScaleR r l).length = l.length
  | [] => rfl
  | q :: qs => by
      show ((r * q) :: listScaleR r qs).length = (q :: qs).length
      rw [List.length_cons, List.length_cons, length_listScaleR r qs]

theorem length_listAddR : ∀ l1 l2 : List Real, (listAddR l1 l2).length = Nat.max l1.length l2.length
  | [], qs => by rw [listAddR_nil_left, List.length_nil, zeromax]
  | p :: ps, [] => by rw [listAddR_nil_right, List.length_nil, maxzero]
  | p :: ps, q :: qs => by
      rw [listAddR_cons_cons, List.length_cons, length_listAddR ps qs,
          List.length_cons, List.length_cons]
      exact max_succ _ _

theorem length_listSubR : ∀ l1 l2 : List Real, (listSubR l1 l2).length = Nat.max l1.length l2.length
  | [], [] => rfl
  | [], q :: qs => by
      rw [listSubR_nil_cons, List.length_cons, length_listSubR [] qs, List.length_nil,
          List.length_cons]
      simp only [zeromax]
  | p :: ps, [] => by
      show (p :: ps).length = Nat.max (p :: ps).length ([] : List Real).length
      rw [List.length_nil, maxzero]
  | p :: ps, q :: qs => by
      show ((p - q) :: listSubR ps qs).length = Nat.max (p :: ps).length (q :: qs).length
      rw [List.length_cons, length_listSubR ps qs, List.length_cons, List.length_cons]
      exact max_succ _ _

/-- **Tight convolution length** (both lists nonempty): `length (listMulR l1 l2) = |l1| + |l2| − 1`. -/
theorem length_listMulR (l2 : List Real) (hl2 : l2 ≠ []) :
    ∀ l1 : List Real, l1 ≠ [] → (listMulR l1 l2).length = l1.length + l2.length - 1
  | [], h => absurd rfl h
  | p :: ps, _ => by
      have hl2pos : (1 : Nat) ≤ l2.length := Nat.pos_of_ne_zero (fun h => hl2 (List.length_eq_zero.mp h))
      show (listAddR (listScaleR p l2) (0 :: listMulR ps l2)).length
          = (p :: ps).length + l2.length - 1
      rw [length_listAddR, length_listScaleR p l2]
      cases ps with
      | nil =>
        rw [show listMulR ([] : List Real) l2 = [] from rfl]
        show Nat.max l2.length 1 = 1 + l2.length - 1
        rw [mymax_eq_left hl2pos]; omega
      | cons p' ps' =>
        have ih := length_listMulR l2 hl2 (p' :: ps') (by simp)
        rw [List.length_cons, ih]
        rw [mymax_eq_right (by simp only [List.length_cons]; omega)]
        simp only [List.length_cons]; omega

/-- **Bridge piece (3).** The converted single-var Poly's coefficient count is `≤ degreeX m + 1`:
`add/sub→max`, `mul→convolution` (`|Lp|+|Lq|−1 ≤ (dp+1)+(dq+1)−1 = dp+dq+1`). -/
theorem length_polyCoeffs_mP2PFL_le : ∀ m : MultiPoly 2,
    (polyCoeffs (multiPolyToPolyForLex m)).length ≤ degreeX m + 1
  | .const _ => Nat.le_refl _
  | .varX => Nat.le_refl _
  | .varY _ => Nat.le_refl _
  | .add p q => by
      show (listAddR (polyCoeffs (multiPolyToPolyForLex p)) (polyCoeffs (multiPolyToPolyForLex q))).length
          ≤ Nat.max (degreeX p) (degreeX q) + 1
      rw [length_listAddR]
      exact Nat.max_le.mpr
        ⟨Nat.le_trans (length_polyCoeffs_mP2PFL_le p) (Nat.add_le_add_right (Nat.le_max_left _ _) 1),
         Nat.le_trans (length_polyCoeffs_mP2PFL_le q) (Nat.add_le_add_right (Nat.le_max_right _ _) 1)⟩
  | .sub p q => by
      show (listSubR (polyCoeffs (multiPolyToPolyForLex p)) (polyCoeffs (multiPolyToPolyForLex q))).length
          ≤ Nat.max (degreeX p) (degreeX q) + 1
      rw [length_listSubR]
      exact Nat.max_le.mpr
        ⟨Nat.le_trans (length_polyCoeffs_mP2PFL_le p) (Nat.add_le_add_right (Nat.le_max_left _ _) 1),
         Nat.le_trans (length_polyCoeffs_mP2PFL_le q) (Nat.add_le_add_right (Nat.le_max_right _ _) 1)⟩
  | .mul p q => by
      show (listMulR (polyCoeffs (multiPolyToPolyForLex p)) (polyCoeffs (multiPolyToPolyForLex q))).length
          ≤ degreeX p + degreeX q + 1
      rw [length_listMulR _ (polyCoeffs_nonempty _) _ (polyCoeffs_nonempty _)]
      have ihp := length_polyCoeffs_mP2PFL_le p
      have ihq := length_polyCoeffs_mP2PFL_le q
      omega

/-- **The measure↔degreeX bridge (CLOSED).** The chain-2 measure's x-component is bounded by the
polynomial's x-degree: `singleExpMeasureCanon(lcY₁ q).2 ≤ degreeX q + 2`. So `B := degreeX p₀ + 2` is a
valid global bound — and since `degreeX` is non-increasing under both recursion arms (reduce +
`degreeX_dropLeadingYAt_le`), the whole B-bound of the explicit chain-2 program holds. -/
theorem singleExpMeasureCanon_snd_le (q : MultiPoly 2) :
    (singleExpMeasureCanon (leadingCoeffY (⟨1, by omega⟩ : Fin 2) q)).2 ≤ degreeX q + 2 := by
  show polyTrueDegreeStrict (polyCoeffs (multiPolyToPolyForLex
        (canonLcY0 (leadingCoeffY (⟨1, by omega⟩ : Fin 2) q)))) ≤ degreeX q + 2
  have h1 := polyTrueDegreeStrict_le_length (polyCoeffs (multiPolyToPolyForLex
        (canonLcY0 (leadingCoeffY (⟨1, by omega⟩ : Fin 2) q))))
  have h3 := length_polyCoeffs_mP2PFL_le (canonLcY0 (leadingCoeffY (⟨1, by omega⟩ : Fin 2) q))
  have h2 := degreeX_canonLcY0_lcY1_le q
  omega

end MachLib.ChainExp2Explicit
