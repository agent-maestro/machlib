import MachLib.Summability
import MachLib.IntermediateValue
import MachLib.Differentiation

/-!
# Uniform convergence and continuity — the Weierstrass M-test

`Summability.lean` proved the Weierstrass term sequence has bounded partial sums, for every
fixed `t>0` and `k`, but explicitly stopped short of (1) an actual x-dependent series (no
`Real.cos`) and (2) uniform convergence. This file closes gap (1)-(2): given an x-indexed family
`term : Nat → Real → Real` dominated by an x-INDEPENDENT nonneg summable majorant `A`, it builds
a genuine pointwise sum `W : Real → Real`, proves the convergence is uniform in `x` (the classical
Weierstrass M-test), and — since a HasDerivAt witness is supplied for each term — concludes `W`
is continuous everywhere.

## The one real obstacle: `term n x` oscillates in sign

Everything in `Summability.lean` only handled NONNEGATIVE sequences (needed for `sup_exists`'s
monotone-partial-sums argument to even make sense). `term n x` does not stay one sign — for the
Weierstrass application it is `A n * cos(θ)`, which crosses zero constantly. Standard fix, done
here explicitly since MachLib has no general "signed series" theory: decompose every term into
`posPart − negPart` (both nonneg, each dominated by `abs (term n x) ≤ A n`), sum EACH piece via
the nonneg machinery, and define `W x := (sum of posPart) − (sum of negPart)`. This is exactly
how the classical proof of "absolutely convergent ⇒ convergent" works when you don't have Cauchy
sequences to fall back on.

## What this proves

  - `continuousSum_of_uniform_dominated` — the abstract M-test: nonneg summable majorant `A` +
    domination `abs(term n x) ≤ A n` + a `HasDerivAt` witness for each `term n` ⟹ a pointwise sum
    `W` exists, the convergence to `W` is uniform in `x`, and `W` is continuous everywhere. Fully
    general — not specific to `cos` or Weierstrass.

## What this does NOT do

Still not the full EML Weierstrass theorem: this is continuity, not `C^∞`. Term-by-term
differentiation — showing the FORMALLY differentiated series (the `k≥1` term sequences, already
summable per `weierstrass_term_hasBoundedPartialSums`) actually equals the derivative of `W` — is
a separate, further theorem (needs a uniform-convergence-of-derivatives ⟹ derivative-of-limit
argument, not attempted here). Wiring this abstract theorem to the actual `a=1/2,b=3` Weierstrass
`Real.cos` series is also left to a follow-up file — this one is the general M-test substrate.

`sorryAx`-free, Mathlib-free, no new axioms beyond what MachLib already has (`sup_exists`,
`hasDerivAt_continuousAt`, `HasDerivAt_*` closure rules — all pre-existing and already trusted).
-/

namespace MachLib
namespace Real

/-! ## §1 — General partial-sum utilities: comparison, splitting, congruence, subtraction -/

theorem partialSum_le_of_le {f g : Nat → Real} (hfg : ∀ i, f i ≤ g i) :
    ∀ n, partialSum f n ≤ partialSum g n
  | 0 => le_refl 0
  | n + 1 => by
      rw [partialSum_succ, partialSum_succ]
      exact add_le_add_both (partialSum_le_of_le hfg n) (hfg n)

theorem partialSum_congr {f g : Nat → Real} (h : ∀ i, f i = g i) :
    ∀ n, partialSum f n = partialSum g n
  | 0 => rfl
  | n + 1 => by rw [partialSum_succ, partialSum_succ, partialSum_congr h n, h n]

private theorem assoc3_ring (p q r : Real) : (p + q) + r = p + (q + r) := by
  mach_mpoly [p, q, r]

theorem partialSum_split (f : Nat → Real) (n : Nat) :
    ∀ m, partialSum f (n + m) = partialSum f n + partialSum (fun i => f (n + i)) m
  | 0 => by
      show partialSum f (n + 0) = partialSum f n + partialSum (fun i => f (n + i)) 0
      rw [Nat.add_zero, show partialSum (fun i => f (n + i)) 0 = 0 from rfl,
          show partialSum f n + 0 = partialSum f n from by mach_ring]
  | m + 1 => by
      have ih := partialSum_split f n m
      have hidx : n + (m + 1) = (n + m) + 1 := by omega
      rw [hidx, partialSum_succ, ih]
      show (partialSum f n + partialSum (fun i => f (n + i)) m) + f (n + m)
        = partialSum f n + partialSum (fun i => f (n + i)) (m + 1)
      rw [partialSum_succ]
      exact assoc3_ring (partialSum f n) (partialSum (fun i => f (n + i)) m) (f (n + m))

theorem hasBoundedPartialSums_of_le {f g : Nat → Real} (hle : ∀ i, f i ≤ g i)
    (hg : HasBoundedPartialSums g) : HasBoundedPartialSums f := by
  obtain ⟨M, hM⟩ := hg
  refine ⟨M, fun x hx => ?_⟩
  obtain ⟨n, hn⟩ := hx
  rw [hn]
  exact le_trans (partialSum_le_of_le hle n) (hM (partialSum g n) ⟨n, rfl⟩)

theorem partialSum_sub (f g : Nat → Real) :
    ∀ n, partialSum (fun i => f i - g i) n = partialSum f n - partialSum g n
  | 0 => by show (0 : Real) = 0 - 0; mach_ring
  | n + 1 => by
      rw [partialSum_succ, partialSum_succ, partialSum_succ, partialSum_sub f g n]
      show (partialSum f n - partialSum g n) + (f n - g n)
        = (partialSum f n + f n) - (partialSum g n + g n)
      mach_mpoly [partialSum f n, partialSum g n, f n, g n]

/-! ## §2 — Tail-to-zero from the LUB property, and tail-comparison under domination -/

private theorem add_le_add_right_local {a b : Real} (h : a ≤ b) (c : Real) : a + c ≤ b + c := by
  rw [add_comm a c, add_comm b c]; exact add_le_add_left h c

private theorem add_lt_add_right_local {a b : Real} (h : a < b) (c : Real) : a + c < b + c := by
  rw [add_comm a c, add_comm b c]; exact add_lt_add_left h c

theorem tail_lt_of_sup {f : Nat → Real} (hfnn : ∀ n, 0 ≤ f n) {s : Real}
    (hlub : ∀ s', (∀ n, partialSum f n ≤ s') → s ≤ s')
    {ε : Real} (hε : 0 < ε) :
    ∃ N, ∀ n, N ≤ n → s - partialSum f n < ε := by
  have hex : ∃ N, s - ε < partialSum f N := by
    apply Classical.byContradiction
    intro hnex
    have hallub : ∀ n, partialSum f n ≤ s - ε := by
      intro n
      rcases lt_total (s - ε) (partialSum f n) with h | h | h
      · exact absurd ⟨n, h⟩ hnex
      · exact (le_iff_lt_or_eq (partialSum f n) (s - ε)).mpr (Or.inr h.symm)
      · exact le_of_lt h
    have hle : s ≤ s - ε := hlub (s - ε) hallub
    have h1 : s + 0 < s + ε := add_lt_add_left hε s
    have h2 : s + (0 : Real) = s := by mach_ring
    rw [h2] at h1
    have h3 : s + ε ≤ (s - ε) + ε := add_le_add_right_local hle ε
    have h4 : (s - ε) + ε = s := by mach_ring
    rw [h4] at h3
    exact absurd (lt_of_lt_of_le h1 h3) (lt_irrefl_ax s)
  obtain ⟨N, hN⟩ := hex
  refine ⟨N, fun n hn => ?_⟩
  have hmono : partialSum f N ≤ partialSum f n := partialSum_mono hfnn hn
  have hlt : s - ε < partialSum f n := lt_of_lt_of_le hN hmono
  have h1 : s < partialSum f n + ε := by
    have h2 := add_lt_add_right_local hlt ε
    rwa [show (s - ε) + ε = s from by mach_ring] at h2
  have h3 := add_lt_add_right_local h1 (-(partialSum f n))
  rwa [show partialSum f n + ε + -(partialSum f n) = ε from by mach_ring,
       show s + -(partialSum f n) = s - partialSum f n from by mach_ring] at h3

theorem tail_le_tail_of_dominated {f g : Nat → Real}
    (hfnn : ∀ i, 0 ≤ f i) (hle : ∀ i, f i ≤ g i)
    {sf sg : Real}
    (hlubf : ∀ s', (∀ n, partialSum f n ≤ s') → sf ≤ s')
    (hubg : ∀ n, partialSum g n ≤ sg) (n : Nat) :
    sf - partialSum f n ≤ sg - partialSum g n := by
  have hbound : sf ≤ partialSum f n + (sg - partialSum g n) := by
    apply hlubf
    intro m
    rcases Nat.le_total m n with hmn | hmn
    · have h1 : (0 : Real) ≤ sg - partialSum g n := sub_nonneg_of_le (hubg n)
      have h2 := add_le_add_left h1 (partialSum f n)
      rw [show partialSum f n + 0 = partialSum f n from by mach_ring] at h2
      exact le_trans (partialSum_mono hfnn hmn) h2
    · obtain ⟨k, hk⟩ := Nat.le.dest hmn
      rw [← hk, partialSum_split f n k]
      have htail_le : partialSum (fun i => f (n + i)) k ≤ partialSum (fun i => g (n + i)) k :=
        partialSum_le_of_le (fun i => hle (n + i)) k
      have hg_split : partialSum g (n + k) = partialSum g n + partialSum (fun i => g (n + i)) k :=
        partialSum_split g n k
      have hgnk_le_sg : partialSum g n + partialSum (fun i => g (n + i)) k ≤ sg := by
        rw [← hg_split]; exact hubg (n + k)
      have hgk_le : partialSum (fun i => g (n + i)) k ≤ sg - partialSum g n := by
        have h2 := add_le_add_left hgnk_le_sg (-(partialSum g n))
        rwa [show -(partialSum g n) + (partialSum g n + partialSum (fun i => g (n + i)) k)
                = partialSum (fun i => g (n + i)) k from by
               mach_mpoly [partialSum g n, partialSum (fun i => g (n + i)) k],
             show -(partialSum g n) + sg = sg - partialSum g n from by mach_mpoly [partialSum g n, sg]]
          at h2
      exact add_le_add_left (le_trans htail_le hgk_le) (partialSum f n)
  have h2 := add_le_add_right_local hbound (-(partialSum f n))
  rwa [show partialSum f n + (sg - partialSum g n) + -(partialSum f n) = sg - partialSum g n
         from by mach_mpoly [partialSum f n, sg, partialSum g n],
       show sf + -(partialSum f n) = sf - partialSum f n from by mach_mpoly [sf, partialSum f n]]
    at h2

/-! ## §3 — Pointwise `posPart`/`negPart` decomposition (handles oscillating-sign terms) -/

noncomputable def posPart (v : Real) : Real := (abs v + v) / (1 + 1)
noncomputable def negPart (v : Real) : Real := (abs v - v) / (1 + 1)

private theorem h11pos : (0 : Real) < 1 + 1 := add_pos one_pos one_pos
private theorem h11ne : (1 + 1 : Real) ≠ 0 := ne_of_gt h11pos

theorem posPart_nonneg (v : Real) : 0 ≤ posPart v := by
  unfold posPart
  have h1 : -v ≤ abs v := neg_le_abs v
  have h2 := add_le_add_right_local h1 v
  rw [show -v + v = (0 : Real) from by mach_ring] at h2
  rw [div_def (abs v + v) (1 + 1) h11ne]
  exact mul_nonneg h2 (le_of_lt (div_pos_of_pos_pos one_pos h11pos))

theorem negPart_nonneg (v : Real) : 0 ≤ negPart v := by
  unfold negPart
  have h1 : (0 : Real) ≤ abs v - v := sub_nonneg_of_le (le_abs_self v)
  rw [div_def (abs v - v) (1 + 1) h11ne]
  exact mul_nonneg h1 (le_of_lt (div_pos_of_pos_pos one_pos h11pos))

theorem posPart_sub_negPart (v : Real) : posPart v - negPart v = v := by
  unfold posPart negPart
  rw [div_sub_div_same h11ne,
      show (abs v + v) - (abs v - v) = (1 + 1) * v from by mach_mpoly [abs v, v]]
  exact mul_div_cancel_left' h11ne

theorem posPart_le_abs (v : Real) : posPart v ≤ abs v := by
  unfold posPart
  have h2 := add_le_add_left (le_abs_self v) (abs v)
  rw [show abs v + abs v = abs v * (1 + 1) from by mach_ring] at h2
  have h4 := mul_le_mul_of_nonneg_right h2 (le_of_lt (div_pos_of_pos_pos one_pos h11pos))
  rw [div_def (abs v + v) (1 + 1) h11ne]
  rwa [show abs v * (1 + 1) * (1 / (1 + 1)) = abs v from by
         rw [mul_assoc, mul_inv (1 + 1) h11ne, mul_one_ax]] at h4

theorem negPart_le_abs (v : Real) : negPart v ≤ abs v := by
  unfold negPart
  have h2 := add_le_add_left (neg_le_abs v) (abs v)
  rw [show abs v + -v = abs v - v from by mach_mpoly [abs v, v],
      show abs v + abs v = abs v * (1 + 1) from by mach_ring] at h2
  have h4 := mul_le_mul_of_nonneg_right h2 (le_of_lt (div_pos_of_pos_pos one_pos h11pos))
  rw [div_def (abs v - v) (1 + 1) h11ne]
  rwa [show abs v * (1 + 1) * (1 / (1 + 1)) = abs v from by
         rw [mul_assoc, mul_inv (1 + 1) h11ne, mul_one_ax]] at h4

/-! ## §4 — Triangle-inequality glue -/

private theorem abs_sub_triangle (a b c : Real) : abs (a - c) ≤ abs (a - b) + abs (b - c) := by
  rw [show a - c = (a - b) + (b - c) from by mach_mpoly [a, b, c]]
  exact abs_add (a - b) (b - c)

private theorem abs_sub_le_local (a b : Real) : abs (a - b) ≤ abs a + abs b := by
  have h := abs_add a (-b)
  rw [show a + -b = a - b from by mach_mpoly [a, b], abs_neg b] at h
  exact h

private theorem add_lt_add_local {a b c d : Real} (h1 : a < b) (h2 : c < d) : a + c < b + d :=
  lt_trans_ax (add_lt_add_right_local h1 c) (add_lt_add_left h2 b)

/-! ## §5 — The abstract Weierstrass M-test -/

/-- **Weierstrass M-test.** Given a nonneg summable majorant `A` and an x-indexed family `term`
dominated by it (`abs (term n x) ≤ A n`) with a `HasDerivAt` witness for each `term n`, the
pointwise sum `W` exists, convergence to it is uniform in `x`, and `W` is continuous everywhere.
`A` is x-INDEPENDENT — that's what makes the convergence uniform, not just pointwise. -/
theorem continuousSum_of_uniform_dominated
    {A : Nat → Real} (hAnn : ∀ n, 0 ≤ A n) (hAbdd : HasBoundedPartialSums A)
    {term term' : Nat → Real → Real}
    (hdom : ∀ n x, abs (term n x) ≤ A n)
    (hderiv : ∀ n x, HasDerivAt (term n) (term' n x) x) :
    ∃ W : Real → Real,
      (∀ ε : Real, 0 < ε → ∃ N, ∀ n, N ≤ n → ∀ x,
        abs (W x - partialSum (fun i => term i x) n) < ε)
      ∧ ∀ x0, ContinuousAt W x0 := by
  obtain ⟨SumA, hSumA_ub, hSumA_lub⟩ := series_sum_exists_of_bounded hAnn hAbdd
  have hGex : ∀ x, ∃ s : Real, (∀ n, partialSum (fun i => posPart (term i x)) n ≤ s) ∧
      ∀ s', (∀ n, partialSum (fun i => posPart (term i x)) n ≤ s') → s ≤ s' := fun x =>
    series_sum_exists_of_bounded (fun n => posPart_nonneg (term n x))
      (hasBoundedPartialSums_of_le (fun n => le_trans (posPart_le_abs (term n x)) (hdom n x)) hAbdd)
  have hHex : ∀ x, ∃ s : Real, (∀ n, partialSum (fun i => negPart (term i x)) n ≤ s) ∧
      ∀ s', (∀ n, partialSum (fun i => negPart (term i x)) n ≤ s') → s ≤ s' := fun x =>
    series_sum_exists_of_bounded (fun n => negPart_nonneg (term n x))
      (hasBoundedPartialSums_of_le (fun n => le_trans (negPart_le_abs (term n x)) (hdom n x)) hAbdd)
  let Gsum : Real → Real := fun x => Classical.choose (hGex x)
  let Hsum : Real → Real := fun x => Classical.choose (hHex x)
  have hGspec : ∀ x, (∀ n, partialSum (fun i => posPart (term i x)) n ≤ Gsum x) ∧
      ∀ s', (∀ n, partialSum (fun i => posPart (term i x)) n ≤ s') → Gsum x ≤ s' :=
    fun x => Classical.choose_spec (hGex x)
  have hHspec : ∀ x, (∀ n, partialSum (fun i => negPart (term i x)) n ≤ Hsum x) ∧
      ∀ s', (∀ n, partialSum (fun i => negPart (term i x)) n ≤ s') → Hsum x ≤ s' :=
    fun x => Classical.choose_spec (hHex x)
  let W : Real → Real := fun x => Gsum x - Hsum x
  have huniform : ∀ ε : Real, 0 < ε → ∃ N, ∀ n, N ≤ n → ∀ x,
      abs (W x - partialSum (fun i => term i x) n) < ε := by
    intro ε hε
    have hε2 : 0 < ε / (1 + 1) := div_pos_of_pos_pos hε h11pos
    obtain ⟨N, hN⟩ := tail_lt_of_sup hAnn hSumA_lub hε2
    refine ⟨N, fun n hn x => ?_⟩
    have hPtail : Gsum x - partialSum (fun i => posPart (term i x)) n ≤ SumA - partialSum A n :=
      tail_le_tail_of_dominated (fun i => posPart_nonneg (term i x))
        (fun i => le_trans (posPart_le_abs (term i x)) (hdom i x)) (hGspec x).2 hSumA_ub n
    have hQtail : Hsum x - partialSum (fun i => negPart (term i x)) n ≤ SumA - partialSum A n :=
      tail_le_tail_of_dominated (fun i => negPart_nonneg (term i x))
        (fun i => le_trans (negPart_le_abs (term i x)) (hdom i x)) (hHspec x).2 hSumA_ub n
    have hPnn : 0 ≤ Gsum x - partialSum (fun i => posPart (term i x)) n :=
      sub_nonneg_of_le ((hGspec x).1 n)
    have hQnn : 0 ≤ Hsum x - partialSum (fun i => negPart (term i x)) n :=
      sub_nonneg_of_le ((hHspec x).1 n)
    have hAtail : SumA - partialSum A n < ε / (1 + 1) := hN n hn
    have hPlt := lt_of_le_of_lt hPtail hAtail
    have hQlt := lt_of_le_of_lt hQtail hAtail
    have hterm_eq : partialSum (fun i => term i x) n
        = partialSum (fun i => posPart (term i x)) n - partialSum (fun i => negPart (term i x)) n := by
      rw [← partialSum_sub]
      exact partialSum_congr (fun i => (posPart_sub_negPart (term i x)).symm) n
    show abs ((Gsum x - Hsum x) - partialSum (fun i => term i x) n) < ε
    rw [hterm_eq,
        show (Gsum x - Hsum x)
            - (partialSum (fun i => posPart (term i x)) n - partialSum (fun i => negPart (term i x)) n)
            = (Gsum x - partialSum (fun i => posPart (term i x)) n)
              - (Hsum x - partialSum (fun i => negPart (term i x)) n) from by
          mach_mpoly [Gsum x, Hsum x, partialSum (fun i => posPart (term i x)) n,
            partialSum (fun i => negPart (term i x)) n]]
    have habs := abs_sub_le_local (Gsum x - partialSum (fun i => posPart (term i x)) n)
      (Hsum x - partialSum (fun i => negPart (term i x)) n)
    rw [abs_of_nonneg hPnn, abs_of_nonneg hQnn] at habs
    refine lt_of_le_of_lt habs ?_
    have h := add_lt_add_local hPlt hQlt
    rwa [show ε / (1 + 1) + ε / (1 + 1) = ε from by
           rw [div_add_div_same h11ne, show ε + ε = (1 + 1) * ε from by mach_ring]
           exact mul_div_cancel_left' h11ne] at h
  refine ⟨W, huniform, fun x0 => ?_⟩
  have hPS_deriv : ∀ N x, HasDerivAt (fun y => partialSum (fun i => term i y) N)
      (partialSum (fun i => term' i x) N) x := by
    intro N x
    induction N with
    | zero => exact HasDerivAt_const 0 x
    | succ n ih =>
        exact HasDerivAt_add (fun y => partialSum (fun i => term i y) n) (term n) _ _ x ih (hderiv n x)
  intro ε hε
  have h3pos : (0 : Real) < 1 + 1 + 1 := by
    have := add_pos h11pos one_pos
    rwa [show (1 : Real) + 1 + 1 = (1 + 1) + 1 from by mach_ring]
  have h3ne : (1 + 1 + 1 : Real) ≠ 0 := ne_of_gt h3pos
  have hε3 : 0 < ε / (1 + 1 + 1) := div_pos_of_pos_pos hε h3pos
  obtain ⟨N, hN⟩ := huniform (ε / (1 + 1 + 1)) hε3
  have hSN_cont : ContinuousAt (fun y => partialSum (fun i => term i y) N) x0 :=
    hasDerivAt_continuousAt (hPS_deriv N x0)
  obtain ⟨δ, hδ, hδprop⟩ := hSN_cont (ε / (1 + 1 + 1)) hε3
  refine ⟨δ, hδ, fun y hy => ?_⟩
  have h1 := hN N (Nat.le_refl N) y
  have h2 := hδprop y hy
  have h3' : abs (partialSum (fun i => term i x0) N - W x0) < ε / (1 + 1 + 1) := by
    rw [abs_sub_comm]; exact hN N (Nat.le_refl N) x0
  have htri1 := abs_sub_triangle (W y) (partialSum (fun i => term i y) N) (W x0)
  have htri2 := abs_sub_triangle (partialSum (fun i => term i y) N)
    (partialSum (fun i => term i x0) N) (W x0)
  have hchain : abs (W y - W x0) ≤ abs (W y - partialSum (fun i => term i y) N)
      + (abs (partialSum (fun i => term i y) N - partialSum (fun i => term i x0) N)
         + abs (partialSum (fun i => term i x0) N - W x0)) :=
    le_trans htri1 (add_le_add_left htri2 (abs (W y - partialSum (fun i => term i y) N)))
  refine lt_of_le_of_lt hchain ?_
  have hs := add_lt_add_local h1 (add_lt_add_local h2 h3')
  rwa [show ε / (1 + 1 + 1) + (ε / (1 + 1 + 1) + ε / (1 + 1 + 1)) = ε from by
         rw [show ε / (1 + 1 + 1) + (ε / (1 + 1 + 1) + ε / (1 + 1 + 1))
               = (ε / (1 + 1 + 1) + ε / (1 + 1 + 1)) + ε / (1 + 1 + 1) from by mach_ring,
             div_add_div_same h3ne, div_add_div_same h3ne,
             show ε + ε + ε = (1 + 1 + 1) * ε from by mach_ring]
         exact mul_div_cancel_left' h3ne] at hs

end Real
end MachLib
