import MachLib.PolynomialRootCount
import MachLib.SturmNonOscillation
import MachLib.FieldLemmas
import MachLib.MultiPoly
import MachLib.PfaffianChain
import MachLib.Log
import MachLib.Exp

/-!
# Constructive Khovanskii for exp+rational chains — Brick 1 (rational base case)

Track B of retiring `PfaffianFunction.zero_count_bound_classical` from the
sin/cos any-depth barrier: extend the constructive Khovanskii step to admit a
rational (`1/x`) generator, which is the one non-exp-type generator EML's
exp+log chains need. Map + plan:
`monogate-research/exploration/eml_exp_rational_khovanskii_extend_scoping_2026_07_07/FINDINGS.md`.

The `1/x` level does not need a Rolle/integrating-factor argument: a Pfaffian
function over the `1/x` bottom is *rational* in `x`, so its zeros are the zeros
of a numerator polynomial — bounded by degree. This file lays the abstract
content of that step, `poly_root_count_bound`-only, division-free:

  **if every zero of `f` on `(a,b)` is also a zero of a not-identically-zero
  polynomial `q`, then `f` has at most `degreeUpper q` zeros there.**

For the `1/x` case, `f z = q z / zᴷ` and (on `z > 0`) `f z = 0 → q z = 0` — the
caller supplies that implication (Brick 1b: the `MultiPoly`-in-`(x,1/x)` →
numerator encoding). This brick is the root-count core the descent's new bottom
case will cite.
-/

namespace MachLib
namespace PolynomialRootCount

open MachLib.Real
open MachLib.PolynomialEvidence

/-- **Brick 1 — zero-count bounded by a dominating polynomial.** If, on `(a,b)`,
every zero of `f` is a zero of a polynomial `q` that is not identically zero,
then any list of distinct zeros of `f` in `(a,b)` has length `≤ degreeUpper q`.
The rational base case (`f = q / xᴷ`, zeros preserved on `x>0`) is the intended
instance; the numerator relation is discharged by the caller via `hsub`. -/
theorem zero_count_bound_of_subset_poly
    (q : Poly) (f : Real → Real) (a b : Real) (hab : a < b)
    (hne : ∃ x : Real, Poly.eval q x ≠ 0)
    (hsub : ∀ z : Real, a < z → z < b → f z = 0 → Poly.eval q z = 0) :
    ∀ zeros : List Real,
      zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ f z = 0) →
      zeros.length ≤ degreeUpper q := by
  intro zeros hnd hz
  refine poly_root_count_bound q a b hab hne zeros hnd (fun z hzmem => ?_)
  obtain ⟨ha, hb, hfz⟩ := hz z hzmem
  exact ⟨ha, hb, hsub z ha hb hfz⟩

end PolynomialRootCount

/-! ## Brick 2 — the reciprocal generator's coherence

The one non-exp generator EML needs is `1/x`, whose Pfaffian relation is
`y' = −y²` (`(1/x)' = −(1/x)²`). This is the coherence the extended descent's
bottom level requires; the `−(y·y)` form matches `MultiPoly.eval (−varY²)` along
a chain with `y = 1/x`. -/

open MachLib.Real

/-- **Brick 2 — reciprocal coherence.** On `x > 0`,
`(1/x)' = −((1/x)·(1/x))` — the `1/x` generator satisfies its Pfaffian relation
`y' = −y²`. Built from `HasDerivAt_inv` (reciprocal rule) with the value bridged
from `−1/(x·x)` to `−((1/x)·(1/x))` via `one_div_mul_one_div` + `neg_div`. -/
theorem reciprocal_hasDerivAt (x : Real) (hx : 0 < x) :
    HasDerivAt (fun x => 1 / x) (-((1 / x) * (1 / x))) x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have h : HasDerivAt (fun y => 1 / y) (-1 / (x * x)) x := by
    simpa using HasDerivAt_inv (fun y => y) 1 x hx0 (HasDerivAt_id x)
  have hb : (-1 / (x * x) : Real) = -((1 / x) * (1 / x)) := by
    rw [one_div_mul_one_div hx, neg_div (ne_of_gt (mul_pos hx hx))]
  rw [hb] at h
  exact h

open MachLib.MultiPolyMod

/-- The Pfaffian relation for a reciprocal generator at level `i`: the
`MultiPoly` `−yᵢ²`. Along a chain whose `yᵢ = 1/x`, its derivative-relation is
`(1/x)' = −(1/x)²` — exactly `reciprocal_hasDerivAt`. -/
noncomputable def reciprocalRelation {n : Nat} (i : Fin n) : MultiPoly n :=
  MultiPoly.neg (MultiPoly.mul (MultiPoly.varY i) (MultiPoly.varY i))

/-- `−yᵢ²` evaluates to `−(env i · env i)`. -/
theorem reciprocal_relation_eval {n : Nat} (i : Fin n) (x : Real)
    (env : Fin n → Real) :
    MultiPoly.eval (reciprocalRelation i) x env = -(env i * env i) := by
  simp only [reciprocalRelation, MultiPoly.neg, MultiPoly.zero, MultiPoly.eval]
  rw [sub_def, zero_add]

/-- **Reciprocal generator coherence (chain form).** A chain level `i` with
`yᵢ = 1/x` and relation `reciprocalRelation i` is coherent at every `x > 0`:
its derivative equals the relation evaluated along the chain. This is the
`IsCoherentAt` obligation for the reciprocal bottom of the extended chain. -/
theorem reciprocal_relation_coherence {n : Nat} (i : Fin n) (x : Real)
    (env : Fin n → Real) (hx : 0 < x) (henv : env i = 1 / x) :
    HasDerivAt (fun x => 1 / x)
      (MultiPoly.eval (reciprocalRelation i) x env) x := by
  rw [reciprocal_relation_eval i x env, henv]
  exact reciprocal_hasDerivAt x hx

/-! ### Structural facts — the reciprocal relation is a valid, triangular,
QUADRATIC bottom (the single obstruction the extension overcomes). -/

/-- **Triangular.** `−yᵢ²` omits every other chain variable
(`degreeY j = 0` for `j ≠ i`), so a reciprocal bottom is a valid triangular
chain level — the descent above it is unaffected. -/
theorem reciprocalRelation_degreeY_of_ne {n : Nat} (i j : Fin n) (h : j ≠ i) :
    MultiPoly.degreeY j (reciprocalRelation i) = 0 := by
  simp [reciprocalRelation, MultiPoly.neg, MultiPoly.zero, MultiPoly.degreeY,
    if_neg h]

/-- **Quadratic in its own variable** (`degreeY i = 2`) — precisely why `1/x`
fails `IsExpChain`, which requires the LINEAR `Gᵢ·yᵢ` (`degreeY i = 1`). This
degree-2 self-relation is the single obstruction the exp+rational extension is
built to clear. -/
theorem reciprocalRelation_degreeY_self {n : Nat} (i : Fin n) :
    MultiPoly.degreeY i (reciprocalRelation i) = 2 := by
  simp [reciprocalRelation, MultiPoly.neg, MultiPoly.zero, MultiPoly.degreeY]

/-! ### The single-reciprocal chain — the descent's new bottom object

The length-1 chain `[1/x]` the extended descent bottoms out at, after stripping
the exp-type levels above. A `MultiPoly` over it is rational in `x`, so its
zeros are bounded by Brick 1 (`zero_count_bound_of_subset_poly`) once the
numerator is cleared (Brick 3b). Its coherence is Brick 2. -/

open MachLib.PfaffianChainMod

/-- The length-1 Pfaffian chain whose only generator is the reciprocal `1/x`
with relation `−y₀²`. -/
noncomputable def reciprocalChain : PfaffianChain 1 :=
  { evals := fun _ x => 1 / x
  , relations := fun i => reciprocalRelation i }

/-- **The reciprocal chain is coherent on any `(a,b) ⊂ (0,∞)`** — each `x>0`
gives `(1/x)' = −(1/x)²` (Brick 2). This is the `IsCoherentOn` obligation the
descent's bottom object must satisfy. -/
theorem reciprocalChain_isCoherentOn (a b : Real) (ha : 0 < a) :
    reciprocalChain.IsCoherentOn a b := by
  intro x hxa hxb i
  have hx : 0 < x := lt_trans_ax ha hxa
  exact reciprocal_relation_coherence i x (reciprocalChain.chainValues x) hx rfl

/-! ## Brick 3b — clearing denominators (`MultiPoly`-in-`(x,1/x)` → numerator)

A `MultiPoly 1` evaluated over the reciprocal bottom (`y = 1/x`) is a rational
function of `x`. Multiplying by `x^(degreeY 0 p)` clears every `1/x`, leaving a
genuine polynomial — the *numerator* `clearNum p`. `clearNum_eval` proves the
key identity `clearNum p = x^(degreeY 0 p) · p(x, 1/x)` on `x > 0`, so on the
positive axis a zero of the reciprocal-evaluated `p` is a zero of `clearNum p`
(the denominator `x^K ≠ 0`). This is the bridge from the reciprocal chain to
`PolynomialRootCount` — no analytic (`rolle`) step at the bottom.

The clearing power is `degreeY 0`: `mul` *adds* it (numerators multiply cleanly),
`add`/`sub` *share* it (`Nat.max`, padding the lower-degree side by `x^(m−dᵢ)`).
`polyVarPow k` carries `xᵏ` inside `Poly` (MachLib has no `Real`-`Nat` power). -/

open MachLib.PolynomialEvidence

/-- `xᵏ` realised as a `Poly` (iterated `var`); keeps the clearing power inside
the polynomial world so `PolynomialRootCount` applies directly. -/
noncomputable def polyVarPow : Nat → Poly
  | 0 => Poly.const 1
  | k + 1 => Poly.mul Poly.var (polyVarPow k)

theorem polyVarPow_eval_zero (x : Real) : Poly.eval (polyVarPow 0) x = 1 := rfl

theorem polyVarPow_eval_succ (k : Nat) (x : Real) :
    Poly.eval (polyVarPow (k + 1)) x = x * Poly.eval (polyVarPow k) x := rfl

/-- `x^(a+b) = x^a · x^b` at the evaluation level. -/
theorem polyVarPow_eval_add (a b : Nat) (x : Real) :
    Poly.eval (polyVarPow (a + b)) x
      = Poly.eval (polyVarPow a) x * Poly.eval (polyVarPow b) x := by
  induction b with
  | zero =>
    show Poly.eval (polyVarPow a) x
      = Poly.eval (polyVarPow a) x * Poly.eval (polyVarPow 0) x
    rw [polyVarPow_eval_zero]; mach_ring
  | succ b ih =>
    show Poly.eval (polyVarPow ((a + b) + 1)) x
        = Poly.eval (polyVarPow a) x * Poly.eval (polyVarPow (b + 1)) x
    rw [polyVarPow_eval_succ, ih, polyVarPow_eval_succ]; mach_ring

/-- `xᵏ > 0` for `x > 0` — the denominator never vanishes on the positive axis,
so clearing it preserves the zero set (and non-vanishing) of the numerator. -/
theorem polyVarPow_eval_pos {x : Real} (hx : 0 < x) (k : Nat) :
    0 < Poly.eval (polyVarPow k) x := by
  induction k with
  | zero => rw [polyVarPow_eval_zero]; exact one_pos
  | succ k ih => rw [polyVarPow_eval_succ]; exact mul_pos hx ih

/-- Padding algebra for the shared-degree `add` case, factored once:
`x^(m−np)·(x^np·A) + x^(m−nq)·(x^nq·B) = x^m·(A + B)` when `np, nq ≤ m`. -/
theorem pad_combine_add {x : Real} (m np nq : Nat) (A B : Real)
    (hp : np ≤ m) (hq : nq ≤ m) :
    Poly.eval (polyVarPow (m - np)) x * (Poly.eval (polyVarPow np) x * A)
      + Poly.eval (polyVarPow (m - nq)) x * (Poly.eval (polyVarPow nq) x * B)
      = Poly.eval (polyVarPow m) x * (A + B) := by
  have h1 : Poly.eval (polyVarPow (m - np)) x * Poly.eval (polyVarPow np) x
      = Poly.eval (polyVarPow m) x := by
    rw [← polyVarPow_eval_add, Nat.sub_add_cancel hp]
  have h2 : Poly.eval (polyVarPow (m - nq)) x * Poly.eval (polyVarPow nq) x
      = Poly.eval (polyVarPow m) x := by
    rw [← polyVarPow_eval_add, Nat.sub_add_cancel hq]
  rw [← mul_assoc, ← mul_assoc, h1, h2]; mach_ring

/-- Padding algebra for the shared-degree `sub` case. -/
theorem pad_combine_sub {x : Real} (m np nq : Nat) (A B : Real)
    (hp : np ≤ m) (hq : nq ≤ m) :
    Poly.eval (polyVarPow (m - np)) x * (Poly.eval (polyVarPow np) x * A)
      - Poly.eval (polyVarPow (m - nq)) x * (Poly.eval (polyVarPow nq) x * B)
      = Poly.eval (polyVarPow m) x * (A - B) := by
  have h1 : Poly.eval (polyVarPow (m - np)) x * Poly.eval (polyVarPow np) x
      = Poly.eval (polyVarPow m) x := by
    rw [← polyVarPow_eval_add, Nat.sub_add_cancel hp]
  have h2 : Poly.eval (polyVarPow (m - nq)) x * Poly.eval (polyVarPow nq) x
      = Poly.eval (polyVarPow m) x := by
    rw [← polyVarPow_eval_add, Nat.sub_add_cancel hq]
  rw [← mul_assoc, ← mul_assoc, h1, h2]; mach_ring

/-- **Brick 3b — the numerator.** Clear the `1/x` denominators of a `MultiPoly 1`
over the reciprocal bottom to a genuine numerator `Poly`. Clearing power is
`degreeY 0`: `mul` adds it, `add`/`sub` share it (pad the lower side by
`x^(m−dᵢ)`), leaves (`varX`) and constants are already polynomial, and the sole
generator `varY` (`= 1/x`) contributes `Poly.const 1` with one cleared power. -/
noncomputable def clearNum : MultiPoly 1 → Poly
  | MultiPoly.const c => Poly.const c
  | MultiPoly.varX => Poly.var
  | MultiPoly.varY _ => Poly.const 1
  | MultiPoly.add p q =>
      Poly.add
        (Poly.mul (polyVarPow (Nat.max (MultiPoly.degreeY 0 p) (MultiPoly.degreeY 0 q)
                                        - MultiPoly.degreeY 0 p)) (clearNum p))
        (Poly.mul (polyVarPow (Nat.max (MultiPoly.degreeY 0 p) (MultiPoly.degreeY 0 q)
                                        - MultiPoly.degreeY 0 q)) (clearNum q))
  | MultiPoly.sub p q =>
      Poly.sub
        (Poly.mul (polyVarPow (Nat.max (MultiPoly.degreeY 0 p) (MultiPoly.degreeY 0 q)
                                        - MultiPoly.degreeY 0 p)) (clearNum p))
        (Poly.mul (polyVarPow (Nat.max (MultiPoly.degreeY 0 p) (MultiPoly.degreeY 0 q)
                                        - MultiPoly.degreeY 0 q)) (clearNum q))
  | MultiPoly.mul p q => Poly.mul (clearNum p) (clearNum q)

/-- **Brick 3b — eval-agreement.** On `x > 0`,
`clearNum p = x^(degreeY 0 p) · p(x, 1/x)`. Hence on the positive axis every
zero of the reciprocal-evaluated `p` is a zero of the numerator `clearNum p`
(denominator `x^K > 0`), and `p ≢ 0` gives `clearNum p ≢ 0`. This is the exact
hypothesis `PolynomialRootCount.zero_count_bound_of_subset_poly` (Brick 1) wants
— the reciprocal bottom's zero-count with no analytic step. -/
theorem clearNum_eval {x : Real} (hx : 0 < x) (p : MultiPoly 1) :
    Poly.eval (clearNum p) x
      = Poly.eval (polyVarPow (MultiPoly.degreeY 0 p)) x
        * MultiPoly.eval p x (fun _ => 1 / x) := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  induction p with
  | const c =>
    show Poly.eval (Poly.const c) x = Poly.eval (polyVarPow 0) x * c
    rw [polyVarPow_eval_zero]; show c = 1 * c; mach_ring
  | varX =>
    show Poly.eval Poly.var x = Poly.eval (polyVarPow 0) x * x
    rw [polyVarPow_eval_zero]; show x = 1 * x; mach_ring
  | varY j =>
    have hj : (0 : Fin 1) = j := by
      apply Fin.ext; exact (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ j.isLt)).symm
    have hd : MultiPoly.degreeY 0 (MultiPoly.varY j) = 1 := by
      show (if (0 : Fin 1) = j then 1 else 0) = 1
      rw [if_pos hj]
    rw [hd]
    show (1 : Real) = Poly.eval (polyVarPow 1) x * (1 / x)
    rw [polyVarPow_eval_succ, polyVarPow_eval_zero]
    show (1 : Real) = x * 1 * (1 / x)
    rw [mul_one_ax]
    exact (mul_div_cancel_left hx0).symm
  | add p q ihp ihq =>
    show Poly.eval (Poly.add
        (Poly.mul (polyVarPow (Nat.max (MultiPoly.degreeY 0 p) (MultiPoly.degreeY 0 q)
                                        - MultiPoly.degreeY 0 p)) (clearNum p))
        (Poly.mul (polyVarPow (Nat.max (MultiPoly.degreeY 0 p) (MultiPoly.degreeY 0 q)
                                        - MultiPoly.degreeY 0 q)) (clearNum q))) x
        = Poly.eval (polyVarPow (Nat.max (MultiPoly.degreeY 0 p) (MultiPoly.degreeY 0 q))) x
          * MultiPoly.eval (MultiPoly.add p q) x (fun _ => 1 / x)
    simp only [Poly.eval, MultiPoly.eval]
    rw [ihp, ihq]
    exact pad_combine_add _ _ _ _ _ (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  | sub p q ihp ihq =>
    show Poly.eval (Poly.sub
        (Poly.mul (polyVarPow (Nat.max (MultiPoly.degreeY 0 p) (MultiPoly.degreeY 0 q)
                                        - MultiPoly.degreeY 0 p)) (clearNum p))
        (Poly.mul (polyVarPow (Nat.max (MultiPoly.degreeY 0 p) (MultiPoly.degreeY 0 q)
                                        - MultiPoly.degreeY 0 q)) (clearNum q))) x
        = Poly.eval (polyVarPow (Nat.max (MultiPoly.degreeY 0 p) (MultiPoly.degreeY 0 q))) x
          * MultiPoly.eval (MultiPoly.sub p q) x (fun _ => 1 / x)
    simp only [Poly.eval, MultiPoly.eval]
    rw [ihp, ihq]
    exact pad_combine_sub _ _ _ _ _ (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  | mul p q ihp ihq =>
    show Poly.eval (Poly.mul (clearNum p) (clearNum q)) x
        = Poly.eval (polyVarPow (MultiPoly.degreeY 0 p + MultiPoly.degreeY 0 q)) x
          * MultiPoly.eval (MultiPoly.mul p q) x (fun _ => 1 / x)
    simp only [Poly.eval, MultiPoly.eval]
    rw [ihp, ihq, polyVarPow_eval_add]; mach_ring

/-! ## Brick 3c — the reciprocal bottom's zero-count (the descent's base case)

Combine Brick 3b (`clearNum_eval`) with Brick 1
(`zero_count_bound_of_subset_poly`): a `MultiPoly 1` evaluated over the
reciprocal bottom `y = 1/x` has, on any `(a,b) ⊂ (0,∞)`, at most
`degreeUpper (clearNum p)` zeros — **provided its numerator is not identically
zero**. The `hsub` obligation is discharged by `clearNum_eval`: on `z > 0`,
`clearNum p z = z^K · p(z,1/z)`, so `p(z,1/z) = 0 ⇒ clearNum p z = 0`.

This is the *new base case* the extended descent bottoms out at, replacing the
exp-chain base `pfaffian_bound2_gen` when the chain's lowest generator is `1/x`.
Its only analytic input is `rolle` (via `PolynomialRootCount`) — no classical
Khovanskii axiom, exactly the point of the exp+rational track. -/

open MachLib.PolynomialRootCount

/-- **Brick 3c — reciprocal-bottom zero-count.** On `(a,b) ⊂ (0,∞)`, the
reciprocal-evaluated `MultiPoly 1` `x ↦ p(x, 1/x)` has at most
`degreeUpper (clearNum p)` distinct zeros, given its numerator is not
identically zero (`hne`). Root-count by degree of the cleared numerator —
`rolle`-only, no `zero_count_bound_classical`. -/
theorem reciprocalPfaffian_zero_count
    (p : MultiPoly 1) (a b : Real) (hab : a < b) (ha : 0 < a)
    (hne : ∃ x : Real, Poly.eval (clearNum p) x ≠ 0) :
    ∀ zeros : List Real,
      zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ MultiPoly.eval p z (fun _ => 1 / z) = 0) →
      zeros.length ≤ degreeUpper (clearNum p) := by
  apply zero_count_bound_of_subset_poly (clearNum p)
    (fun x => MultiPoly.eval p x (fun _ => 1 / x)) a b hab hne
  intro z hza _ hfz
  have hz : 0 < z := lt_trans_ax ha hza
  rw [clearNum_eval hz p, show MultiPoly.eval p z (fun _ => 1 / z) = 0 from hfz]
  mach_ring

/-! ## Brick 3d-ii — zero-count transfer across the `x = eᵗ` bijection

The log-substitution route re-charts EML from `x` to `t = log x` and bounds
zeros in the `t`-chart (where the chain is exp-type after clearing). This brick
pulls such a `t`-chart bound back to the `x`-chart: zeros of `f` on `(a,b)`
correspond, via `x = eᵗ`, to zeros of `t ↦ f(eᵗ)` on `(log a, log b)`, and the
correspondence preserves the count. Self-contained (`exp`/`log` bijection only)
and needed by every version of the descent-transfer, independent of how the
`t`-chart bound itself is obtained. -/

/-- **Brick 3d-ii — transfer.** If every nodup list of zeros of `t ↦ f(eᵗ)` on
`(log a, log b)` has length `≤ N`, then so does every nodup list of zeros of `f`
on `(a,b) ⊂ (0,∞)`. Map the `x`-zeros through `log`: the list stays nodup
(`log` injective on positives, via `exp_log`) and length-preserving
(`List.length_map`), and each image is a zero of `f∘exp` in `(log a, log b)`
(`log` strictly monotone, via `log_lt_log`). -/
theorem zero_count_transfer
    (f : Real → Real) (a b : Real) (ha : 0 < a) (N : Nat)
    (hgbound : ∀ zeros : List Real,
        zeros.Nodup →
        (∀ s ∈ zeros, log a < s ∧ s < log b ∧ f (exp s) = 0) →
        zeros.length ≤ N) :
    ∀ zeros : List Real,
      zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ f z = 0) →
      zeros.length ≤ N := by
  intro Z hZnd hZ
  have hpos : ∀ z ∈ Z, 0 < z := fun z hz => lt_trans_ax ha (hZ z hz).1
  have hmap : (Z.map log).length = Z.length := List.length_map Z log
  rw [← hmap]
  apply hgbound (Z.map log)
  · rw [List.Nodup, List.pairwise_map]
    refine hZnd.imp_of_mem (fun {x y} hx hy hxy => ?_)
    intro hlog
    exact hxy (by
      have := congrArg exp hlog
      rwa [exp_log (hpos x hx), exp_log (hpos y hy)] at this)
  · intro s hs
    rw [List.mem_map] at hs
    obtain ⟨z, hzZ, hzs⟩ := hs
    obtain ⟨haz, hzb, hfz⟩ := hZ z hzZ
    have hz0 : 0 < z := hpos z hzZ
    subst hzs
    exact ⟨log_lt_log ha haz, log_lt_log hz0 hzb, by rw [exp_log hz0]; exact hfz⟩

end MachLib
