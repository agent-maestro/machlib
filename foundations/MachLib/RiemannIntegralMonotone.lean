import MachLib.Summability
import MachLib.IntermediateValue
import MachLib.NatCastArith
import MachLib.Decimal
import MachLib.FieldLemmas
import MachLib.DivisionError
import MachLib.WitnessResidualDeepNumeric

/-!
# Riemann integration, uniform partitions, monotone functions

The scoped first piece of the integration-theory substrate MachLib doesn't have (see
`MachLib.ProbabilisticBound`'s header for the standing "no measure theory" boundary, and
`MachLib.ElementaryEMLErf` for what that boundary currently blocks). Full Riemann integration
(general partitions, continuous integrands via Heine-Cantor uniform continuity) is a much larger
undertaking; this file scopes to what's tractable in one push: **uniform partitions only** (`n`
equally spaced points, not general finite point sets), and **monotone integrands only** (so the
Darboux upper/lower sum on each subinterval is just the function value at an endpoint — no
per-subinterval `sup_exists`/`inf_exists`/choice needed, only ordinary finite sums, reusing
`Summability.partialSum`).

## Why monotone-first is the right scope

For a general bounded `f`, the Darboux lower/upper sum on subinterval `i` is `inf`/`sup` of `f`
over that subinterval — an existential object needing `inf_exists`/`sup_exists` applied once per
subinterval. For monotone `f`, those are just `f` at the left/right endpoint: no existential
machinery below the top level. This turns the whole construction into ordinary `partialSum`
manipulation, at the cost of only covering monotone integrands. Continuous integrands (needing
Heine-Cantor uniform continuity, which does not exist anywhere in MachLib) are explicitly left for
a follow-up.

## What's proved

Uniform partitions of `[a,b]` into `n` equal pieces give `lowerSum`/`upperSum`. For monotone `f`:
`lowerSum n ≤ upperSum n` and the gap telescopes exactly to `(f b - f a) * (b-a)/n`. To turn this
into a genuine existence result without a general partition-refinement theory, this file uses
**dyadic doubling**: refining a uniform-`n` partition to uniform-`2n` (each subinterval exactly
split in half) only raises the lower sum and only lowers the upper sum. This makes
`{lowerSum (2^k)}` increasing and `{upperSum (2^k)}` decreasing in `k`, and — the actual payoff —
makes EVERY dyadic lower sum `≤` EVERY dyadic upper sum regardless of index
(`lowerSum_le_upperSum_cross`), not just at matching indices. `sup_exists` applied to
`{lowerSum (2^k)}` (bounded above by any fixed dyadic upper sum, via the cross lemma) produces the
headline value `I`; `I` sits between every dyadic lower/upper pair by construction, and the gap
shrinks below any `ε > 0` via `archimedean` on `(f b − f a)(b−a)`. That's `monotone_riemann_integrable`.

`sorryAx`-free, no new axioms — everything here is derived from `sup_exists`/`inf_exists`/
`archimedean` (all pre-existing) plus ordinary field/`Nat` reasoning.
-/

namespace MachLib
namespace Real

/-! ## §1 — Uniform mesh partitions -/

/-- Width of each of the `n` equal subintervals partitioning `[a,b]`. -/
noncomputable def meshWidth (a b : Real) (n : Nat) : Real := (b - a) / natCast n

/-- The `i`-th of `n` equally spaced points partitioning `[a,b]`, `i = 0, …, n`. -/
noncomputable def meshPoint (a b : Real) (n i : Nat) : Real := a + natCast i * meshWidth a b n

theorem meshWidth_nonneg {a b : Real} (hab : a ≤ b) (n : Nat) : 0 ≤ meshWidth a b n := by
  show 0 ≤ (b - a) / natCast n
  exact div_nonneg (sub_nonneg_of_le hab) (natCast_nonneg n)

theorem meshPoint_zero (a b : Real) (n : Nat) : meshPoint a b n 0 = a := by
  show a + natCast 0 * meshWidth a b n = a
  rw [natCast_zero, zero_mul, add_zero]

theorem meshPoint_n (a b : Real) (n : Nat) (hn : 0 < n) : meshPoint a b n n = b := by
  show a + natCast n * meshWidth a b n = b
  show a + natCast n * ((b - a) / natCast n) = b
  rw [mul_div_cancel_left (natCast_ne_zero hn)]
  mach_mpoly [a, b]

/-- Local copy of `natCast`'s monotonicity (avoids importing an unrelated hardware-error file
just for this one Nat-cast fact). -/
theorem natCast_le_of_nat_le {i n : Nat} (h : i ≤ n) : natCast i ≤ natCast n := by
  obtain ⟨d, hd⟩ := Nat.le.dest h
  rw [← hd, natCast_add]
  exact le_add_of_nonneg_right (natCast_nonneg d)

theorem meshPoint_le_succ (a b : Real) (n i : Nat) (hab : a ≤ b) :
    meshPoint a b n i ≤ meshPoint a b n (i + 1) := by
  show a + natCast i * meshWidth a b n ≤ a + natCast (i + 1) * meshWidth a b n
  apply add_le_add_left
  exact mul_le_mul_of_nonneg_right (natCast_le_of_nat_le (by omega)) (meshWidth_nonneg hab n)

theorem meshPoint_mem (a b : Real) (n i : Nat) (hab : a ≤ b) (hn : 0 < n) (hi : i ≤ n) :
    a ≤ meshPoint a b n i ∧ meshPoint a b n i ≤ b := by
  have hcast_nonneg : 0 ≤ natCast i * meshWidth a b n :=
    mul_nonneg (natCast_nonneg i) (meshWidth_nonneg hab n)
  have hupper : natCast i * meshWidth a b n ≤ natCast n * meshWidth a b n :=
    mul_le_mul_of_nonneg_right (natCast_le_of_nat_le hi) (meshWidth_nonneg hab n)
  have hn_width : natCast n * meshWidth a b n = b - a := by
    show natCast n * ((b - a) / natCast n) = b - a
    exact mul_div_cancel_left (natCast_ne_zero hn)
  refine ⟨le_add_of_nonneg_right hcast_nonneg, ?_⟩
  show a + natCast i * meshWidth a b n ≤ b
  rw [hn_width] at hupper
  have hstep : a + natCast i * meshWidth a b n ≤ a + (b - a) := add_le_add_left hupper a
  have heq : a + (b - a) = b := by mach_mpoly [a, b]
  rwa [heq] at hstep

/-! ## §2 — Small reusable field/`partialSum` helpers -/

private theorem sub_add_sub_regroup (p q x y : Real) : (p + x) - (q + y) = (p - q) + (x - y) := by
  mach_mpoly [p, q, x, y]

private theorem three_term_telescope (p q r : Real) : (p - r) + (q - p) = q - r := by
  mach_mpoly [p, q, r]

private theorem sub_mul_common (x y w : Real) : x * w - y * w = (x - y) * w := by
  mach_mpoly [x, y, w]

private theorem mul_add_local (c x y : Real) : c * x + c * y = c * (x + y) := by
  mach_mpoly [c, x, y]

/-- Reciprocal of a product, via `mul_left_cancel` and the `mul_inv` axiom (mirrors
`FieldLemmas.mul_left_cancel`'s own proof shape). -/
private theorem one_div_mul_local {p q : Real} (hp : p ≠ 0) (hq : q ≠ 0) :
    1 / p * (1 / q) = 1 / (p * q) := by
  apply mul_left_cancel (mul_ne_zero hp hq)
  rw [show (p * q) * (1 / p * (1 / q)) = (p * (1 / p)) * (q * (1 / q)) from by mach_ring,
    mul_inv p hp, mul_inv q hq, mul_one_ax, mul_inv (p * q) (mul_ne_zero hp hq)]

/-- Termwise `≤` (on indices `< n`) lifts to `partialSum ≤`. -/
theorem partialSum_le_of_termwise_le {g h : Nat → Real} : ∀ n,
    (∀ i, i < n → h i ≤ g i) → partialSum h n ≤ partialSum g n
  | 0, _ => le_refl 0
  | k + 1, hle => by
      show partialSum h k + h k ≤ partialSum g k + g k
      exact add_le_add_both
        (partialSum_le_of_termwise_le k (fun i hi => hle i (by omega)))
        (hle k (by omega))

/-- Pulling a constant multiple out of a `partialSum`. -/
theorem partialSum_const_mul (c : Real) (g : Nat → Real) : ∀ n,
    partialSum (fun i => c * g i) n = c * partialSum g n
  | 0 => by show (0 : Real) = c * 0; rw [mul_zero]
  | k + 1 => by
      show partialSum (fun i => c * g i) k + c * g k = c * (partialSum g k + g k)
      rw [partialSum_const_mul c g k]
      exact mul_add_local c (partialSum g k) (g k)

/-- **Telescoping** (shift-and-subtract form): `Σᵢ<n g(i+1) − Σᵢ<n g(i) = g n − g 0`. -/
theorem partialSum_shift_sub (g : Nat → Real) : ∀ n : Nat,
    partialSum (fun i => g (i + 1)) n - partialSum g n = g n - g 0
  | 0 => by show (0 : Real) - 0 = g 0 - g 0; mach_mpoly [g 0]
  | k + 1 => by
      show (partialSum (fun i => g (i + 1)) k + g (k + 1)) - (partialSum g k + g k)
        = g (k + 1) - g 0
      rw [sub_add_sub_regroup (partialSum (fun i => g (i + 1)) k) (partialSum g k) (g (k + 1)) (g k)]
      rw [partialSum_shift_sub g k]
      exact three_term_telescope (g k) (g (k + 1)) (g 0)

/-- **Pair-split**: summing `2m` terms equals summing `m` consecutive pairs. -/
theorem partialSum_pair_split (g : Nat → Real) : ∀ m : Nat,
    partialSum g (2 * m) = partialSum (fun i => g (2 * i) + g (2 * i + 1)) m
  | 0 => by show partialSum g 0 = 0; rfl
  | k + 1 => by
      have hidx : 2 * (k + 1) = 2 * k + 1 + 1 := by omega
      rw [hidx]
      show (partialSum g (2 * k) + g (2 * k)) + g (2 * k + 1)
        = partialSum (fun i => g (2 * i) + g (2 * i + 1)) k + (g (2 * k) + g (2 * k + 1))
      rw [partialSum_pair_split g k]
      exact add_assoc _ _ _

/-! ## §3 — Darboux sums for monotone functions -/

/-- `f` is monotone (non-decreasing) on `[a,b]`. -/
def MonotoneOn (f : Real → Real) (a b : Real) : Prop :=
  ∀ x y, a ≤ x → x ≤ y → y ≤ b → f x ≤ f y

/-- Lower Darboux sum, uniform `n`-partition: for monotone `f`, the min on each subinterval is the
left endpoint, so this is just `(Σᵢ<n f(meshPoint i)) · width`. -/
noncomputable def lowerSum (f : Real → Real) (a b : Real) (n : Nat) : Real :=
  partialSum (fun i => f (meshPoint a b n i)) n * meshWidth a b n

/-- Upper Darboux sum, uniform `n`-partition: the max on each subinterval is the right endpoint. -/
noncomputable def upperSum (f : Real → Real) (a b : Real) (n : Nat) : Real :=
  partialSum (fun i => f (meshPoint a b n (i + 1))) n * meshWidth a b n

theorem lowerSum_le_upperSum {f : Real → Real} {a b : Real} (hab : a ≤ b)
    (hmono : MonotoneOn f a b) (n : Nat) (hn : 0 < n) :
    lowerSum f a b n ≤ upperSum f a b n := by
  show partialSum (fun i => f (meshPoint a b n i)) n * meshWidth a b n
    ≤ partialSum (fun i => f (meshPoint a b n (i + 1))) n * meshWidth a b n
  apply mul_le_mul_of_nonneg_right _ (meshWidth_nonneg hab n)
  apply partialSum_le_of_termwise_le
  intro i hi
  have hmemi := meshPoint_mem a b n i hab hn (by omega)
  have hmemi1 := meshPoint_mem a b n (i + 1) hab hn (by omega)
  exact hmono (meshPoint a b n i) (meshPoint a b n (i + 1)) hmemi.1
    (meshPoint_le_succ a b n i hab) hmemi1.2

/-- **The exact gap.** `upperSum n − lowerSum n = (f b − f a) · width`, via telescoping. -/
theorem upperSum_sub_lowerSum (f : Real → Real) (a b : Real) (n : Nat) (hn : 0 < n) :
    upperSum f a b n - lowerSum f a b n = (f b - f a) * meshWidth a b n := by
  show partialSum (fun i => f (meshPoint a b n (i + 1))) n * meshWidth a b n
    - partialSum (fun i => f (meshPoint a b n i)) n * meshWidth a b n
    = (f b - f a) * meshWidth a b n
  rw [sub_mul_common]
  congr 1
  rw [partialSum_shift_sub (fun i => f (meshPoint a b n i)) n, meshPoint_n a b n hn,
    meshPoint_zero a b n]

/-! ## §4 — Dyadic doubling refinement -/

private theorem natCast_one_local : natCast 1 = 1 := by
  rw [natCast_succ, natCast_zero]; exact zero_add 1

theorem natCast_two : natCast (2 : Nat) = 1 + 1 := by
  show natCast (1 + 1 : Nat) = 1 + 1
  rw [natCast_add, natCast_one_local]

/-- Halving the mesh width under doubling. -/
theorem meshWidth_double (a b : Real) (n : Nat) (hn : 0 < n) :
    meshWidth a b (2 * n) = meshWidth a b n / (1 + 1) := by
  show (b - a) / natCast (2 * n) = (b - a) / natCast n / (1 + 1)
  rw [natCast_mul, natCast_two]
  rw [div_def (b - a) ((1 + 1) * natCast n) (mul_ne_zero two_ne_zero (natCast_ne_zero hn))]
  rw [div_def (b - a) (natCast n) (natCast_ne_zero hn)]
  rw [div_def ((b - a) * (1 / natCast n)) (1 + 1) two_ne_zero]
  rw [← one_div_mul_local two_ne_zero (natCast_ne_zero hn)]
  mach_ring

/-- The even-indexed doubled mesh point lands exactly on the coarse mesh point. -/
theorem meshPoint_double_even (a b : Real) (n i : Nat) (hn : 0 < n) :
    meshPoint a b (2 * n) (2 * i) = meshPoint a b n i := by
  show a + natCast (2 * i) * meshWidth a b (2 * n) = a + natCast i * meshWidth a b n
  congr 1
  rw [meshWidth_double a b n hn]
  rw [show (2 * i : Nat) = i * 2 from by omega, natCast_mul, natCast_two]
  rw [div_def (meshWidth a b n) (1 + 1) two_ne_zero]
  rw [show natCast i * (1 + 1) * (meshWidth a b n * (1 / (1 + 1)))
        = natCast i * meshWidth a b n * ((1 + 1) * (1 / (1 + 1))) from by mach_ring]
  rw [mul_inv (1 + 1) two_ne_zero, mul_one_ax]

theorem meshPoint_double_odd_ge (a b : Real) (n i : Nat) (hab : a ≤ b) (hn : 0 < n) :
    meshPoint a b n i ≤ meshPoint a b (2 * n) (2 * i + 1) := by
  have h1 : meshPoint a b (2 * n) (2 * i) ≤ meshPoint a b (2 * n) (2 * i + 1) :=
    meshPoint_le_succ a b (2 * n) (2 * i) hab
  rwa [meshPoint_double_even a b n i hn] at h1

theorem meshPoint_double_odd_mem (a b : Real) (n i : Nat) (hab : a ≤ b) (hn : 0 < n) (hi : i < n) :
    a ≤ meshPoint a b (2 * n) (2 * i + 1) ∧ meshPoint a b (2 * n) (2 * i + 1) ≤ b :=
  meshPoint_mem a b (2 * n) (2 * i + 1) hab (by omega) (by omega)

private theorem half_mul_double (X : Real) : (1 + 1) * X = X + X := by mach_ring

/-- **Doubling only raises the lower sum.** -/
theorem lowerSum_double_ge {f : Real → Real} {a b : Real} (hab : a ≤ b) (hmono : MonotoneOn f a b)
    (n : Nat) (hn : 0 < n) : lowerSum f a b n ≤ lowerSum f a b (2 * n) := by
  show partialSum (fun i => f (meshPoint a b n i)) n * meshWidth a b n
    ≤ partialSum (fun j => f (meshPoint a b (2 * n) j)) (2 * n) * meshWidth a b (2 * n)
  rw [partialSum_pair_split (fun j => f (meshPoint a b (2 * n) j)) n, meshWidth_double a b n hn]
  have hpair : ∀ i, i < n →
      (1 + 1) * f (meshPoint a b n i)
        ≤ f (meshPoint a b (2 * n) (2 * i)) + f (meshPoint a b (2 * n) (2 * i + 1)) := by
    intro i hi
    have hi_le : i ≤ n := by omega
    have hle1 : f (meshPoint a b n i) ≤ f (meshPoint a b (2 * n) (2 * i)) := by
      rw [meshPoint_double_even a b n i hn]; exact le_refl _
    have hle2 : f (meshPoint a b n i) ≤ f (meshPoint a b (2 * n) (2 * i + 1)) :=
      hmono (meshPoint a b n i) (meshPoint a b (2 * n) (2 * i + 1))
        (meshPoint_mem a b n i hab hn hi_le).1 (meshPoint_double_odd_ge a b n i hab hn)
        (meshPoint_double_odd_mem a b n i hab hn hi).2
    rw [half_mul_double]
    exact add_le_add_both hle1 hle2
  have hsum_le : partialSum (fun i => (1 + 1) * f (meshPoint a b n i)) n
      ≤ partialSum
          (fun i => f (meshPoint a b (2 * n) (2 * i)) + f (meshPoint a b (2 * n) (2 * i + 1))) n :=
    partialSum_le_of_termwise_le n hpair
  rw [partialSum_const_mul (1 + 1) (fun i => f (meshPoint a b n i)) n] at hsum_le
  have hcancel : partialSum (fun i => f (meshPoint a b n i)) n * meshWidth a b n
      = ((1 + 1) * partialSum (fun i => f (meshPoint a b n i)) n) * (meshWidth a b n / (1 + 1)) := by
    rw [div_def (meshWidth a b n) (1 + 1) two_ne_zero]
    rw [show (1 + 1) * partialSum (fun i => f (meshPoint a b n i)) n
          * (meshWidth a b n * (1 / (1 + 1)))
        = partialSum (fun i => f (meshPoint a b n i)) n * meshWidth a b n
          * ((1 + 1) * (1 / (1 + 1))) from by mach_ring]
    rw [mul_inv (1 + 1) two_ne_zero, mul_one_ax]
  rw [hcancel]
  exact mul_le_mul_of_nonneg_right hsum_le
    (div_nonneg (meshWidth_nonneg hab n) (le_of_lt two_pos))

theorem meshPoint_double_odd_le (a b : Real) (n i : Nat) (hab : a ≤ b) (hn : 0 < n) :
    meshPoint a b (2 * n) (2 * i + 1) ≤ meshPoint a b n (i + 1) := by
  have h1 : meshPoint a b (2 * n) (2 * i + 1) ≤ meshPoint a b (2 * n) (2 * i + 1 + 1) :=
    meshPoint_le_succ a b (2 * n) (2 * i + 1) hab
  have h2 : (2 * i + 1 + 1 : Nat) = 2 * (i + 1) := by omega
  rwa [h2, meshPoint_double_even a b n (i + 1) hn] at h1

theorem meshPoint_double_odd_mem' (a b : Real) (n i : Nat) (hab : a ≤ b) (hn : 0 < n) (hi : i < n) :
    a ≤ meshPoint a b (2 * n) (2 * i + 1) ∧ meshPoint a b (2 * n) (2 * i + 1) ≤ b :=
  meshPoint_mem a b (2 * n) (2 * i + 1) hab (by omega) (by omega)

/-- **Doubling only lowers the upper sum.** Direct mirror of `lowerSum_double_ge`: both fine
subinterval endpoints in a pair land `≤` the coarse RIGHT endpoint (instead of `≥` the coarse
LEFT endpoint), so the fine pair-sum is bounded ABOVE (instead of below) by twice the coarse term. -/
theorem upperSum_double_le {f : Real → Real} {a b : Real} (hab : a ≤ b) (hmono : MonotoneOn f a b)
    (n : Nat) (hn : 0 < n) : upperSum f a b (2 * n) ≤ upperSum f a b n := by
  show partialSum (fun j => f (meshPoint a b (2 * n) (j + 1))) (2 * n) * meshWidth a b (2 * n)
    ≤ partialSum (fun i => f (meshPoint a b n (i + 1))) n * meshWidth a b n
  rw [partialSum_pair_split (fun j => f (meshPoint a b (2 * n) (j + 1))) n, meshWidth_double a b n hn]
  have hpair : ∀ i, i < n →
      f (meshPoint a b (2 * n) (2 * i + 1)) + f (meshPoint a b (2 * n) (2 * i + 1 + 1))
        ≤ (1 + 1) * f (meshPoint a b n (i + 1)) := by
    intro i hi
    have hle1 : f (meshPoint a b (2 * n) (2 * i + 1)) ≤ f (meshPoint a b n (i + 1)) :=
      hmono _ _ (meshPoint_double_odd_mem' a b n i hab hn hi).1
        (meshPoint_double_odd_le a b n i hab hn) (meshPoint_mem a b n (i + 1) hab hn (by omega)).2
    have heq2 : (2 * i + 1 + 1 : Nat) = 2 * (i + 1) := by omega
    have hle2 : f (meshPoint a b (2 * n) (2 * i + 1 + 1)) ≤ f (meshPoint a b n (i + 1)) := by
      rw [heq2, meshPoint_double_even a b n (i + 1) hn]; exact le_refl _
    rw [half_mul_double]
    exact add_le_add_both hle1 hle2
  have hsum_le :
      partialSum (fun i => f (meshPoint a b (2 * n) (2 * i + 1))
        + f (meshPoint a b (2 * n) (2 * i + 1 + 1))) n
      ≤ partialSum (fun i => (1 + 1) * f (meshPoint a b n (i + 1))) n :=
    partialSum_le_of_termwise_le n hpair
  rw [partialSum_const_mul (1 + 1) (fun i => f (meshPoint a b n (i + 1))) n] at hsum_le
  have hcancel :
      ((1 + 1) * partialSum (fun i => f (meshPoint a b n (i + 1))) n) * (meshWidth a b n / (1 + 1))
      = partialSum (fun i => f (meshPoint a b n (i + 1))) n * meshWidth a b n := by
    rw [div_def (meshWidth a b n) (1 + 1) two_ne_zero]
    rw [show (1 + 1) * partialSum (fun i => f (meshPoint a b n (i + 1))) n
          * (meshWidth a b n * (1 / (1 + 1)))
        = partialSum (fun i => f (meshPoint a b n (i + 1))) n * meshWidth a b n
          * ((1 + 1) * (1 / (1 + 1))) from by mach_ring]
    rw [mul_inv (1 + 1) two_ne_zero, mul_one_ax]
  calc partialSum (fun i => f (meshPoint a b (2 * n) (2 * i + 1))
        + f (meshPoint a b (2 * n) (2 * i + 1 + 1))) n * (meshWidth a b n / (1 + 1))
      ≤ ((1 + 1) * partialSum (fun i => f (meshPoint a b n (i + 1))) n)
          * (meshWidth a b n / (1 + 1)) :=
        mul_le_mul_of_nonneg_right hsum_le (div_nonneg (meshWidth_nonneg hab n) (le_of_lt two_pos))
    _ = partialSum (fun i => f (meshPoint a b n (i + 1))) n * meshWidth a b n := hcancel

/-! ## §5 — Existence via `sup_exists`/`inf_exists` on the dyadic family, `archimedean` -/

theorem two_pow_succ (k : Nat) : (2 : Nat) ^ (k + 1) = 2 * 2 ^ k := by
  rw [Nat.pow_succ, Nat.mul_comm]

theorem two_pow_pos : ∀ k : Nat, 0 < (2 : Nat) ^ k
  | 0 => by decide
  | k + 1 => by rw [two_pow_succ]; have := two_pow_pos k; omega

theorem nat_le_two_pow : ∀ N : Nat, N ≤ 2 ^ N
  | 0 => by decide
  | N + 1 => by
      have ih := nat_le_two_pow N
      have hpos := two_pow_pos N
      rw [two_pow_succ]
      omega

/-- `lowerSum` is monotone increasing along the dyadic family `2^k`. -/
theorem lowerSum_dyadic_mono {f : Real → Real} {a b : Real} (hab : a ≤ b) (hmono : MonotoneOn f a b) :
    ∀ k j, lowerSum f a b (2 ^ k) ≤ lowerSum f a b (2 ^ (k + j))
  | k, 0 => le_refl _
  | k, j + 1 => by
      have ih := lowerSum_dyadic_mono hab hmono k j
      have hstep : lowerSum f a b (2 ^ (k + j)) ≤ lowerSum f a b (2 ^ (k + j + 1)) := by
        rw [show k + j + 1 = (k + j) + 1 from rfl, two_pow_succ (k + j)]
        exact lowerSum_double_ge hab hmono (2 ^ (k + j)) (two_pow_pos (k + j))
      exact le_trans ih hstep

/-- `upperSum` is monotone decreasing along the dyadic family `2^k`. -/
theorem upperSum_dyadic_anti {f : Real → Real} {a b : Real} (hab : a ≤ b) (hmono : MonotoneOn f a b) :
    ∀ k j, upperSum f a b (2 ^ (k + j)) ≤ upperSum f a b (2 ^ k)
  | k, 0 => le_refl _
  | k, j + 1 => by
      have ih := upperSum_dyadic_anti hab hmono k j
      have hstep : upperSum f a b (2 ^ (k + j + 1)) ≤ upperSum f a b (2 ^ (k + j)) := by
        rw [show k + j + 1 = (k + j) + 1 from rfl, two_pow_succ (k + j)]
        exact upperSum_double_le hab hmono (2 ^ (k + j)) (two_pow_pos (k + j))
      exact le_trans hstep ih

/-- **Cross comparison**: any dyadic lower sum is `≤` any dyadic upper sum, regardless of index —
the payoff of the two monotone dyadic families above (no general partition-refinement theory
needed). -/
theorem lowerSum_le_upperSum_cross {f : Real → Real} {a b : Real} (hab : a ≤ b)
    (hmono : MonotoneOn f a b) (j k : Nat) :
    lowerSum f a b (2 ^ j) ≤ upperSum f a b (2 ^ k) := by
  rcases Nat.le_total j k with hjk | hkj
  · obtain ⟨d, hd⟩ := Nat.le.dest hjk
    have h1 : lowerSum f a b (2 ^ j) ≤ lowerSum f a b (2 ^ k) := by
      rw [← hd]; exact lowerSum_dyadic_mono hab hmono j d
    exact le_trans h1 (lowerSum_le_upperSum hab hmono (2 ^ k) (two_pow_pos k))
  · obtain ⟨d, hd⟩ := Nat.le.dest hkj
    have h2 : upperSum f a b (2 ^ j) ≤ upperSum f a b (2 ^ k) := by
      rw [← hd]; exact upperSum_dyadic_anti hab hmono k d
    exact le_trans (lowerSum_le_upperSum hab hmono (2 ^ j) (two_pow_pos j)) h2

/-- **Monotone functions are Riemann integrable.** There is a value `I` sandwiched between every
dyadic lower and upper sum, with the gap shrinking below any `ε > 0`. -/
theorem monotone_riemann_integrable {f : Real → Real} {a b : Real} (hab : a ≤ b)
    (hmono : MonotoneOn f a b) :
    ∃ I : Real,
      (∀ k, lowerSum f a b (2 ^ k) ≤ I ∧ I ≤ upperSum f a b (2 ^ k)) ∧
      (∀ ε : Real, 0 < ε → ∃ k, upperSum f a b (2 ^ k) - lowerSum f a b (2 ^ k) < ε) := by
  have hne : ∃ x, ∃ k, x = lowerSum f a b (2 ^ k) := ⟨lowerSum f a b (2 ^ 0), 0, rfl⟩
  have hbd : BoundedAbove (fun x => ∃ k, x = lowerSum f a b (2 ^ k)) :=
    ⟨upperSum f a b (2 ^ 0), fun x hx => by
      obtain ⟨k, hk⟩ := hx; rw [hk]; exact lowerSum_le_upperSum_cross hab hmono k 0⟩
  obtain ⟨I, hIub, hIlub⟩ := sup_exists (fun x => ∃ k, x = lowerSum f a b (2 ^ k)) hne hbd
  refine ⟨I, fun k => ⟨hIub (lowerSum f a b (2 ^ k)) ⟨k, rfl⟩, ?_⟩, ?_⟩
  · apply hIlub
    intro x hx
    obtain ⟨j, hj⟩ := hx
    rw [hj]
    exact lowerSum_le_upperSum_cross hab hmono j k
  · intro ε hε
    have hC : 0 ≤ (f b - f a) * (b - a) := by
      have hfba : 0 ≤ f b - f a := sub_nonneg_of_le (hmono a b (le_refl a) hab (le_refl b))
      exact mul_nonneg hfba (sub_nonneg_of_le hab)
    have hCepos : 0 ≤ ((f b - f a) * (b - a)) / ε := div_nonneg hC (le_of_lt hε)
    obtain ⟨N, hN⟩ := archimedean (((f b - f a) * (b - a)) / ε)
    have hNpos : 0 < N := by
      rcases Nat.eq_zero_or_pos N with h0 | hpos
      · exfalso; rw [h0, natCast_zero] at hN; exact lt_irrefl_ax 0 (lt_of_le_of_lt hCepos hN)
      · exact hpos
    refine ⟨N, ?_⟩
    have hgap : upperSum f a b (2 ^ N) - lowerSum f a b (2 ^ N)
        = (f b - f a) * (b - a) / natCast (2 ^ N) := by
      rw [upperSum_sub_lowerSum f a b (2 ^ N) (two_pow_pos N)]
      show (f b - f a) * ((b - a) / natCast (2 ^ N)) = (f b - f a) * (b - a) / natCast (2 ^ N)
      rw [div_def (b - a) (natCast (2 ^ N)) (natCast_ne_zero (two_pow_pos N)),
        div_def ((f b - f a) * (b - a)) (natCast (2 ^ N)) (natCast_ne_zero (two_pow_pos N))]
      mach_ring
    rw [hgap]
    have hNcast : natCast N ≤ natCast (2 ^ N) := natCast_le_of_nat_le (nat_le_two_pow N)
    have hCN : (((f b - f a) * (b - a)) / ε) * ε < natCast N * ε := mul_lt_mul_of_pos_right hN hε
    rw [div_mul_cancel (ne_of_gt hε)] at hCN
    have hCN_comm : (f b - f a) * (b - a) < ε * natCast N := by
      rw [mul_comm ε (natCast N)]; exact hCN
    have hlt2 : (f b - f a) * (b - a) / natCast N < ε := div_lt_of_lt_mul hCN_comm (natCast_pos hNpos)
    have hle3 : (f b - f a) * (b - a) / natCast (2 ^ N) ≤ (f b - f a) * (b - a) / natCast N :=
      div_le_div_pos hC (le_refl _) (natCast_pos hNpos) hNcast
    exact lt_of_le_of_lt hle3 hlt2

end Real
end MachLib
