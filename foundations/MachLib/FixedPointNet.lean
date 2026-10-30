import MachLib.FixedPointCertifier
import MachLib.FixedPointRealBridge

/-!
# Fixed-point forward error over integer words, with `max`

`FxExpr`/`fx_sound` (`FixedPointCertifier`) has no `max`, charges a step on every add, and takes its
truncation as a hypothesis. This is its sibling for programs of constant multiplies, adds and selects,
such as a ReLU network, and it differs in three ways:

* **The evaluator is executable.** `word` is `Int` arithmetic: a constant multiply is the full product
  floored by `/ 65536` (`Int` division by a positive numeral is floor), an add is exact, a select is a
  select. `wrapEval` adds the 32-bit wrap. Both can be run and compared with an RTL simulation.
* **Weights are integer mantissas.** A constant in a term is the `Int` `m`, denoting `m / 2^16`.
* **`floor` is not used.** MachLib's `floor` is an axiom on `Real` with no integrality law, so it cannot
  be tied to a word. The residue here is a fact about `Int`, and the footprint stays field and order.

`FxNet.Enum` computes the bound as a `Nat`, in units of `2^-32`, so a closed term's bound is `rfl`.

**What the main theorem does not say.** `fxnet_eps` is conditional on `noOverflow`, per node and per input:
the wrap is excluded, not bounded. It relates the term to its own real semantics; that the term is a
given program, and that an RTL implements it, is outside Lean. It says nothing about approximating anything.
-/

namespace MachLib
namespace Real

/-! ## `Int` into `Real` -/

/-- `Int` into `Real`, as the difference of its positive and negative parts. -/
noncomputable def ic (m : Int) : Real := natCast m.toNat - natCast (-m).toNat

private theorem sub_eq_of_add_eq {a b p q : Real} (h : a + q = b + p) : a - b = p - q := by
  calc a - b = (a + q) - (b + q) := by mach_mpoly [a, b, q]
    _ = (b + p) - (b + q) := by rw [h]
    _ = p - q := by mach_mpoly [b, p, q]

theorem ic_nat_sub (p q : Nat) : ic ((p : Int) - (q : Int)) = natCast p - natCast q := by
  unfold ic
  apply sub_eq_of_add_eq
  rw [← natCast_add, ← natCast_add]
  congr 1
  omega

theorem ic_ofNat (n : Nat) : ic (n : Int) = natCast n := by
  have h := ic_nat_sub n 0
  have e : (n : Int) - ((0 : Nat) : Int) = (n : Int) := by omega
  rw [e, natCast_zero] at h
  rw [h]
  mach_mpoly [natCast n]

theorem ic_add (a b : Int) : ic (a + b) = ic a + ic b := by
  have e : a + b = ((a.toNat + b.toNat : Nat) : Int) - (((-a).toNat + (-b).toNat : Nat) : Int) := by
    omega
  rw [e, ic_nat_sub, natCast_add, natCast_add]
  unfold ic
  mach_mpoly [natCast a.toNat, natCast b.toNat, natCast (-a).toNat, natCast (-b).toNat]

private theorem int_mul_parts (p q r s : Nat) :
    ((p : Int) - (q : Int)) * ((r : Int) - (s : Int))
      = ((p * r + q * s : Nat) : Int) - ((p * s + q * r : Nat) : Int) := by
  push_cast
  grind

theorem ic_mul (a b : Int) : ic (a * b) = ic a * ic b := by
  have ha : a = (a.toNat : Int) - ((-a).toNat : Int) := by omega
  have hb : b = (b.toNat : Int) - ((-b).toNat : Int) := by omega
  have e : a * b = ((a.toNat * b.toNat + (-a).toNat * (-b).toNat : Nat) : Int)
      - ((a.toNat * (-b).toNat + (-a).toNat * b.toNat : Nat) : Int) := by
    rw [← int_mul_parts, ← ha, ← hb]
  rw [e, ic_nat_sub, natCast_add, natCast_add, natCast_mul, natCast_mul, natCast_mul, natCast_mul]
  unfold ic
  mach_mpoly [natCast a.toNat, natCast b.toNat, natCast (-a).toNat, natCast (-b).toNat]

theorem ic_nonneg {n : Int} (h : 0 ≤ n) : 0 ≤ ic n := by
  have e : n = (n.toNat : Int) := by omega
  rw [e, ic_ofNat]
  exact natCast_nonneg _

theorem ic_le {a b : Int} (h : a ≤ b) : ic a ≤ ic b := by
  have e : b = a + (b - a) := by omega
  have k : 0 ≤ ic (b - a) := ic_nonneg (by omega)
  rw [e, ic_add]
  have := add_le_add_left k (ic a)
  rwa [add_zero] at this

theorem abs_ic (m : Int) : abs (ic m) = natCast m.natAbs := by
  by_cases h : 0 ≤ m
  · have e : m = (m.natAbs : Int) := by omega
    have hm : ic m = natCast m.natAbs := by
      have k := ic_ofNat m.natAbs
      rwa [← e] at k
    rw [hm]
    exact abs_of_nonneg (natCast_nonneg _)
  · have e : -m = (m.natAbs : Int) := by omega
    have k := ic_ofNat m.natAbs
    rw [← e] at k
    have hn : ic (-m) = -ic m := by
      have z := ic_add m (-m)
      have o : m + -m = ((0 : Nat) : Int) := by omega
      rw [o, ic_ofNat, natCast_zero] at z
      have q : -ic m = -ic m + (ic m + ic (-m)) := by rw [← z]; mach_mpoly [ic m]
      rw [q]; mach_mpoly [ic m, ic (-m)]
    rw [hn] at k
    rw [← abs_neg, k]
    exact abs_of_nonneg (natCast_nonneg _)

/-! ## Mantissas -/

/-- The value `m / 2^16` of a Q16.16 word `m`. -/
noncomputable def mant (m : Int) : Real := ic m * ulp

private theorem scale65536 : natCast 65536 * ulp = 1 := by
  have h : 2 ^ RTL.FRAC = 65536 := by decide
  rw [← h]; exact ulp_scale

theorem mant_add (a b : Int) : mant (a + b) = mant a + mant b := by
  unfold mant; rw [ic_add]; mach_mpoly [ic a, ic b, ulp]

theorem mant_le {a b : Int} (h : a ≤ b) : mant a ≤ mant b :=
  mul_le_mul_of_nonneg_right (ic_le h) (le_of_lt ulp_pos)

theorem abs_mant (m : Int) : abs (mant m) = natCast m.natAbs * ulp := by
  unfold mant
  rw [abs_mul, abs_ic, abs_of_nonneg (le_of_lt ulp_pos)]

/-- `mant 65536 = 1`: the word of the literal `1.0`. -/
theorem mant_one : mant 65536 = 1 := by
  unfold mant
  have e : (65536 : Int) = ((65536 : Nat) : Int) := rfl
  rw [e, ic_ofNat]
  exact scale65536

private theorem residue_alg (iq ir S u : Real) (hS : S * u = 1) (hu : 0 ≤ u)
    (h0 : 0 ≤ ir) (h1 : ir ≤ S) : abs (iq * u - (S * iq + ir) * (u * u)) ≤ u := by
  have e : iq * u - (S * iq + ir) * (u * u) = -(ir * (u * u)) + iq * u * (1 - S * u) := by
    mach_mpoly [iq, ir, S, u]
  have z : (1 : Real) - S * u = 0 := by rw [hS]; mach_ring
  rw [e, z, mul_zero, add_zero, abs_neg, abs_of_nonneg (mul_nonneg h0 (mul_nonneg hu hu))]
  have k : ir * (u * u) ≤ S * (u * u) := mul_le_mul_of_nonneg_right h1 (mul_nonneg hu hu)
  have e3 : S * (u * u) = (S * u) * u := by mach_mpoly [S, u]
  rw [e3, hS, one_mul_thm] at k
  exact k

/-- **The floor residue on words.** `(m * a) / 65536` is within one `ulp` of the exact product. -/
theorem mant_floor_residue (m a : Int) :
    abs (mant (m * a / 65536) - mant m * mant a) ≤ ulp := by
  generalize hq : m * a / 65536 = q
  have hr0 : 0 ≤ m * a - 65536 * q := by omega
  have hr1 : m * a - 65536 * q ≤ 65536 := by omega
  have hn : m * a = ((65536 : Nat) : Int) * q + (m * a - 65536 * q) := by omega
  have hi : ic m * ic a = natCast 65536 * ic q + ic (m * a - 65536 * q) := by
    rw [← ic_mul, ← ic_ofNat 65536, ← ic_mul, ← ic_add, ← hn]
  have e : mant q - mant m * mant a
      = ic q * ulp - (natCast 65536 * ic q + ic (m * a - 65536 * q)) * (ulp * ulp) := by
    rw [← hi]; unfold mant; mach_mpoly [ic q, ic m, ic a, ulp]
  rw [e]
  apply residue_alg _ _ _ _ scale65536 (le_of_lt ulp_pos) (ic_nonneg hr0)
  have k := ic_le hr1
  have o : (65536 : Int) = ((65536 : Nat) : Int) := rfl
  rwa [o, ic_ofNat] at k

/-! ## `fxerr_max` and `fxerr_min`: a select propagates the operand's error and adds none -/

private theorem abs_max_le (x c : Real) : abs (max x c) ≤ abs x + abs c := by
  unfold max
  split
  · have := add_le_add_left (abs_nonneg x) (abs c)
    rw [add_zero, add_comm] at this
    exact this
  · have := add_le_add_left (abs_nonneg c) (abs x)
    rwa [add_zero] at this

private theorem abs_min_le (x c : Real) : abs (min x c) ≤ abs x + abs c := by
  unfold min
  split
  · have := add_le_add_left (abs_nonneg c) (abs x)
    rwa [add_zero] at this
  · have := add_le_add_left (abs_nonneg x) (abs c)
    rw [add_zero, add_comm] at this
    exact this

/-- `max` with a constant, the ReLU step: the error is unchanged (`max_lipschitz`). -/
theorem fxerr_max {M E v ve : Real} (c : Real) (h : FxErr M E v ve) :
    FxErr (M + abs c) E (max v c) (max ve c) := by
  refine ⟨le_trans (abs_max_le ve c) ?_, le_trans (max_lipschitz v ve c) h.2⟩
  have := add_le_add_left h.1 (abs c)
  rw [add_comm (abs c), add_comm (abs c)] at this
  exact this

/-- `min` with a constant: the error is unchanged (`min_lipschitz`). -/
theorem fxerr_min {M E v ve : Real} (c : Real) (h : FxErr M E v ve) :
    FxErr (M + abs c) E (min v c) (min ve c) := by
  refine ⟨le_trans (abs_min_le ve c) ?_, le_trans (min_lipschitz v ve c) h.2⟩
  have := add_le_add_left h.1 (abs c)
  rw [add_comm (abs c), add_comm (abs c)] at this
  exact this

private theorem max_of_le_right {x y : Real} (h : x ≤ y) : max x y = y := by
  unfold max; rw [if_pos h]

private theorem max_of_le_left {x y : Real} (h : y ≤ x) : max x y = x := by
  unfold max
  split
  · exact le_antisymm ‹x ≤ y› h |>.symm
  · rfl

private theorem min_of_le_left {x y : Real} (h : x ≤ y) : min x y = x := by
  unfold min; rw [if_pos h]

private theorem min_of_le_right {x y : Real} (h : y ≤ x) : min x y = y := by
  unfold min
  split
  · exact le_antisymm ‹x ≤ y› h
  · rfl

/-! ## The sibling of `FxExpr` -/

/-- A program of constant multiplies, exact adds and selects against constants, over Q16.16 words. -/
inductive FxNet where
  | input (w : Int)
  | lit (m : Int)
  | add (a b : FxNet)
  | cmul (m : Int) (a : FxNet)
  | maxc (a : FxNet) (c : Int)
  | minc (a : FxNet) (c : Int)

namespace FxNet

/-- The exact value of the program over the reals, at the exact constants. -/
noncomputable def exact : FxNet → Real
  | .input w => mant w
  | .lit m => mant m
  | .add a b => exact a + exact b
  | .cmul m a => mant m * exact a
  | .maxc a c => max (exact a) (mant c)
  | .minc a c => min (exact a) (mant c)

/-- The fixed-point evaluation with no wrap: each constant multiply floored, the rest exact. -/
def word : FxNet → Int
  | .input w => w
  | .lit m => m
  | .add a b => word a + word b
  | .cmul m a => m * word a / 65536
  | .maxc a c => if word a ≤ c then c else word a
  | .minc a c => if word a ≤ c then word a else c

/-- The error bound as a `Nat`, in units of `2^-32`. A floored multiply contributes one `ulp`
(`2^16` units) plus the operand's bound scaled by the constant, rounded up. -/
def Enum : FxNet → Nat
  | .input _ => 0
  | .lit _ => 0
  | .add a b => Enum a + Enum b
  | .cmul m a => (m.natAbs * Enum a + 65535) / 65536 + 65536
  | .maxc a _ => Enum a
  | .minc a _ => Enum a

private theorem cmul_bound (w e q u : Real) (A E K : Nat)
    (hu : 0 ≤ u) (hS : natCast 65536 * u = 1) (hw : abs w = natCast A * u)
    (hq : abs (q - w * e) ≤ u) (hK : A * E ≤ K * 65536) (x : Real)
    (hx : abs (e - x) ≤ natCast E * (u * u)) :
    abs (q - w * x) ≤ natCast (K + 65536) * (u * u) := by
  have split : q - w * x = (q - w * e) + w * (e - x) := by mach_mpoly [q, w, e, x]
  have h1 : abs (q - w * x) ≤ u + natCast A * u * (natCast E * (u * u)) := by
    rw [split]
    refine le_trans (abs_add _ _) (add_le_add_both hq ?_)
    rw [abs_mul, hw]
    exact mul_le_mul_of_nonneg_left hx (mul_nonneg (natCast_nonneg _) hu)
  have hcast : natCast A * natCast E ≤ natCast K * natCast 65536 := by
    rw [← natCast_mul, ← natCast_mul]
    exact natCast_le_mono hK
  have huuu : 0 ≤ u * (u * u) := mul_nonneg hu (mul_nonneg hu hu)
  have h2 : natCast A * u * (natCast E * (u * u)) ≤ natCast K * (u * u) := by
    have k := mul_le_mul_of_nonneg_right hcast huuu
    have l : natCast A * natCast E * (u * (u * u)) = natCast A * u * (natCast E * (u * u)) := by
      mach_mpoly [natCast A, natCast E, u]
    have r : natCast K * natCast 65536 * (u * (u * u))
        = natCast K * (u * u) * (natCast 65536 * u) := by
      mach_mpoly [natCast K, natCast 65536, u]
    rw [l, r, hS, mul_one_ax] at k
    exact k
  have h3 : u = natCast 65536 * (u * u) := by
    have e3 : natCast 65536 * (u * u) = (natCast 65536 * u) * u := by mach_mpoly [natCast 65536, u]
    rw [e3, hS, one_mul_thm]
  refine le_trans h1 ?_
  rw [natCast_add]
  have e4 : (natCast K + natCast 65536) * (u * u) = natCast 65536 * (u * u) + natCast K * (u * u) := by
    mach_mpoly [natCast K, natCast 65536, u]
  rw [e4, ← h3]
  have := add_le_add_left h2 u
  exact this

/-- **Soundness of the fold.** The word evaluation is within `Enum t · 2^-32` of the exact value. -/
theorem word_sound : ∀ t : FxNet, abs (mant (word t) - exact t) ≤ natCast (Enum t) * (ulp * ulp)
  | .input w => by
      simp only [word, exact, Enum]
      rw [show mant w - mant w = (0 : Real) from by mach_mpoly [mant w], abs_zero, natCast_zero,
        zero_mul]
      exact le_refl _
  | .lit m => by
      simp only [word, exact, Enum]
      rw [show mant m - mant m = (0 : Real) from by mach_mpoly [mant m], abs_zero, natCast_zero,
        zero_mul]
      exact le_refl _
  | .add a b => by
      have ha := word_sound a
      have hb := word_sound b
      simp only [word, exact, Enum]
      rw [mant_add, natCast_add]
      have e : mant (word a) + mant (word b) - (exact a + exact b)
          = (mant (word a) - exact a) + (mant (word b) - exact b) := by
        mach_mpoly [mant (word a), mant (word b), exact a, exact b]
      have r : (natCast (Enum a) + natCast (Enum b)) * (ulp * ulp)
          = natCast (Enum a) * (ulp * ulp) + natCast (Enum b) * (ulp * ulp) := by
        mach_mpoly [natCast (Enum a), natCast (Enum b), ulp]
      rw [e, r]
      exact le_trans (abs_add _ _) (add_le_add_both ha hb)
  | .cmul m a => by
      have ha := word_sound a
      simp only [word, exact, Enum]
      have hK : m.natAbs * Enum a ≤ ((m.natAbs * Enum a + 65535) / 65536) * 65536 := by omega
      exact cmul_bound (mant m) (mant (word a)) (mant (m * word a / 65536)) ulp m.natAbs (Enum a) _
        (le_of_lt ulp_pos) scale65536 (abs_mant m) (mant_floor_residue m (word a))
        hK (exact a) ha
  | .maxc a c => by
      have ha := word_sound a
      simp only [word, exact, Enum]
      have hm : mant (if word a ≤ c then c else word a) = max (mant (word a)) (mant c) := by
        by_cases h : word a ≤ c
        · rw [if_pos h, max_of_le_right (mant_le h)]
        · rw [if_neg h, max_of_le_left (mant_le (by omega))]
      rw [hm]
      exact (fxerr_max (mant c) (M := abs (exact a)) ⟨le_refl _, ha⟩).2
  | .minc a c => by
      have ha := word_sound a
      simp only [word, exact, Enum]
      have hm : mant (if word a ≤ c then word a else c) = min (mant (word a)) (mant c) := by
        by_cases h : word a ≤ c
        · rw [if_pos h, min_of_le_left (mant_le h)]
        · rw [if_neg h, min_of_le_right (mant_le (by omega))]
      rw [hm]
      exact (fxerr_min (mant c) (M := abs (exact a)) ⟨le_refl _, ha⟩).2

/-! ## The wrap, and the condition that excludes it -/

/-- 32-bit two's-complement wrap. -/
def wrap32 (v : Int) : Int := (v + 2147483648) % 4294967296 - 2147483648

/-- Representable in 32 bits. -/
def inRange (v : Int) : Bool := decide (-2147483648 ≤ v) && decide (v < 2147483648)

/-- The datapath: `word` with each add and each floored multiply held in 32 bits. -/
def wrapEval : FxNet → Int
  | .input w => w
  | .lit m => m
  | .add a b => wrap32 (wrapEval a + wrapEval b)
  | .cmul m a => wrap32 (m * wrapEval a / 65536)
  | .maxc a c => if wrapEval a ≤ c then c else wrapEval a
  | .minc a c => if wrapEval a ≤ c then wrapEval a else c

/-- No node of this evaluation leaves 32 bits. Decidable, and per input: it is checked at a point, not
over a domain. -/
def noOverflow : FxNet → Bool
  | .input w => inRange w
  | .lit m => inRange m
  | .add a b => noOverflow a && noOverflow b && inRange (word a + word b)
  | .cmul m a => noOverflow a && inRange (m * word a / 65536)
  | .maxc a c => noOverflow a && inRange c
  | .minc a c => noOverflow a && inRange c

private theorem wrap32_of_inRange {v : Int} (h : inRange v = true) : wrap32 v = v := by
  simp only [inRange, Bool.and_eq_true, decide_eq_true_eq] at h
  unfold wrap32
  omega

/-- Without overflow, the datapath and the unwrapped evaluation are the same word. -/
theorem wrapEval_eq_word : ∀ t : FxNet, noOverflow t = true → wrapEval t = word t
  | .input _, _ => rfl
  | .lit _, _ => rfl
  | .add a b, h => by
      simp only [noOverflow, Bool.and_eq_true] at h
      simp only [wrapEval, word]
      rw [wrapEval_eq_word a h.1.1, wrapEval_eq_word b h.1.2]
      exact wrap32_of_inRange h.2
  | .cmul m a, h => by
      simp only [noOverflow, Bool.and_eq_true] at h
      simp only [wrapEval, word]
      rw [wrapEval_eq_word a h.1]
      exact wrap32_of_inRange h.2
  | .maxc a c, h => by
      simp only [noOverflow, Bool.and_eq_true] at h
      simp only [wrapEval, word]
      rw [wrapEval_eq_word a h.1]
  | .minc a c, h => by
      simp only [noOverflow, Bool.and_eq_true] at h
      simp only [wrapEval, word]
      rw [wrapEval_eq_word a h.1]

/-- **The fixed-point forward-error certificate.** Where no node overflows, the datapath's word is within
`Enum t · 2^-32` of the program's exact value at its exact constants. -/
theorem fxnet_eps (t : FxNet) (h : noOverflow t = true) :
    abs (mant (wrapEval t) - exact t) ≤ natCast (Enum t) * (ulp * ulp) := by
  rw [wrapEval_eq_word t h]
  exact word_sound t

/-- The clamp, as the DAG writes it, is MachLib's `clamp` of the exact value at the word constants. -/
theorem exact_clamp (a : FxNet) (lo hi : Int) :
    exact (.maxc (.minc a hi) lo) = clamp (exact a) (mant lo) (mant hi) := by
  simp only [exact]
  unfold clamp
  exact max_comm _ _

end FxNet

end Real
end MachLib
