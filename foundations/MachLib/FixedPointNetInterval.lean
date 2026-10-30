import MachLib.FixedPointNet

/-!
# Interval soundness over integer words: a universal range and an exact maximum, closed by the kernel

`FixedPointNet` proves a forward error at one input, given `noOverflow` at that input. This file lets both of
the remaining claims about a network quantify over every Q16.16 word in a box, by computation the kernel checks.

* **Range.** `FxSym.rng` encloses every node's word over a box. `noOverflow_of_safe` turns one `safe` check into
  `noOverflow` at every word in the box, which removes `fxnet_eps`'s condition there.
* **Approximation.** `FxSym.aff` carries an affine form with a slack through the program, in exact integers. A unit
  whose sign is fixed on a box is exactly affine, so its cancellation against an affine law is exact and only the
  undecided units add slack. `check` splits boxes until the bound holds, and needs no certificate: `check_sound`
  makes a returned `true` a theorem. So a closed term's bound is `decide +kernel`.

**Words only.** Every theorem here is over `Int` inputs, that is Q16.16 words, which are what a deployed datapath
receives. Nothing is claimed between words. **No axiom is added; nothing here is about an RTL.**
-/

namespace MachLib
namespace Real

/-- A program over two symbolic inputs: `FxNet` with its input words left open. -/
inductive FxSym where
  | v1
  | v2
  | lit (m : Int)
  | add (a b : FxSym)
  | cmul (m : Int) (a : FxSym)
  | maxc (a : FxSym) (c : Int)
  | minc (a : FxSym) (c : Int)

/-- A box of words. -/
structure FxBox where
  x0 : Int
  x1 : Int
  y0 : Int
  y1 : Int

/-- `(x1, x2)` lies in the box. -/
def FxBox.Has (b : FxBox) (x1 x2 : Int) : Prop :=
  b.x0 ≤ x1 ∧ x1 ≤ b.x1 ∧ b.y0 ≤ x2 ∧ x2 ≤ b.y1

private def imin (a b : Int) : Int := if a ≤ b then a else b
private def imax (a b : Int) : Int := if a ≤ b then b else a

private theorem imin_le_left (a b : Int) : imin a b ≤ a := by unfold imin; split <;> omega
private theorem imin_le_right (a b : Int) : imin a b ≤ b := by unfold imin; split <;> omega
private theorem le_imax_left (a b : Int) : a ≤ imax a b := by unfold imax; split <;> omega
private theorem le_imax_right (a b : Int) : b ≤ imax a b := by unfold imax; split <;> omega

/-- A constant times something between `lo` and `hi` lies between the two end products. -/
private theorem mul_between (g a lo hi : Int) (h1 : lo ≤ a) (h2 : a ≤ hi) :
    imin (g * lo) (g * hi) ≤ g * a ∧ g * a ≤ imax (g * lo) (g * hi) := by
  by_cases hg : 0 ≤ g
  · have l := Int.mul_le_mul_of_nonneg_left h1 hg
    have r := Int.mul_le_mul_of_nonneg_left h2 hg
    exact ⟨Int.le_trans (imin_le_left _ _) l, Int.le_trans r (le_imax_right _ _)⟩
  · have hn : g ≤ 0 := by omega
    have l := Int.mul_le_mul_of_nonpos_left hn h1
    have r := Int.mul_le_mul_of_nonpos_left hn h2
    exact ⟨Int.le_trans (imin_le_right _ _) r, Int.le_trans l (le_imax_left _ _)⟩

namespace FxSym

/-- The concrete program at two input words. -/
def inst (x1 x2 : Int) : FxSym → FxNet
  | .v1 => .input x1
  | .v2 => .input x2
  | .lit m => .lit m
  | .add a b => .add (inst x1 x2 a) (inst x1 x2 b)
  | .cmul m a => .cmul m (inst x1 x2 a)
  | .maxc a c => .maxc (inst x1 x2 a) c
  | .minc a c => .minc (inst x1 x2 a) c

/-! ## The range of a word -/

/-- An enclosure `(lo, hi)` of the word at each node, over a box. Floor is monotone. -/
def rng (b : FxBox) : FxSym → Int × Int
  | .v1 => (b.x0, b.x1)
  | .v2 => (b.y0, b.y1)
  | .lit m => (m, m)
  | .add p q => ((rng b p).1 + (rng b q).1, (rng b p).2 + (rng b q).2)
  | .cmul m p =>
      (imin (m * (rng b p).1) (m * (rng b p).2) / 65536,
       imax (m * (rng b p).1) (m * (rng b p).2) / 65536)
  | .maxc p c => (imax (rng b p).1 c, imax (rng b p).2 c)
  | .minc p c => (imin (rng b p).1 c, imin (rng b p).2 c)

/-- Every node's enclosure is representable in 32 bits. -/
def safe (b : FxBox) : FxSym → Bool
  | .v1 => FxNet.inRange b.x0 && FxNet.inRange b.x1
  | .v2 => FxNet.inRange b.y0 && FxNet.inRange b.y1
  | .lit m => FxNet.inRange m
  | .add p q => safe b p && safe b q &&
      FxNet.inRange (rng b (.add p q)).1 && FxNet.inRange (rng b (.add p q)).2
  | .cmul m p => safe b p &&
      FxNet.inRange (rng b (.cmul m p)).1 && FxNet.inRange (rng b (.cmul m p)).2
  | .maxc p c => safe b p && FxNet.inRange c
  | .minc p c => safe b p && FxNet.inRange c

theorem rng_sound {b : FxBox} {x1 x2 : Int} (h : b.Has x1 x2) : ∀ t : FxSym,
    (rng b t).1 ≤ FxNet.word (inst x1 x2 t) ∧ FxNet.word (inst x1 x2 t) ≤ (rng b t).2
  | .v1 => ⟨h.1, h.2.1⟩
  | .v2 => ⟨h.2.2.1, h.2.2.2⟩
  | .lit _ => by simp only [rng, inst, FxNet.word]; omega
  | .add p q => by
      have hp := rng_sound h p
      have hq := rng_sound h q
      simp only [rng, inst, FxNet.word]
      omega
  | .cmul m p => by
      have hp := rng_sound h p
      have hb := mul_between m _ _ _ hp.1 hp.2
      simp only [rng, inst, FxNet.word]
      exact ⟨Int.ediv_le_ediv (by decide) hb.1, Int.ediv_le_ediv (by decide) hb.2⟩
  | .maxc p c => by
      have hp := rng_sound h p
      simp only [rng, inst, FxNet.word, imax]
      split <;> split <;> split <;> omega
  | .minc p c => by
      have hp := rng_sound h p
      simp only [rng, inst, FxNet.word, imin]
      split <;> split <;> split <;> omega

private theorem inRange_between {lo hi v : Int} (h1 : FxNet.inRange lo = true)
    (h2 : FxNet.inRange hi = true) (hl : lo ≤ v) (hh : v ≤ hi) : FxNet.inRange v = true := by
  simp only [FxNet.inRange, Bool.and_eq_true, decide_eq_true_eq] at h1 h2 ⊢
  omega

/-- **The range lemma.** One `safe` check on a box gives `noOverflow` at every word in it. -/
theorem noOverflow_of_safe {b : FxBox} {x1 x2 : Int} (h : b.Has x1 x2) : ∀ t : FxSym,
    safe b t = true → FxNet.noOverflow (inst x1 x2 t) = true
  | .v1, s => by
      simp only [safe, Bool.and_eq_true] at s
      exact inRange_between s.1 s.2 h.1 h.2.1
  | .v2, s => by
      simp only [safe, Bool.and_eq_true] at s
      exact inRange_between s.1 s.2 h.2.2.1 h.2.2.2
  | .lit _, s => s
  | .add p q, s => by
      simp only [safe, Bool.and_eq_true] at s
      have r := rng_sound h (.add p q)
      have e : FxNet.word (inst x1 x2 (.add p q))
          = FxNet.word (inst x1 x2 p) + FxNet.word (inst x1 x2 q) := rfl
      rw [e] at r
      simp only [inst, FxNet.noOverflow, Bool.and_eq_true]
      exact ⟨⟨noOverflow_of_safe h p s.1.1.1, noOverflow_of_safe h q s.1.1.2⟩,
        inRange_between s.1.2 s.2 r.1 r.2⟩
  | .cmul m p, s => by
      simp only [safe, Bool.and_eq_true] at s
      have r := rng_sound h (.cmul m p)
      have e : FxNet.word (inst x1 x2 (.cmul m p)) = m * FxNet.word (inst x1 x2 p) / 65536 := rfl
      rw [e] at r
      simp only [inst, FxNet.noOverflow, Bool.and_eq_true]
      exact ⟨noOverflow_of_safe h p s.1.1, inRange_between s.1.2 s.2 r.1 r.2⟩
  | .maxc p c, s => by
      simp only [safe, Bool.and_eq_true] at s
      simp only [inst, FxNet.noOverflow, Bool.and_eq_true]
      exact ⟨noOverflow_of_safe h p s.1, s.2⟩
  | .minc p c, s => by
      simp only [safe, Bool.and_eq_true] at s
      simp only [inst, FxNet.noOverflow, Bool.and_eq_true]
      exact ⟨noOverflow_of_safe h p s.1, s.2⟩

/-! ## The exact value, scaled to an integer -/

/-- `65536 ^ n`, kernel-friendly. -/
def pow16 : Nat → Int
  | 0 => 1
  | n + 1 => 65536 * pow16 n

/-- The exact value of the program times `2^(16 k)`, an integer once `k` is deep enough (`wf`). -/
def val (x1 x2 : Int) : Nat → FxSym → Int
  | k, .v1 => x1 * pow16 (k - 1)
  | k, .v2 => x2 * pow16 (k - 1)
  | k, .lit m => m * pow16 (k - 1)
  | k, .add p q => val x1 x2 k p + val x1 x2 k q
  | k, .cmul m p => m * val x1 x2 (k - 1) p
  | k, .maxc p c => if val x1 x2 k p ≤ c * pow16 (k - 1) then c * pow16 (k - 1) else val x1 x2 k p
  | k, .minc p c => if val x1 x2 k p ≤ c * pow16 (k - 1) then val x1 x2 k p else c * pow16 (k - 1)

/-- `k` leaves a factor of `2^-16` for every constant and input the term meets. -/
def wf : Nat → FxSym → Bool
  | 0, _ => false
  | _ + 1, .v1 => true
  | _ + 1, .v2 => true
  | _ + 1, .lit _ => true
  | k + 1, .add p q => wf (k + 1) p && wf (k + 1) q
  | k + 1, .cmul _ p => wf k p
  | k + 1, .maxc p _ => wf (k + 1) p
  | k + 1, .minc p _ => wf (k + 1) p

/-- `ulp ^ k`. -/
noncomputable def ulpp : Nat → Real
  | 0 => 1
  | k + 1 => ulp * ulpp k

theorem ulpp_nonneg : ∀ k : Nat, 0 ≤ ulpp k
  | 0 => le_of_lt zero_lt_one_ax
  | k + 1 => mul_nonneg (le_of_lt ulp_pos) (ulpp_nonneg k)

private theorem scale65536' : natCast 65536 * ulp = 1 := by
  have h : 2 ^ RTL.FRAC = 65536 := by decide
  rw [← h]; exact ulp_scale

private theorem ic_65536 : ic 65536 = natCast 65536 := by
  have e : (65536 : Int) = ((65536 : Nat) : Int) := rfl
  rw [e, ic_ofNat]

private theorem ic_one : ic 1 = 1 := by
  have e : (1 : Int) = ((1 : Nat) : Int) := rfl
  rw [e, ic_ofNat, show (1 : Nat) = 0 + 1 from rfl, natCast_succ, natCast_zero]
  exact zero_add 1

theorem ic_pow16 : ∀ j : Nat, ic (pow16 j) * ulpp j = 1
  | 0 => by
      show ic 1 * 1 = 1
      rw [ic_one]; exact mul_one_ax 1
  | j + 1 => by
      show ic (65536 * pow16 j) * (ulp * ulpp j) = 1
      rw [ic_mul, ic_65536]
      have e : natCast 65536 * ic (pow16 j) * (ulp * ulpp j)
          = (natCast 65536 * ulp) * (ic (pow16 j) * ulpp j) := by
        mach_mpoly [natCast 65536, ic (pow16 j), ulp, ulpp j]
      rw [e, scale65536', ic_pow16 j, one_mul_thm]

/-- A word's value in `ulp ^ (j + 1)` units. -/
theorem mant_scaled (m : Int) (j : Nat) : mant m = ic (m * pow16 j) * ulpp (j + 1) := by
  show ic m * ulp = ic (m * pow16 j) * (ulp * ulpp j)
  rw [ic_mul]
  have e : ic m * ic (pow16 j) * (ulp * ulpp j) = ic m * ulp * (ic (pow16 j) * ulpp j) := by
    mach_mpoly [ic m, ic (pow16 j), ulp, ulpp j]
  rw [e, ic_pow16, mul_one_ax]

private theorem ic_mul_le {a b : Int} (s : Real) (hs : 0 ≤ s) (h : a ≤ b) : ic a * s ≤ ic b * s :=
  mul_le_mul_of_nonneg_right (ic_le h) hs

private theorem rmax_right {x y : Real} (h : x ≤ y) : max x y = y := by
  unfold max; rw [if_pos h]

private theorem rmax_left {x y : Real} (h : y ≤ x) : max x y = x := by
  unfold max
  split
  · exact le_antisymm ‹x ≤ y› h |>.symm
  · rfl

private theorem rmin_left {x y : Real} (h : x ≤ y) : min x y = x := by
  unfold min; rw [if_pos h]

private theorem rmin_right {x y : Real} (h : y ≤ x) : min x y = y := by
  unfold min
  split
  · exact le_antisymm ‹x ≤ y› h
  · rfl

/-- `val` is the exact value, scaled. -/
theorem exact_eq (x1 x2 : Int) : ∀ (t : FxSym) (k : Nat), wf k t = true →
    FxNet.exact (inst x1 x2 t) = ic (val x1 x2 k t) * ulpp k
  | .v1, 0, h => by simp [wf] at h
  | .v2, 0, h => by simp [wf] at h
  | .lit _, 0, h => by simp [wf] at h
  | .add _ _, 0, h => by simp [wf] at h
  | .cmul _ _, 0, h => by simp [wf] at h
  | .maxc _ _, 0, h => by simp [wf] at h
  | .minc _ _, 0, h => by simp [wf] at h
  | .v1, j + 1, _ => mant_scaled x1 j
  | .v2, j + 1, _ => mant_scaled x2 j
  | .lit m, j + 1, _ => mant_scaled m j
  | .add p q, j + 1, h => by
      simp only [wf, Bool.and_eq_true] at h
      show FxNet.exact (inst x1 x2 p) + FxNet.exact (inst x1 x2 q)
        = ic (val x1 x2 (j + 1) p + val x1 x2 (j + 1) q) * ulpp (j + 1)
      rw [exact_eq x1 x2 p (j + 1) h.1, exact_eq x1 x2 q (j + 1) h.2, ic_add]
      mach_mpoly [ic (val x1 x2 (j + 1) p), ic (val x1 x2 (j + 1) q), ulpp (j + 1)]
  | .cmul m p, j + 1, h => by
      simp only [wf] at h
      show mant m * FxNet.exact (inst x1 x2 p) = ic (m * val x1 x2 j p) * (ulp * ulpp j)
      rw [exact_eq x1 x2 p j h, ic_mul]
      unfold mant
      mach_mpoly [ic m, ic (val x1 x2 j p), ulp, ulpp j]
  | .maxc p c, j + 1, h => by
      simp only [wf] at h
      show max (FxNet.exact (inst x1 x2 p)) (mant c) = ic (val x1 x2 (j + 1) (.maxc p c)) * ulpp (j + 1)
      rw [exact_eq x1 x2 p (j + 1) h, mant_scaled c j]
      have hs := ulpp_nonneg (j + 1)
      show _ = ic (if val x1 x2 (j + 1) p ≤ c * pow16 j then c * pow16 j else val x1 x2 (j + 1) p)
        * ulpp (j + 1)
      by_cases hc : val x1 x2 (j + 1) p ≤ c * pow16 j
      · rw [if_pos hc, rmax_right (ic_mul_le _ hs hc)]
      · rw [if_neg hc, rmax_left (ic_mul_le _ hs (by omega))]
  | .minc p c, j + 1, h => by
      simp only [wf] at h
      show min (FxNet.exact (inst x1 x2 p)) (mant c) = ic (val x1 x2 (j + 1) (.minc p c)) * ulpp (j + 1)
      rw [exact_eq x1 x2 p (j + 1) h, mant_scaled c j]
      have hs := ulpp_nonneg (j + 1)
      show _ = ic (if val x1 x2 (j + 1) p ≤ c * pow16 j then val x1 x2 (j + 1) p else c * pow16 j)
        * ulpp (j + 1)
      by_cases hc : val x1 x2 (j + 1) p ≤ c * pow16 j
      · rw [if_pos hc, rmin_left (ic_mul_le _ hs hc)]
      · rw [if_neg hc, rmin_right (ic_mul_le _ hs (by omega))]

/-! ## The affine form -/

/-- `c + gx·x1 + gy·x2`, plus a slack in `[lo, hi]`. -/
structure Aff where
  c : Int
  gx : Int
  gy : Int
  lo : Int
  hi : Int

/-- `v` is within the form at `(x1, x2)`. -/
def Aff.Holds (A : Aff) (x1 x2 v : Int) : Prop :=
  A.lo ≤ v - (A.c + A.gx * x1 + A.gy * x2) ∧ v - (A.c + A.gx * x1 + A.gy * x2) ≤ A.hi

/-- The form's least value on a box. -/
def Aff.rlo (A : Aff) (b : FxBox) : Int :=
  A.c + imin (A.gx * b.x0) (A.gx * b.x1) + imin (A.gy * b.y0) (A.gy * b.y1) + A.lo

/-- The form's greatest value on a box. -/
def Aff.rhi (A : Aff) (b : FxBox) : Int :=
  A.c + imax (A.gx * b.x0) (A.gx * b.x1) + imax (A.gy * b.y0) (A.gy * b.y1) + A.hi

theorem Aff.range {A : Aff} {b : FxBox} {x1 x2 v : Int} (hb : b.Has x1 x2) (h : A.Holds x1 x2 v) :
    A.rlo b ≤ v ∧ v ≤ A.rhi b := by
  have hx := mul_between A.gx x1 b.x0 b.x1 hb.1 hb.2.1
  have hy := mul_between A.gy x2 b.y0 b.y1 hb.2.2.1 hb.2.2.2
  unfold Aff.Holds at h
  unfold Aff.rlo Aff.rhi
  omega

/-- The affine form of `val` over a box, in `2^(-16 k)` units. -/
def aff (b : FxBox) : Nat → FxSym → Aff
  | k, .v1 => ⟨0, pow16 (k - 1), 0, 0, 0⟩
  | k, .v2 => ⟨0, 0, pow16 (k - 1), 0, 0⟩
  | k, .lit m => ⟨m * pow16 (k - 1), 0, 0, 0, 0⟩
  | k, .add p q =>
      let A := aff b k p
      let B := aff b k q
      ⟨A.c + B.c, A.gx + B.gx, A.gy + B.gy, A.lo + B.lo, A.hi + B.hi⟩
  | k, .cmul m p =>
      let A := aff b (k - 1) p
      ⟨m * A.c, m * A.gx, m * A.gy, imin (m * A.lo) (m * A.hi), imax (m * A.lo) (m * A.hi)⟩
  | k, .maxc p c =>
      let A := aff b k p
      let C := c * pow16 (k - 1)
      if C ≤ A.rlo b then A
      else if A.rhi b ≤ C then ⟨C, 0, 0, 0, 0⟩
      else ⟨C, 0, 0, 0, A.rhi b - C⟩
  | k, .minc p c =>
      let A := aff b k p
      let C := c * pow16 (k - 1)
      if A.rhi b ≤ C then A
      else if C ≤ A.rlo b then ⟨C, 0, 0, 0, 0⟩
      else ⟨C, 0, 0, A.rlo b - C, 0⟩

theorem aff_sound {b : FxBox} {x1 x2 : Int} (hb : b.Has x1 x2) : ∀ (t : FxSym) (k : Nat),
    (aff b k t).Holds x1 x2 (val x1 x2 k t)
  | .v1, k => by
      simp only [aff, val, Aff.Holds]
      have e : x1 * pow16 (k - 1) = pow16 (k - 1) * x1 := Int.mul_comm _ _
      rw [e, Int.zero_mul]
      omega
  | .v2, k => by
      simp only [aff, val, Aff.Holds]
      have e : x2 * pow16 (k - 1) = pow16 (k - 1) * x2 := Int.mul_comm _ _
      rw [e, Int.zero_mul]
      omega
  | .lit m, k => by
      simp only [aff, val, Aff.Holds, Int.zero_mul]
      omega
  | .add p q, k => by
      have hp := aff_sound hb p k
      have hq := aff_sound hb q k
      simp only [Aff.Holds] at hp hq
      simp only [aff, val, Aff.Holds, Int.add_mul]
      omega
  | .cmul m p, k => by
      have hp := aff_sound hb p (k - 1)
      simp only [Aff.Holds] at hp
      simp only [aff, val, Aff.Holds]
      generalize aff b (k - 1) p = A at hp ⊢
      generalize val x1 x2 (k - 1) p = v at hp ⊢
      have hm := mul_between m (v - (A.c + A.gx * x1 + A.gy * x2)) A.lo A.hi hp.1 hp.2
      have e : m * (v - (A.c + A.gx * x1 + A.gy * x2))
          = m * v - (m * A.c + m * A.gx * x1 + m * A.gy * x2) := by
        simp only [Int.mul_sub, Int.mul_add, Int.mul_assoc]
      rw [e] at hm
      exact hm
  | .maxc p c, k => by
      have hp := aff_sound hb p k
      have hr := Aff.range hb hp
      simp only [aff, val]
      generalize aff b k p = A at hp hr ⊢
      generalize val x1 x2 k p = v at hp hr ⊢
      generalize c * pow16 (k - 1) = C
      by_cases h1 : C ≤ A.rlo b
      · rw [if_pos h1, show (if v ≤ C then C else v) = v by split <;> omega]
        exact hp
      · rw [if_neg h1]
        by_cases h2 : A.rhi b ≤ C
        · rw [if_pos h2, show (if v ≤ C then C else v) = C by split <;> omega]
          simp only [Aff.Holds, Int.zero_mul]
          omega
        · rw [if_neg h2]
          simp only [Aff.Holds, Int.zero_mul]
          split <;> omega
  | .minc p c, k => by
      have hp := aff_sound hb p k
      have hr := Aff.range hb hp
      simp only [aff, val]
      generalize aff b k p = A at hp hr ⊢
      generalize val x1 x2 k p = v at hp hr ⊢
      generalize c * pow16 (k - 1) = C
      by_cases h1 : A.rhi b ≤ C
      · rw [if_pos h1, show (if v ≤ C then v else C) = v by split <;> omega]
        exact hp
      · rw [if_neg h1]
        by_cases h2 : C ≤ A.rlo b
        · rw [if_pos h2, show (if v ≤ C then v else C) = C by split <;> omega]
          simp only [Aff.Holds, Int.zero_mul]
          omega
        · rw [if_neg h2]
          simp only [Aff.Holds, Int.zero_mul]
          split <;> omega

/-! ## The maximum gap between two programs, by splitting boxes -/

/-- The form of a difference. -/
def Aff.sub (A L : Aff) : Aff :=
  ⟨A.c - L.c, A.gx - L.gx, A.gy - L.gy, A.lo - L.hi, A.hi - L.lo⟩

theorem Aff.sub_holds {A L : Aff} {x1 x2 v w : Int} (hA : A.Holds x1 x2 v) (hL : L.Holds x1 x2 w) :
    (A.sub L).Holds x1 x2 (v - w) := by
  simp only [Aff.Holds, Aff.sub, Int.sub_mul] at *
  omega

/-- The gap is within `T` on all of this box, by its affine form alone. -/
def gapOk (T : Int) (k : Nat) (t l : FxSym) (b : FxBox) : Bool :=
  let G := (aff b k t).sub (aff b k l)
  decide (G.rhi b ≤ T) && decide (-T ≤ G.rlo b)

/-- Split the wider side until `gapOk` holds or the fuel runs out. `false` proves nothing either way. -/
def check (T : Int) (k : Nat) (t l : FxSym) : Nat → FxBox → Bool
  | 0, b => gapOk T k t l b
  | n + 1, b =>
      gapOk T k t l b ||
        (if b.y1 - b.y0 ≤ b.x1 - b.x0 then
           check T k t l n ⟨b.x0, (b.x0 + b.x1) / 2, b.y0, b.y1⟩ &&
             check T k t l n ⟨(b.x0 + b.x1) / 2, b.x1, b.y0, b.y1⟩
         else
           check T k t l n ⟨b.x0, b.x1, b.y0, (b.y0 + b.y1) / 2⟩ &&
             check T k t l n ⟨b.x0, b.x1, (b.y0 + b.y1) / 2, b.y1⟩)

private theorem gapOk_sound {T : Int} {k : Nat} {t l : FxSym} {b : FxBox} {x1 x2 : Int}
    (hb : b.Has x1 x2) (h : gapOk T k t l b = true) :
    -T ≤ val x1 x2 k t - val x1 x2 k l ∧ val x1 x2 k t - val x1 x2 k l ≤ T := by
  simp only [gapOk, Bool.and_eq_true, decide_eq_true_eq] at h
  have r := Aff.range hb (Aff.sub_holds (aff_sound hb t k) (aff_sound hb l k))
  omega

/-- **`check` is sound.** A returned `true` bounds the gap at every word in the box. -/
theorem check_sound {T : Int} {k : Nat} {t l : FxSym} {x1 x2 : Int} :
    ∀ (n : Nat) (b : FxBox), check T k t l n b = true → b.Has x1 x2 →
      -T ≤ val x1 x2 k t - val x1 x2 k l ∧ val x1 x2 k t - val x1 x2 k l ≤ T
  | 0, _, h, hb => gapOk_sound hb h
  | n + 1, b, h, hb => by
      simp only [check, Bool.or_eq_true] at h
      rcases h with h | h
      · exact gapOk_sound hb h
      · obtain ⟨h1, h2, h3, h4⟩ := hb
        by_cases hs : b.y1 - b.y0 ≤ b.x1 - b.x0
        · rw [if_pos hs, Bool.and_eq_true] at h
          by_cases hm : x1 ≤ (b.x0 + b.x1) / 2
          · exact check_sound n _ h.1 ⟨h1, hm, h3, h4⟩
          · exact check_sound n _ h.2 ⟨by show (b.x0 + b.x1) / 2 ≤ x1; omega, h2, h3, h4⟩
        · rw [if_neg hs, Bool.and_eq_true] at h
          by_cases hm : x2 ≤ (b.y0 + b.y1) / 2
          · exact check_sound n _ h.1 ⟨h1, h2, h3, hm⟩
          · exact check_sound n _ h.2 ⟨h1, h2, by show (b.y0 + b.y1) / 2 ≤ x2; omega, h4⟩

/-- The gap between two programs' exact values, as an integer in `ulp ^ k` units. -/
theorem gap_eq (x1 x2 : Int) (t l : FxSym) (k : Nat) (ht : wf k t = true) (hl : wf k l = true) :
    FxNet.exact (inst x1 x2 t) - FxNet.exact (inst x1 x2 l)
      = ic (val x1 x2 k t - val x1 x2 k l) * ulpp k := by
  rw [exact_eq x1 x2 t k ht, exact_eq x1 x2 l k hl]
  have e : ic (val x1 x2 k t) = ic (val x1 x2 k t - val x1 x2 k l) + ic (val x1 x2 k l) := by
    rw [← ic_add]
    congr 1
    omega
  rw [e]
  mach_mpoly [ic (val x1 x2 k t - val x1 x2 k l), ic (val x1 x2 k l), ulpp k]

/-- **The approximation bound.** If `check` returns `true` on a box, then at every word in it the two programs'
exact values differ by at most `T · 2^(-16 k)`. -/
theorem gap_bound {T : Nat} {k n : Nat} {t l : FxSym} {b : FxBox} {x1 x2 : Int}
    (ht : wf k t = true) (hl : wf k l = true) (h : check (T : Int) k t l n b = true) (hb : b.Has x1 x2) :
    abs (FxNet.exact (inst x1 x2 t) - FxNet.exact (inst x1 x2 l)) ≤ natCast T * ulpp k := by
  rw [gap_eq x1 x2 t l k ht hl, abs_mul, abs_ic, abs_of_nonneg (ulpp_nonneg k)]
  have r := check_sound n b h hb
  exact mul_le_mul_of_nonneg_right (natCast_le_mono (by omega)) (ulpp_nonneg k)

end FxSym

end Real
end MachLib
