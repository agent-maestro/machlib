import MachLib.TransNodes
import MachLib.OperatorBasisComplete

/-!
# `arcsin` / `arccos` are locally Lipschitz on `[-R, R]`, `R < 1` — the symmetric-domain twin of `exp`

`InverseTrig.lean` added the domain-guarded derivative axioms `HasDerivAt_arcsin` /
`HasDerivAt_arccos` (`d/dx arcsin x = 1/√(1−x²)`, `d/dx arccos x = −1/√(1−x²)`, both valid only for
`abs x < 1`). Like `exp` (`ExpLipschitz`), `arcsin`/`arccos` are NOT globally Lipschitz — their
derivative blows up as `x → ±1` — so they need a domain-bounded local-Lipschitz argument via MVT,
exactly `exp_lip_lt`/`exp_lip_local`'s shape. Unlike `exp` (one-sided `(−∞, hi]`) or `log`/`sqrt`
(one-sided `[lo, ∞)`), the domain here is SYMMETRIC: `[-R, R]` with `R < 1`, matching
`sinh`/`cosh`'s shape in `TransNodes.lean` rather than `log`'s.

For `c` with `abs c ≤ R < 1`: `c·c ≤ R·R` (squaring preserves the bound), so `1 − R·R ≤ 1 − c·c`,
so `√(1−R·R) ≤ √(1−c·c)` (`sqrt_mono`), so `1/√(1−c·c) ≤ 1/√(1−R·R)` (`div_le_div_pos`) — the MVT
slope at any interior point `c` is dominated by the slope at the domain's boundary radius `R`. The
Lipschitz constant is `1/√(1−R·R)`.

`sorryAx`-free; the only new axioms anywhere in this arc are `HasDerivAt_arcsin`/`HasDerivAt_arccos`
in `InverseTrig.lean`.
-/

namespace MachLib.Real

/-- `|x − y| = |y − x|` (local copy — see `ExpLipschitz.abs_sub_comm'` / `TransNodes.abs_sub_comm2`;
each Lipschitz file keeps its own private copy rather than importing across siblings). -/
private theorem abs_sub_comm3 (x y : Real) : abs (x - y) = abs (y - x) := by
  have h : y - x = -(x - y) := by mach_ring
  rw [h, abs_neg]

/-- `abs c ≤ R → c·c ≤ R·R` — squaring preserves a magnitude bound (no sign assumption on `R`
needed: `abs c ≤ R` already forces `0 ≤ R` via `abs_nonneg`). -/
private theorem sq_le_of_abs_le {c R : Real} (h : abs c ≤ R) : c * c ≤ R * R := by
  have e : abs c * abs c = c * c := by
    rw [← abs_mul, abs_of_nonneg (mul_self_nonneg c)]
  rw [← e]
  exact le_trans (mul_le_mul_of_nonneg_right h (abs_nonneg c))
                 (mul_le_mul_of_nonneg_left h (le_trans (abs_nonneg c) h))

/-- `R < 1` together with a witness `abs x ≤ R` (which forces `0 ≤ R`) gives `R·R < 1`. Not
`private`: reused by `AbsoluteFoldLocal.pipeline_arcsin_of_arith`/`pipeline_arccos_of_arith` to derive
the pipeline's `0 ≤ L` hypothesis from the same in-domain witness `absenc_arcsin_local`/
`absenc_arccos_local` already use. -/
theorem sq_lt_one_of_abs_le_lt_one {R : Real} (hR : R < 1) {x : Real} (hx : abs x ≤ R) :
    R * R < 1 := by
  have hR0 : 0 ≤ R := le_trans (abs_nonneg x) hx
  have hRR_le_R : R * R ≤ R := by
    have h := mul_le_mul_of_nonneg_left (le_of_lt hR) hR0
    rwa [mul_one_ax] at h
  exact lt_of_le_of_lt hRR_le_R hR

/-! ## `arcsin` -/

/-- One-sided MVT bound: for `-R ≤ a < b ≤ R` (`R < 1`), `|arcsin b − arcsin a| ≤ (1/√(1−R²))·(b−a)`.
The MVT slope `1/√(1−c²)` (for `c ∈ (a,b) ⊆ [-R,R]`) is `≤ 1/√(1−R²)` since `c·c ≤ R·R` and `√` is
monotone. -/
theorem arcsin_lip_lt {a b R : Real} (hR : R < 1) (haR : -R ≤ a) (hbR : b ≤ R) (hab : a < b) :
    abs (arcsin b - arcsin a) ≤ (1 / sqrt (1 - R * R)) * (b - a) := by
  obtain ⟨c, f', hac, hcb, hd, heq⟩ :=
    mean_value_theorem_ct arcsin a b hab (fun c hca hcb =>
      ⟨1 / sqrt (1 - c * c), HasDerivAt_arcsin c
        (lt_of_le_of_lt (abs_le_iff.mpr ⟨le_trans haR hca, le_trans hcb hbR⟩) hR)⟩)
  have hcR : abs c ≤ R := abs_le_iff.mpr ⟨le_trans haR (le_of_lt hac), le_trans (le_of_lt hcb) hbR⟩
  have hf' : f' = 1 / sqrt (1 - c * c) :=
    HasDerivAt_unique arcsin f' (1 / sqrt (1 - c * c)) c hd
      (HasDerivAt_arcsin c (lt_of_le_of_lt hcR hR))
  have hcc_le_RR : c * c ≤ R * R := sq_le_of_abs_le hcR
  have h1 : 1 - R * R ≤ 1 - c * c := sub_le_sub_left hcc_le_RR 1
  have h1RR_pos : 0 < 1 - R * R := sub_pos_of_lt (sq_lt_one_of_abs_le_lt_one hR hcR)
  have h1cc_pos : 0 < 1 - c * c :=
    sub_pos_of_lt (lt_of_le_of_lt hcc_le_RR (sq_lt_one_of_abs_le_lt_one hR hcR))
  have hsqrt_mono : sqrt (1 - R * R) ≤ sqrt (1 - c * c) := sqrt_mono (le_of_lt h1RR_pos) h1
  have hdiv : 1 / sqrt (1 - c * c) ≤ 1 / sqrt (1 - R * R) :=
    div_le_div_pos (le_of_lt zero_lt_one_ax) (le_refl 1) (sqrt_pos h1RR_pos) hsqrt_mono
  have hba_nn : 0 ≤ b - a := sub_nonneg_of_le (le_of_lt hab)
  rw [heq, hf', abs_mul, abs_of_nonneg hba_nn,
      abs_of_nonneg (le_of_lt (one_div_pos_of_pos (sqrt_pos h1cc_pos)))]
  exact mul_le_mul_of_nonneg_right hdiv hba_nn

/-- **`arcsin` is `1/√(1−R²)`-Lipschitz on `[-R,R]`** (`R < 1`) — the `absenc_lip_local` hypothesis
for `arcsin`. For any `p, q ∈ [-R,R]`, `|arcsin p − arcsin q| ≤ (1/√(1−R²))·|p − q|`. -/
theorem arcsin_lip_local (R : Real) (hR : R < 1) :
    ∀ p q : Real, -R ≤ p → p ≤ R → -R ≤ q → q ≤ R →
      abs (arcsin p - arcsin q) ≤ (1 / sqrt (1 - R * R)) * abs (p - q) := by
  intro p q hRp hpR hRq hqR
  rcases lt_total p q with h | h | h
  · have hpq : abs (p - q) = q - p := by
      rw [abs_sub_comm3 p q]; exact abs_of_nonneg (sub_nonneg_of_le (le_of_lt h))
    rw [abs_sub_comm3 (arcsin p) (arcsin q), hpq]
    exact arcsin_lip_lt hR hRp hqR h
  · subst h
    have hpR' : abs p ≤ R := abs_le_iff.mpr ⟨hRp, hpR⟩
    rw [show arcsin p - arcsin p = (0 : Real) from by mach_ring, abs_zero]
    exact mul_nonneg
      (le_of_lt (one_div_pos_of_pos (sqrt_pos (sub_pos_of_lt (sq_lt_one_of_abs_le_lt_one hR hpR')))))
      (abs_nonneg (p - p))
  · rw [show abs (p - q) = p - q from abs_of_nonneg (sub_nonneg_of_le (le_of_lt h))]
    exact arcsin_lip_lt hR hRq hpR h

/-- **The `arcsin` forward-error node.** Input within `Ex`, both in `[-R,R]` (`R < 1`) ⟹ output
within `Eround + (1/√(1−R²))·Ex`. -/
theorem absenc_arcsin_local {flx xe Ex flf Eround R : Real} (hR : R < 1)
    (hx : AbsEnc Ex flx xe) (hflx : abs flx ≤ R) (hxe : abs xe ≤ R)
    (hround : abs (flf - arcsin flx) ≤ Eround) :
    AbsEnc (Eround + (1 / sqrt (1 - R * R)) * Ex) flf (arcsin xe) :=
  absenc_lip_local (lo := -R) (hi := R)
    (le_of_lt (one_div_pos_of_pos (sqrt_pos (sub_pos_of_lt (sq_lt_one_of_abs_le_lt_one hR hxe)))))
    (arcsin_lip_local R hR) hx
    (abs_le_iff.mp hflx).1 (abs_le_iff.mp hflx).2 (abs_le_iff.mp hxe).1 (abs_le_iff.mp hxe).2 hround

/-! ## `arccos` -/

/-- One-sided MVT bound: for `-R ≤ a < b ≤ R` (`R < 1`), `|arccos b − arccos a| ≤ (1/√(1−R²))·(b−a)`.
Same shape as `arcsin_lip_lt`, with the sign of the derivative absorbed by `abs_neg`. -/
theorem arccos_lip_lt {a b R : Real} (hR : R < 1) (haR : -R ≤ a) (hbR : b ≤ R) (hab : a < b) :
    abs (arccos b - arccos a) ≤ (1 / sqrt (1 - R * R)) * (b - a) := by
  obtain ⟨c, f', hac, hcb, hd, heq⟩ :=
    mean_value_theorem_ct arccos a b hab (fun c hca hcb =>
      ⟨-(1 / sqrt (1 - c * c)), HasDerivAt_arccos c
        (lt_of_le_of_lt (abs_le_iff.mpr ⟨le_trans haR hca, le_trans hcb hbR⟩) hR)⟩)
  have hcR : abs c ≤ R := abs_le_iff.mpr ⟨le_trans haR (le_of_lt hac), le_trans (le_of_lt hcb) hbR⟩
  have hf' : f' = -(1 / sqrt (1 - c * c)) :=
    HasDerivAt_unique arccos f' (-(1 / sqrt (1 - c * c))) c hd
      (HasDerivAt_arccos c (lt_of_le_of_lt hcR hR))
  have hcc_le_RR : c * c ≤ R * R := sq_le_of_abs_le hcR
  have h1 : 1 - R * R ≤ 1 - c * c := sub_le_sub_left hcc_le_RR 1
  have h1RR_pos : 0 < 1 - R * R := sub_pos_of_lt (sq_lt_one_of_abs_le_lt_one hR hcR)
  have h1cc_pos : 0 < 1 - c * c :=
    sub_pos_of_lt (lt_of_le_of_lt hcc_le_RR (sq_lt_one_of_abs_le_lt_one hR hcR))
  have hsqrt_mono : sqrt (1 - R * R) ≤ sqrt (1 - c * c) := sqrt_mono (le_of_lt h1RR_pos) h1
  have hdiv : 1 / sqrt (1 - c * c) ≤ 1 / sqrt (1 - R * R) :=
    div_le_div_pos (le_of_lt zero_lt_one_ax) (le_refl 1) (sqrt_pos h1RR_pos) hsqrt_mono
  have hba_nn : 0 ≤ b - a := sub_nonneg_of_le (le_of_lt hab)
  rw [heq, hf', abs_mul, abs_neg, abs_of_nonneg hba_nn,
      abs_of_nonneg (le_of_lt (one_div_pos_of_pos (sqrt_pos h1cc_pos)))]
  exact mul_le_mul_of_nonneg_right hdiv hba_nn

/-- **`arccos` is `1/√(1−R²)`-Lipschitz on `[-R,R]`** (`R < 1`) — the `absenc_lip_local` hypothesis
for `arccos`. -/
theorem arccos_lip_local (R : Real) (hR : R < 1) :
    ∀ p q : Real, -R ≤ p → p ≤ R → -R ≤ q → q ≤ R →
      abs (arccos p - arccos q) ≤ (1 / sqrt (1 - R * R)) * abs (p - q) := by
  intro p q hRp hpR hRq hqR
  rcases lt_total p q with h | h | h
  · have hpq : abs (p - q) = q - p := by
      rw [abs_sub_comm3 p q]; exact abs_of_nonneg (sub_nonneg_of_le (le_of_lt h))
    rw [abs_sub_comm3 (arccos p) (arccos q), hpq]
    exact arccos_lip_lt hR hRp hqR h
  · subst h
    have hpR' : abs p ≤ R := abs_le_iff.mpr ⟨hRp, hpR⟩
    rw [show arccos p - arccos p = (0 : Real) from by mach_ring, abs_zero]
    exact mul_nonneg
      (le_of_lt (one_div_pos_of_pos (sqrt_pos (sub_pos_of_lt (sq_lt_one_of_abs_le_lt_one hR hpR')))))
      (abs_nonneg (p - p))
  · rw [show abs (p - q) = p - q from abs_of_nonneg (sub_nonneg_of_le (le_of_lt h))]
    exact arccos_lip_lt hR hRq hpR h

/-- **The `arccos` forward-error node.** Input within `Ex`, both in `[-R,R]` (`R < 1`) ⟹ output
within `Eround + (1/√(1−R²))·Ex`. -/
theorem absenc_arccos_local {flx xe Ex flf Eround R : Real} (hR : R < 1)
    (hx : AbsEnc Ex flx xe) (hflx : abs flx ≤ R) (hxe : abs xe ≤ R)
    (hround : abs (flf - arccos flx) ≤ Eround) :
    AbsEnc (Eround + (1 / sqrt (1 - R * R)) * Ex) flf (arccos xe) :=
  absenc_lip_local (lo := -R) (hi := R)
    (le_of_lt (one_div_pos_of_pos (sqrt_pos (sub_pos_of_lt (sq_lt_one_of_abs_le_lt_one hR hxe)))))
    (arccos_lip_local R hR) hx
    (abs_le_iff.mp hflx).1 (abs_le_iff.mp hflx).2 (abs_le_iff.mp hxe).1 (abs_le_iff.mp hxe).2 hround

end MachLib.Real
