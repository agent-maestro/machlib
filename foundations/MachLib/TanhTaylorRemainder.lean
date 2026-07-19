import MachLib.SinTaylorRemainder
import MachLib.HyperbolicLipschitz
import MachLib.NatCastArith
import MachLib.TanTaylorRemainder
import MachLib.AbsoluteError


/-!
# `tanh` Taylor-remainder bound — same 8-level MVT chain as `tan`, alternating signs

`eml_tanh.v` computes the 4-term Maclaurin truncation `tanh(x) ≈ x − x³/3 + 2x⁵/15 − 17x⁷/315`
(valid `|x| ≤ 1`). `tanh' = 1 − tanh²` (vs `tan' = 1 + tan²`), so — like `tan` — every derivative of
`tanh` is a higher-degree polynomial in `tanh` itself: the chain never closes on a flat constant
alone. Initially assumed this would be EASIER than `tan` (no domain restriction needed, since
`|tanh| ≤ 1` everywhere, unlike `tan` blowing up at `π/2`) — that part is true, but it does NOT
avoid the real cost: `tan`'s own `Rtan1..Rtan7` already mix a T-polynomial part with a y-monomial
correction (e.g. `Rtan6 = 720tan⁷ − 1680tan⁵ + 1232tan³ − 272tan − 272y`), because each `Rk` is
`tan^(k)(y) − P^(k)(y)` and the truncation polynomial's own k-th derivative isn't zero except at
the very top level. `tanh` needs the exact same bookkeeping, just alternating signs. Verified
symbolically (sympy, both the T-recursion `g1..g8` and every `Rk = gk(T) − P^(k)(y)` cross-checked
via direct differentiation) before encoding — see the commit message for the full derivation.

**Result**: `Rtanh0_bound` is `|tanh(x) − (x − x³/3 + 2x⁵/15 − 17x⁷/315)| ≤ 354560·x^8` for
`x ∈ [0,1]` — actually a FLAT bound (no growing `Mtan(x)`-style quantity), since `|tanh| ≤ 1`
throughout the whole domain rather than approaching a singularity. `sorryAx`-free, 0 new axioms
(reuses `HasDerivAt_tanh` from `HyperbolicLipschitz.lean`).
-/

namespace MachLib.Real

/-- `1/(cosh c)² = 1 − tanh(c)²`, from `cosh² − sinh² = 1` (`pythagorean_hyp`) divided by `cosh²`.
The hyperbolic analogue of `TanTaylorRemainder`'s `sec_sq_eq_one_add_tan_sq`. -/
theorem sech_sq_eq_one_sub_tanh_sq (c : Real) :
    1 / (cosh c * cosh c) = 1 - tanh c * tanh c := by
  have hcpos : 0 < cosh c := cosh_pos c
  have hcne : cosh c ≠ 0 := ne_of_gt hcpos
  have hccne : cosh c * cosh c ≠ 0 := mul_ne_zero hcne hcne
  have htanh : tanh c = sinh c / cosh c := tanh_eq_sinh_div_cosh c
  have key : (1 - tanh c * tanh c) * (cosh c * cosh c) = 1 := by
    rw [htanh, div_def (sinh c) (cosh c) hcne]
    rw [show (1 - sinh c * (1 / cosh c) * (sinh c * (1 / cosh c))) * (cosh c * cosh c)
        = cosh c * cosh c - sinh c * sinh c * ((1 / cosh c) * (1 / cosh c) * (cosh c * cosh c))
        from by mach_mpoly [cosh c, sinh c, (1 / cosh c : Real)]]
    rw [show (1 / cosh c : Real) * (1 / cosh c) * (cosh c * cosh c)
        = ((1 / cosh c) * cosh c) * ((1 / cosh c) * cosh c) from by mach_ring,
      mul_comm (1 / cosh c : Real) (cosh c), mul_inv (cosh c) hcne,
      show (1 : Real) * 1 = 1 from by mach_ring]
    rw [mul_one_ax]
    exact pythagorean_hyp c
  refine mul_right_cancel' hccne ?_
  rw [key, mul_comm (1 / (cosh c * cosh c) : Real) (cosh c * cosh c), mul_inv (cosh c * cosh c) hccne]

/-- `HasDerivAt tanh (1 − tanh c · tanh c) c` — `HasDerivAt_tanh` re-expressed via
`sech_sq_eq_one_sub_tanh_sq` so every derivative in the chain is purely in terms of `tanh`. No
domain restriction (unlike `tan`'s `abs c < pi/2`) — `tanh`'s derivative holds for all real `c`. -/
theorem HasDerivAt_tanh' (c : Real) : HasDerivAt tanh (1 - tanh c * tanh c) c :=
  hasDerivAt_congr_val (HasDerivAt_tanh c) (sech_sq_eq_one_sub_tanh_sq c)

/-! ## Derivative combinators for powers of `tanh` — domain-unrestricted analogues of
`TanTaylorRemainder`'s `hDtan_2..hDtan_8`. -/

theorem hDtanh_2 (c : Real) :
    HasDerivAt (fun y => tanh y * tanh y)
      ((1 - tanh c * tanh c) * tanh c + tanh c * (1 - tanh c * tanh c)) c :=
  HasDerivAt_mul tanh tanh (1 - tanh c * tanh c) (1 - tanh c * tanh c) c
    (HasDerivAt_tanh' c) (HasDerivAt_tanh' c)

theorem hDtanh_3 (c : Real) :
    HasDerivAt (fun y => tanh y * tanh y * tanh y)
      (((1 - tanh c * tanh c) * tanh c + tanh c * (1 - tanh c * tanh c)) * tanh c
        + (tanh c * tanh c) * (1 - tanh c * tanh c)) c :=
  HasDerivAt_mul (fun y => tanh y * tanh y) tanh
    ((1 - tanh c * tanh c) * tanh c + tanh c * (1 - tanh c * tanh c)) (1 - tanh c * tanh c) c
    (hDtanh_2 c) (HasDerivAt_tanh' c)

theorem hDtanh_4raw (c : Real) :
    HasDerivAt (fun y => (tanh y * tanh y) * (tanh y * tanh y))
      (((1 - tanh c * tanh c) * tanh c + tanh c * (1 - tanh c * tanh c)) * (tanh c * tanh c)
        + (tanh c * tanh c) * ((1 - tanh c * tanh c) * tanh c + tanh c * (1 - tanh c * tanh c))) c :=
  HasDerivAt_mul (fun y => tanh y * tanh y) (fun y => tanh y * tanh y)
    ((1 - tanh c * tanh c) * tanh c + tanh c * (1 - tanh c * tanh c))
    ((1 - tanh c * tanh c) * tanh c + tanh c * (1 - tanh c * tanh c)) c (hDtanh_2 c) (hDtanh_2 c)

theorem hDtanh_4 (c : Real) :
    HasDerivAt (fun y => tanh y * tanh y * tanh y * tanh y)
      (((1 - tanh c * tanh c) * tanh c + tanh c * (1 - tanh c * tanh c)) * (tanh c * tanh c)
        + (tanh c * tanh c) * ((1 - tanh c * tanh c) * tanh c + tanh c * (1 - tanh c * tanh c))) c :=
  HasDerivAt_of_eq (fun y => (tanh y * tanh y) * (tanh y * tanh y))
    (fun y => tanh y * tanh y * tanh y * tanh y) _ c (fun y => by mach_ring) (hDtanh_4raw c)

theorem hDtanh_5raw (c : Real) :
    HasDerivAt (fun y => (tanh y * tanh y) * (tanh y * tanh y * tanh y))
      (((1 - tanh c * tanh c) * tanh c + tanh c * (1 - tanh c * tanh c)) * (tanh c * tanh c * tanh c)
        + (tanh c * tanh c) * (((1 - tanh c * tanh c) * tanh c + tanh c * (1 - tanh c * tanh c)) * tanh c
          + (tanh c * tanh c) * (1 - tanh c * tanh c))) c :=
  HasDerivAt_mul (fun y => tanh y * tanh y) (fun y => tanh y * tanh y * tanh y)
    ((1 - tanh c * tanh c) * tanh c + tanh c * (1 - tanh c * tanh c))
    (((1 - tanh c * tanh c) * tanh c + tanh c * (1 - tanh c * tanh c)) * tanh c
      + (tanh c * tanh c) * (1 - tanh c * tanh c)) c (hDtanh_2 c) (hDtanh_3 c)

theorem hDtanh_5 (c : Real) :
    HasDerivAt (fun y => tanh y * tanh y * tanh y * tanh y * tanh y)
      (((1 - tanh c * tanh c) * tanh c + tanh c * (1 - tanh c * tanh c)) * (tanh c * tanh c * tanh c)
        + (tanh c * tanh c) * (((1 - tanh c * tanh c) * tanh c + tanh c * (1 - tanh c * tanh c)) * tanh c
          + (tanh c * tanh c) * (1 - tanh c * tanh c))) c :=
  HasDerivAt_of_eq (fun y => (tanh y * tanh y) * (tanh y * tanh y * tanh y))
    (fun y => tanh y * tanh y * tanh y * tanh y * tanh y) _ c (fun y => by mach_ring) (hDtanh_5raw c)

theorem hDtanh_6raw (c : Real) :
    HasDerivAt (fun y => (tanh y * tanh y * tanh y) * (tanh y * tanh y * tanh y))
      ((((1 - tanh c * tanh c) * tanh c + tanh c * (1 - tanh c * tanh c)) * tanh c
          + (tanh c * tanh c) * (1 - tanh c * tanh c)) * (tanh c * tanh c * tanh c)
        + (tanh c * tanh c * tanh c)
          * (((1 - tanh c * tanh c) * tanh c + tanh c * (1 - tanh c * tanh c)) * tanh c
            + (tanh c * tanh c) * (1 - tanh c * tanh c))) c :=
  HasDerivAt_mul (fun y => tanh y * tanh y * tanh y) (fun y => tanh y * tanh y * tanh y)
    (((1 - tanh c * tanh c) * tanh c + tanh c * (1 - tanh c * tanh c)) * tanh c
      + (tanh c * tanh c) * (1 - tanh c * tanh c))
    (((1 - tanh c * tanh c) * tanh c + tanh c * (1 - tanh c * tanh c)) * tanh c
      + (tanh c * tanh c) * (1 - tanh c * tanh c)) c (hDtanh_3 c) (hDtanh_3 c)

theorem hDtanh_6 (c : Real) :
    HasDerivAt (fun y => tanh y * tanh y * tanh y * tanh y * tanh y * tanh y)
      ((((1 - tanh c * tanh c) * tanh c + tanh c * (1 - tanh c * tanh c)) * tanh c
          + (tanh c * tanh c) * (1 - tanh c * tanh c)) * (tanh c * tanh c * tanh c)
        + (tanh c * tanh c * tanh c)
          * (((1 - tanh c * tanh c) * tanh c + tanh c * (1 - tanh c * tanh c)) * tanh c
            + (tanh c * tanh c) * (1 - tanh c * tanh c))) c :=
  HasDerivAt_of_eq (fun y => (tanh y * tanh y * tanh y) * (tanh y * tanh y * tanh y))
    (fun y => tanh y * tanh y * tanh y * tanh y * tanh y * tanh y) _ c (fun y => by mach_ring)
    (hDtanh_6raw c)

theorem hDtanh_7raw (c : Real) :
    HasDerivAt (fun y => (tanh y * tanh y * tanh y) * (tanh y * tanh y * tanh y * tanh y))
      ((((1 - tanh c * tanh c) * tanh c + tanh c * (1 - tanh c * tanh c)) * tanh c
          + (tanh c * tanh c) * (1 - tanh c * tanh c)) * (tanh c * tanh c * tanh c * tanh c)
        + (tanh c * tanh c * tanh c)
          * (((1 - tanh c * tanh c) * tanh c + tanh c * (1 - tanh c * tanh c)) * (tanh c * tanh c)
            + (tanh c * tanh c) * ((1 - tanh c * tanh c) * tanh c + tanh c * (1 - tanh c * tanh c)))) c :=
  HasDerivAt_mul (fun y => tanh y * tanh y * tanh y) (fun y => tanh y * tanh y * tanh y * tanh y)
    (((1 - tanh c * tanh c) * tanh c + tanh c * (1 - tanh c * tanh c)) * tanh c
      + (tanh c * tanh c) * (1 - tanh c * tanh c))
    (((1 - tanh c * tanh c) * tanh c + tanh c * (1 - tanh c * tanh c)) * (tanh c * tanh c)
      + (tanh c * tanh c) * ((1 - tanh c * tanh c) * tanh c + tanh c * (1 - tanh c * tanh c))) c
    (hDtanh_3 c) (hDtanh_4 c)

theorem hDtanh_7 (c : Real) :
    HasDerivAt (fun y => tanh y * tanh y * tanh y * tanh y * tanh y * tanh y * tanh y)
      ((((1 - tanh c * tanh c) * tanh c + tanh c * (1 - tanh c * tanh c)) * tanh c
          + (tanh c * tanh c) * (1 - tanh c * tanh c)) * (tanh c * tanh c * tanh c * tanh c)
        + (tanh c * tanh c * tanh c)
          * (((1 - tanh c * tanh c) * tanh c + tanh c * (1 - tanh c * tanh c)) * (tanh c * tanh c)
            + (tanh c * tanh c) * ((1 - tanh c * tanh c) * tanh c + tanh c * (1 - tanh c * tanh c)))) c :=
  HasDerivAt_of_eq (fun y => (tanh y * tanh y * tanh y) * (tanh y * tanh y * tanh y * tanh y))
    (fun y => tanh y * tanh y * tanh y * tanh y * tanh y * tanh y * tanh y) _ c (fun y => by mach_ring)
    (hDtanh_7raw c)

theorem hDtanh_8raw (c : Real) :
    HasDerivAt (fun y => (tanh y * tanh y * tanh y * tanh y) * (tanh y * tanh y * tanh y * tanh y))
      ((((1 - tanh c * tanh c) * tanh c + tanh c * (1 - tanh c * tanh c)) * (tanh c * tanh c)
          + (tanh c * tanh c) * ((1 - tanh c * tanh c) * tanh c + tanh c * (1 - tanh c * tanh c)))
          * (tanh c * tanh c * tanh c * tanh c)
        + (tanh c * tanh c * tanh c * tanh c)
          * (((1 - tanh c * tanh c) * tanh c + tanh c * (1 - tanh c * tanh c)) * (tanh c * tanh c)
            + (tanh c * tanh c) * ((1 - tanh c * tanh c) * tanh c + tanh c * (1 - tanh c * tanh c)))) c :=
  HasDerivAt_mul (fun y => tanh y * tanh y * tanh y * tanh y) (fun y => tanh y * tanh y * tanh y * tanh y)
    (((1 - tanh c * tanh c) * tanh c + tanh c * (1 - tanh c * tanh c)) * (tanh c * tanh c)
      + (tanh c * tanh c) * ((1 - tanh c * tanh c) * tanh c + tanh c * (1 - tanh c * tanh c)))
    (((1 - tanh c * tanh c) * tanh c + tanh c * (1 - tanh c * tanh c)) * (tanh c * tanh c)
      + (tanh c * tanh c) * ((1 - tanh c * tanh c) * tanh c + tanh c * (1 - tanh c * tanh c))) c
    (hDtanh_4 c) (hDtanh_4 c)

theorem hDtanh_8 (c : Real) :
    HasDerivAt (fun y => tanh y * tanh y * tanh y * tanh y * tanh y * tanh y * tanh y * tanh y)
      ((((1 - tanh c * tanh c) * tanh c + tanh c * (1 - tanh c * tanh c)) * (tanh c * tanh c)
          + (tanh c * tanh c) * ((1 - tanh c * tanh c) * tanh c + tanh c * (1 - tanh c * tanh c)))
          * (tanh c * tanh c * tanh c * tanh c)
        + (tanh c * tanh c * tanh c * tanh c)
          * (((1 - tanh c * tanh c) * tanh c + tanh c * (1 - tanh c * tanh c)) * (tanh c * tanh c)
            + (tanh c * tanh c) * ((1 - tanh c * tanh c) * tanh c + tanh c * (1 - tanh c * tanh c)))) c :=
  HasDerivAt_of_eq (fun y => (tanh y * tanh y * tanh y * tanh y) * (tanh y * tanh y * tanh y * tanh y))
    (fun y => tanh y * tanh y * tanh y * tanh y * tanh y * tanh y * tanh y * tanh y) _ c
    (fun y => by mach_ring) (hDtanh_8raw c)

/-! ## `g8h` — `tanh`'s 8th derivative, `Rtanh7`'s own derivative. Same coefficient MAGNITUDES as
`tan`'s `g8` (`7936,56320,129024,120960,40320`), confirmed by direct symbolic recursion
(`T' = 1−T²` vs `tan`'s `T'=1+T²`), alternating sign starting `+` at `T¹`. Unlike `g8`, the bound
here is FLAT (`354560`, no `Mtan(x)`-style growing quantity) since `|tanh| ≤ 1` everywhere — no
domain restriction needed at all. -/

noncomputable def g8h (y : Real) : Real :=
  natCast 7936 * tanh y - natCast 56320 * (tanh y * tanh y * tanh y)
    + natCast 129024 * (tanh y * tanh y * tanh y * tanh y * tanh y)
    - natCast 120960 * (tanh y * tanh y * tanh y * tanh y * tanh y * tanh y * tanh y)
    + natCast 40320
      * (tanh y * tanh y * tanh y * tanh y * tanh y * tanh y * tanh y * tanh y * tanh y)

theorem g8h_bound (t : Real) : abs (g8h t) ≤ natCast 354560 := by
  have hT1 : abs (tanh t) ≤ 1 := abs_tanh_le_one t
  have hT2 : abs (tanh t * tanh t) ≤ 1 := by
    rw [abs_mul]; exact mul_le_one_of_le_one (abs_nonneg _) (abs_nonneg _) hT1 hT1
  have hT3 : abs (tanh t * tanh t * tanh t) ≤ 1 := by
    rw [abs_mul]; exact mul_le_one_of_le_one (abs_nonneg _) (abs_nonneg _) hT2 hT1
  have hT4 : abs (tanh t * tanh t * tanh t * tanh t) ≤ 1 := by
    rw [abs_mul]; exact mul_le_one_of_le_one (abs_nonneg _) (abs_nonneg _) hT3 hT1
  have hT5 : abs (tanh t * tanh t * tanh t * tanh t * tanh t) ≤ 1 := by
    rw [abs_mul]; exact mul_le_one_of_le_one (abs_nonneg _) (abs_nonneg _) hT4 hT1
  have hT6 : abs (tanh t * tanh t * tanh t * tanh t * tanh t * tanh t) ≤ 1 := by
    rw [abs_mul]; exact mul_le_one_of_le_one (abs_nonneg _) (abs_nonneg _) hT5 hT1
  have hT7 : abs (tanh t * tanh t * tanh t * tanh t * tanh t * tanh t * tanh t) ≤ 1 := by
    rw [abs_mul]; exact mul_le_one_of_le_one (abs_nonneg _) (abs_nonneg _) hT6 hT1
  have hT8 : abs (tanh t * tanh t * tanh t * tanh t * tanh t * tanh t * tanh t * tanh t) ≤ 1 := by
    rw [abs_mul]; exact mul_le_one_of_le_one (abs_nonneg _) (abs_nonneg _) hT7 hT1
  have hT9 : abs (tanh t * tanh t * tanh t * tanh t * tanh t * tanh t * tanh t * tanh t * tanh t) ≤ 1 := by
    rw [abs_mul]; exact mul_le_one_of_le_one (abs_nonneg _) (abs_nonneg _) hT8 hT1
  have hnn7936 : (0 : Real) ≤ natCast 7936 := natCast_nonneg 7936
  have hnn56320 : (0 : Real) ≤ natCast 56320 := natCast_nonneg 56320
  have hnn129024 : (0 : Real) ≤ natCast 129024 := natCast_nonneg 129024
  have hnn120960 : (0 : Real) ≤ natCast 120960 := natCast_nonneg 120960
  have hnn40320 : (0 : Real) ≤ natCast 40320 := natCast_nonneg 40320
  have e1 : abs (natCast 7936 * tanh t) ≤ natCast 7936 := by
    rw [abs_mul, abs_of_nonneg hnn7936]
    have hstep := mul_le_mul_of_nonneg_left hT1 hnn7936
    rwa [mul_one_ax] at hstep
  have e2 : abs (natCast 56320 * (tanh t * tanh t * tanh t)) ≤ natCast 56320 := by
    rw [abs_mul, abs_of_nonneg hnn56320]
    have hstep := mul_le_mul_of_nonneg_left hT3 hnn56320
    rwa [mul_one_ax] at hstep
  have e3 : abs (natCast 129024 * (tanh t * tanh t * tanh t * tanh t * tanh t)) ≤ natCast 129024 := by
    rw [abs_mul, abs_of_nonneg hnn129024]
    have hstep := mul_le_mul_of_nonneg_left hT5 hnn129024
    rwa [mul_one_ax] at hstep
  have e4 : abs (natCast 120960
      * (tanh t * tanh t * tanh t * tanh t * tanh t * tanh t * tanh t)) ≤ natCast 120960 := by
    rw [abs_mul, abs_of_nonneg hnn120960]
    have hstep := mul_le_mul_of_nonneg_left hT7 hnn120960
    rwa [mul_one_ax] at hstep
  have e5 : abs (natCast 40320
      * (tanh t * tanh t * tanh t * tanh t * tanh t * tanh t * tanh t * tanh t * tanh t))
      ≤ natCast 40320 := by
    rw [abs_mul, abs_of_nonneg hnn40320]
    have hstep := mul_le_mul_of_nonneg_left hT9 hnn40320
    rwa [mul_one_ax] at hstep
  unfold g8h
  rw [show natCast 354560 = ((((natCast 7936 + natCast 56320) + natCast 129024)
      + natCast 120960) + natCast 40320) from by
    rw [← natCast_add, ← natCast_add, ← natCast_add, ← natCast_add]]
  -- g8h = ((((A - B) + C) - D) + E) -- peel outside-in via abs_add / abs_sub_le'.
  refine le_trans (abs_add _ _) (add_le_add_both ?_ e5)
  refine le_trans (abs_sub_le' _ _) (add_le_add_both ?_ e4)
  refine le_trans (abs_add _ _) (add_le_add_both ?_ e3)
  exact le_trans (abs_sub_le' _ _) (add_le_add_both e1 e2)


/-! ## `Rtanh7` — the base level (`Rtanh6' = Rtanh7`, `Rtanh7' = g8h`). Pure T-polynomial (the
constant term of `tanh`'s 7th derivative cancels against the 7th derivative of the truncation
polynomial, exactly like `Rtan7`). -/

noncomputable def Rtanh7 (y : Real) : Real :=
  natCast 3968 * (tanh y * tanh y) - natCast 12096 * (tanh y * tanh y * tanh y * tanh y)
    + natCast 13440 * (tanh y * tanh y * tanh y * tanh y * tanh y * tanh y)
    - natCast 5040 * (tanh y * tanh y * tanh y * tanh y * tanh y * tanh y * tanh y * tanh y)

theorem Rtanh7_deriv (c : Real) : HasDerivAt Rtanh7 (g8h c) c := by
  have h2 : HasDerivAt (fun y => natCast 3968 * (tanh y * tanh y))
      (0 * (tanh c * tanh c)
        + natCast 3968 * ((1 - tanh c * tanh c) * tanh c + tanh c * (1 - tanh c * tanh c))) c :=
    HasDerivAt_mul (fun _ => natCast 3968) (fun y => tanh y * tanh y) 0 _ c
      (HasDerivAt_const (natCast 3968) c) (hDtanh_2 c)
  have h4 : HasDerivAt (fun y => natCast 12096 * (tanh y * tanh y * tanh y * tanh y))
      (0 * (tanh c * tanh c * tanh c * tanh c)
        + natCast 12096
          * (((1 - tanh c * tanh c) * tanh c + tanh c * (1 - tanh c * tanh c)) * (tanh c * tanh c)
            + (tanh c * tanh c) * ((1 - tanh c * tanh c) * tanh c + tanh c * (1 - tanh c * tanh c)))) c :=
    HasDerivAt_mul (fun _ => natCast 12096) (fun y => tanh y * tanh y * tanh y * tanh y) 0 _ c
      (HasDerivAt_const (natCast 12096) c) (hDtanh_4 c)
  have h6 : HasDerivAt (fun y => natCast 13440 * (tanh y * tanh y * tanh y * tanh y * tanh y * tanh y))
      (0 * (tanh c * tanh c * tanh c * tanh c * tanh c * tanh c)
        + natCast 13440
          * ((((1 - tanh c * tanh c) * tanh c + tanh c * (1 - tanh c * tanh c)) * tanh c
              + (tanh c * tanh c) * (1 - tanh c * tanh c)) * (tanh c * tanh c * tanh c)
            + (tanh c * tanh c * tanh c)
              * (((1 - tanh c * tanh c) * tanh c + tanh c * (1 - tanh c * tanh c)) * tanh c
                + (tanh c * tanh c) * (1 - tanh c * tanh c)))) c :=
    HasDerivAt_mul (fun _ => natCast 13440)
      (fun y => tanh y * tanh y * tanh y * tanh y * tanh y * tanh y) 0 _ c
      (HasDerivAt_const (natCast 13440) c) (hDtanh_6 c)
  have h8 : HasDerivAt
      (fun y => natCast 5040 * (tanh y * tanh y * tanh y * tanh y * tanh y * tanh y * tanh y * tanh y))
      (0 * (tanh c * tanh c * tanh c * tanh c * tanh c * tanh c * tanh c * tanh c)
        + natCast 5040
          * ((((1 - tanh c * tanh c) * tanh c + tanh c * (1 - tanh c * tanh c)) * (tanh c * tanh c)
              + (tanh c * tanh c) * ((1 - tanh c * tanh c) * tanh c + tanh c * (1 - tanh c * tanh c)))
              * (tanh c * tanh c * tanh c * tanh c)
            + (tanh c * tanh c * tanh c * tanh c)
              * (((1 - tanh c * tanh c) * tanh c + tanh c * (1 - tanh c * tanh c)) * (tanh c * tanh c)
                + (tanh c * tanh c) * ((1 - tanh c * tanh c) * tanh c
                  + tanh c * (1 - tanh c * tanh c))))) c :=
    HasDerivAt_mul (fun _ => natCast 5040)
      (fun y => tanh y * tanh y * tanh y * tanh y * tanh y * tanh y * tanh y * tanh y) 0 _ c
      (HasDerivAt_const (natCast 5040) c) (hDtanh_8 c)
  have hsub1 := HasDerivAt_sub (fun y => natCast 3968 * (tanh y * tanh y))
    (fun y => natCast 12096 * (tanh y * tanh y * tanh y * tanh y)) _ _ c h2 h4
  have hadd := HasDerivAt_add _
    (fun y => natCast 13440 * (tanh y * tanh y * tanh y * tanh y * tanh y * tanh y)) _ _ c hsub1 h6
  have hfull := HasDerivAt_sub _
    (fun y => natCast 5040 * (tanh y * tanh y * tanh y * tanh y * tanh y * tanh y * tanh y * tanh y))
    _ _ c hadd h8
  have hT1 : natCast 7936 = (1 + 1) * natCast 3968 := (two_mul_natCast 3968).symm
  have hT3 : natCast 56320 = (1 + 1) * natCast 3968 + (1 + 1 + 1 + 1) * natCast 12096 := by
    rw [two_mul_natCast, four_mul_natCast, ← natCast_add]
  have hT5 : natCast 129024
      = (1 + 1 + 1 + 1) * natCast 12096 + (1 + 1 + 1 + 1 + 1 + 1) * natCast 13440 := by
    rw [four_mul_natCast, six_mul_natCast, ← natCast_add]
  have hT7 : natCast 120960 = (1 + 1 + 1 + 1 + 1 + 1) * natCast 13440
      + (1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) * natCast 5040 := by
    rw [six_mul_natCast, eight_mul_natCast, ← natCast_add]
  have hT9 : natCast 40320 = (1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) * natCast 5040 :=
    (eight_mul_natCast 5040).symm
  refine hasDerivAt_congr_val hfull ?_
  unfold g8h
  rw [hT1, hT3, hT5, hT7, hT9]
  mach_mpoly [tanh c, natCast 3968, natCast 12096, natCast 13440, natCast 5040]

theorem Rtanh7_zero : Rtanh7 0 = 0 := by unfold Rtanh7; rw [tanh_zero]; mach_ring

/-- `|Rtanh7(x)| ≤ 354560 · x` for `x ∈ [0,1]` — flat bound (`g8h_bound` is already flat), unlike
`Rtan7`'s `Mtan(x)^9·x`. -/
theorem Rtanh7_bound (x : Real) (hx0 : 0 ≤ x) : abs (Rtanh7 x) ≤ natCast 354560 * x := by
  apply abs_mvt_step Rtanh7 g8h x (natCast 354560) hx0 (natCast_nonneg 354560)
    (fun c => Rtanh7_deriv c) Rtanh7_zero
  intro t _ _; exact g8h_bound t

/-! ## `Rtanh6` (`Rtanh5' = Rtanh6`, `Rtanh6' = Rtanh7`). `Rtanh6(y) = 720tanh⁷ − 1680tanh⁵ +
1232tanh³ − 272tanh + 272y` — the first level needing the y-monomial correction (`tanh`'s 6th
derivative minus the truncation's own 6th derivative, `−272y`, giving `+272y` after subtracting a
negative). -/

noncomputable def Rtanh6 (y : Real) : Real :=
  natCast 720 * (tanh y * tanh y * tanh y * tanh y * tanh y * tanh y * tanh y)
    - natCast 1680 * (tanh y * tanh y * tanh y * tanh y * tanh y)
    + natCast 1232 * (tanh y * tanh y * tanh y) - natCast 272 * tanh y + natCast 272 * y

set_option maxHeartbeats 1000000 in
theorem Rtanh6_deriv (c : Real) : HasDerivAt Rtanh6 (Rtanh7 c) c := by
  have h7 := HasDerivAt_mul (fun _ => natCast 720)
    (fun y => tanh y * tanh y * tanh y * tanh y * tanh y * tanh y * tanh y) 0 _ c
    (HasDerivAt_const (natCast 720) c) (hDtanh_7 c)
  have h5 := HasDerivAt_mul (fun _ => natCast 1680)
    (fun y => tanh y * tanh y * tanh y * tanh y * tanh y) 0 _ c
    (HasDerivAt_const (natCast 1680) c) (hDtanh_5 c)
  have h3 := HasDerivAt_mul (fun _ => natCast 1232) (fun y => tanh y * tanh y * tanh y) 0 _ c
    (HasDerivAt_const (natCast 1232) c) (hDtanh_3 c)
  have h1 := HasDerivAt_mul (fun _ => natCast 272) tanh 0 _ c (HasDerivAt_const (natCast 272) c)
    (HasDerivAt_tanh' c)
  have hy := HasDerivAt_mul (fun _ => natCast 272) (fun y => y) 0 1 c
    (HasDerivAt_const (natCast 272) c) (HasDerivAt_id c)
  have hsub1 := HasDerivAt_sub
    (fun y => natCast 720 * (tanh y * tanh y * tanh y * tanh y * tanh y * tanh y * tanh y))
    (fun y => natCast 1680 * (tanh y * tanh y * tanh y * tanh y * tanh y)) _ _ c h7 h5
  have hadd1 := HasDerivAt_add _ (fun y => natCast 1232 * (tanh y * tanh y * tanh y)) _ _ c hsub1 h3
  have hsub2 := HasDerivAt_sub _ (fun y => natCast 272 * tanh y) _ _ c hadd1 h1
  have hfull := HasDerivAt_add _ (fun y => natCast 272 * y) _ _ c hsub2 hy
  have hT2 : natCast 3968 = natCast 272 + (1 + 1 + 1) * natCast 1232 := by
    rw [three_mul_natCast, ← natCast_add]
  have hT4 : natCast 12096
      = (1 + 1 + 1) * natCast 1232 + (1 + 1 + 1 + 1 + 1) * natCast 1680 := by
    rw [three_mul_natCast, five_mul_natCast, ← natCast_add]
  have hT6 : natCast 13440
      = (1 + 1 + 1 + 1 + 1) * natCast 1680 + (1 + 1 + 1 + 1 + 1 + 1 + 1) * natCast 720 := by
    rw [five_mul_natCast, seven_mul_natCast, ← natCast_add]
  have hT8 : natCast 5040 = (1 + 1 + 1 + 1 + 1 + 1 + 1) * natCast 720 :=
    (seven_mul_natCast 720).symm
  refine hasDerivAt_congr_val hfull ?_
  unfold Rtanh7
  rw [hT2, hT4, hT6, hT8]
  mach_mpoly [tanh c, natCast 272, natCast 1232, natCast 1680, natCast 720]

theorem Rtanh6_zero : Rtanh6 0 = 0 := by unfold Rtanh6; rw [tanh_zero]; mach_ring

/-- `|Rtanh6(x)| ≤ (354560·x)·x` for `x ∈ [0,1]` — direct flat propagation from `Rtanh7_bound`. -/
theorem Rtanh6_bound (x : Real) (hx0 : 0 ≤ x) : abs (Rtanh6 x) ≤ (natCast 354560 * x) * x := by
  apply abs_mvt_step Rtanh6 Rtanh7 x (natCast 354560 * x) hx0
    (mul_nonneg (natCast_nonneg 354560) hx0) (fun c => Rtanh6_deriv c) Rtanh6_zero
  intro t ht0 htx
  exact le_trans (Rtanh7_bound t ht0) (mul_le_mul_of_nonneg_left htx (natCast_nonneg 354560))

/-! ## `Rtanh5` (`Rtanh4' = Rtanh5`, `Rtanh5' = Rtanh6`). `Rtanh5(y) = -136tanh² + 240tanh⁴ −
120tanh⁶ + 136y²`. -/

noncomputable def Rtanh5 (y : Real) : Real :=
  natCast 240 * (tanh y * tanh y * tanh y * tanh y)
    - natCast 120 * (tanh y * tanh y * tanh y * tanh y * tanh y * tanh y)
    - natCast 136 * (tanh y * tanh y) + natCast 136 * (y * y)

set_option maxHeartbeats 1000000 in
theorem Rtanh5_deriv (c : Real) : HasDerivAt Rtanh5 (Rtanh6 c) c := by
  have h4 := HasDerivAt_mul (fun _ => natCast 240) (fun y => tanh y * tanh y * tanh y * tanh y)
    0 _ c (HasDerivAt_const (natCast 240) c) (hDtanh_4 c)
  have h6 := HasDerivAt_mul (fun _ => natCast 120)
    (fun y => tanh y * tanh y * tanh y * tanh y * tanh y * tanh y) 0 _ c
    (HasDerivAt_const (natCast 120) c) (hDtanh_6 c)
  have h2 := HasDerivAt_mul (fun _ => natCast 136) (fun y => tanh y * tanh y) 0 _ c
    (HasDerivAt_const (natCast 136) c) (hDtanh_2 c)
  have hy2 := HasDerivAt_mul (fun _ => natCast 136) (fun y => y * y) 0 _ c
    (HasDerivAt_const (natCast 136) c) (hD_y2 c)
  have hsub1 := HasDerivAt_sub (fun y => natCast 240 * (tanh y * tanh y * tanh y * tanh y))
    (fun y => natCast 120 * (tanh y * tanh y * tanh y * tanh y * tanh y * tanh y)) _ _ c h4 h6
  have hsub2 := HasDerivAt_sub _ (fun y => natCast 136 * (tanh y * tanh y)) _ _ c hsub1 h2
  have hfull := HasDerivAt_add _ (fun y => natCast 136 * (y * y)) _ _ c hsub2 hy2
  have hT1 : natCast 272 = (1 + 1) * natCast 136 := (two_mul_natCast 136).symm
  have hT3 : natCast 1232 = (1 + 1) * natCast 136 + (1 + 1 + 1 + 1) * natCast 240 := by
    rw [two_mul_natCast, four_mul_natCast, ← natCast_add]
  have hT5 : natCast 1680
      = (1 + 1 + 1 + 1) * natCast 240 + (1 + 1 + 1 + 1 + 1 + 1) * natCast 120 := by
    rw [four_mul_natCast, six_mul_natCast, ← natCast_add]
  have hT7 : natCast 720 = (1 + 1 + 1 + 1 + 1 + 1) * natCast 120 :=
    (six_mul_natCast 120).symm
  refine hasDerivAt_congr_val hfull ?_
  unfold Rtanh6
  rw [hT1, hT3, hT5, hT7]
  mach_mpoly [tanh c, natCast 136, natCast 240, natCast 120]

theorem Rtanh5_zero : Rtanh5 0 = 0 := by unfold Rtanh5; rw [tanh_zero]; mach_ring

/-- `|Rtanh5(x)| ≤ ((354560·x)·x)·x` for `x ∈ [0,1]` — direct flat propagation. -/
theorem Rtanh5_bound (x : Real) (hx0 : 0 ≤ x) :
    abs (Rtanh5 x) ≤ ((natCast 354560 * x) * x) * x := by
  apply abs_mvt_step Rtanh5 Rtanh6 x ((natCast 354560 * x) * x) hx0
    (mul_nonneg (mul_nonneg (natCast_nonneg 354560) hx0) hx0) (fun c => Rtanh5_deriv c) Rtanh5_zero
  intro t ht0 htx
  exact le_trans (Rtanh6_bound t ht0)
    (mul_le_mul' (mul_nonneg (natCast_nonneg 354560) ht0)
      (mul_le_mul_of_nonneg_left htx (natCast_nonneg 354560)) ht0 htx)

/-! ## `Rtanh4` (`Rtanh3' = Rtanh4`, `Rtanh4' = Rtanh5`). `Rtanh4(y) = 24tanh⁵ − 40tanh³ + 16tanh +
(136/3)y³ − 16y` — the first FRACTIONAL y-monomial coefficient (`136·(1/3)`, cancelling to `136y²`
on differentiation via `(1+1+1)·(1/3) = 1`). -/

theorem natCast136_third_cancel : (1 + 1 + 1) * (natCast 136 * (1 / natCast 3)) = natCast 136 := by
  rw [show (1 + 1 + 1 : Real) * (natCast 136 * (1 / natCast 3))
      = natCast 136 * ((1 + 1 + 1) * (1 / natCast 3)) from by mach_ring,
    ← natCast_three, mul_inv (natCast 3) (natCast_ne_zero (by decide)), mul_one_ax]

noncomputable def Rtanh4 (y : Real) : Real :=
  natCast 24 * (tanh y * tanh y * tanh y * tanh y * tanh y)
    - natCast 40 * (tanh y * tanh y * tanh y) + natCast 16 * tanh y
    + y * y * y * (natCast 136 * (1 / natCast 3)) - natCast 16 * y

set_option maxHeartbeats 1000000 in
theorem Rtanh4_deriv (c : Real) : HasDerivAt Rtanh4 (Rtanh5 c) c := by
  have h5 := HasDerivAt_mul (fun _ => natCast 24)
    (fun y => tanh y * tanh y * tanh y * tanh y * tanh y) 0 _ c
    (HasDerivAt_const (natCast 24) c) (hDtanh_5 c)
  have h3 := HasDerivAt_mul (fun _ => natCast 40) (fun y => tanh y * tanh y * tanh y) 0 _ c
    (HasDerivAt_const (natCast 40) c) (hDtanh_3 c)
  have h1 := HasDerivAt_mul (fun _ => natCast 16) tanh 0 _ c (HasDerivAt_const (natCast 16) c)
    (HasDerivAt_tanh' c)
  have hy3 := HasDerivAt_mul (fun y => y * y * y) (fun _ => natCast 136 * (1 / natCast 3))
    (c * c + c * c + c * c) 0 c (hD_y3 c) (HasDerivAt_const (natCast 136 * (1 / natCast 3)) c)
  have hy1 := HasDerivAt_mul (fun _ => natCast 16) (fun y => y) 0 1 c
    (HasDerivAt_const (natCast 16) c) (HasDerivAt_id c)
  have hsub1 := HasDerivAt_sub (fun y => natCast 24 * (tanh y * tanh y * tanh y * tanh y * tanh y))
    (fun y => natCast 40 * (tanh y * tanh y * tanh y)) _ _ c h5 h3
  have hadd1 := HasDerivAt_add _ (fun y => natCast 16 * tanh y) _ _ c hsub1 h1
  have hadd2 := HasDerivAt_add _ (fun y => y * y * y * (natCast 136 * (1 / natCast 3))) _ _ c hadd1 hy3
  have hfull := HasDerivAt_sub _ (fun y => natCast 16 * y) _ _ c hadd2 hy1
  refine hasDerivAt_congr_val hfull ?_
  unfold Rtanh5
  rw [show (c * c + c * c + c * c) * (natCast 136 * (1 / natCast 3)) = natCast 136 * (c * c) from by
    rw [show (c * c + c * c + c * c : Real) * (natCast 136 * (1 / natCast 3))
        = ((1 + 1 + 1) * (natCast 136 * (1 / natCast 3))) * (c * c) from by mach_ring,
      natCast136_third_cancel]]
  have hA : natCast 120 = (1 + 1 + 1 + 1 + 1) * natCast 24 := (five_mul_natCast 24).symm
  have hB : natCast 240 = (1 + 1 + 1 + 1 + 1) * natCast 24 + (1 + 1 + 1) * natCast 40 := by
    rw [five_mul_natCast, three_mul_natCast, ← natCast_add]
  have hC : natCast 136 = (1 + 1 + 1) * natCast 40 + natCast 16 := by
    rw [three_mul_natCast, ← natCast_add]
  rw [hA, hB, hC]
  mach_mpoly [tanh c, natCast 24, natCast 40, natCast 16]

theorem Rtanh4_zero : Rtanh4 0 = 0 := by unfold Rtanh4; rw [tanh_zero]; mach_ring

/-- `|Rtanh4(x)| ≤ (((354560·x)·x)·x)·x` for `x ∈ [0,1]` — direct flat propagation. -/
theorem Rtanh4_bound (x : Real) (hx0 : 0 ≤ x) :
    abs (Rtanh4 x) ≤ (((natCast 354560 * x) * x) * x) * x := by
  apply abs_mvt_step Rtanh4 Rtanh5 x (((natCast 354560 * x) * x) * x) hx0
    (mul_nonneg (mul_nonneg (mul_nonneg (natCast_nonneg 354560) hx0) hx0) hx0)
    (fun c => Rtanh4_deriv c) Rtanh4_zero
  intro t ht0 htx
  exact le_trans (Rtanh5_bound t ht0)
    (mul_le_mul' (mul_nonneg (mul_nonneg (natCast_nonneg 354560) ht0) ht0)
      (mul_le_mul' (mul_nonneg (natCast_nonneg 354560) ht0)
        (mul_le_mul_of_nonneg_left htx (natCast_nonneg 354560)) ht0 htx)
      ht0 htx)

/-- Generic form of `natCast136_third_cancel` — `(1+1+1)·(n/3) = n` for any `n`, reused at every
level below where a `y³`/`y⁶`-style term's `(1+1+1)`-multiplicity fully cancels a `1/3` denominator
on differentiation. -/
theorem natCast_third_cancel (n : Nat) : (1 + 1 + 1) * (natCast n * (1 / natCast 3)) = natCast n := by
  rw [show (1 + 1 + 1 : Real) * (natCast n * (1 / natCast 3))
      = natCast n * ((1 + 1 + 1) * (1 / natCast 3)) from by mach_ring,
    ← natCast_three, mul_inv (natCast 3) (natCast_ne_zero (by decide)), mul_one_ax]

/-- `5·(1/15) = 1/3` — the fraction reduction `Rtanh2`'s own `y⁵` term (`34/15`) and `Rtanh0`'s `y⁵`
term (`2/15`) both need on differentiation (`5/15` cancels to `1/3`). -/
theorem frac5_15 : (1 + 1 + 1 + 1 + 1 : Real) * (1 / natCast 15) = 1 / natCast 3 :=
  frac_reduce (1 + 1 + 1 + 1 + 1) (natCast 3) (natCast 15)
    (natCast_ne_zero (by decide)) (natCast_ne_zero (by decide)) (five_mul_natCast 3)

/-! ## `Rtanh3` (`Rtanh2' = Rtanh3`, `Rtanh3' = Rtanh4`). `Rtanh3(y) = 8tanh² − 6tanh⁴ + (34/3)y⁴ −
8y²`. -/

noncomputable def Rtanh3 (y : Real) : Real :=
  natCast 8 * (tanh y * tanh y) - natCast 6 * (tanh y * tanh y * tanh y * tanh y)
    + y * y * y * y * (natCast 34 * (1 / natCast 3)) - natCast 8 * (y * y)

set_option maxHeartbeats 1000000 in
theorem Rtanh3_deriv (c : Real) : HasDerivAt Rtanh3 (Rtanh4 c) c := by
  have h2 := HasDerivAt_mul (fun _ => natCast 8) (fun y => tanh y * tanh y) 0 _ c
    (HasDerivAt_const (natCast 8) c) (hDtanh_2 c)
  have h4 := HasDerivAt_mul (fun _ => natCast 6) (fun y => tanh y * tanh y * tanh y * tanh y) 0 _ c
    (HasDerivAt_const (natCast 6) c) (hDtanh_4 c)
  have hy4 := HasDerivAt_mul (fun y => y * y * y * y) (fun _ => natCast 34 * (1 / natCast 3))
    ((c + c) * (c * c) + (c * c) * (c + c)) 0 c (hD_y4 c)
    (HasDerivAt_const (natCast 34 * (1 / natCast 3)) c)
  have hy2 := HasDerivAt_mul (fun _ => natCast 8) (fun y => y * y) 0 _ c
    (HasDerivAt_const (natCast 8) c) (hD_y2 c)
  have hsub1 := HasDerivAt_sub (fun y => natCast 8 * (tanh y * tanh y))
    (fun y => natCast 6 * (tanh y * tanh y * tanh y * tanh y)) _ _ c h2 h4
  have hadd1 := HasDerivAt_add _ (fun y => y * y * y * y * (natCast 34 * (1 / natCast 3))) _ _ c
    hsub1 hy4
  have hfull := HasDerivAt_sub _ (fun y => natCast 8 * (y * y)) _ _ c hadd1 hy2
  refine hasDerivAt_congr_val hfull ?_
  unfold Rtanh4
  have hEqY4 : ((c + c) * (c * c) + (c * c) * (c + c)) * (natCast 34 * (1 / natCast 3))
      = c * c * c * (natCast 136 * (1 / natCast 3)) := by
    calc ((c + c) * (c * c) + (c * c) * (c + c)) * (natCast 34 * (1 / natCast 3))
        = ((1 + 1 + 1 + 1) * (c * c * c)) * (natCast 34 * (1 / natCast 3)) := by mach_ring
      _ = ((1 + 1 + 1 + 1) * natCast 34) * ((1 / natCast 3) * (c * c * c)) := by mach_ring
      _ = natCast 136 * ((1 / natCast 3) * (c * c * c)) := by rw [four_mul_natCast]
      _ = c * c * c * (natCast 136 * (1 / natCast 3)) := by mach_ring
  rw [hEqY4]
  have hA : natCast 16 = (1 + 1) * natCast 8 := (two_mul_natCast 8).symm
  have hB : natCast 40 = (1 + 1) * natCast 8 + (1 + 1 + 1 + 1) * natCast 6 := by
    rw [two_mul_natCast, four_mul_natCast, ← natCast_add]
  have hC : natCast 24 = (1 + 1 + 1 + 1) * natCast 6 := (four_mul_natCast 6).symm
  rw [hA, hB, hC]
  mach_mpoly [tanh c, natCast 8, natCast 6]

theorem Rtanh3_zero : Rtanh3 0 = 0 := by unfold Rtanh3; rw [tanh_zero]; mach_ring

/-- `|Rtanh3(x)| ≤ ((((354560·x)·x)·x)·x)·x` for `x ∈ [0,1]` — direct flat propagation. -/
theorem Rtanh3_bound (x : Real) (hx0 : 0 ≤ x) :
    abs (Rtanh3 x) ≤ ((((natCast 354560 * x) * x) * x) * x) * x := by
  apply abs_mvt_step Rtanh3 Rtanh4 x ((((natCast 354560 * x) * x) * x) * x) hx0
    (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (natCast_nonneg 354560) hx0) hx0) hx0) hx0)
    (fun c => Rtanh3_deriv c) Rtanh3_zero
  intro t ht0 htx
  exact le_trans (Rtanh4_bound t ht0)
    (mul_le_mul' (mul_nonneg (mul_nonneg (mul_nonneg (natCast_nonneg 354560) ht0) ht0) ht0)
    (mul_le_mul' (mul_nonneg (mul_nonneg (natCast_nonneg 354560) ht0) ht0)
    (mul_le_mul' (mul_nonneg (natCast_nonneg 354560) ht0)
    (mul_le_mul_of_nonneg_left htx (natCast_nonneg 354560)) ht0 htx) ht0 htx) ht0 htx)

/-! ## `Rtanh2` (`Rtanh1' = Rtanh2`, `Rtanh2' = Rtanh3`). `Rtanh2(y) = 2tanh³ − 2tanh + (34/15)y⁵ −
(8/3)y³ + 2y`. -/

noncomputable def Rtanh2 (y : Real) : Real :=
  natCast 2 * (tanh y * tanh y * tanh y) - natCast 2 * tanh y
    + y * y * y * y * y * (natCast 34 * (1 / natCast 15))
    - y * y * y * (natCast 8 * (1 / natCast 3)) + natCast 2 * y

set_option maxHeartbeats 1000000 in
theorem Rtanh2_deriv (c : Real) : HasDerivAt Rtanh2 (Rtanh3 c) c := by
  have h3 := HasDerivAt_mul (fun _ => natCast 2) (fun y => tanh y * tanh y * tanh y) 0 _ c
    (HasDerivAt_const (natCast 2) c) (hDtanh_3 c)
  have h1 := HasDerivAt_mul (fun _ => natCast 2) tanh 0 _ c (HasDerivAt_const (natCast 2) c)
    (HasDerivAt_tanh' c)
  have hy5 := HasDerivAt_mul (fun y => y * y * y * y * y) (fun _ => natCast 34 * (1 / natCast 15))
    ((c + c) * (c * c * c) + (c * c) * (c * c + c * c + c * c)) 0 c (hD_y5 c)
    (HasDerivAt_const (natCast 34 * (1 / natCast 15)) c)
  have hy3 := HasDerivAt_mul (fun y => y * y * y) (fun _ => natCast 8 * (1 / natCast 3))
    (c * c + c * c + c * c) 0 c (hD_y3 c) (HasDerivAt_const (natCast 8 * (1 / natCast 3)) c)
  have hy1 := HasDerivAt_mul (fun _ => natCast 2) (fun y => y) 0 1 c
    (HasDerivAt_const (natCast 2) c) (HasDerivAt_id c)
  have hsub1 := HasDerivAt_sub (fun y => natCast 2 * (tanh y * tanh y * tanh y))
    (fun y => natCast 2 * tanh y) _ _ c h3 h1
  have hadd1 := HasDerivAt_add _ (fun y => y * y * y * y * y * (natCast 34 * (1 / natCast 15))) _ _ c
    hsub1 hy5
  have hsub2 := HasDerivAt_sub _ (fun y => y * y * y * (natCast 8 * (1 / natCast 3))) _ _ c hadd1 hy3
  have hfull := HasDerivAt_add _ (fun y => natCast 2 * y) _ _ c hsub2 hy1
  refine hasDerivAt_congr_val hfull ?_
  unfold Rtanh3
  have hEqY5 : ((c + c) * (c * c * c) + (c * c) * (c * c + c * c + c * c))
      * (natCast 34 * (1 / natCast 15)) = c * c * c * c * (natCast 34 * (1 / natCast 3)) := by
    calc ((c + c) * (c * c * c) + (c * c) * (c * c + c * c + c * c))
          * (natCast 34 * (1 / natCast 15))
        = ((1 + 1 + 1 + 1 + 1) * (c * c * c * c)) * (natCast 34 * (1 / natCast 15)) := by mach_ring
      _ = natCast 34 * (((1 + 1 + 1 + 1 + 1) * (1 / natCast 15)) * (c * c * c * c)) := by mach_ring
      _ = natCast 34 * ((1 / natCast 3) * (c * c * c * c)) := by rw [frac5_15]
      _ = c * c * c * c * (natCast 34 * (1 / natCast 3)) := by mach_ring
  rw [hEqY5]
  have hEqY3 : (c * c + c * c + c * c) * (natCast 8 * (1 / natCast 3)) = natCast 8 * (c * c) := by
    calc (c * c + c * c + c * c) * (natCast 8 * (1 / natCast 3))
        = ((1 + 1 + 1) * (natCast 8 * (1 / natCast 3))) * (c * c) := by mach_ring
      _ = natCast 8 * (c * c) := by rw [natCast_third_cancel]
  rw [hEqY3]
  have hA : natCast 8 = (1 + 1 + 1 + 1) * natCast 2 := (four_mul_natCast 2).symm
  have hC : natCast 6 = (1 + 1 + 1) * natCast 2 := (three_mul_natCast 2).symm
  rw [hA, hC]
  mach_mpoly [tanh c, natCast 2]

theorem Rtanh2_zero : Rtanh2 0 = 0 := by unfold Rtanh2; rw [tanh_zero]; mach_ring

/-- `|Rtanh2(x)| ≤ (((((354560·x)·x)·x)·x)·x)·x` for `x ∈ [0,1]` — direct flat propagation. -/
theorem Rtanh2_bound (x : Real) (hx0 : 0 ≤ x) :
    abs (Rtanh2 x) ≤ (((((natCast 354560 * x) * x) * x) * x) * x) * x := by
  apply abs_mvt_step Rtanh2 Rtanh3 x (((((natCast 354560 * x) * x) * x) * x) * x) hx0
    (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (natCast_nonneg 354560) hx0) hx0) hx0) hx0) hx0)
    (fun c => Rtanh2_deriv c) Rtanh2_zero
  intro t ht0 htx
  exact le_trans (Rtanh3_bound t ht0)
    (mul_le_mul' (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (natCast_nonneg 354560) ht0) ht0) ht0) ht0)
    (mul_le_mul' (mul_nonneg (mul_nonneg (mul_nonneg (natCast_nonneg 354560) ht0) ht0) ht0)
    (mul_le_mul' (mul_nonneg (mul_nonneg (natCast_nonneg 354560) ht0) ht0)
    (mul_le_mul' (mul_nonneg (natCast_nonneg 354560) ht0)
    (mul_le_mul_of_nonneg_left htx (natCast_nonneg 354560)) ht0 htx) ht0 htx) ht0 htx) ht0 htx)

/-! ## `Rtanh1` (`Rtanh0' = Rtanh1`, `Rtanh1' = Rtanh2`). `Rtanh1(y) = y² − tanh² + (17/45)y⁶ −
(2/3)y⁴`. -/

noncomputable def Rtanh1 (y : Real) : Real :=
  y * y - tanh y * tanh y + y * y * y * y * y * y * (natCast 17 * (1 / natCast 45))
    - y * y * y * y * (natCast 2 * (1 / natCast 3))

set_option maxHeartbeats 1000000 in
theorem Rtanh1_deriv (c : Real) : HasDerivAt Rtanh1 (Rtanh2 c) c := by
  have hy2 := hD_y2 c
  have h2 := hDtanh_2 c
  have hy6 := HasDerivAt_mul (fun y => y * y * y * y * y * y) (fun _ => natCast 17 * (1 / natCast 45))
    ((c * c + c * c + c * c) * (c * c * c) + (c * c * c) * (c * c + c * c + c * c)) 0 c (hD_y6 c)
    (HasDerivAt_const (natCast 17 * (1 / natCast 45)) c)
  have hy4 := HasDerivAt_mul (fun y => y * y * y * y) (fun _ => natCast 2 * (1 / natCast 3))
    ((c + c) * (c * c) + (c * c) * (c + c)) 0 c (hD_y4 c)
    (HasDerivAt_const (natCast 2 * (1 / natCast 3)) c)
  have hsub1 := HasDerivAt_sub (fun y => y * y) (fun y => tanh y * tanh y) _ _ c hy2 h2
  have hadd1 := HasDerivAt_add _ (fun y => y * y * y * y * y * y * (natCast 17 * (1 / natCast 45)))
    _ _ c hsub1 hy6
  have hfull := HasDerivAt_sub _ (fun y => y * y * y * y * (natCast 2 * (1 / natCast 3))) _ _ c
    hadd1 hy4
  refine hasDerivAt_congr_val hfull ?_
  unfold Rtanh2
  have hcoef6 : (1 + 1 + 1 + 1 + 1 + 1 : Real) * (natCast 17 * (1 / natCast 45))
      = natCast 34 * (1 / natCast 15) := by
    have e1 : (1 + 1 + 1 + 1 + 1 + 1 : Real) * natCast 17 = natCast 3 * natCast 34 := by
      rw [six_mul_natCast, ← natCast_mul]
    have e2 : natCast 3 * (1 / natCast 45) = 1 / natCast 15 :=
      frac_reduce (natCast 3) (natCast 15) (natCast 45)
        (natCast_ne_zero (by decide)) (natCast_ne_zero (by decide)) (by rw [← natCast_mul])
    calc (1 + 1 + 1 + 1 + 1 + 1 : Real) * (natCast 17 * (1 / natCast 45))
        = ((1 + 1 + 1 + 1 + 1 + 1) * natCast 17) * (1 / natCast 45) := by mach_ring
      _ = (natCast 3 * natCast 34) * (1 / natCast 45) := by rw [e1]
      _ = natCast 34 * (natCast 3 * (1 / natCast 45)) := by mach_ring
      _ = natCast 34 * (1 / natCast 15) := by rw [e2]
  have hEqY6 : ((c * c + c * c + c * c) * (c * c * c) + (c * c * c) * (c * c + c * c + c * c))
      * (natCast 17 * (1 / natCast 45)) = c * c * c * c * c * (natCast 34 * (1 / natCast 15)) := by
    calc ((c * c + c * c + c * c) * (c * c * c) + (c * c * c) * (c * c + c * c + c * c))
          * (natCast 17 * (1 / natCast 45))
        = ((1 + 1 + 1 + 1 + 1 + 1) * (c * c * c * c * c)) * (natCast 17 * (1 / natCast 45)) := by
          mach_ring
      _ = ((1 + 1 + 1 + 1 + 1 + 1) * (natCast 17 * (1 / natCast 45))) * (c * c * c * c * c) := by
          mach_ring
      _ = (natCast 34 * (1 / natCast 15)) * (c * c * c * c * c) := by rw [hcoef6]
      _ = c * c * c * c * c * (natCast 34 * (1 / natCast 15)) := by mach_ring
  rw [hEqY6]
  have hEqY4 : ((c + c) * (c * c) + (c * c) * (c + c)) * (natCast 2 * (1 / natCast 3))
      = c * c * c * (natCast 8 * (1 / natCast 3)) := by
    calc ((c + c) * (c * c) + (c * c) * (c + c)) * (natCast 2 * (1 / natCast 3))
        = ((1 + 1 + 1 + 1) * (c * c * c)) * (natCast 2 * (1 / natCast 3)) := by mach_ring
      _ = ((1 + 1 + 1 + 1) * natCast 2) * ((1 / natCast 3) * (c * c * c)) := by mach_ring
      _ = natCast 8 * ((1 / natCast 3) * (c * c * c)) := by rw [four_mul_natCast]
      _ = c * c * c * (natCast 8 * (1 / natCast 3)) := by mach_ring
  rw [hEqY4]
  rw [show natCast 2 = (1 + 1 : Real) from natCast_two]
  mach_mpoly [tanh c]

theorem Rtanh1_zero : Rtanh1 0 = 0 := by unfold Rtanh1; rw [tanh_zero]; mach_ring

/-- `|Rtanh1(x)| ≤ ((((((354560·x)·x)·x)·x)·x)·x)·x` for `x ∈ [0,1]` — direct flat propagation. -/
theorem Rtanh1_bound (x : Real) (hx0 : 0 ≤ x) :
    abs (Rtanh1 x) ≤ ((((((natCast 354560 * x) * x) * x) * x) * x) * x) * x := by
  apply abs_mvt_step Rtanh1 Rtanh2 x ((((((natCast 354560 * x) * x) * x) * x) * x) * x) hx0
    (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (natCast_nonneg 354560) hx0) hx0) hx0) hx0) hx0) hx0)
    (fun c => Rtanh1_deriv c) Rtanh1_zero
  intro t ht0 htx
  exact le_trans (Rtanh2_bound t ht0)
    (mul_le_mul' (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (natCast_nonneg 354560) ht0) ht0) ht0) ht0) ht0)
    (mul_le_mul' (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (natCast_nonneg 354560) ht0) ht0) ht0) ht0)
    (mul_le_mul' (mul_nonneg (mul_nonneg (mul_nonneg (natCast_nonneg 354560) ht0) ht0) ht0)
    (mul_le_mul' (mul_nonneg (mul_nonneg (natCast_nonneg 354560) ht0) ht0)
    (mul_le_mul' (mul_nonneg (natCast_nonneg 354560) ht0)
    (mul_le_mul_of_nonneg_left htx (natCast_nonneg 354560)) ht0 htx) ht0 htx) ht0 htx) ht0 htx) ht0 htx)

/-! ## `Rtanh0` — THE TARGET. `Rtanh0(y) = tanh(y) − (y − y³/3 + 2y⁵/15 − 17y⁷/315)`, exactly
`eml_tanh.v`'s claimed 4-term Maclaurin truncation, subtracted from the true `tanh`. -/

noncomputable def Rtanh0 (y : Real) : Real :=
  tanh y - y + y * y * y * (1 / natCast 3) - y * y * y * y * y * (natCast 2 * (1 / natCast 15))
    + y * y * y * y * y * y * y * (natCast 17 * (1 / natCast 315))

set_option maxHeartbeats 1000000 in
theorem Rtanh0_deriv (c : Real) : HasDerivAt Rtanh0 (Rtanh1 c) c := by
  have h1 := HasDerivAt_tanh' c
  have hy1 := HasDerivAt_id c
  have hy3 := HasDerivAt_mul (fun y => y * y * y) (fun _ => (1 : Real) / natCast 3)
    (c * c + c * c + c * c) 0 c (hD_y3 c) (HasDerivAt_const ((1 : Real) / natCast 3) c)
  have hy5 := HasDerivAt_mul (fun y => y * y * y * y * y) (fun _ => natCast 2 * (1 / natCast 15))
    ((c + c) * (c * c * c) + (c * c) * (c * c + c * c + c * c)) 0 c (hD_y5 c)
    (HasDerivAt_const (natCast 2 * (1 / natCast 15)) c)
  have hy7 := HasDerivAt_mul (fun y => y * y * y * y * y * y * y) (fun _ => natCast 17 * (1 / natCast 315))
    ((c * c + c * c + c * c) * (c * c * c * c) + (c * c * c) * ((c + c) * (c * c) + (c * c) * (c + c)))
    0 c (hD_y7 c) (HasDerivAt_const (natCast 17 * (1 / natCast 315)) c)
  have hsub1 := HasDerivAt_sub tanh (fun y => y) _ _ c h1 hy1
  have hadd1 := HasDerivAt_add _ (fun y => y * y * y * (1 / natCast 3)) _ _ c hsub1 hy3
  have hsub2 := HasDerivAt_sub _ (fun y => y * y * y * y * y * (natCast 2 * (1 / natCast 15))) _ _ c
    hadd1 hy5
  have hfull := HasDerivAt_add _
    (fun y => y * y * y * y * y * y * y * (natCast 17 * (1 / natCast 315))) _ _ c hsub2 hy7
  refine hasDerivAt_congr_val hfull ?_
  unfold Rtanh1
  have hEqY3 : (c * c + c * c + c * c) * ((1 : Real) / natCast 3) = c * c := by
    have hthird_cancel_bare : (1 + 1 + 1 : Real) * (1 / natCast 3) = 1 := by
      rw [← natCast_three, mul_inv (natCast 3) (natCast_ne_zero (by decide))]
    calc (c * c + c * c + c * c) * ((1 : Real) / natCast 3)
        = ((1 + 1 + 1) * (1 / natCast 3)) * (c * c) := by mach_ring
      _ = 1 * (c * c) := by rw [hthird_cancel_bare]
      _ = c * c := by mach_ring
  rw [hEqY3]
  have hEqY5 : ((c + c) * (c * c * c) + (c * c) * (c * c + c * c + c * c))
      * (natCast 2 * (1 / natCast 15)) = c * c * c * c * (natCast 2 * (1 / natCast 3)) := by
    calc ((c + c) * (c * c * c) + (c * c) * (c * c + c * c + c * c))
          * (natCast 2 * (1 / natCast 15))
        = ((1 + 1 + 1 + 1 + 1) * (c * c * c * c)) * (natCast 2 * (1 / natCast 15)) := by mach_ring
      _ = natCast 2 * (((1 + 1 + 1 + 1 + 1) * (1 / natCast 15)) * (c * c * c * c)) := by mach_ring
      _ = natCast 2 * ((1 / natCast 3) * (c * c * c * c)) := by rw [frac5_15]
      _ = c * c * c * c * (natCast 2 * (1 / natCast 3)) := by mach_ring
  rw [hEqY5]
  have hEqY7 : ((c * c + c * c + c * c) * (c * c * c * c)
      + (c * c * c) * ((c + c) * (c * c) + (c * c) * (c + c))) * (natCast 17 * (1 / natCast 315))
      = c * c * c * c * c * c * (natCast 17 * (1 / natCast 45)) := by
    calc ((c * c + c * c + c * c) * (c * c * c * c)
            + (c * c * c) * ((c + c) * (c * c) + (c * c) * (c + c)))
          * (natCast 17 * (1 / natCast 315))
        = ((1 + 1 + 1 + 1 + 1 + 1 + 1) * (c * c * c * c * c * c)) * (natCast 17 * (1 / natCast 315))
          := by mach_ring
      _ = ((1 + 1 + 1 + 1 + 1 + 1 + 1) * natCast 17) * ((1 / natCast 315) * (c * c * c * c * c * c))
          := by mach_ring
      _ = natCast 119 * ((1 / natCast 315) * (c * c * c * c * c * c)) := by rw [seven_mul_natCast]
      _ = (natCast 119 * (1 / natCast 315)) * (c * c * c * c * c * c) := by mach_ring
      _ = (natCast 17 * (1 / natCast 45)) * (c * c * c * c * c * c) := by
          rw [natcast_arith_template_frac_reduce]
      _ = c * c * c * c * c * c * (natCast 17 * (1 / natCast 45)) := by mach_ring
  rw [hEqY7]
  mach_mpoly [tanh c]

theorem Rtanh0_zero : Rtanh0 0 = 0 := by unfold Rtanh0; rw [tanh_zero]; mach_ring

/-- **THE MAIN RESULT**: `|tanh(x) − (x − x³/3 + 2x⁵/15 − 17x⁷/315)| ≤ 354560·x⁸` for `x ∈ [0,1]`. -/
theorem Rtanh0_bound (x : Real) (hx0 : 0 ≤ x) :
    abs (Rtanh0 x) ≤ (((((((natCast 354560 * x) * x) * x) * x) * x) * x) * x) * x := by
  apply abs_mvt_step Rtanh0 Rtanh1 x (((((((natCast 354560 * x) * x) * x) * x) * x) * x) * x) hx0
    (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (natCast_nonneg 354560) hx0) hx0) hx0) hx0) hx0) hx0) hx0)
    (fun c => Rtanh0_deriv c) Rtanh0_zero
  intro t ht0 htx
  exact le_trans (Rtanh1_bound t ht0)
    (mul_le_mul' (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (natCast_nonneg 354560) ht0) ht0) ht0) ht0) ht0) ht0)
    (mul_le_mul' (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (natCast_nonneg 354560) ht0) ht0) ht0) ht0) ht0)
    (mul_le_mul' (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (natCast_nonneg 354560) ht0) ht0) ht0) ht0)
    (mul_le_mul' (mul_nonneg (mul_nonneg (mul_nonneg (natCast_nonneg 354560) ht0) ht0) ht0)
    (mul_le_mul' (mul_nonneg (mul_nonneg (natCast_nonneg 354560) ht0) ht0)
    (mul_le_mul' (mul_nonneg (natCast_nonneg 354560) ht0)
    (mul_le_mul_of_nonneg_left htx (natCast_nonneg 354560)) ht0 htx) ht0 htx) ht0 htx) ht0 htx) ht0 htx) ht0 htx)

end MachLib.Real
