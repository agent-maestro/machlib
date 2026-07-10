import MachLib.AbsoluteFoldNest
import MachLib.AbsoluteFoldNestMag
import MachLib.TrigLipschitz
import MachLib.HyperbolicLipschitz
import MachLib.InverseTrig
import MachLib.ExpLipschitz

/-!
# `pipeline_nested_glob` — the globally-Lipschitz transcendental fold, hypotheses pre-discharged

`pipeline_nested` (in `AbsoluteFoldNest`) takes a `globLip` predicate + a `realOf1` map + the Lipschitz
hypotheses as parameters. This file fixes them to the globally-Lipschitz primitive set
`{sin, cos, tanh, atan}` — each `1`-Lipschitz (`sin_lipschitz`, …) — and discharges the `hLnn`/`hLip`
hypotheses, so an emitted per-kernel certificate only has to supply the `IsFold` proof (generated from
the AST) and the primitive rounding facts (`hround`). This is the transcendental analog of instantiating
`pipeline_arith` directly for an arithmetic kernel: the certifier's `lean_certificate` emits a call to
`pipeline_nested_glob` for a kernel whose transcendental core uses only these primitives.
-/

namespace Certcom

open MachLib.Real

/-- Real semantics of the globally-Lipschitz primitives; anything else maps to `id` (never used, since
`GlobLip` excludes it). -/
noncomputable def realOfGlob : Trans1 → MachLib.Real → MachLib.Real
  | .sin => sin
  | .cos => cos
  | .tanh => tanh
  | .atan => atan
  | _ => id

/-- The globally-`1`-Lipschitz primitive set. -/
def GlobLip (t : Trans1) : Prop := t = .sin ∨ t = .cos ∨ t = .tanh ∨ t = .atan

/-- Each primitive in `GlobLip` is `1`-Lipschitz (its `*_lipschitz` lemma). -/
theorem globLip_lipschitz (t : Trans1) (h : GlobLip t) (p q : MachLib.Real) :
    abs (realOfGlob t p - realOfGlob t q) ≤ 1 * abs (p - q) := by
  rw [one_mul_thm]
  rcases h with rfl | rfl | rfl | rfl
  · exact sin_lipschitz p q
  · exact cos_lipschitz p q
  · exact tanh_lipschitz p q
  · exact atan_lipschitz p q

/-- **The globally-Lipschitz transcendental pipeline, hypotheses pre-discharged.** For any `IsFold
GlobLip e` (arithmetic + `sin`/`cos`/`tanh`/`atan` nodes, any depth), the emitted C's value through
`toR` is within some absolute bound of `exactRn … realOfGlob … e`, given only the primitive rounding
`hround`. -/
theorem pipeline_nested_glob {toR : Float → MachLib.Real} (br : FPBridge toR)
    (i1 : Trans1 → Float → Float) (i2 : Trans2 → Float → Float → Float)
    (r1 : String → Float → Float) (r2 : String → Float → Float → Float)
    (hrt1 : ∀ (t : Trans1) (v : Float), r1 t.cName v = i1 t v)
    (hrt2 : ∀ (t : Trans2) (u v : Float), r2 t.cName u v = i2 t u v) (env : Env)
    (hround : ∀ (t : Trans1) (a : Float),
        abs (toR (i1 t a) - realOfGlob t (toR a)) ≤ u * abs (realOfGlob t (toR a)))
    (e : EML) (he : IsFold GlobLip e) :
    ∃ E, AbsEnc E (toR (evalC r1 r2 env (emitC e)).toF) (exactRn toR realOfGlob env e) :=
  pipeline_nested br realOfGlob (fun _ => 1) i1 i2 r1 r2 hrt1 hrt2 env
    (fun _ _ => le_of_lt zero_lt_one_ax) globLip_lipschitz hround e he

/-! ## `pipeline_nested_std` — the full symmetric-domain fold (adds `exp`/`sinh` to the globals)

Via `nested_fold_mag` (magnitude propagation), covering `{sin, cos, tanh, atan, exp, sinh}` — every
supported primitive whose Lipschitz constant is nonneg for all `R` (so `hLipNonneg` discharges without a
sign hypothesis). `cosh` is the sole omission: its tight constant `sinh R` is negative for `R < 0`, which
`nested_fold_mag`'s `∀ R` non-negativity hypothesis rejects (a follow-on needs an `R ≥ 0`-threaded
variant). `atan`'s magnitude uses `|atan x| ≤ |x| ≤ M`; `exp`/`sinh` their monotone bounds. -/

/-- Real semantics of the `StdLip` primitive set. -/
noncomputable def realOfStd : Trans1 → MachLib.Real → MachLib.Real
  | .sin => sin
  | .cos => cos
  | .tanh => tanh
  | .atan => atan
  | .exp => exp
  | .sinh => sinh
  | _ => id

/-- The primitives `pipeline_nested_std` covers. -/
def StdLip (t : Trans1) : Prop :=
  t = .sin ∨ t = .cos ∨ t = .tanh ∨ t = .atan ∨ t = .exp ∨ t = .sinh

/-- Per-primitive Lipschitz constant on `[-R, R]`: `1` (globals), `exp R` (`exp`), `cosh R` (`sinh`). -/
noncomputable def LipStd : Trans1 → MachLib.Real → MachLib.Real
  | .exp => fun R => exp R
  | .sinh => fun R => cosh R
  | _ => fun _ => 1

/-- Per-primitive output magnitude for `|input| ≤ M`. -/
noncomputable def MagStd : Trans1 → MachLib.Real → MachLib.Real
  | .atan => fun M => M
  | .exp => fun M => exp M
  | .sinh => fun M => sinh M
  | _ => fun _ => 1

theorem stdLip_nonneg (t : Trans1) (R : MachLib.Real) (h : StdLip t) : 0 ≤ LipStd t R := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl
  · exact le_of_lt zero_lt_one_ax
  · exact le_of_lt zero_lt_one_ax
  · exact le_of_lt zero_lt_one_ax
  · exact le_of_lt zero_lt_one_ax
  · exact le_of_lt (exp_pos R)
  · exact le_of_lt (cosh_pos R)

theorem stdLip_lipschitz (t : Trans1) (R : MachLib.Real) (h : StdLip t) (p q : MachLib.Real)
    (hp : abs p ≤ R) (hq : abs q ≤ R) :
    abs (realOfStd t p - realOfStd t q) ≤ LipStd t R * abs (p - q) := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [realOfStd, LipStd]; rw [one_mul_thm]; exact sin_lipschitz p q
  · simp only [realOfStd, LipStd]; rw [one_mul_thm]; exact cos_lipschitz p q
  · simp only [realOfStd, LipStd]; rw [one_mul_thm]; exact tanh_lipschitz p q
  · simp only [realOfStd, LipStd]; rw [one_mul_thm]; exact atan_lipschitz p q
  · simp only [realOfStd, LipStd]
    exact exp_lip_local (-R) R p q (abs_le_iff.mp hp).1 (abs_le_iff.mp hp).2
      (abs_le_iff.mp hq).1 (abs_le_iff.mp hq).2
  · simp only [realOfStd, LipStd]; exact sinh_lipschitz_bound hp hq

theorem stdMag (t : Trans1) (M : MachLib.Real) (h : StdLip t) (x : MachLib.Real) (hx : abs x ≤ M) :
    abs (realOfStd t x) ≤ MagStd t M := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [realOfStd, MagStd]; exact abs_sin_le_one x
  · simp only [realOfStd, MagStd]; exact abs_cos_le_one x
  · simp only [realOfStd, MagStd]; exact abs_tanh_le_one x
  · simp only [realOfStd, MagStd]; exact le_trans (abs_atan_le_abs x) hx
  · simp only [realOfStd, MagStd]
    rw [abs_of_nonneg (le_of_lt (exp_pos x))]; exact exp_monotone (abs_le_iff.mp hx).2
  · simp only [realOfStd, MagStd]; exact abs_sinh_le_of_abs_le hx

/-- **The full standard transcendental pipeline, hypotheses pre-discharged.** For any `IsFold StdLip e`
(arithmetic + `sin`/`cos`/`tanh`/`atan`/`exp`/`sinh` nodes, any depth), the emitted C's value is within
some absolute bound of `exactRn … realOfStd … e`, given only the primitive rounding `hround`. -/
theorem pipeline_nested_std {toR : Float → MachLib.Real} (br : FPBridge toR)
    (i1 : Trans1 → Float → Float) (i2 : Trans2 → Float → Float → Float)
    (r1 : String → Float → Float) (r2 : String → Float → Float → Float)
    (hrt1 : ∀ (t : Trans1) (v : Float), r1 t.cName v = i1 t v)
    (hrt2 : ∀ (t : Trans2) (u v : Float), r2 t.cName u v = i2 t u v) (env : Env)
    (hround : ∀ (t : Trans1) (a : Float), StdLip t →
        abs (toR (i1 t a) - realOfStd t (toR a)) ≤ u * abs (realOfStd t (toR a)))
    (e : EML) (he : IsFold StdLip e) :
    ∃ E M, AbsEnc E (toR (evalC r1 r2 env (emitC e)).toF) (exactRn toR realOfStd env e)
           ∧ abs (exactRn toR realOfStd env e) ≤ M :=
  pipeline_nested_mag br realOfStd LipStd MagStd i1 i2 r1 r2 hrt1 hrt2 env
    stdLip_nonneg stdLip_lipschitz stdMag hround e he

end Certcom
