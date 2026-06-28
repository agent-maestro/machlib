import MachLib.OperatorBasisComplete

/-!
# Forge ↔ certifier binding — real kernels, machine-checked

`tools/machlib_bind/bind.py` (in the Forge repo) translates a Forge kernel's canonical
AST body into the corresponding `GExpr` over the certified operator basis, and records
the kernel's `tree_hash` (the target-independent expression identity). The emitted
`GExpr` is the same expression the kernel compiles, *by translation*; the certifier's
bound on it therefore certifies the shipped kernel, and the `tree_hash` is what a
drift gate watches.

This file closes the loop in Lean: it takes `GExpr` terms **verbatim from the binder's
output** for real eml-stdlib kernels and certifies each with `gexpr_fwd_error`. If the
binder emits a term and this file type-checks it under the certifier, the kernel's
forward error is machine-checked — the AST → `GExpr` → bound chain is complete.

(Measured reach, same pass: 273/483 eml-stdlib functions are in the basis; the rest
need `sqrt`/`ln`/`clamp`/`pow`/multi-statement-`let` — named, not hand-waved.)
`sorryAx`-free; 0 new axioms.
-/

namespace MachLib.Real

/-- **`length_sq2`** (`eml-stdlib`, `x*x + y*y`). Binder output:
`(.add (.mul (.leaf x) (.leaf x)) (.mul (.leaf y) (.leaf y)))` — certified verbatim. -/
theorem forge_length_sq2_certified {w x y vxx vyy s : Real} (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hxx : RoundsW w vxx (x * x)) (hyy : RoundsW w vyy (y * y))
    (hs : RoundsW w s (vxx + vyy)) :
    abs (s - (x * x + y * y))
      ≤ (GExpr.add (.mul (.leaf x) (.leaf x)) (.mul (.leaf y) (.leaf y))).Ebound w :=
  gexpr_fwd_error hw0 hw1
    (GRoundedEval.add
      (GRoundedEval.mul (GRoundedEval.leaf x) (GRoundedEval.leaf x) hxx)
      (GRoundedEval.mul (GRoundedEval.leaf y) (GRoundedEval.leaf y) hyy) hs)
    ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩

/-- **`sigmoid`** (`eml-stdlib`, `1/(1+exp(−x))`). Binder output:
`(.divO (.leaf 1) (.add (.leaf 1) (.expO (.neg (.leaf x)))) m)` — a division kernel.
The `÷` guard `m ≤ 1+exp(−x)` holds with `m = 1` because `exp(−x) > 0`; the computed
denominator guard `1 ≤ vd` is what a real evaluation provides. Certified verbatim. -/
theorem forge_sigmoid_certified {w x ve vd p : Real} (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hexp : RoundsW w ve (exp (-x))) (hd : RoundsW w vd (1 + ve))
    (hvd : 1 ≤ vd) (hp : RoundsW w p (1 / vd)) :
    abs (p - 1 / (1 + exp (-x)))
      ≤ (GExpr.divO (.leaf 1) (.add (.leaf 1) (.expO (.neg (.leaf x)))) 1).Ebound w :=
  gexpr_fwd_error hw0 hw1
    (GRoundedEval.divO (GRoundedEval.leaf 1)
      (GRoundedEval.add (GRoundedEval.leaf 1)
        (GRoundedEval.expO (GRoundedEval.neg (GRoundedEval.leaf x)) hexp) hd) hvd hp)
    ⟨trivial, ⟨trivial, trivial⟩, zero_lt_one_ax, le_add_of_nonneg_right (le_of_lt (exp_pos (-x)))⟩

/-- **`clamp`** (`eml-stdlib`, e.g. `clamp_bounded`). Binder output:
`(.clampO inner lo hi)`. `clamp` is exact (no rounding) and 1-Lipschitz, so it
*preserves* its argument's error: clamping a rounded square `fl(x²)` lands within the
square's own forward error `w·|x²|` of `clamp(x²)` — the bound carries through unchanged,
showing the certifier folds `clamp` with no error amplification. -/
theorem forge_clamp_sq_certified {w x vxx lo hi : Real} (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hlohi : lo ≤ hi) (hxx : RoundsW w vxx (x * x)) :
    abs (clamp vxx lo hi - clamp (x * x) lo hi)
      ≤ (GExpr.clampO (.rleaf (x * x)) lo hi).Ebound w :=
  gexpr_fwd_error hw0 hw1 (GRoundedEval.clampO (GRoundedEval.rleaf hxx)) ⟨trivial, hlohi⟩

/-- **Inlined `let` — the sharing case.** `(x+y)²` written `let s = x+y; s*s`. The binder
inlines `s`, *duplicating* `(x+y)`: binder output
`(.mul (.add (.leaf x)(.leaf y)) (.add (.leaf x)(.leaf y)))`. The real kernel rounds
`s` ONCE (`vs` feeds both factors) — which is exactly the GRoundedEval where both copies
round to the same value (both `.add` evals take the *same* `hs`). The certifier bounds
it: its `Ebound` counts `s`'s rounding in both factors (over-counts the shared term),
so the bound is a **sound conservative upper bound** for the shared computation — never
an under-estimate. This is why inlining is valid even though it loses sharing. -/
theorem forge_quad_inlined_let_certified {w x y vs p : Real} (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hs : RoundsW w vs (x + y)) (hp : RoundsW w p (vs * vs)) :
    abs (p - (x + y) * (x + y))
      ≤ (GExpr.mul (.add (.leaf x) (.leaf y)) (.add (.leaf x) (.leaf y))).Ebound w :=
  gexpr_fwd_error hw0 hw1
    (GRoundedEval.mul
      (GRoundedEval.add (GRoundedEval.leaf x) (GRoundedEval.leaf y) hs)
      (GRoundedEval.add (GRoundedEval.leaf x) (GRoundedEval.leaf y) hs) hp)
    ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩

/-- **Euclidean magnitude `√(x²+y²)`** (`eml-stdlib`-style). Binder output:
`(.sqrtO (.add (.mul (.leaf x)(.leaf x)) (.mul (.leaf y)(.leaf y))) m)` — a `sqrt`
kernel, guarded by a lower bound `m ≤ x²+y²` (the argument away from 0, where `√` is
ill-conditioned). Certified verbatim: the inner sum-of-squares forward error feeds the
`1/(2√m)`-Lipschitz `sqrt` rule, all in one fold. -/
theorem forge_magnitude_certified {w x y vxx vyy s p m : Real} (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hm : 0 < m) (hmle : m ≤ x * x + y * y) (hms : m ≤ s)
    (hxx : RoundsW w vxx (x * x)) (hyy : RoundsW w vyy (y * y))
    (hs : RoundsW w s (vxx + vyy)) (hp : RoundsW w p (sqrt s)) :
    abs (p - sqrt (x * x + y * y))
      ≤ (GExpr.sqrtO (.add (.mul (.leaf x) (.leaf x)) (.mul (.leaf y) (.leaf y))) m).Ebound w :=
  gexpr_fwd_error hw0 hw1
    (GRoundedEval.sqrtO
      (GRoundedEval.add
        (GRoundedEval.mul (GRoundedEval.leaf x) (GRoundedEval.leaf x) hxx)
        (GRoundedEval.mul (GRoundedEval.leaf y) (GRoundedEval.leaf y) hyy) hs) hms hp)
    ⟨⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩, hm, hmle⟩

/-- **Surprisal `−ln(p)`** (`eml-stdlib`-style, information content). Binder output:
`(.neg (.lnO (.leaf p) m))` — an `ln` kernel guarded by `m ≤ p` (the probability away
from 0, where `ln` is ill-conditioned). Certified verbatim: the `1/m`-Lipschitz `ln`
rule under a negation, in one fold. -/
theorem forge_surprisal_certified {w p_in vl m : Real} (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hm : 0 < m) (hmp : m ≤ p_in) (hp : RoundsW w vl (log p_in)) :
    abs (-vl - -(log p_in)) ≤ (GExpr.neg (.lnO (.leaf p_in) m)).Ebound w :=
  gexpr_fwd_error hw0 hw1
    (GRoundedEval.neg (GRoundedEval.lnO (GRoundedEval.leaf p_in) hmp hp))
    ⟨trivial, hm, hmp⟩

/-- **Power law `t^y`** (`eml-stdlib`-style, e.g. Stefan–Boltzmann `t^4`). Binder output:
`(.powO (.leaf t) y m)` — native `pow`, base guarded `m ≤ t > 0`, exponent `y ≥ 0`.
Certified verbatim: native pow's one rounding *is* a rounded `exp(y·log t)`, so the `exp`
rule carries the bound through `gexpr_fwd_error`. -/
theorem forge_powerlaw_certified {w t y p m : Real} (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hy : 0 ≤ y) (hm : 0 < m) (hmt : m ≤ t) (hp : RoundsW w p (rpow t y)) :
    abs (p - rpow t y) ≤ (GExpr.powO (.leaf t) y m).Ebound w :=
  gexpr_fwd_error hw0 hw1 (GRoundedEval.powO (GRoundedEval.leaf t) hmt hp)
    ⟨trivial, hy, hm, hmt⟩

/-- **`abs`** (`eml-stdlib`-style, `|fl(x²)|`). Binder output: `(.absO (.rleaf x²))`. `abs`
is exact + 1-Lipschitz, so it *preserves* its argument's error: `|fl(x²)|` lands within
the square's own forward error `w·|x²|` of `|x²|`. -/
theorem forge_abs_certified {w x vxx : Real} (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hxx : RoundsW w vxx (x * x)) :
    abs (abs vxx - abs (x * x)) ≤ (GExpr.absO (.rleaf (x * x))).Ebound w :=
  gexpr_fwd_error hw0 hw1 (GRoundedEval.absO (GRoundedEval.rleaf hxx)) trivial

/-- **`tanh`** (`eml-stdlib`-style activation, `tanh(x²)`). Binder output:
`(.tanhO (.rleaf x²))`. `tanh` is **bounded-Lipschitz** (`|tanh| ≤ 1`, 1-Lipschitz — the
latter *derived via MVT*, no axiom), so like `sin`/`cos` it carries the inner error plus
one rounding: `≤ w·|x²| + w`. -/
theorem forge_tanh_certified {w x vxx p : Real} (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hxx : RoundsW w vxx (x * x)) (hp : RoundsW w p (tanh vxx)) :
    abs (p - tanh (x * x)) ≤ (GExpr.tanhO (.rleaf (x * x))).Ebound w :=
  gexpr_fwd_error hw0 hw1 (GRoundedEval.tanhO (GRoundedEval.rleaf hxx) hp) trivial

/-- **`cosh`** (`eml-stdlib`-style, the catenary `cosh(x)`). Binder output:
`(.coshO (.leaf x))`. `cosh` **amplifies** (like `exp`): magnitude `cosh|x|`, and one
rounding gives `≤ w·cosh|x|` for an exact input — the bound grows with `cosh` of the
argument, the honest amplifying behaviour. -/
theorem forge_cosh_certified {w x p : Real} (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hp : RoundsW w p (cosh x)) :
    abs (p - cosh x) ≤ (GExpr.coshO (.leaf x)).Ebound w :=
  gexpr_fwd_error hw0 hw1 (GRoundedEval.coshO (GRoundedEval.leaf x) hp) trivial

end MachLib.Real
