import MachLib.CertifyNested
import MachLib.AbsoluteFoldPos
import MachLib.SinNotInEML

/-!
# The `EMLTree` ↔ Certcom `EML` bridge — a real, compiled witness

Track C's compact-interval non-approximation theorem (`CompactIntervalNonApproximation.lean`) and
its Certcom combination (`CertcomCompactIntervalHandshake.lean`) both take `hround` — the closeness
of a compiled artifact to a `T : EMLTree` — as an ABSTRACT hypothesis. This file asks whether that
hypothesis is actually satisfiable by Certcom's REAL, already-proven rounding-certification
pipelines, for a genuine translated `EMLTree`, rather than left as an uninstantiated assumption.

**Finding.** Certcom's own `EML` already names `exp(x) − log(y)` as a primitive
(`Trans2.eml`, `EMLToC.lean:60-67`, `mg_eml(x,y) = exp(x) − log(y)`) — almost certainly the origin
of this whole grammar's name. But `AbsoluteFoldNest.lean`'s own scoping note says "`tr2` decomposes
into `tr1` + arithmetic": none of the certified fold pipelines (`nested_fold`, `pipeline_nested_std`,
`pipeline_pos_over_arith`) accept a bare `Trans2.eml` node. The natural translation therefore is NOT
`EMLTree.eml t1 t2 ↦ Certcom.EML.tr2 .eml ⟦t1⟧ ⟦t2⟧`, but the decomposed
`EMLTree.eml t1 t2 ↦ .bin .sub (.tr1 .exp ⟦t1⟧) (.tr1 .ln ⟦t2⟧)` — which routes `exp` through
`pipeline_nested_std` (`.exp ∈ StdLip`) and `log` through `pipeline_pos_over_arith` (`.ln ∈ PosLip`,
domain-restricted exactly the way `EMLPfaffianValidOn` already tracks `eml`'s log argument).

**Scope.** This file closes the SIMPLEST nontrivial case — depth-1, `EMLTree.eml EMLTree.var
EMLTree.var` (`T.eval x = exp x − log x`) — POINTWISE, at one environment. Composing the two REAL
pipeline theorems through `absenc_sub` gives a genuine `AbsEnc` bound for the compiled evaluation of
a real translated `EMLTree`, with zero new axioms. What remains for a literal `hround` instantiation
in the compact-interval theorems (uniform over an interval, and — the deeper gap — extended from
Float-indexed points to a `Real → Real` domain) is recorded at the end, not claimed here.
-/

namespace Certcom

open MachLib MachLib.Real

/-- Certcom's compilation of `EMLTree.eml EMLTree.var EMLTree.var`: the natural leaf-for-leaf,
`tr2`-decomposed translation (see the module docstring). -/
def emlVarVar : EML := .bin .sub (.tr1 .exp (.var "x")) (.tr1 .ln (.var "x"))

/-- What `emlVarVar` compiles: `(eml var var).eval x = exp x − log x`, by direct unfolding of
`EMLTree.eval`'s `eml`/`var` cases. -/
theorem emlVarVar_eval (x : MachLib.Real) :
    (EMLTree.eml EMLTree.var EMLTree.var).eval x = exp x - log x := rfl

/-- **The real connection.** Certcom's ACTUAL rounding-certification pipelines —
`pipeline_nested_std` for the `exp` node, `pipeline_pos_over_arith` for the `log` node — composed
through `absenc_sub`, certify the compiled evaluation of `emlVarVar` (a genuine translated
`EMLTree.eml var var`) against its exact real value `exp X − log X`, at a given environment. `lo`
is the positivity floor `EMLPfaffianValidOn` already demands of `eml`'s log argument — here that
argument literally IS the shared variable, so `lo` bounds it directly. `sorryAx`-free. -/
theorem eml_var_var_pipeline {toR : Float → MachLib.Real} (br : FPBridge toR)
    (i1 : Trans1 → Float → Float) (i2 : Trans2 → Float → Float → Float)
    (r1 : String → Float → Float) (r2 : String → Float → Float → Float)
    (hrt1 : ∀ (t : Trans1) (v : Float), r1 t.cName v = i1 t v)
    (hrt2 : ∀ (t : Trans2) (u v : Float), r2 t.cName u v = i2 t u v) (env : Env)
    (hround_std : ∀ (t : Trans1) (a : Float), StdLip t →
        abs (toR (i1 t a) - realOfStd t (toR a)) ≤ u * abs (realOfStd t (toR a)))
    (hround_ln : ∀ a : Float, abs (toR (i1 .ln a) - log (toR a)) ≤ u * abs (log (toR a)))
    (lo : MachLib.Real) (hlo : 0 < lo) (hlo_x : lo ≤ toR (env "x").toF) :
    ∃ E, AbsEnc E (toR (evalC r1 r2 env (emitC emlVarVar)).toF)
                   (exp (toR (env "x").toF) - log (toR (env "x").toF)) := by
  obtain ⟨E1, M1, hE1, -⟩ := pipeline_nested_std br i1 i2 r1 r2 hrt1 hrt2 env hround_std
    (.tr1 .exp (.var "x"))
    (IsFold.tr1 .exp (.var "x") (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (IsFold.var "x"))
  obtain ⟨E2, hE2⟩ := pipeline_pos_over_arith br i1 i2 r1 r2 hrt1 hrt2 env
    .ln (Or.inl rfl) (.var "x") (IsFold.var "x") lo hlo hround_ln hlo_x hlo_x
  have hexact1 : exactRn toR realOfStd env (.tr1 .exp (.var "x")) = exp (toR (env "x").toF) := rfl
  have hexact2 : exactRn toR realOfPos env (.var "x") = toR (env "x").toF := rfl
  rw [hexact1] at hE1
  rw [hexact2] at hE2
  have hsub : RoundsW u (toR (evalC r1 r2 env (emitC emlVarVar)).toF)
      (toR (evalC r1 r2 env (emitC (.tr1 .exp (.var "x")))).toF
        - toR (evalC r1 r2 env (emitC (.tr1 .ln (.var "x")))).toF) := by
    show RoundsW u
        (toR ((evalC r1 r2 env (emitC (.tr1 .exp (.var "x")))).toF
            - (evalC r1 r2 env (emitC (.tr1 .ln (.var "x")))).toF))
        (toR (evalC r1 r2 env (emitC (.tr1 .exp (.var "x")))).toF
          - toR (evalC r1 r2 env (emitC (.tr1 .ln (.var "x")))).toF)
    exact br.sub _ _
  exact ⟨_, absenc_sub hE1 hE2 hsub⟩

end Certcom
