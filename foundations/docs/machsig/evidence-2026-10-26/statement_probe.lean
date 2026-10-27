import Lean
import MachLib.EMLAsymptoticClass
import MachLib.SinNotInEMLDepth2Sweep
import MachLib.Hyperbolic
import MachLib.FPModel
open Lean Elab Command

/-! Statement-identity probe for the 2026-10-26 transition (check C7 of
`docs/machsig/transition_2026-10-26.py`). Written by the independent review of that date, kept as evidence.

Run from `foundations/` (the branch built): `tools/capped_lean.sh --cap 16G lake env lean
docs/machsig/evidence-2026-10-26/statement_probe.lean`. It writes `statement_probe.tsv` beside itself.

Review probe (branch side). Prints, for each name: kind, defining module, level params, and two
serializations of the stored TYPE:
  * `SER`  = a byte-for-byte copy of tools/machsig/extract_trust.lean's `serExpr` (binder names,
             binder info and mdata dropped), so `sha256(SER)` is comparable with a baseline's
             `axiom_statements` pin;
  * `FULL` = the same plus binder NAMES and binder INFO (implicit/explicit/inst), which `serExpr`
             drops. -/

partial def serLevel (ps : List Name) : Level → String
  | .zero => "0"
  | .succ l => "(s " ++ serLevel ps l ++ ")"
  | .max a b => "(max " ++ serLevel ps a ++ " " ++ serLevel ps b ++ ")"
  | .imax a b => "(imax " ++ serLevel ps a ++ " " ++ serLevel ps b ++ ")"
  | .param n => match ps.idxOf? n with
    | some i => "u" ++ toString i
    | none => "(free " ++ n.toString ++ ")"
  | .mvar _ => "(?)"

partial def serExpr (ps : List Name) : Expr → String
  | .bvar i => "(B " ++ toString i ++ ")"
  | .fvar _ => "(F)"
  | .mvar _ => "(M)"
  | .sort l => "(S " ++ serLevel ps l ++ ")"
  | .const n ls => "(C " ++ n.toString ++ " [" ++ " ".intercalate (ls.map (serLevel ps)) ++ "])"
  | .app f a => "(A " ++ serExpr ps f ++ " " ++ serExpr ps a ++ ")"
  | .lam _ t b _ => "(L " ++ serExpr ps t ++ " " ++ serExpr ps b ++ ")"
  | .forallE _ t b _ => "(P " ++ serExpr ps t ++ " " ++ serExpr ps b ++ ")"
  | .letE _ t v b _ => "(Z " ++ serExpr ps t ++ " " ++ serExpr ps v ++ " " ++ serExpr ps b ++ ")"
  | .lit (.natVal n) => "(N " ++ toString n ++ ")"
  | .lit (.strVal s) => "(T " ++ s.quote ++ ")"
  | .mdata _ e => serExpr ps e
  | .proj s i e => "(J " ++ s.toString ++ " " ++ toString i ++ " " ++ serExpr ps e ++ ")"

def bi : BinderInfo → String
  | .default => "d" | .implicit => "i" | .strictImplicit => "s" | .instImplicit => "c"

partial def serFull (ps : List Name) : Expr → String
  | .lam n t b i => "(L " ++ n.toString ++ ":" ++ bi i ++ " " ++ serFull ps t ++ " " ++ serFull ps b ++ ")"
  | .forallE n t b i => "(P " ++ n.toString ++ ":" ++ bi i ++ " " ++ serFull ps t ++ " " ++ serFull ps b ++ ")"
  | .app f a => "(A " ++ serFull ps f ++ " " ++ serFull ps a ++ ")"
  | .mdata _ e => serFull ps e
  | e => serExpr ps e

def kindOf : ConstantInfo → String
  | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque" | .ctorInfo _ => "ctor" | .inductInfo _ => "inductive"
  | .recInfo _ => "rec" | .quotInfo _ => "quot"

def probeNames : List Name :=
  [`MachLib.exp_tangent_line_strict, `MachLib.Real.exp_gt_two_x, `MachLib.Real.tanh_zero,
   `MachLib.Real.sqrt_one, `MachLib.Real.u_le_one,
   -- controls: unchanged axioms whose pins the NEW baseline holds, so SER must reproduce them
   `MachLib.Real.tanh_neg, `MachLib.Real.u_lt_one, `MachLib.Real.sqrt_zero,
   `MachLib.Real.exp_gt_one_plus_self,
   -- negative-control names: must be reported ABSENT
   `MachLib.Real.Real.tanh_zero, `MachLib.Real.exp_tangent_line_strict]

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut out := ""
  for n in probeNames do
    match env.find? n with
    | none => out := out ++ s!"{n}\tABSENT\n"
    | some ci =>
      let mod := match env.getModuleIdxFor? n with
        | some i => (env.header.moduleNames[i.toNat]!).toString
        | none => "<current>"
      out := out ++ s!"{n}\t{kindOf ci}\t{mod}\t{ci.levelParams}\tSER={serExpr ci.levelParams ci.type}\tFULL={serFull ci.levelParams ci.type}\n"
  IO.FS.writeFile "docs/machsig/evidence-2026-10-26/statement_probe.tsv" out
  logInfo m!"wrote {probeNames.length} rows"
