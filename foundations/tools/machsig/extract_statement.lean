/-
  tools/machsig/extract_statement.lean — MachSig Phase 2A statement + proof extractor.

  SCOPE: MachLib.* AND Certcom.*. Phase 1's declaration census was MachLib-only, which silently
  excluded the Forge-facing grammar. The scope is declared here and reported in the output so the
  omission cannot recur unnoticed.

  POPULATION (MachSig v0.4-wide, 2026-10-13). Until then the scope was a NAME test -- `MachLib.*` or
  `Certcom.*`, not `isInternal`, not matching a substring list meant to catch generated names -- and
  the trust gate watched the theorems it kept. An independent review counted what that missed: 301
  Certcom theorems (no axiom census), 65 hand-written theorems the substrings mistook for generated
  ones (`.rec` caught `recip_*`, `.inj` caught `injective_*`, `.below`, `.eq_`, `proof_`), 39
  root-namespace theorems in MachLib.SinTaylorRemainder, and every private theorem (`_private.…` names
  are `isInternal`). Now: every constant whose MODULE is MachLib's own (or whose name is under
  `MachLib`/`Certcom`), private ones decided by `isPrivateName` and judged by their user name, minus
  tools/theorem_ledger's exclusion rule (`auxReason`, copied below, as in extract_trust.lean). Axioms
  are always kept. The gate thereby watches exactly what the theorem ledger counts; sig.py refuses to
  write a set if this file and extract_trust.lean disagree on the theorem population.

  DIGESTS. `ser` below is a structural encoding of the STORED Lean expression. It keeps constructor
  shape, constant names and de Bruijn indices; it DROPS binder names and `mdata`, both of which are
  cosmetic and would otherwise make a rename look like a change.

  It is a REPRESENTATION digest, not a semantic one. Two mathematically equivalent statements with
  different stored types get different digests, and that is correct behaviour — the digest answers
  "did the kernel-facing representation change?", never "are these equivalent?".
-/
import MachLib
open Lean Elab Command Term

private def isOwnModule (m : Name) : Bool := (`MachLib).isPrefixOf m || m == `CertcomLibm

private def lastComponent : Name → String
  | .str _ s => s
  | _ => ""

/-- tools/theorem_ledger/probe.lean.in `auxReason`, minus the axiom-only compiler-artifact rule. -/
private partial def auxReason (env : Environment) (ranged : Name → Bool) (n : Name) : Option String :=
  let user := (privateToUserName? n).getD n
  let ci? := env.find? n
  if user.isInternalDetail then some "internal-name"
  else if ci? matches some (.recInfo _) then some "recursor"
  else if isAuxRecursor env n then some "aux-recursor"
  else if isNoConfusion env n then some "no-confusion"
  else if Meta.isMatcherCore env n then some "matcher"
  else if isReservedName env n then some "reserved-name"
  else if ["inj", "injEq", "sizeOf_spec"].contains (lastComponent n)
      && (env.find? n.getPrefix matches some (.ctorInfo _)) then some "constructor-lemma"
  else if !n.getPrefix.isAnonymous && env.contains n.getPrefix
      && (auxReason env ranged n.getPrefix).isSome then some "child-of-auxiliary"
  else if !ranged n then some "no-source-range"
  else none

private def kindOf : ConstantInfo → String
  | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque" | .ctorInfo _ => "ctor" | .inductInfo _ => "inductive"
  | .recInfo _ => "rec" | .quotInfo _ => "quot"


/-- Structural serialization. Binder names and mdata are deliberately dropped. -/
private partial def ser : Expr → String
  | .bvar i => "b" ++ toString i
  | .fvar _ => "f"
  | .mvar _ => "m"
  | .sort _ => "s"
  | .const n _ => "c" ++ n.toString
  | .app f a => "(" ++ ser f ++ " " ++ ser a ++ ")"
  | .lam _ t b _ => "L<" ++ ser t ++ ">" ++ ser b
  | .forallE _ t b _ => "P<" ++ ser t ++ ">" ++ ser b
  | .letE _ t v b _ => "E<" ++ ser t ++ "|" ++ ser v ++ ">" ++ ser b
  | .lit (.natVal k) => "n" ++ toString k
  | .lit (.strVal s) => "t" ++ s
  | .mdata _ b => ser b
  | .proj s i b => "j" ++ s.toString ++ toString i ++ ser b

/-- Statement shape counters: node count, depth, and logical-head occurrences. -/
private structure SF where
  nodes : Nat := 0
  depth : Nat := 0
  eqs : Nat := 0
  imps : Nat := 0
  ands : Nat := 0
  ors : Nat := 0
  exs : Nat := 0
  deriving Inhabited

private partial def shape : Expr → SF
  | .app f a =>
    let l := shape f; let r := shape a
    let base : SF := { nodes := 1 + l.nodes + r.nodes, depth := 1 + max l.depth r.depth,
                       eqs := l.eqs + r.eqs, imps := l.imps + r.imps, ands := l.ands + r.ands,
                       ors := l.ors + r.ors, exs := l.exs + r.exs }
    match f.getAppFn with
    | .const n _ =>
      if n == ``Eq then { base with eqs := base.eqs + 1 }
      else if n == ``And then { base with ands := base.ands + 1 }
      else if n == ``Or then { base with ors := base.ors + 1 }
      else if n == ``Exists then { base with exs := base.exs + 1 }
      else base
    | _ => base
  | .lam _ t b _ =>
    let l := shape t; let r := shape b
    { nodes := 1 + l.nodes + r.nodes, depth := 1 + max l.depth r.depth, eqs := l.eqs + r.eqs,
      imps := l.imps + r.imps, ands := l.ands + r.ands, ors := l.ors + r.ors, exs := l.exs + r.exs }
  | .forallE _ t b _ =>
    let l := shape t; let r := shape b
    -- a non-dependent ∀ over a Prop is an implication in the stored representation
    let isImp := !b.hasLooseBVars
    { nodes := 1 + l.nodes + r.nodes, depth := 1 + max l.depth r.depth, eqs := l.eqs + r.eqs,
      imps := l.imps + r.imps + (if isImp then 1 else 0), ands := l.ands + r.ands,
      ors := l.ors + r.ors, exs := l.exs + r.exs }
  | .letE _ t v b _ =>
    let a := shape t; let c := shape v; let d := shape b
    { nodes := 1 + a.nodes + c.nodes + d.nodes, depth := 1 + max a.depth (max c.depth d.depth),
      eqs := a.eqs+c.eqs+d.eqs, imps := a.imps+c.imps+d.imps, ands := a.ands+c.ands+d.ands,
      ors := a.ors+c.ors+d.ors, exs := a.exs+c.exs+d.exs }
  | .mdata _ b => shape b
  | .proj _ _ b => let l := shape b; { l with nodes := l.nodes + 1, depth := l.depth + 1 }
  | _ => { nodes := 1, depth := 0 }

private partial def constsIn (e : Expr) (acc : NameSet) : NameSet :=
  match e with
  | .const n _ => acc.insert n
  | .app f a => constsIn a (constsIn f acc)
  | .lam _ t b _ => constsIn b (constsIn t acc)
  | .forallE _ t b _ => constsIn b (constsIn t acc)
  | .letE _ t v b _ => constsIn b (constsIn v (constsIn t acc))
  | .mdata _ b => constsIn b acc
  | .proj _ _ b => constsIn b acc
  | _ => acc

run_cmd Command.liftTermElabM do
  let env ← getEnv
  let mods := env.header.moduleNames
  let own (nm : Name) : Bool := match env.getModuleIdxFor? nm with
    | some i => if h : i.toNat < mods.size then isOwnModule mods[i.toNat] else false
    | none => false
  IO.println "STMT_SCOPE\townModules+MachLib.*+Certcom.*\tprivate=identity\texclusion=theorem_ledger.auxReason"
  IO.println "STMT_SCHEMA\tname\tkind\tmodule\tnodes\tdepth\teqs\timps\tands\tors\texists\tdistinct_consts\tstmt_ser_len\tstmt_ser\tproof_approx_depth\tproof_expr_fp64\thas_value"
  let mut raw := 0; let mut gen := 0; let mut kept := 0
  let mut scope : Array (Name × ConstantInfo) := #[]
  let mut ranged : NameSet := {}
  for (nm, ci) in env.constants.toList do
    if own nm || (`MachLib).isPrefixOf nm || (`Certcom).isPrefixOf nm then
      scope := scope.push (nm, ci)
      if (← findDeclarationRangesCore? nm).isSome then ranged := ranged.insert nm
  for (nm, ci) in scope do
    do
      raw := raw + 1
      let excluded := match ci with
        | .axiomInfo _ => none
        | _ => auxReason env ranged.contains nm
      if excluded.isSome then gen := gen + 1
      else
        kept := kept + 1
        let sf := shape ci.type
        let ss := ser ci.type
        -- `ConstantInfo.value?` returns NONE for theorems in this Lean version, so a naive
        -- `value?` read silently empties the entire proof layer. Destructure explicitly.
        -- Proof terms are large; serializing them to strings is quadratic in practice.
        -- Use Lean's own cached structural `Expr` hash plus `approxDepth`. This is a 64-bit
        -- NON-CRYPTOGRAPHIC fingerprint, adequate for detecting change in ONE declaration across
        -- commits; it must not be presented as a cryptographic digest.
        let pv : Option Expr := match ci with
          | .thmInfo v => some v.value
          | .defnInfo v => some v.value
          | .opaqueInfo v => some v.value
          | _ => none
        let pfp := match pv with | some v => toString (Hashable.hash v) | none => "-"
        let pdep := match pv with | some v => toString v.approxDepth | none => "-"
        let dc := (constsIn ci.type {}).size
        let mod := match env.getModuleIdxFor? nm with
          | some i => (env.header.moduleNames[i.toNat]!).toString
          | none => "<current>"
        IO.println s!"STMT\t{nm}\t{kindOf ci}\t{mod}\t{sf.nodes}\t{sf.depth}\t{sf.eqs}\t{sf.imps}\t{sf.ands}\t{sf.ors}\t{sf.exs}\t{dc}\t{ss.length}\t{ss}\t{pdep}\t{pfp}\t{pv.isSome}"
  IO.println s!"STMT_POPULATION\traw={raw}\tgenerated_excluded={gen}\tanalyzed={kept}"
