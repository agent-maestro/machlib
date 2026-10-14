/-
  tools/machsig/extract_trust.lean — MachSig v0.4 trust extractor (2026-10-13).

  Three things the trust gate could not see before, each found by the independent review of
  2026-10-13 (docs/machsig/GATE14_REPAIR.md):

  * AXIOM STATEMENTS. The baseline pinned axiom NAMES; sixteen Certcom axioms were restated under
    the same names in one window and every footprint holding them looked unchanged. `TAX` rows give
    every axiom in the environment with a canonical serialization of its type.

  * DEFINITION CLOSURE. `StatementDigest` hashes a theorem's stored TYPE, so redefining `clamp`
    changed the meaning of thirty watched theorems with no digest change. `TCON` rows give the
    dependency graph the meaning of a statement rests on: from each constant in a statement, through
    definition bodies, stopping at axioms, opaque constants and theorems (a proof does not change
    what a statement means). Each node carries a 128-bit structural fingerprint of its type and, for
    a definition, its value. tools/machsig/sig.py turns the graph into one SHA-256 digest per theorem.

  * POPULATION. `TTHM` rows give every theorem whose module is MachLib's own or whose name is under
    `MachLib`/`Certcom`, private ones included (decided by identity, `isPrivateName`, never by
    spelling), each with the reason the theorem ledger's exclusion rule gives for not counting it
    (`-` when it counts), its `Lean.collectAxioms` set and the constants its statement mentions.
    The rule is tools/theorem_ledger/probe.lean.in's `auxReason`, copied: the gate must watch what
    the ledger counts, and sig.py checks the two agree on the count.

  FINGERPRINT. Two independent 64-bit lanes of `mixHash` over the expression structure, memoized
  per subterm, so shared subterms cost once. Binder names, binder info and `mdata` are excluded
  (cosmetic). It is a NON-CRYPTOGRAPHIC change detector, like ProofFingerprint64 but 128 bits wide
  where Lean's own `Expr.hash` keeps 32; the per-theorem digest that combines them is SHA-256.

  Run:  python3 tools/machsig/regen.py
-/
import MachLib
open Lean Elab Command Meta

namespace MachSigTrust

abbrev H := UInt64 × UInt64

def mix (a : H) (b : H) : H := (mixHash a.1 b.1, mixHash (a.2 ^^^ 0x9e3779b97f4a7c15) (b.2 + 0x632be59bd9b4e019))

def strH (s : String) : H := (hash s, hash ("#machsig#" ++ s))

def natH (n : Nat) : H := strH (toString n)

def tagH (t : String) : H := strH ("tag:" ++ t)

def levelStr (l : Level) : String := toString l

partial def fp (e : Expr) : StateM (Std.HashMap Expr H) H := do
  if let some h := (← get)[e]? then return h
  let r : H ← match e with
    | .bvar i => pure (mix (tagH "bvar") (natH i))
    | .fvar _ => pure (tagH "fvar")
    | .mvar _ => pure (tagH "mvar")
    | .sort l => pure (mix (tagH "sort") (strH (levelStr l)))
    | .const n ls => pure (mix (mix (tagH "const") (strH n.toString)) (strH (",".intercalate (ls.map levelStr))))
    | .app f a => do pure (mix (mix (tagH "app") (← fp f)) (← fp a))
    | .lam _ t b _ => do pure (mix (mix (tagH "lam") (← fp t)) (← fp b))
    | .forallE _ t b _ => do pure (mix (mix (tagH "pi") (← fp t)) (← fp b))
    | .letE _ t v b _ => do pure (mix (mix (mix (tagH "let") (← fp t)) (← fp v)) (← fp b))
    | .lit (.natVal n) => pure (mix (tagH "nat") (natH n))
    | .lit (.strVal s) => pure (mix (tagH "str") (strH s))
    | .mdata _ b => fp b
    | .proj s i b => do pure (mix (mix (mix (tagH "proj") (strH s.toString)) (natH i)) (← fp b))
  modify (·.insert e r)
  return r

/-- Universe levels with parameters written positionally (theorem ledger's `serLevel`). -/
partial def serLevel (ps : List Name) : Level → String
  | .zero => "0"
  | .succ l => "(s " ++ serLevel ps l ++ ")"
  | .max a b => "(max " ++ serLevel ps a ++ " " ++ serLevel ps b ++ ")"
  | .imax a b => "(imax " ++ serLevel ps a ++ " " ++ serLevel ps b ++ ")"
  | .param n => match ps.idxOf? n with
    | some i => "u" ++ toString i
    | none => "(free " ++ n.toString ++ ")"
  | .mvar _ => "(?)"

/-- Canonical serialization of an axiom's statement (theorem ledger's `serExpr`): constructor shape,
    constants with universe arguments, de Bruijn indices, quoted literals; binder names and mdata
    dropped. String literals are QUOTED, so no tab or newline can split a row. -/
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

def kindOf : ConstantInfo → String
  | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque" | .ctorInfo _ => "ctor" | .inductInfo _ => "inductive"
  | .recInfo _ => "rec" | .quotInfo _ => "quot"

/-- The edges of the definition closure. A definition contributes its body; an inductive its
    constructors; a constructor or recursor its inductive. Axioms, opaque constants and theorems
    STOP the walk: their type is fingerprinted, their contents are not followed. -/
def deps (ci : ConstantInfo) : Array Name :=
  let ty := ci.type.getUsedConstants
  match ci with
  | .defnInfo v => ty ++ v.value.getUsedConstants
  | .inductInfo v => ty ++ v.ctors.toArray
  | .ctorInfo v => ty.push v.induct
  | .recInfo v => ty ++ v.all.toArray
  | .quotInfo _ => ty
  | .axiomInfo _ | .opaqueInfo _ | .thmInfo _ => #[]

def lastComponent : Name → String
  | .str _ s => s
  | _ => ""

/-- tools/theorem_ledger/probe.lean.in `auxReason`, minus the axiom-only compiler-artifact rule
    (this is applied to theorems only). -/
partial def auxReason (env : Environment) (ranged : Name → Bool) (n : Name) : Option String :=
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

def isOwnModule (m : Name) : Bool := (`MachLib).isPrefixOf m || m == `CertcomLibm

end MachSigTrust

open MachSigTrust in
run_cmd Command.liftTermElabM do
  let env ← getEnv
  let mods := env.header.moduleNames
  let modOf (nm : Name) : String := match env.getModuleIdxFor? nm with
    | some i => if h : i.toNat < mods.size then mods[i.toNat].toString else "<?>"
    | none => "<current>"
  let own (nm : Name) : Bool := match env.getModuleIdxFor? nm with
    | some i => if h : i.toNat < mods.size then isOwnModule mods[i.toNat] else false
    | none => false
  IO.println "TRUST_SCHEMA\tv1\tTAX name module ser\tTTHM name module private aux axioms stmt_consts\tTCON name kind h1 h2 deps"
  -- 1. every axiom in the environment, with its statement
  let mut nAx := 0
  for (nm, ci) in env.constants.toList do
    if let .axiomInfo _ := ci then
      nAx := nAx + 1
      IO.println s!"TAX\t{nm}\t{modOf nm}\t{serExpr ci.levelParams ci.type}"
  -- 2. the theorem population, as the theorem ledger defines it (ranged = has a source range)
  let mut scope : Array (Name × ConstantInfo) := #[]
  let mut ranged : NameSet := {}
  for (nm, ci) in env.constants.toList do
    if own nm || (`MachLib).isPrefixOf nm || (`Certcom).isPrefixOf nm then
      scope := scope.push (nm, ci)
      if (← findDeclarationRangesCore? nm).isSome then ranged := ranged.insert nm
  let mut roots : Array Name := #[]
  let mut nThm := 0
  for (nm, ci) in scope do
    if let .thmInfo _ := ci then
      nThm := nThm + 1
      let reason := (auxReason env ranged.contains nm).getD "-"
      let axs ← Lean.collectAxioms nm
      let sc := ci.type.getUsedConstants
      roots := roots ++ sc
      IO.println s!"TTHM\t{nm}\t{modOf nm}\t{isPrivateName nm}\t{reason}\t{",".intercalate (axs.toList.map toString)}\t{",".intercalate (sc.toList.map toString)}"
  -- 3. the definition-closure graph reachable from every statement
  let mut seen : NameSet := {}
  let mut stack := roots
  let mut cache : Std.HashMap Expr H := {}
  let mut nCon := 0
  while !stack.isEmpty do
    let c := stack.back!
    stack := stack.pop
    if seen.contains c then continue
    seen := seen.insert c
    match env.find? c with
    | none => IO.println s!"TCON\t{c}\tmissing\t0\t0\t"
    | some ci =>
      let (ht, cache') := (fp ci.type).run cache
      cache := cache'
      let mut h := mix (tagH (kindOf ci)) ht
      if let .defnInfo v := ci then
        let (hv, cache'') := (fp v.value).run cache
        cache := cache''
        h := mix h hv
      let ds := deps ci
      for d in ds do
        if !seen.contains d then stack := stack.push d
      nCon := nCon + 1
      IO.println s!"TCON\t{c}\t{kindOf ci}\t{h.1}\t{h.2}\t{",".intercalate (ds.toList.map toString)}"
  IO.println s!"TRUST_TOTAL\taxioms={nAx}\ttheorems={nThm}\tclosure_nodes={nCon}"
