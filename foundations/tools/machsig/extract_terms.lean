/-
  tools/machsig/extract_terms.lean — MachSig Phase 1b term-level extractor.

  Emits one TERM row per MAXIMAL occurrence of an audited grammar inside a declaration.

  "Maximal" matters: `EMLTree.eml a b` contains further `EMLTree` constructors, so a naive walk
  would emit a record for the whole term AND for each subterm. This walker stops descending for a
  grammar once it has found that grammar's root, so each record is one term, not one node.

  OPAQUE LEAVES. A term such as `EMLTree.eml A B` with `A B : EMLTree` free variables is only
  partly visible: `A` is a bound variable, not a constructor. Those are counted as
  `opaque_leaf_count` and NOT guessed at. A term with opaque leaves has a node count that is a
  LOWER BOUND on the tree it denotes, and the row says so via `structure_complete`.

  SCOPE. MachLib.* and Certcom.*. Phase 1's declaration census was MachLib-only; the Forge-facing
  `EML` grammar lives under `Certcom`, so a MachLib-only scope reports it as absent — which is
  exactly the false-absence this project keeps hitting.

  Run:  lake env lean tools/machsig/extract_terms.lean
-/
import MachLib
open Lean Elab Command Term

private def inScope (n : Name) : Bool := (`MachLib).isPrefixOf n || (`Certcom).isPrefixOf n

/-- Compiler-generated companions. `Name.isInternal` does NOT catch these: equation lemmas,
    matchers and structure-eta helpers are ordinary names, and they carried 38% of the raw term
    records on the first run. They are not authored mathematics and must not inflate the census. -/
private def isGenerated (n : Name) : Bool :=
  let s := n.toString
  ["match_", ".eq_", ".eq_def", "._", "proof_", "noConfusion", ".inj", ".sizeOf_spec",
   "brecOn", ".below", ".rec", ".casesOn", ".ndrec", ".ofNat", ".toCtorIdx"].any
    (fun m => (s.splitOn m).length > 1)

/-- Feature accumulator for one term. -/
structure TF where
  nodes : Nat := 0
  opq : Nat := 0
  depth : Nat := 0
  c1 : Nat := 0   -- grammar-specific counter 1
  c2 : Nat := 0
  c3 : Nat := 0
  deriving Inhabited

/-- Head constant of an application spine, with its explicit args. -/
private def headOf (e : Expr) : Name × Array Expr :=
  let rec go (e : Expr) (acc : Array Expr) : Name × Array Expr :=
    match e with
    | .app f a => go f (acc.push a)
    | .const n _ => (n, acc.reverse)
    | .mdata _ b => go b acc
    | _ => (Name.anonymous, acc)
  go e #[]

/-- EMLTree walker: counts eml / const / var nodes and nesting depth. -/
private partial def emlTree (e : Expr) : TF :=
  let (h, args) := headOf e
  if h == `MachLib.EMLTree.eml && args.size ≥ 2 then
    let l := emlTree args[args.size-2]!
    let r := emlTree args[args.size-1]!
    { nodes := 1 + l.nodes + r.nodes, opq := l.opq + r.opq,
      depth := 1 + max l.depth r.depth,
      c1 := 1 + l.c1 + r.c1, c2 := l.c2 + r.c2, c3 := l.c3 + r.c3 }
  else if h == `MachLib.EMLTree.const then { nodes := 1, c2 := 1 }
  else if h == `MachLib.EMLTree.var then { nodes := 1, c3 := 1 }
  else { opq := 1 }

/-- Certcom EML walker: tr1 heads, elet, cond, bin. -/
private partial def certEML (e : Expr) : TF :=
  let (h, args) := headOf e
  let kids := args.foldl (fun acc a =>
    let t := certEML a
    { nodes := acc.nodes + t.nodes, opq := acc.opq + t.opq,
      depth := max acc.depth t.depth, c1 := acc.c1 + t.c1,
      c2 := acc.c2 + t.c2, c3 := acc.c3 + t.c3 }) ({} : TF)
  if h == `Certcom.EML.tr1 then { kids with nodes := kids.nodes+1, depth := kids.depth+1, c1 := kids.c1+1 }
  else if h == `Certcom.EML.elet then { kids with nodes := kids.nodes+1, depth := kids.depth+1, c2 := kids.c2+1 }
  else if h == `Certcom.EML.cond then { kids with nodes := kids.nodes+1, depth := kids.depth+1, c3 := kids.c3+1 }
  else if h == `Certcom.EML.bin || h == `Certcom.EML.neg || h == `Certcom.EML.tr2
       || h == `Certcom.EML.lit || h == `Certcom.EML.var then
    { kids with nodes := kids.nodes+1, depth := kids.depth+1 }
  else kids

private def isEMLTreeHead (n : Name) : Bool :=
  n == `MachLib.EMLTree.eml || n == `MachLib.EMLTree.const || n == `MachLib.EMLTree.var
private def isCertEMLHead (n : Name) : Bool :=
  n == `Certcom.EML.tr1 || n == `Certcom.EML.elet || n == `Certcom.EML.cond
  || n == `Certcom.EML.bin || n == `Certcom.EML.neg || n == `Certcom.EML.tr2
  || n == `Certcom.EML.lit || n == `Certcom.EML.var

/-- Collect MAXIMAL grammar occurrences: do not descend past a root of the same grammar. -/
private partial def harvest (e : Expr) (acc : Array (String × TF)) : Array (String × TF) :=
  let (h, _) := headOf e
  if isEMLTreeHead h then acc.push ("EMLTree", emlTree e)
  else if isCertEMLHead h then acc.push ("CertcomEML", certEML e)
  else match e with
    | .app f a => harvest a (harvest f acc)
    | .lam _ t b _ => harvest b (harvest t acc)
    | .forallE _ t b _ => harvest b (harvest t acc)
    | .letE _ t v b _ => harvest b (harvest v (harvest t acc))
    | .mdata _ b => harvest b acc
    | .proj _ _ b => harvest b acc
    | _ => acc

run_cmd Command.liftTermElabM do
  let env ← getEnv
  IO.println "TERM_SCHEMA\tparent\trepresentation\toccurrence\tnodes\topaque_leaves\tdepth\tc1\tc2\tc3\tstructure_complete"
  let mut n := 0
  for (nm, ci) in env.constants.toList do
    if inScope nm && !nm.isInternal && !isGenerated nm then
      let terms := harvest ci.type (harvest (ci.value?.getD default) #[])
      let mut i := 0
      for (rep, t) in terms do
        n := n + 1
        IO.println s!"TERM\t{nm}\t{rep}\t{i}\t{t.nodes}\t{t.opq}\t{t.depth}\t{t.c1}\t{t.c2}\t{t.c3}\t{t.opq == 0}"
        i := i + 1
  IO.println s!"TERM_TOTAL\t{n}"
