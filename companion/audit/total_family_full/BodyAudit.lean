import SparseComponent.TotalFamily.FullCorollaries
import SparseComponent.TotalFamily.FullControls
import SparseComponent.TotalFamily.ThroughSevenControls
import SparseComponent.TotalFamily.Controls
import Lean
open Lean Elab Command
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000

private def ownedModule (n : Name) : Bool :=
  (`SparseComponent).isPrefixOf n || n == `IndependentLiteral || n == `IndependentControls

private def kind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "definition"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def directDependencies (ci : ConstantInfo) : Array Name := Id.run do
  let mut ds := ci.type.getUsedConstants
  if let some v := ci.value? true then ds := ds ++ v.getUsedConstants
  if let .inductInfo v := ci then ds := ds ++ v.all.toArray ++ v.ctors.toArray
  if let .ctorInfo v := ci then ds := ds.push v.induct
  if let .recInfo v := ci then
    ds := ds ++ v.all.toArray
    for rule in v.rules do ds := ds.push rule.ctor ++ rule.rhs.getUsedConstants
  return ds

/-- Independent body traversal. It intentionally does not use the imported
precomputed axiom table or Lean.collectAxioms to discover dependencies. -/
private partial def walkProofDependencies (env : Environment) (pending : List Name)
    (seen : NameSet) (axioms : NameSet) : CommandElabM (NameSet × NameSet) := do
  match pending with
  | [] => return (seen, axioms)
  | n :: rest =>
    if seen.contains n then return ← walkProofDependencies env rest seen axioms
    let some ci := env.checked.get.find? n | throwError "Missing declaration body/type: {n}"
    let seen := seen.insert n
    let axioms := if kind ci == "axiom" then axioms.insert n else axioms
    if ci.isUnsafe then throwError "Unsafe transitive dependency: {n}"
    walkProofDependencies env ((directDependencies ci).toList ++ rest) seen axioms

run_cmd do
  let env := (← getEnv).setExporting false
  let entries := env.constants.fold (init := #[]) fun acc n ci =>
    match env.getModuleIdxFor? n with
    | none => acc
    | some idx =>
      let m := env.header.moduleNames[idx.toNat]!
      if ownedModule m then acc.push (n,m,ci) else acc
  let entries := entries.qsort fun a b => Name.quickLt a.1 b.1
  for (n,m,ci) in entries do
    if ci.isUnsafe then throwError "Unsafe owned declaration: {n}"
    if kind ci == "axiom" || kind ci == "opaque" then
      throwError "Unapproved owned declaration kind: {n}"
    let j := Json.mkObj [
      ("name",toJson n.toString), ("module",toJson m.toString),
      ("kind",toJson (kind ci)), ("has_body",toJson (ci.hasValue true)),
      ("type_hash",toJson ci.type.hash),
      ("body_hash",toJson ((ci.value? true).map Expr.hash)),
      ("direct_dependencies",toJson ((directDependencies ci).toList.map Name.toString))]
    liftIO <| IO.println ("DECL " ++ j.compress)
  let (seen, axioms) ← walkProofDependencies env (entries.toList.map fun x => x.1) {} {}
  let bad := axioms.toArray.filter fun a => !([`propext, `Classical.choice, `Quot.sound].contains a)
  if !bad.isEmpty then throwError "Unexpected body-traced axioms: {bad}"
  let j := Json.mkObj [
    ("owned_declarations",toJson entries.size),
    ("transitive_declarations",toJson seen.size),
    ("body_traced_axioms",toJson (axioms.toArray.toList.map Name.toString))]
  liftIO <| IO.println ("BODY_AUDIT " ++ j.compress)
  for m in env.header.moduleNames do
    liftIO <| IO.println ("IMPORT " ++ m.toString)
    if ownedModule m then liftIO <| IO.println ("MODULE " ++ m.toString)

/- Endpoint cached-table checks supplement the independently traversed complete body graph. -/
run_cmd do
  for n in [``SparseComponent.TotalFamily.determinant_total_family,
      ``SparseComponent.TotalFamily.determinant_total_family_equality_iff,
      ``SparseComponent.TotalFamily.determinant_total_family_budget,
      ``SparseComponent.TotalFamily.determinant_total_family_budget_equality_iff,
      ``SparseComponent.TotalFamily.literal_total_family,
      ``SparseComponent.TotalFamily.determinant_family_unused_budget_loss,
      ``SparseComponent.TotalFamily.determinant_family_strict_budget,
      ``SparseComponent.TotalFamily.determinant_family_equality_degrees] do
    let ax ← collectAxioms n
    let bad := ax.filter fun a => !([`propext, `Classical.choice, `Quot.sound].contains a)
    if !bad.isEmpty then throwError "Unexpected endpoint axioms: {n}: {bad}"
    liftIO <| IO.println ("ENDPOINT " ++ (Json.mkObj [
      ("name",toJson n.toString), ("cached_axioms",toJson (ax.toList.map Name.toString))]).compress)

#print SparseComponent.TotalFamily.literal_total_family
#print SparseComponent.TotalFamily.determinant_total_family
#print SparseComponent.TotalFamily.determinant_total_family_equality_iff
#print SparseComponent.TotalFamily.determinant_total_family_budget_equality_iff
#print SparseComponent.TotalFamily.determinant_from_certificate

#print SparseComponent.TotalFamily.determinant_family_unused_budget_loss
#print SparseComponent.TotalFamily.determinant_family_strict_budget
#print SparseComponent.TotalFamily.determinant_family_equality_degrees
