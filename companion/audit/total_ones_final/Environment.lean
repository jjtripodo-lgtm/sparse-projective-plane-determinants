import SparseComponent.TotalOnes.TotalOnes
import audit.total_ones_final.Controls
import audit.total_ones_final.ExternalInterface
import Lean
open Lean Elab Command

/-- All owned scalar dependencies, including generated and private declarations. -/
private def wantedModule (n : Name) : Bool :=
  [`SparseComponent, `audit.total_ones_final, `audit.fano_equality, `audit.total_ones_scalar].any fun p => p.isPrefixOf n
private def infoKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "definition"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

run_cmd do
  let env ← getEnv
  let entries := env.constants.fold (init := #[]) fun acc n ci =>
    match env.getModuleIdxFor? n with
    | none => acc
    | some idx =>
      let m := env.header.moduleNames[idx.toNat]!
      if wantedModule m then acc.push (n,m,ci) else acc
  let entries := entries.qsort fun a b => Name.quickLt a.1 b.1
  for (n,m,ci) in entries do
    let axs ← collectAxioms n
    let bad := axs.filter fun a => !([`propext, `Classical.choice, `Quot.sound].contains a)
    if !bad.isEmpty then throwError "Unapproved axioms for {n}: {bad}"
    if ci.isUnsafe then throwError "Unsafe project declaration: {n}"
    if infoKind ci == "axiom" || infoKind ci == "opaque" then
      throwError "Local axiom or opaque declaration: {n}"
    let j := Json.mkObj [
      ("name",toJson n.toString), ("module",toJson m.toString),
      ("kind",toJson (infoKind ci)), ("unsafe",toJson ci.isUnsafe),
      ("axioms",toJson (axs.toList.map Name.toString))]
    liftIO <| IO.println ("DECL " ++ j.compress)
  for m in env.header.moduleNames do
    if wantedModule m then liftIO <| IO.println ("MODULE " ++ m.toString)




#print SparseComponent.TotalOnes.determinant_total_ones_literal
#print SparseComponent.TotalOnes.determinant_total_three_ones
#print SparseComponent.TotalOnes.determinant_total_ones_equality_iff
#print SparseComponent.TotalOnes.determinant_total_three_ones_equality_iff
