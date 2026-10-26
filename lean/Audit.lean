import Muon
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-! Axiom audit of every `Muon` declaration, including its transitive dependencies.
Fails on any axiom other than `propext`, `Classical.choice`, `Quot.sound` and `sorryAx`
(an open obligation, reported). Writes `.lake/audit.json`: for each user-facing
declaration, its kind and whether it depends on `sorryAx`. Read by `scripts/verify.py`. -/
open Lean in
run_cmd do
  let env ← getEnv
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound, `sorryAx]
  let mut rows : Array Json := #[]
  let mut open_ : Nat := 0
  for (name, info) in env.constants.toList do
    let project := match env.getModuleIdxFor? name with
      | some idx => (`Muon).isPrefixOf env.header.moduleNames[idx.toNat]!
      | none => false
    unless project do continue
    let axioms ← collectAxioms name
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unauthorized axiom {ax} in {name}"
    if name.isInternalDetail then continue
    let sorry_ := axioms.contains ``sorryAx
    if sorry_ then open_ := open_ + 1
    let kind := match info with
      | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .inductInfo _ => "inductive"
      | .ctorInfo _ => "ctor" | .recInfo _ => "rec" | _ => "other"
    rows := rows.push <| Json.mkObj [("name", toJson name.toString), ("kind", toJson kind),
      ("sorry", toJson sorry_)]
  IO.FS.writeFile ".lake/audit.json" (Json.arr rows).compress
  logInfo m!"Audited {rows.size} Muon declarations; {open_} depend on sorryAx; no other non-standard axioms."
