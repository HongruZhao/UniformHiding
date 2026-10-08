import FinalHidingAudit
import Lean.Util.CollectAxioms

open Lean in
run_cmd do
  let env ← getEnv
  let roots := ["A1", "A2", "A3", "A4", "LogdetLean", "GBSHiding", "Challenge",
    "ComplexGramHafnians", "HidingStatement", "UniformHiding", "HidingVerification",
    "AllFourIntegration", "AllFourProviderSmoke", "AllFourReplacementAudit",
    "FinalHidingAudit"]
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations := env.constants.toList.toArray.qsort (fun a b ↦ Name.quickLt a.1 b.1)
  for (name, info) in declarations do
    if !info.isTheorem then continue
    let some index := env.getModuleIdxFor? name | continue
    let moduleName := env.allImportedModuleNames[index.toNat]!
    if !(roots.any fun tag ↦ moduleName.toString == tag ||
        moduleName.toString.startsWith (tag ++ ".")) then continue
    let axioms ← collectAxioms name
    let unexpected := axioms.filter fun ax => !allowed.contains ax
    unless unexpected.isEmpty do
      throwError "{name}: unexpected scientific axioms {unexpected}"
    IO.println s!"FINAL_PROOF\t{moduleName}\t{name}\t{String.intercalate "," (axioms.toList.map Name.toString)}"
  IO.println "FINAL_IMPORTED_THEOREM_INVENTORY_COMPLETE"
