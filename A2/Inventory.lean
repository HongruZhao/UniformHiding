import A2.FullTheoremAudit
import A2.SupportingInventory
import Lean.Util.CollectAxioms

open LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

example : Target := A2_takagi_weyl_integration

open Lean in
run_cmd do
  let env ← getEnv
  let declarations := env.constants.toList.toArray.qsort (fun a b ↦ Name.quickLt a.1 b.1)
  for (name, info) in declarations do
    if !info.isTheorem then continue
    let some index := env.getModuleIdxFor? name | continue
    let moduleName := env.allImportedModuleNames[index.toNat]!
    if !(moduleName == `A2 || moduleName.toString.startsWith "A2.") then continue
    let axioms ← collectAxioms name
    let ax := String.intercalate "," (axioms.toList.map Name.toString)
    IO.println s!"A2_PROOF\t{moduleName}\t{name}\t{ax}"
  for name in [
      `LogdetLean.GramHafnian.UltimateHiding.DenseScore.A2_takagi_weyl_integration,
      `LogdetLean.GramHafnian.UltimateHiding.DenseScore.A2_exact_original_target_verified] do
    let axioms ← collectAxioms name
    let ax := String.intercalate "," (axioms.toList.map Name.toString)
    IO.println s!"A2_FULL_DEFINITION\t{name}\t{ax}"
  IO.println "A2_FULL_TARGET_EXACT_KERNEL_CHECKED"
