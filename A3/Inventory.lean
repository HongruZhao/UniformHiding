import A3.FullTheoremAudit
import Lean.Util.CollectAxioms

open LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

example : A3OriginalTarget := A3_edelmanSutton_proposition_1_2

open Lean in
run_cmd do
  let env ← getEnv
  let declarations := env.constants.toList.toArray.qsort (fun a b ↦ Name.quickLt a.1 b.1)
  for (name, info) in declarations do
    if !info.isTheorem then continue
    let some index := env.getModuleIdxFor? name | continue
    let moduleName := env.allImportedModuleNames[index.toNat]!
    if !(moduleName == `A3 || moduleName.toString.startsWith "A3." ||
        moduleName == `A4 || moduleName.toString.startsWith "A4.") then continue
    let axioms ← collectAxioms name
    let ax := String.intercalate "," (axioms.toList.map Name.toString)
    IO.println s!"A3_PROOF\t{moduleName}\t{name}\t{ax}"
  for name in [
      `LogdetLean.GramHafnian.UltimateHiding.DenseScore.A3_edelmanSutton_proposition_1_2,
      `LogdetLean.GramHafnian.UltimateHiding.DenseScore.A3_exact_original_target_verified] do
    let axioms ← collectAxioms name
    let ax := String.intercalate "," (axioms.toList.map Name.toString)
    IO.println s!"A3_FULL_DEFINITION\t{name}\t{ax}"
  IO.println "A3_FULL_TARGET_EXACT_KERNEL_CHECKED"
