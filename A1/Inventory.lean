import A1.FullTheoremAudit
import Lean.Util.CollectAxioms

open LogdetLean.GramHafnian.UltimateHiding.DenseScore.FriedmanMelloA1
noncomputable section

example : Target := A1_friedmanMello_matrixLaw

open Lean in
run_cmd do
  let env ← getEnv
  let declarations := env.constants.toList.toArray.qsort (fun a b ↦ Name.quickLt a.1 b.1)
  for (name, info) in declarations do
    if !info.isTheorem then continue
    let some index := env.getModuleIdxFor? name | continue
    let moduleName := env.allImportedModuleNames[index.toNat]!
    if !(["A1", "A2", "A3", "A4"].any fun tag ↦
        moduleName.toString == tag || moduleName.toString.startsWith (tag ++ ".")) then continue
    let axioms ← collectAxioms name
    let ax := String.intercalate "," (axioms.toList.map Name.toString)
    IO.println s!"A1_PROOF\t{moduleName}\t{name}\t{ax}"
  for name in [
      `LogdetLean.GramHafnian.UltimateHiding.DenseScore.FriedmanMelloA1.A1_friedmanMello_matrixLaw,
      `LogdetLean.GramHafnian.UltimateHiding.DenseScore.FriedmanMelloA1.A1_exact_original_target_verified] do
    let axioms ← collectAxioms name
    let ax := String.intercalate "," (axioms.toList.map Name.toString)
    IO.println s!"A1_FULL_DEFINITION\t{name}\t{ax}"
  IO.println "A1_FULL_TARGET_EXACT_KERNEL_CHECKED"
