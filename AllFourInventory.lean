import AllFourReplacementAudit
import Lean.Util.CollectAxioms

open Lean in
run_cmd do
  let env ← getEnv
  let declarations := env.constants.toList.toArray.qsort (fun a b ↦ Name.quickLt a.1 b.1)
  for (name, info) in declarations do
    if !info.isTheorem then continue
    let some index := env.getModuleIdxFor? name | continue
    let moduleName := env.allImportedModuleNames[index.toNat]!
    if !(["A1", "A2", "A3", "A4", "LogdetLean", "AllFourIntegration",
        "AllFourProviderSmoke", "AllFourReplacementAudit"].any fun tag ↦
        moduleName.toString == tag || moduleName.toString.startsWith (tag ++ ".")) then continue
    let axioms ← collectAxioms name
    let ax := String.intercalate "," (axioms.toList.map Name.toString)
    IO.println s!"ALL_FOUR_PROOF\t{moduleName}\t{name}\t{ax}"
  for name in [
      `LogdetLean.GramHafnian.UltimateHiding.DenseScore.FriedmanMelloA1.A1_friedmanMello_matrixLaw,
      `LogdetLean.GramHafnian.UltimateHiding.DenseScore.A2_takagi_weyl_integration,
      `LogdetLean.GramHafnian.UltimateHiding.DenseScore.A3_edelmanSutton_proposition_1_2,
      `MatsumotoPaper.completedMatsumotoTheorem3,
      `LogdetLean.GramHafnian.UltimateHiding.DenseScore.FriedmanMelloA1.matrixLaw_external,
      `LogdetLean.GramHafnian.UltimateHiding.DenseScore.A2Prime_complexSymmetricTakagiWeyl_symmetricIntegration,
      `MatsumotoPaper.A4_matsumoto_theorem_3,
      `LogdetLean.GramHafnian.UltimateHiding.uniformlyHidingSquaredAt_explicitConstant_A1A4Only,
      `LogdetLean.GramHafnian.UltimateHiding.uniformlyHiding_A1A4Only,
      `AllFourIntegration.original_public_constant_expanded,
      `AllFourIntegration.original_public_exists_expanded] do
    let axioms ← collectAxioms name
    let ax := String.intercalate "," (axioms.toList.map Name.toString)
    IO.println s!"ALL_FOUR_ENDPOINT\t{name}\t{ax}"
  IO.println "ALL_FOUR_INVENTORY_COMPLETE"
