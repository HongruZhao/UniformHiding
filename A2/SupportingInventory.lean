import A2.SpectralExceptionalSets
import A2.UnitaryCongruenceMatrixVolume
import A2.MatrixInverseDerivative
import A2.TakagiRadialSqrtDerivative
import A2.TakagiOrbitCongruence
import A2.TakagiExistence
import A2.TakagiCayleyDerivative
import A2.SpectrumTakagiFiber
import A2.TakagiRadialRegularity
import A2.WeylIntegrationSeparatedDensity
import A2.WeylIntegrationLiteralBridge
import A2.OrbitMeasureTakagiAtlas
import A2.OrbitMeasureEuclideanFiber
import Lean.Util.CollectAxioms

/-! This inventory audits supporting proofs. It deliberately does not
assert that the original A2 target has been inhabited. -/

open Lean in
run_cmd do
  let env ← getEnv
  let declarations := env.constants.toList.toArray.qsort (fun a b ↦ Name.quickLt a.1 b.1)
  for (name, info) in declarations do
    if !info.isTheorem then continue
    let some index := env.getModuleIdxFor? name | continue
    let moduleName := env.allImportedModuleNames[index.toNat]!
    if !moduleName.toString.startsWith "A2." then continue
    let axioms ← collectAxioms name
    let ax := String.intercalate "," (axioms.toList.map Name.toString)
    IO.println s!"A2_SUPPORT_PROOF\t{moduleName}\t{name}\t{ax}"
  IO.println "A2_SUPPORTING_INVENTORY_ONLY"
