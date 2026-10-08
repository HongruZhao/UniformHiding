import A4
import Lean.Util.CollectAxioms

example : MatsumotoPaper.Target := MatsumotoPaper.completedMatsumotoTheorem3

open Lean in
run_cmd do
  let env ← getEnv
  let declarations := env.constants.toList.toArray.qsort (fun a b ↦ Name.quickLt a.1 b.1)
  for (name, info) in declarations do
    if !info.isTheorem then continue
    let some index := env.getModuleIdxFor? name | continue
    let moduleName := env.allImportedModuleNames[index.toNat]!
    if !moduleName.toString.startsWith "A4." then continue
    let axioms ← collectAxioms name
    let ax := String.intercalate "," (axioms.toList.map Name.toString)
    IO.println s!"A4_PROOF\t{moduleName}\t{name}\t{ax}"
  IO.println "A4_FULL_TARGET_EXACT_KERNEL_CHECKED"
