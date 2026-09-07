import UniformHiding
import Lean.Util.CollectAxioms

open Lean Elab Command

/-! The build fails on any unexpected or missing proof dependency. -/
run_cmd do
  let foundations : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let literature : Array Name := #[
    ``LogdetLean.GramHafnian.UltimateHiding.DenseScore.FriedmanMelloA1.matrixLaw_external,
    ``LogdetLean.GramHafnian.UltimateHiding.DenseScore.A2Prime_complexSymmetricTakagiWeyl_symmetricIntegration,
    ``LogdetLean.GramHafnian.UltimateHiding.DenseScore.A3_edelmanSutton_proposition_1_2,
    ``MatsumotoPaper.A4_matsumoto_theorem_3]
  for decl in #[``UniformHiding.theorem2_1, ``UniformHiding.routeOneSmallBall,
    ``UniformHiding.theorem3_2_route1, ``UniformHiding.theorem3_2_route1_optimized,
    ``ComplexGramHafnians.theorem2_1, ``ComplexGramHafnians.theorem2_3,
    ``UniformHiding.routeTwoConditional] do
    let expected := if decl.getRoot == `ComplexGramHafnians ||
      decl == ``UniformHiding.routeTwoConditional then foundations else foundations ++ literature
    let actual ← Lean.collectAxioms decl
    let unexpected := actual.filter fun ax => !expected.contains ax
    let missing := expected.filter fun ax => !actual.contains ax
    unless unexpected.isEmpty && missing.isEmpty do
      throwError "{decl}: unexpected axioms {unexpected}; missing expected axioms {missing}"
    logInfo m!"PASS {decl}: exactly {actual.size} axioms: {actual}"

#print UniformHiding.theorem2_1
#print UniformHiding.theorem3_2_route1
#print UniformHiding.theorem3_2_route1_optimized
#print UniformHiding.routeTwoConditional
