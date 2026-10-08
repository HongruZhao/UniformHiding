import UniformHiding
import GBSHiding.CompletionAudit
import Lean.Util.CollectAxioms

open Lean Elab Command

run_cmd verifyHidingCompletionAxioms

/-! Version 1.4.0: every endpoint must have exactly the three standard
foundations after the A1--A4 proof providers are merged. -/
run_cmd do
  let foundations : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``UniformHiding.theorem2_1,
    ``UniformHiding.theorem2_1_unscaled,
    ``UniformHiding.corollary2_2, ``UniformHiding.corollary2_2_unscaled,
    ``UniformHiding.corollary2_2_s62_scaled, ``UniformHiding.corollary2_2_s62,
    ``UniformHiding.routeOneSmallBall,
    ``UniformHiding.theorem3_2_route1, ``UniformHiding.theorem3_2_route1_optimized,
    ``ComplexGramHafnians.theorem2_1, ``ComplexGramHafnians.theorem2_3,
    ``UniformHiding.routeTwoConditional] do
    let expected := foundations
    let actual ← Lean.collectAxioms decl
    let unexpected := actual.filter fun ax => !expected.contains ax
    let missing := expected.filter fun ax => !actual.contains ax
    unless unexpected.isEmpty && missing.isEmpty do
      throwError "{decl}: unexpected axioms {unexpected}; missing expected axioms {missing}"
    logInfo m!"PASS {decl}: exactly {actual.size} axioms: {actual}"

#print UniformHiding.Theorem21
#print UniformHiding.Corollary22
#print UniformHiding.theorem2_1
#print UniformHiding.theorem2_1_unscaled
#print UniformHiding.corollary2_2
#print UniformHiding.corollary2_2_unscaled
#print UniformHiding.corollary2_2_s62_scaled
#print UniformHiding.corollary2_2_s62
#print axioms UniformHiding.s62HaarProductLaw_eq_matrixLaw
#print axioms UniformHiding.s62GaussianProductLaw_eq_matrixLaw
#print UniformHiding.theorem3_2_route1
#print UniformHiding.theorem3_2_route1_optimized
#print UniformHiding.routeTwoConditional
