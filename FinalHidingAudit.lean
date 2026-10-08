import HidingVerification
import AllFourReplacementAudit
import Lean.Util.CollectAxioms

open MeasureTheory
open LogdetLean.GramHafnian.LocalAnticoncentration
open LogdetLean.GramHafnian.UltimateHiding

namespace FinalHidingAudit

/-- The published normalized theorem with every dimension and coefficient expanded. -/
theorem all_input_normalized_expanded :
    ∀ (H : UnitaryHaarProbabilityFamily) (M N K : ℕ),
      1 ≤ N → N ≤ M → 1 ≤ K → K ≤ M →
      probabilityTotalVariationLE
        (normalizedHaarTransposeGramLaw H M N K)
        (normalizedGaussianTransposeGramLaw N K)
        (min 1 (615172 * ((N : ℝ) ^ 2 / (M : ℝ)))) := by
  simpa only [UniformHiding.Theorem21, ultimateSquaredHidingRate] using
    UniformHiding.theorem2_1

/-- The equivalent product theorem, including the published range K < N. -/
theorem all_input_product_expanded :
    ∀ (H : UnitaryHaarProbabilityFamily) (M N K : ℕ),
      1 ≤ N → N ≤ M → 1 ≤ K → K ≤ M →
      probabilityTotalVariationLE
        (scaledHaarTransposeGramLaw H M N K)
        (gaussianTransposeGramLaw N K)
        (min 1 (615172 * ((N : ℝ) ^ 2 / (M : ℝ)))) := by
  simpa only [ultimateSquaredHidingRate] using UniformHiding.theorem2_1_unscaled

end FinalHidingAudit

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[
      ``LogdetLean.GramHafnian.UltimateHiding.DenseScore.FriedmanMelloA1.A1_friedmanMello_matrixLaw,
      ``LogdetLean.GramHafnian.UltimateHiding.DenseScore.A2_takagi_weyl_integration,
      ``LogdetLean.GramHafnian.UltimateHiding.DenseScore.A3_edelmanSutton_proposition_1_2,
      ``MatsumotoPaper.completedMatsumotoTheorem3,
      ``LogdetLean.GramHafnian.UltimateHiding.DenseScore.FriedmanMelloA1.matrixLaw_external,
      ``LogdetLean.GramHafnian.UltimateHiding.DenseScore.A2Prime_complexSymmetricTakagiWeyl_symmetricIntegration,
      ``MatsumotoPaper.A4_matsumoto_theorem_3,
      ``GBSHiding.uniformHiding, ``GBSHiding.normalizedHiding,
      ``GBSHiding.finiteHaarSmallBall,
      ``UniformHiding.theorem2_1, ``UniformHiding.theorem2_1_unscaled,
      ``UniformHiding.corollary2_2, ``UniformHiding.corollary2_2_s62,
      ``UniformHiding.theorem3_2_route1, ``UniformHiding.theorem3_2_route1_optimized,
      ``FinalHidingAudit.all_input_normalized_expanded,
      ``FinalHidingAudit.all_input_product_expanded] do
    unless (← getEnv).contains decl do
      throwError "Required provider/public declaration missing: {decl}"
    let axioms ← Lean.collectAxioms decl
    let unexpected := axioms.filter fun ax => !allowed.contains ax
    unless unexpected.isEmpty do
      throwError "{decl}: unexpected scientific axioms {unexpected}"
    IO.println s!"FINAL_ENDPOINT\t{decl}\t{String.intercalate "," (axioms.toList.map Name.toString)}"
  IO.println "FINAL_PUBLIC_TYPES_AND_AXIOMS_CHECKED"
