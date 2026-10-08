import AllFourProviderSmoke
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Literature.H6_A2Prime_TakagiWeylSymmetricIntegration
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H6_A3_EdelmanSuttonProp12Conditional
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H5_FriedmanMelloA1External
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.MatsumotoTheorem3ProjectBridge
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.MatsumotoA4InternalClosure
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H6_A2Prime_A1TraceTransport
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H12_ExactMomentClosureA4
import LogdetLean.GramHafnian.UltimateHiding.UniformlyHidingA1A4Only

#check (MatsumotoPaper.A4_matsumoto_theorem_3 : MatsumotoPaper.Target)
#print axioms MatsumotoPaper.completedMatsumotoTheorem3
#print axioms MatsumotoPaper.A4_matsumoto_theorem_3
#print axioms LogdetLean.GramHafnian.UltimateHiding.DenseScore.h12h14_matsumotoIdentityTraceFourMoment_of_A4
#print axioms LogdetLean.GramHafnian.UltimateHiding.DenseScore.h12h14_matsumotoIdentityTraceFourMoment_of_A4_internal
#print axioms LogdetLean.GramHafnian.UltimateHiding.DenseScore.h12h14_projectTraceFourMoment_of_A4_internal
#print axioms LogdetLean.GramHafnian.UltimateHiding.DenseScore.coeTakagiMuirhead_traceVector_betaPrime_A1A2PrimeA3
#print axioms LogdetLean.GramHafnian.UltimateHiding.DenseScore.h12MatsumotoIdentityTraceFourBoundContract_of_A4_internal
#print axioms LogdetLean.GramHafnian.UltimateHiding.DenseScore.h12DenominatorFourthTracePolynomialBounds_of_A4_internal
#print axioms LogdetLean.GramHafnian.UltimateHiding.uniformlyHidingSquaredAt_explicitConstant_A1A4Only
#print axioms LogdetLean.GramHafnian.UltimateHiding.uniformlyHiding_A1A4Only

#print axioms LogdetLean.GramHafnian.UltimateHiding.DenseScore.FriedmanMelloA1.matrixLaw_external
#print axioms LogdetLean.GramHafnian.UltimateHiding.DenseScore.A2Prime_complexSymmetricTakagiWeyl_symmetricIntegration
#print axioms LogdetLean.GramHafnian.UltimateHiding.DenseScore.A3_edelmanSutton_proposition_1_2

open LogdetLean.GramHafnian.LocalAnticoncentration
open LogdetLean.GramHafnian.UltimateHiding

namespace AllFourIntegration

/-- Expanded exact original numeral-only public theorem type. -/
theorem original_public_constant_expanded :
    0 ≤ (615172 : ℝ) ∧
      ∀ (H : UnitaryHaarProbabilityFamily) (M N K : ℕ),
        1 ≤ N → N ≤ K → K ≤ M →
        probabilityTotalVariationLE
          (scaledHaarTransposeGramLaw H M N K)
          (gaussianTransposeGramLaw N K)
          (min 1 (615172 * ((N : ℝ) ^ 2 / (M : ℝ)))) := by
  simpa only [UniformProductMatrixHidingSquaredAt, ultimateSquaredHidingRate] using
    uniformlyHidingSquaredAt_explicitConstant_A1A4Only

/-- Expanded exact original existential public theorem type. -/
theorem original_public_exists_expanded :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (H : UnitaryHaarProbabilityFamily) (M N K : ℕ),
        1 ≤ N → N ≤ K → K ≤ M →
        probabilityTotalVariationLE
          (scaledHaarTransposeGramLaw H M N K)
          (gaussianTransposeGramLaw N K)
          (min 1 (C * ((N : ℝ) ^ 2 / (M : ℝ)))) := by
  simpa only [UniformProductMatrixHidingSquared, UniformProductMatrixHidingSquaredAt,
    ultimateSquaredHidingRate] using uniformlyHiding_A1A4Only

end AllFourIntegration

#print axioms AllFourIntegration.original_public_constant_expanded
#print axioms AllFourIntegration.original_public_exists_expanded
run_cmd Lean.logInfo "ALL_FOUR_PUBLIC_EXACT_TYPES_KERNEL_CHECKED"
