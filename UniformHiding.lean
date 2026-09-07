import HidingStatement
import GBSHiding
import ComplexGramHafnians

open MeasureTheory
open LogdetLean.GramHafnian LogdetLean.GramHafnian.CurrentPRL
open LogdetLean.GramHafnian.UltimateHiding
open LogdetLean.GramHafnian.ThreePaper
open LogdetLean.GramHafnian.ThreePaper.FairAbsoluteThresholdComparison

namespace UniformHiding
noncomputable section

/-- Theorem 2.1, conditional on exactly the four cited literature axioms. -/
theorem theorem2_1 : Theorem21 := GBSHiding.normalizedHiding

/-- Route 1 disk transfer uses the public companion theorem directly. -/
theorem routeOneSmallBall
    (H : UnitaryHaarProbabilityFamily) {M n K : ℕ}
    (hn : 1 ≤ n) (hK : 4 * n ≤ K) (hKM : K ≤ M)
    (z : ℂ) (eps : ℝ) (heps : 0 ≤ eps) :
    (scaledHaarGramHafnianLaw H M n K).real
      (shiftedComplexDisk z (eps * gramHafnianSigma K n)) ≤
      min 1 (paperBkn K n * eps ^ 2 + deltaOne M n) := by
  have htv := (PRXQUniformHiding.matrixLaw.apply H
    (show 1 ≤ 2 * n by omega) (show 2 * n ≤ K by omega) hKM).map
      (measurable_hafnianMatrixObservable n)
  have htransfer := htv.event_le
    (measurableSet_shiftedComplexDisk z (eps * gramHafnianSigma K n))
  change (scaledHaarGramHafnianLaw H M n K).real _ ≤
    (gaussianGramHafnianLaw n K).real _ + deltaOne M n at htransfer
  rw [gaussianGramHafnianLaw_shiftedDisk_eq] at htransfer
  have hanti := (ComplexGramHafnians.theorem2_1 n K hn hK).shiftedSmallBall z eps heps
  let := scaledHaarGramHafnianLaw_isProbability H (show 2 * n ≤ M by omega) hKM
  apply le_min measureReal_le_one
  exact htransfer.trans (add_le_add_right (hanti.trans (min_le_right _ _)) _)

/-- Route 1 of Theorem 3.2 at the physical threshold tau. The marginal
hypothesis specifies the Haar amplitude on a joint space that may include
estimator randomness; no independence of the estimator is assumed. -/
theorem theorem3_2_route1
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (amplitude : Ω → ℂ) (hamplitude : Measurable amplitude) (deltaP : Ω → ℝ)
    (H : UnitaryHaarProbabilityFamily)
    {r : ℝ} (hr : 0 < r) {M n K : ℕ}
    (hn : 1 ≤ n) (hK : 4 * n ≤ K) (hKM : K ≤ M)
    {rho tau : ℝ} (hrho : 0 < rho) (htau : 0 ≤ tau)
    (hmarginal : Measure.map amplitude μ = scaledHaarGramHafnianLaw H M n K) :
    μ.real (relativeFailureEvent deltaP
      (fun ω ↦ gbsProbabilityFromScaledAmplitude r M K n (amplitude ω)) rho) ≤
      routeOneBound μ deltaP r M K n rho tau := by
  have hM : 0 < M := by omega
  have hp := PRLConsequences.gbsGaussianReferenceProbability_pos
    hr hM (show 0 < K by omega) n
  let eta := tau / gbsGaussianReferenceProbability r M K n
  have heta : 0 ≤ eta := div_nonneg htau hp.le
  have hscale : eta * gbsGaussianReferenceProbability r M K n = tau :=
    div_mul_cancel₀ tau hp.ne'
  have ht : 0 ≤ eta / rho := div_nonneg heta hrho.le
  have hhaar := routeOneSmallBall H hn hK hKM 0 (Real.sqrt (eta / rho)) (Real.sqrt_nonneg _)
  rw [← scaledAmplitudeSmallDenominatorSet_eq_shiftedComplexDisk hr hM K n ht] at hhaar
  rw [Real.sq_sqrt ht] at hhaar
  have hadd : μ.real (additiveFailureEvent deltaP eta
      (gbsGaussianReferenceProbability r M K n)) ≤
      μ.real (absoluteAdditiveFailureEvent deltaP tau) := by
    simp only [additiveFailureEvent, absoluteAdditiveFailureEvent, hscale, le_refl]
  have h := randomizedConversion_from_finiteHaarSmallDenominator
    μ amplitude hamplitude deltaP H hr hM K n heta hrho
    (measureReal_nonneg) hmarginal hadd (hhaar.trans (min_le_right _ _))
  have hratio : eta / rho = tau / (rho * gbsGaussianReferenceProbability r M K n) := by
    dsimp [eta]
    rw [div_div, mul_comm]
  simpa only [routeOneBound, hratio] using h

/-- Optimization in the Route 1 half of Theorem 3.2. -/
theorem theorem3_2_route1_optimized
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (amplitude : Ω → ℂ) (hamplitude : Measurable amplitude) (deltaP : Ω → ℝ)
    (H : UnitaryHaarProbabilityFamily)
    {r : ℝ} (hr : 0 < r) {M n K : ℕ}
    (hn : 1 ≤ n) (hK : 4 * n ≤ K) (hKM : K ≤ M)
    {rho : ℝ} (hrho : 0 < rho)
    (hmarginal : Measure.map amplitude μ = scaledHaarGramHafnianLaw H M n K) :
    μ.real (relativeFailureEvent deltaP
      (fun ω ↦ gbsProbabilityFromScaledAmplitude r M K n (amplitude ω)) rho) ≤
      optimizedRouteOneBound μ deltaP r M K n rho := by
  letI : Nonempty {t : ℝ // 0 ≤ t} := ⟨⟨0, le_refl _⟩⟩
  apply le_ciInf
  intro tau
  exact theorem3_2_route1 μ amplitude hamplitude deltaP H hr hn hK hKM
    hrho tau.property hmarginal

/-- Route 2 is a conditional deduction. Its Shou comparison premise
is not proved or declared as a fifth axiom in this repository. -/
abbrev routeTwoConditional := @PRLConsequences.routeTwoFairRelativeFailure_of_shou

end
end UniformHiding
