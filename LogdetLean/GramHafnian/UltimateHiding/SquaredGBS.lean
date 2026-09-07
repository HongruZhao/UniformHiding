import LogdetLean.GramHafnian.UltimateHiding.Basic
import LogdetLean.GramHafnian.ThreePaper.PRLCommonDefinitions

/-!
# GBS consequences of squared-rate product matrix hiding

These are internal data-processing and event-composition theorems.  They do
not assume the old Shou--Miller--Galitski axiom: their only scientific input is
an explicit proof object of `UniformProductMatrixHidingSquaredAt C`.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding

noncomputable section

open CurrentPRL

theorem shiftedGramHafnianSmallBall_of_uniformProductMatrixHidingSquared
    {C : ℝ} (hhide : UniformProductMatrixHidingSquaredAt C)
    (H : UnitaryHaarProbabilityFamily)
    {M n K : ℕ} (hn : 1 <= n) (hK : 4 * n <= K) (hKM : K <= M)
    (z : ℂ) (eps : ℝ) (heps : 0 <= eps) :
    (scaledHaarGramHafnianLaw H M n K).real
        (shiftedComplexDisk z
          (eps * LogdetLean.GramHafnian.gramHafnianSigma K n)) <=
      min 1
        (LogdetLean.GramHafnian.shiftedAnticoncentrationConstant K n * eps ^ 2 +
          C * ultimateSquaredHidingRate M (2 * n)) := by
  have hNM : 2 * n <= M := by omega
  have hNK : 2 * n <= K := by omega
  have hNpos : 1 <= 2 * n := by omega
  have htvMatrix := hhide.apply H hNpos hNK hKM
  have htvHafnian := htvMatrix.map (measurable_hafnianMatrixObservable n)
  have htv : probabilityTotalVariationLE
      (scaledHaarGramHafnianLaw H M n K)
      (gaussianGramHafnianLaw n K)
      (min 1 (C * ultimateSquaredHidingRate M (2 * n))) := by
    simpa [scaledHaarGramHafnianLaw, gaussianGramHafnianLaw] using htvHafnian
  letI : IsProbabilityMeasure (scaledHaarGramHafnianLaw H M n K) :=
    scaledHaarGramHafnianLaw_isProbability H hNM hKM
  have htransfer := htv.event_le
    (measurableSet_shiftedComplexDisk z
      (eps * LogdetLean.GramHafnian.gramHafnianSigma K n))
  rw [gaussianGramHafnianLaw_shiftedDisk_eq] at htransfer
  have hgaussian :=
    LogdetLean.GramHafnian.gaussianGramHafnianShiftedAnticoncentration
      n K hn hK z eps heps
  apply le_min measureReal_le_one
  calc
    (scaledHaarGramHafnianLaw H M n K).real
        (shiftedComplexDisk z
          (eps * LogdetLean.GramHafnian.gramHafnianSigma K n)) <=
        LogdetLean.GramHafnian.gramHafnianShiftedSmallBallProbability
          K n z eps + min 1 (C * ultimateSquaredHidingRate M (2 * n)) :=
      htransfer
    _ <= LogdetLean.GramHafnian.shiftedAnticoncentrationConstant K n * eps ^ 2 +
          C * ultimateSquaredHidingRate M (2 * n) :=
      add_le_add hgaussian (min_le_right _ _)

theorem gbsSmallDenominator_of_uniformProductMatrixHidingSquared
    {C : ℝ} (hhide : UniformProductMatrixHidingSquaredAt C)
    (H : UnitaryHaarProbabilityFamily)
    {r : ℝ} (hr : 0 < r)
    {M n K : ℕ} (hn : 1 <= n) (hK : 4 * n <= K) (hKM : K <= M)
    {t : ℝ} (ht : 0 <= t) :
    (scaledHaarGramHafnianLaw H M n K).real
        (scaledAmplitudeSmallDenominatorSet r M K n t) <=
      min 1
        (LogdetLean.GramHafnian.shiftedAnticoncentrationConstant K n * t +
          C * ultimateSquaredHidingRate M (2 * n)) := by
  have hM : 0 < M := by omega
  rw [scaledAmplitudeSmallDenominatorSet_eq_shiftedComplexDisk
    hr hM K n ht]
  have h := shiftedGramHafnianSmallBall_of_uniformProductMatrixHidingSquared
    hhide H hn hK hKM 0 (Real.sqrt t) (Real.sqrt_nonneg t)
  simpa [Real.sq_sqrt ht] using h

theorem randomizedEstimatorConversion_of_uniformProductMatrixHidingSquared
    {C : ℝ} (hhide : UniformProductMatrixHidingSquaredAt C)
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (amplitude : Omega -> ℂ) (hamplitude : Measurable amplitude)
    (deltaP : Omega -> ℝ)
    (H : UnitaryHaarProbabilityFamily)
    {r : ℝ} (hr : 0 < r) {M n K : ℕ}
    (hn : 1 <= n) (hK : 4 * n <= K) (hKM : K <= M)
    {eta rho gamma : ℝ}
    (heta : 0 <= eta) (hrho : 0 < rho) (hgamma : 0 <= gamma)
    (hmarginal : Measure.map amplitude mu =
      scaledHaarGramHafnianLaw H M n K)
    (hadd : mu.real
      (additiveFailureEvent deltaP eta
        (gbsGaussianReferenceProbability r M K n)) <= gamma) :
    mu.real
        (relativeFailureEvent deltaP
          (fun omega =>
            gbsProbabilityFromScaledAmplitude r M K n (amplitude omega))
          rho) <=
      min 1
        (gamma +
          LogdetLean.GramHafnian.shiftedAnticoncentrationConstant K n *
            (eta / rho) +
          C * ultimateSquaredHidingRate M (2 * n)) := by
  have hM : 0 < M := by omega
  have ht : 0 <= eta / rho := div_nonneg heta hrho.le
  have hhaar := gbsSmallDenominator_of_uniformProductMatrixHidingSquared
    hhide H hr hn hK hKM ht
  have hhaar' :
      (scaledHaarGramHafnianLaw H M n K).real
          (scaledAmplitudeSmallDenominatorSet r M K n (eta / rho)) <=
        LogdetLean.GramHafnian.shiftedAnticoncentrationConstant K n *
            (eta / rho) +
          C * ultimateSquaredHidingRate M (2 * n) :=
    hhaar.trans (min_le_right _ _)
  exact randomizedConversion_from_finiteHaarSmallDenominator
    mu amplitude hamplitude deltaP H hr hM K n
    heta hrho hgamma hmarginal hadd hhaar'

end

end LogdetLean.GramHafnian.UltimateHiding
