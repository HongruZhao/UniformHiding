import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H6_A2Prime_WeightedSymmetricMap
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H6_A2Prime_PositiveSupport
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H6_A1A3_NoA2Conditional

/-!
# Direct A1 + A2-prime trace transport

This isolated module derives the concrete COE trace-vector law from the
approved Friedman--Mello matrix law A1 and the invariant Takagi--Weyl formula
A2'.  The Weyl formula is used only with permutation-invariant tests.  In
particular, no equality between the canonically ordered spectrum and the full
unordered radial law is asserted.
-/

open scoped BigOperators ENNReal
open Set MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.CurrentPRL
open LogdetLean.GramHafnian.UltimateHiding.Dense
open H6CoordinateAlgebra H6DensityTransform H6VectorChangeOfVariables
open H6RadialMeasureAdapters

private theorem openUnitCube_comp_perm_iff
    {N : ℕ} (sigma : Equiv.Perm (Fin N)) (lambda : Fin N → ℝ) :
    lambda ∘ sigma ∈ openUnitCube N ↔ lambda ∈ openUnitCube N := by
  constructor
  · intro h i
    simpa only [Function.comp_apply, sigma.apply_symm_apply] using h (sigma.symm i)
  · intro h i
    exact h (sigma i)

private theorem unitBoundaryRpowProduct_comp_perm
    {N : ℕ} (sigma : Equiv.Perm (Fin N)) (alpha : ℝ)
    (lambda : Fin N → ℝ) :
    unitBoundaryRpowProduct N alpha (lambda ∘ sigma) =
      unitBoundaryRpowProduct N alpha lambda := by
  unfold unitBoundaryRpowProduct
  simpa only [Function.comp_apply] using
    Equiv.prod_comp sigma (fun i ↦ Real.rpow (1 - lambda i) alpha)

private theorem coeTakagiBoundaryDensity_symmetric (N K : ℕ) :
    IsPermutationInvariantSpectralTest (coeTakagiBoundaryDensity N K) := by
  intro sigma lambda
  by_cases hcube : lambda ∈ openUnitCube N
  · have hcube' : lambda ∘ sigma ∈ openUnitCube N :=
      (openUnitCube_comp_perm_iff sigma lambda).mpr hcube
    simp only [coeTakagiBoundaryDensity, if_pos hcube, if_pos hcube']
    rw [unitBoundaryRpowProduct_comp_perm sigma]
  · have hcube' : lambda ∘ sigma ∉ openUnitCube N := by
      simpa only [openUnitCube_comp_perm_iff sigma lambda] using hcube
    simp [coeTakagiBoundaryDensity, hcube, hcube']

private theorem betaPrimePowerSum_symmetric (r N : ℕ) :
    IsPermutationInvariantSpectralTest
      (spectralPowerSumVector r N ∘ betaPrimeForwardVector N) := by
  intro sigma lambda
  funext j
  unfold spectralPowerSumVector betaPrimeForwardVector
  exact Equiv.sum_comp sigma
    (fun i ↦ (betaPrimeForward (lambda i)) ^ (j.1 + 1))

/-- Raw determinant-weighted trace statistic under A2'.  This is the direct
symmetric-test consequence of the weighted Weyl adapter. -/
theorem TakagiWeylSymmetricIntegrationLaw.raw_betaPrimePowerSum_law
    {N : ℕ} (h : TakagiWeylSymmetricIntegrationLaw N) (K r : ℕ) :
    Measure.map
        ((spectralPowerSumVector r N ∘ betaPrimeForwardVector N) ∘
          canonicalGapSquaredSpectrum N)
        (coeCornerRawDeterminantDensityMeasure N K) =
      (h.orbitConstant : ℝ≥0∞) •
        Measure.map (spectralPowerSumVector r N ∘ betaPrimeForwardVector N)
          (coeEigenvalueRadialMeasure N K) := by
  let F := spectralPowerSumVector r N ∘ betaPrimeForwardVector N
  let w := coeTakagiBoundaryDensity N K
  have hF : Measurable F :=
    (measurable_spectralPowerSumVector r N).comp
      (measurable_betaPrimeForwardVector N)
  have hFsym : IsPermutationInvariantSpectralTest F :=
    betaPrimePowerSum_symmetric r N
  have hw : Measurable w := measurable_coeTakagiBoundaryDensity N K
  have hwsym : IsPermutationInvariantSpectralTest w :=
    coeTakagiBoundaryDensity_symmetric N K
  calc
    Measure.map (F ∘ canonicalGapSquaredSpectrum N)
        (coeCornerRawDeterminantDensityMeasure N K) =
      Measure.map (F ∘ canonicalGapSquaredSpectrum N)
        ((complexSymmetricMatrixVolume N).withDensity
          (coeCornerMatrixDeterminantWeight N K)) := by
      rw [coeCornerRawDeterminantDensityMeasure_eq_withDensity]
    _ = Measure.map (F ∘ canonicalGapSquaredSpectrum N)
        ((complexSymmetricMatrixVolume N).withDensity
          (w ∘ canonicalGapSquaredSpectrum N)) := by
      congr 1
      exact withDensity_congr_ae (h.matrixWeight_ae_eq_boundary_comp K)
    _ = (h.orbitConstant : ℝ≥0∞) •
        Measure.map F
          ((takagiFlatEigenvalueRadialMeasure N).withDensity w) :=
      h.weighted_symmetric_map_law F w hF hFsym hw hwsym
    _ = (h.orbitConstant : ℝ≥0∞) •
        Measure.map F (coeEigenvalueRadialMeasure N K) := by
      rw [takagiFlatRadial_withDensity_boundary_eq_coeRadial]

/-- Canonical normalization cancels the unknown positive orbit constant in
the symmetric trace statistic. -/
theorem TakagiWeylSymmetricIntegrationLaw.normalized_betaPrimePowerSum_law
    {N : ℕ} (h : TakagiWeylSymmetricIntegrationLaw N) (K r : ℕ) :
    Measure.map
        ((spectralPowerSumVector r N ∘ betaPrimeForwardVector N) ∘
          canonicalGapSquaredSpectrum N)
        (coeCornerDeterminantDensityProbabilityMeasure N K) =
      Measure.map (spectralPowerSumVector r N ∘ betaPrimeForwardVector N)
        (normalizedCOEEigenvalueRadialMeasure N K) := by
  let F := spectralPowerSumVector r N ∘ betaPrimeForwardVector N
  have hF : Measurable F :=
    (measurable_spectralPowerSumVector r N).comp
      (measurable_betaPrimeForwardVector N)
  have hFspec : Measurable (F ∘ canonicalGapSquaredSpectrum N) :=
    hF.comp h.measurable_spectrum
  have hmatrix := map_normalizeMeasure_of_map_eq_nnreal_smul
    (coeCornerRawDeterminantDensityMeasure N K)
    (Measure.map F (coeEigenvalueRadialMeasure N K))
    (F ∘ canonicalGapSquaredSpectrum N) h.orbitConstant
    hFspec h.orbitConstant_ne_zero (h.raw_betaPrimePowerSum_law K r)
  have hradial := map_normalizeMeasure_of_map_eq_nnreal_smul
    (coeEigenvalueRadialMeasure N K)
    (Measure.map F (coeEigenvalueRadialMeasure N K))
    F (1 : NNReal) hF one_ne_zero (by simp)
  calc
    Measure.map (F ∘ canonicalGapSquaredSpectrum N)
        (coeCornerDeterminantDensityProbabilityMeasure N K) =
      Measure.map (F ∘ canonicalGapSquaredSpectrum N)
        (normalizeMeasure (coeCornerRawDeterminantDensityMeasure N K)) := by
      rfl
    _ = normalizeMeasure
        (Measure.map F (coeEigenvalueRadialMeasure N K)) := hmatrix
    _ = Measure.map F
        (normalizeMeasure (coeEigenvalueRadialMeasure N K)) := hradial.symm
    _ = Measure.map F
        (normalizedCOEEigenvalueRadialMeasure N K) := by rfl

/-- A2' gives the unscaled determinant-model trace law directly, without a
full ordered-spectrum law. -/
theorem TakagiWeylSymmetricIntegrationLaw.unscaled_traceVector_betaPrime
    {N : ℕ} (h : TakagiWeylSymmetricIntegrationLaw N)
    (K r : ℕ) (hN : 1 ≤ N) :
    Measure.map (unscaledCOETracePowerVector r N)
        (coeCornerDeterminantDensityProbabilityMeasure N K) =
      Measure.map (spectralPowerSumVector r N)
        (normalizedBetaPrimeEigenvalueRadialMeasure N K) := by
  let F := spectralPowerSumVector r N ∘ betaPrimeForwardVector N
  have hfactor :
      unscaledCOETracePowerVector r N =ᵐ[
        coeCornerDeterminantDensityProbabilityMeasure N K]
        F ∘ canonicalGapSquaredSpectrum N := by
    filter_upwards
      [coeCornerDeterminantDensityProbabilityMeasure_ae_support N K]
      with C hsupport
    exact unscaledCOETracePowerVector_eq_canonicalGapSpectrum C hsupport.2
  calc
    Measure.map (unscaledCOETracePowerVector r N)
        (coeCornerDeterminantDensityProbabilityMeasure N K) =
      Measure.map (F ∘ canonicalGapSquaredSpectrum N)
        (coeCornerDeterminantDensityProbabilityMeasure N K) :=
      Measure.map_congr hfactor
    _ = Measure.map F (normalizedCOEEigenvalueRadialMeasure N K) :=
      h.normalized_betaPrimePowerSum_law K r
    _ = Measure.map (spectralPowerSumVector r N)
        (Measure.map (betaPrimeForwardVector N)
          (normalizedCOEEigenvalueRadialMeasure N K)) := by
      rw [Measure.map_map (measurable_spectralPowerSumVector r N)
        (measurable_betaPrimeForwardVector N)]
    _ = Measure.map (spectralPowerSumVector r N)
        (normalizedBetaPrimeEigenvalueRadialMeasure N K) := by
      rw [map_normalizedCOEEigenvalueRadialMeasure_eq_normalizedBetaPrime hN]

/-- Concrete scaled COE trace law from exactly A1 and A2'. -/
theorem H6_A1_A2Prime_projectCOE_traceVector_betaPrime_unordered
    {r N K : ℕ} (hN : 1 ≤ N) (h2NK : 2 * N ≤ K) :
    Measure.map (concreteCOETracePowerVector r N K)
        (concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K) =
      Measure.map (spectralPowerSumVector r N)
        (normalizedBetaPrimeEigenvalueRadialMeasure N K) := by
  let hWeyl := A2Prime_complexSymmetricTakagiWeyl_symmetricIntegration N hN
  have hH5 :=
    friedmanMello1985_unscaledCOECornerLaw_eq_determinantDensity_of_A1
      hN h2NK
  rw [concreteCOETracePowerVector_eq_unscaled_comp]
  rw [← Measure.map_map (measurable_unscaledCOETracePowerVector r N)
    (measurable_unscaleCOECorner N K)]
  change Measure.map (unscaledCOETracePowerVector r N)
      (concreteUnscaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K) = _
  rw [hH5]
  exact hWeyl.unscaled_traceVector_betaPrime K r hN

/-- Closed H6 equality from A1, A2', and the already A2-free A3 transport. -/
theorem coeTakagiMuirhead_traceVector_betaPrime_A1A2PrimeA3
    {r N K : ℕ} (hN : 1 ≤ N) (h2NK : 2 * N ≤ K) :
    Measure.map (concreteCOETracePowerVector r N K)
        (concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K) =
      Measure.map (realBetaPrimeTracePowerVector r N K)
        (realBetaPrimeGaussianSourceLaw N K) := by
  exact
    (H6_A1_A2Prime_projectCOE_traceVector_betaPrime_unordered hN h2NK).trans
      (H6_A3_projectRealSource_traceVector_betaPrime_unordered_A2Free
        hN h2NK).symm

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
