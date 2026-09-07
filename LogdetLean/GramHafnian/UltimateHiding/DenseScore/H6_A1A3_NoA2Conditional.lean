import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H6_A3_ProjectTraceTransport
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H6_TakagiWeylAdapters
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H6_BetaJacobiNormalizationA2Free

/-!
# A2-free H6 reduction from A1, the Takagi--Weyl formula, and A3

This module deliberately does not use the Forrester A2 law as proof evidence.
It proves that the exact H6 endpoint follows from the approved A1 and A3
atoms once the project supplies the source-native complex-symmetric
Takagi--Weyl coarea theorem `TakagiWeylFlatContract`.

The contract is not discharged here.  Thus the last theorem is an exact
diagnostic of the remaining gap, not yet an unconditional replacement for
the current A2+A3 endpoint.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.CurrentPRL
open LogdetLean.GramHafnian.UltimateHiding.Dense
open H6CoordinateAlgebra H6VectorChangeOfVariables

/-! ## A1 plus Takagi--Weyl supplies the normalization missing from A3 -/

/-- A1 and the flat Takagi--Weyl pushforward show that the H6 beta-Jacobi
measure has mass one.  This replaces the current proof of the same fact from
A2 and is also enough to recover AE-measurability of the A3 coordinate map. -/
theorem H6_betaJacobiProbabilityMeasure_univ_of_A1_TakagiWeyl
    {N K : ℕ} (hN : 1 ≤ N) (h2NK : 2 * N ≤ K)
    (hTakagi : TakagiWeylFlatContract N) :
    betaJacobiProbabilityMeasure N 1
        ((K - 2 * N : ℕ) : ℝ) 1 Set.univ = 1 := by
  have hH5 :=
    friedmanMello1985_unscaledCOECornerLaw_eq_determinantDensity_of_A1
      hN h2NK
  have hK : 1 ≤ K := by omega
  have hNK : N ≤ K := by omega
  have hdetMass :
      coeCornerDeterminantDensityProbabilityMeasure N K Set.univ = 1 := by
    rw [← hH5]
    rw [concreteUnscaledCOECornerLaw_eq_map_unscaledCOECornerMatrix hK hNK]
    rw [Measure.map_apply (measurable_unscaledCOECornerMatrix hNK)
      MeasurableSet.univ]
    simp
  have hradialMass :
      normalizedCOEEigenvalueRadialMeasure N K Set.univ = 1 := by
    rw [← hTakagi.normalized_coe_radial_law K]
    rw [Measure.map_apply hTakagi.measurable_spectrum MeasurableSet.univ]
    simpa using hdetMass
  rw [betaJacobiProbabilityMeasure_h6_eq_normalizedCOERadial h2NK]
  exact hradialMass

/-- The corrected A3 contract directly makes the selected squared-GSV
coordinates measurable, hence AE-measurable, without A2. -/
theorem H6_A3_project_squaredGSV_aemeasurable_A2Free
    {N K : ℕ} (hN : 1 ≤ N) (h2NK : 2 * N ≤ K) :
    AEMeasurable
      (edelmanSuttonSquaredGSVCoordinates N 1 (K - 2 * N) 1)
      (edelmanSuttonGaussianPairLaw N 1 (K - 2 * N) 1) := by
  exact H6_A3_project_squaredGSV_aemeasurable hN h2NK

/-! ## A3 transported to the literal project Gaussian source, without A2 -/

/-- Source-faithful A3 transport through the proved real-to-complex source
embedding.  Only measurable permutation-invariant tests are compared. -/
theorem H6_A3_projectRealSource_unordered_symmetric_test_A2Free
    {γ : Type} [MeasurableSpace γ]
    {N K : ℕ} (hN : 1 ≤ N) (h2NK : 2 * N ≤ K) :
    ∀ (F : (Fin N → ℝ) → γ),
      Measurable F →
      IsA2SymmetricTest F →
    Measure.map
        (fun p ↦ F
          (edelmanSuttonSquaredGSVCoordinates N 1 (K - 2 * N) 1
            (h6A3ProjectPairEmbedding h2NK p)))
        (realBetaPrimeGaussianSourceLaw N K) =
      Measure.map F
        (betaJacobiProbabilityMeasure N 1
          ((K - 2 * N : ℕ) : ℝ) 1) := by
  exact H6_A3_projectRealSource_unordered_symmetric_test hN h2NK

/-- The project Wishart trace vector has the normalized beta-prime radial
law using A3 only through the permutation-invariant power-sum statistic. -/
theorem H6_A3_projectRealSource_traceVector_betaPrime_unordered_A2Free
    {r N K : ℕ} (hN : 1 ≤ N) (h2NK : 2 * N ≤ K) :
    Measure.map (realBetaPrimeTracePowerVector r N K)
        (realBetaPrimeGaussianSourceLaw N K) =
      Measure.map (spectralPowerSumVector r N)
        (normalizedBetaPrimeEigenvalueRadialMeasure N K) := by
  exact H6_A3_projectRealSource_traceVector_betaPrime_unordered hN h2NK

/-! ## A1/Takagi COE side and the exact conditional H6 endpoint -/

/-- A1 plus the source-native Takagi--Weyl coarea theorem transports the COE
trace vector to the normalized beta-prime radial law. -/
theorem H6_A1_TakagiWeyl_projectCOE_traceVector_betaPrime_unordered
    {r N K : ℕ} (hN : 1 ≤ N) (h2NK : 2 * N ≤ K)
    (hTakagi : TakagiWeylFlatContract N) :
    Measure.map (concreteCOETracePowerVector r N K)
        (concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K) =
      Measure.map (spectralPowerSumVector r N)
        (normalizedBetaPrimeEigenvalueRadialMeasure N K) := by
  let hRadial := hTakagi.toCOETakagiWeylRadialContract K
  have hH5 :=
    friedmanMello1985_unscaledCOECornerLaw_eq_determinantDensity_of_A1
      hN h2NK
  have hforward : Measurable (betaPrimeForwardVector N) :=
    measurable_betaPrimeForwardVector N
  have hpowers : Measurable (spectralPowerSumVector r N) :=
    measurable_spectralPowerSumVector r N
  rw [concreteCOETracePowerVector_eq_unscaled_comp]
  rw [← Measure.map_map (measurable_unscaledCOETracePowerVector r N)
    (measurable_unscaleCOECorner N K)]
  change Measure.map (unscaledCOETracePowerVector r N)
      (concreteUnscaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K) = _
  rw [hH5]
  calc
    Measure.map (unscaledCOETracePowerVector r N)
        (coeCornerDeterminantDensityProbabilityMeasure N K) =
      Measure.map
        (spectralPowerSumVector r N ∘ betaPrimeForwardVector N ∘
          hRadial.spectrum)
        (coeCornerDeterminantDensityProbabilityMeasure N K) := by
          exact Measure.map_congr (hRadial.trace_factorization r)
    _ = Measure.map (spectralPowerSumVector r N ∘ betaPrimeForwardVector N)
        (Measure.map hRadial.spectrum
          (coeCornerDeterminantDensityProbabilityMeasure N K)) := by
          rw [Measure.map_map (hpowers.comp hforward)
            hRadial.measurable_spectrum]
          rfl
    _ = Measure.map (spectralPowerSumVector r N)
        (Measure.map (betaPrimeForwardVector N)
          (Measure.map hRadial.spectrum
            (coeCornerDeterminantDensityProbabilityMeasure N K))) := by
          rw [Measure.map_map hpowers hforward]
    _ = Measure.map (spectralPowerSumVector r N)
        (normalizedBetaPrimeEigenvalueRadialMeasure N K) := by
          rw [hRadial.radial_law,
            map_normalizedCOEEigenvalueRadialMeasure_eq_normalizedBetaPrime
              hN]

/-- Exact H6 conclusion from approved A1 and A3 plus one source-native
Takagi--Weyl coarea input.  Discharging `TakagiWeylFlatContract N` from Lean
foundations is precisely the remaining obligation needed to delete A2. -/
theorem coeTakagiMuirhead_traceVector_betaPrime_A1A3_noA2_conditional
    {r N K : ℕ} (hN : 1 ≤ N) (h2NK : 2 * N ≤ K)
    (hTakagi : TakagiWeylFlatContract N) :
    Measure.map (concreteCOETracePowerVector r N K)
        (concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K) =
      Measure.map (realBetaPrimeTracePowerVector r N K)
        (realBetaPrimeGaussianSourceLaw N K) := by
  exact
    (H6_A1_TakagiWeyl_projectCOE_traceVector_betaPrime_unordered
      hN h2NK hTakagi).trans
    (H6_A3_projectRealSource_traceVector_betaPrime_unordered_A2Free
      hN h2NK).symm

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
