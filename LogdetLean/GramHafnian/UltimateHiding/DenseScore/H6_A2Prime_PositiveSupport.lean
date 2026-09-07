import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Literature.H6_A2Prime_TakagiWeylSymmetricIntegration

/-!
# Positive-support consequence of A2-prime

The full-orthant Takagi radial measure is almost surely strictly positive in
every coordinate.  Applying the symmetric-test Weyl formula to the indicator
of failure of this property transfers that support fact to the canonical gap
spectrum.  Thus no separate full-rank or nondegeneracy axiom is needed.
-/

open scoped ENNReal
open Set MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open H6CoordinateAlgebra

theorem openPositiveOrthant_comp_perm_iff
    {N : ℕ} (sigma : Equiv.Perm (Fin N)) (lambda : Fin N → ℝ) :
    lambda ∘ sigma ∈ openPositiveOrthant N ↔
      lambda ∈ openPositiveOrthant N := by
  constructor
  · intro h i
    simpa only [Function.comp_apply, sigma.apply_symm_apply] using
      h (sigma.symm i)
  · intro h i
    exact h (sigma i)

/-- A measurable symmetric detector of failure of strict positivity. -/
def positiveOrthantFailureIndicator (N : ℕ)
    (lambda : Fin N → ℝ) : ℝ := by
  classical
  exact if lambda ∈ openPositiveOrthant N then 0 else 1

theorem measurable_positiveOrthantFailureIndicator (N : ℕ) :
    Measurable (positiveOrthantFailureIndicator N) := by
  classical
  unfold positiveOrthantFailureIndicator
  exact Measurable.ite (measurableSet_openPositiveOrthant_h6 N)
    measurable_const measurable_const

theorem positiveOrthantFailureIndicator_symmetric (N : ℕ) :
    IsPermutationInvariantSpectralTest
      (positiveOrthantFailureIndicator N) := by
  classical
  intro sigma lambda
  unfold positiveOrthantFailureIndicator
  rw [if_congr (openPositiveOrthant_comp_perm_iff sigma lambda) rfl rfl]

/-- A2' itself forces the canonical squared spectrum to lie in the strict
positive orthant almost everywhere under flat complex-symmetric volume. -/
theorem TakagiWeylSymmetricIntegrationLaw.canonicalSpectrum_ae_positive
    {N : ℕ} (h : TakagiWeylSymmetricIntegrationLaw N) :
    ∀ᵐ C ∂complexSymmetricMatrixVolume N,
      canonicalGapSquaredSpectrum N C ∈ openPositiveOrthant N := by
  classical
  let F := positiveOrthantFailureIndicator N
  have hF : Measurable F := measurable_positiveOrthantFailureIndicator N
  have hFsym : IsPermutationInvariantSpectralTest F :=
    positiveOrthantFailureIndicator_symmetric N
  have hradialZero :
      ∀ᵐ lambda ∂takagiFlatEigenvalueRadialMeasure N, F lambda = 0 := by
    filter_upwards [takagiFlatEigenvalueRadialMeasure_ae_positive N]
      with lambda hlambda
    simp [F, positiveOrthantFailureIndicator, hlambda]
  have hmapRadialZero :
      ∀ᵐ y ∂Measure.map F (takagiFlatEigenvalueRadialMeasure N), y = 0 :=
    (ae_map_iff hF.aemeasurable
      (show MeasurableSet {y : ℝ | y = 0} by measurability)).mpr
        hradialZero
  have hscaledZero :
      ∀ᵐ y ∂(h.orbitConstant : ℝ≥0∞) •
          Measure.map F (takagiFlatEigenvalueRadialMeasure N), y = 0 :=
    Measure.smul_absolutelyContinuous.ae_le hmapRadialZero
  have hlaw := h.symmetric_flat_radial_law F hF hFsym
  have hmapSourceZero :
      ∀ᵐ y ∂Measure.map (F ∘ canonicalGapSquaredSpectrum N)
          (complexSymmetricMatrixVolume N), y = 0 :=
    hlaw.symm ▸ hscaledZero
  have hsourceZero :
      ∀ᵐ C ∂complexSymmetricMatrixVolume N,
        (F ∘ canonicalGapSquaredSpectrum N) C = 0 :=
    (ae_map_iff (hF.comp h.measurable_spectrum).aemeasurable
      (show MeasurableSet {y : ℝ | y = 0} by measurability)).mp
        hmapSourceZero
  filter_upwards [hsourceZero] with C hzero
  by_contra hnot
  have : (F ∘ canonicalGapSquaredSpectrum N) C = 1 := by
    simp [F, positiveOrthantFailureIndicator, hnot]
  linarith

/-- Consequently the literal matrix determinant weight agrees almost
everywhere with the symmetric boundary density evaluated at the canonical
spectrum. -/
theorem TakagiWeylSymmetricIntegrationLaw.matrixWeight_ae_eq_boundary_comp
    {N : ℕ} (h : TakagiWeylSymmetricIntegrationLaw N) (K : ℕ) :
    coeCornerMatrixDeterminantWeight N K =ᵐ[
      complexSymmetricMatrixVolume N]
      coeTakagiBoundaryDensity N K ∘ canonicalGapSquaredSpectrum N := by
  filter_upwards [h.canonicalSpectrum_ae_positive] with C hpos
  exact coeCornerMatrixDeterminantWeight_eq_boundary_canonicalSpectrum C hpos

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
