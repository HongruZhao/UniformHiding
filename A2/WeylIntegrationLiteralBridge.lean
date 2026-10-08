import A2.OrbitMeasureCoordinateVolume
import A2.OrbitMeasureRadialRegularity
import A2.SpectralExceptionalSets
import A2.SpectrumTakagi

open MeasureTheory MeasureTheory.Measure Set Function
open scoped BigOperators ENNReal

noncomputable section

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

set_option maxHeartbeats 600000

/-- The actual symmetric matrix represented by the full upper real coordinates. -/
def takagiMatrixOfRealCoordinates {N : ℕ} (x : TakagiRealCoordinates N) :
    Matrix (Fin N) (Fin N) ℂ :=
  complexSymmetricMatrixOfCoordinates (takagiRealComplexCoordinatesEquiv N x)

theorem measurable_takagiMatrixOfRealCoordinates (N : ℕ) :
    Measurable (@takagiMatrixOfRealCoordinates N) :=
  (measurable_complexSymmetricMatrixOfCoordinates N).comp
    (measurePreserving_takagiRealComplexCoordinatesEquiv N).measurable

theorem map_takagiMatrixOfRealCoordinates_volume (N : ℕ) :
    Measure.map (@takagiMatrixOfRealCoordinates N)
      (volume : Measure (TakagiRealCoordinates N)) = complexSymmetricMatrixVolume N := by
  change Measure.map (complexSymmetricMatrixOfCoordinates ∘
    takagiRealComplexCoordinatesEquiv N) volume = _
  rw [← Measure.map_map (measurable_complexSymmetricMatrixOfCoordinates N)
      (measurePreserving_takagiRealComplexCoordinatesEquiv N).measurable,
    map_takagiRealComplexCoordinatesEquiv_volume]
  rfl

@[simp] theorem takagiMatrixOfRealCoordinates_takagiRealOrbitCoordinates {N : ℕ}
    (U : Matrix.unitaryGroup (Fin N) ℂ) (lambda : Fin N → ℝ) :
    takagiMatrixOfRealCoordinates (takagiRealOrbitCoordinates U lambda) =
      takagiOrbit U lambda := by
  simp only [takagiMatrixOfRealCoordinates, takagiRealOrbitCoordinates,
    LinearEquiv.apply_symm_apply]
  exact complexSymmetricMatrixOfCoordinates_takagiOrbit U lambda

def regularTakagiRealMatrixSet (N : ℕ) : Set (TakagiRealCoordinates N) :=
  (canonicalGapSquaredSpectrum N ∘ takagiMatrixOfRealCoordinates) ⁻¹'
    regularTakagiSquaredRadii N

theorem measurableSet_regularTakagiRealMatrixSet (N : ℕ) :
    MeasurableSet (regularTakagiRealMatrixSet N) :=
  (isOpen_regularTakagiSquaredRadii N).measurableSet.preimage
    ((measurable_canonicalGapSquaredSpectrum N).comp
      (measurable_takagiMatrixOfRealCoordinates N))

/-- The concrete nonsingular, simple-spectrum orbit domain has full real
coordinate volume, by the checked characteristic-resultant exceptional sets. -/
theorem ae_mem_regularTakagiRealMatrixSet (N : ℕ) :
    ∀ᵐ x ∂(volume : Measure (TakagiRealCoordinates N)),
      x ∈ regularTakagiRealMatrixSet N := by
  have hmatrix : ∀ᵐ C ∂complexSymmetricMatrixVolume N,
      canonicalGapSquaredSpectrum N C ∈ regularTakagiSquaredRadii N :=
    A2Research.ae_positive_injective_canonicalGapSquaredSpectrum_matrixVolume N
  rw [← map_takagiMatrixOfRealCoordinates_volume N] at hmatrix
  exact (ae_map_iff (measurable_takagiMatrixOfRealCoordinates N).aemeasurable
    ((isOpen_regularTakagiSquaredRadii N).measurableSet.preimage
      (measurable_canonicalGapSquaredSpectrum N))).mp hmatrix

theorem canonicalGapSquaredSpectrum_permutation_of_takagiOrbit {N : ℕ}
    (U : Matrix.unitaryGroup (Fin N) ℂ) (lambda : Fin N → ℝ)
    (hlambda : ∀ i, 0 ≤ lambda i) :
    ∃ sigma : Equiv.Perm (Fin N),
      canonicalGapSquaredSpectrum N (takagiOrbit U lambda) = lambda ∘ sigma := by
  obtain ⟨sigma, hsigma⟩ := canonicalGapSquaredSpectrum_permutation_of_unitary_congruence
    (takagiOrbit U lambda) U (fun i ↦ Real.sqrt (lambda i)) rfl
  refine ⟨sigma, hsigma.trans ?_⟩
  funext i
  exact Real.sq_sqrt (hlambda (sigma i))

theorem takagiRealOrbitCoordinates_mem_regular {N : ℕ}
    (U : Matrix.unitaryGroup (Fin N) ℂ) (lambda : Fin N → ℝ)
    (hlambda : IsRegularTakagiSpectrum lambda) :
    takagiRealOrbitCoordinates U lambda ∈ regularTakagiRealMatrixSet N := by
  change IsRegularTakagiSpectrum (canonicalGapSquaredSpectrum N
    (takagiMatrixOfRealCoordinates (takagiRealOrbitCoordinates U lambda)))
  rw [takagiMatrixOfRealCoordinates_takagiRealOrbitCoordinates]
  obtain ⟨sigma, hsigma⟩ := canonicalGapSquaredSpectrum_permutation_of_takagiOrbit
    U lambda (fun i ↦ (hlambda.1 i).le)
  rw [hsigma]
  exact ⟨fun i ↦ hlambda.1 (sigma i), hlambda.2.comp sigma.injective⟩

/-- Permutation-invariant tests agree pointwise on each actual positive
Takagi orbit, with the literal canonical spectrum used by the original target. -/
theorem invariant_test_takagiOrbit
    {N : ℕ} {Y : Type} (F : (Fin N → ℝ) → Y)
    (hF : IsPermutationInvariantSpectralTest F)
    (U : Matrix.unitaryGroup (Fin N) ℂ) (lambda : Fin N → ℝ)
    (hlambda : ∀ i, 0 ≤ lambda i) :
    F (canonicalGapSquaredSpectrum N (takagiOrbit U lambda)) = F lambda := by
  obtain ⟨sigma, hsigma⟩ := canonicalGapSquaredSpectrum_permutation_of_takagiOrbit
    U lambda hlambda
  rw [hsigma]
  exact hF sigma lambda

theorem map_invariant_test_matrixVolume_eq_realVolume
    {N : ℕ} {Y : Type*} [MeasurableSpace Y]
    (F : (Fin N → ℝ) → Y) (hF : Measurable F) :
    Measure.map (F ∘ canonicalGapSquaredSpectrum N) (complexSymmetricMatrixVolume N) =
      Measure.map (F ∘ canonicalGapSquaredSpectrum N ∘ takagiMatrixOfRealCoordinates)
        (volume : Measure (TakagiRealCoordinates N)) := by
  rw [← map_takagiMatrixOfRealCoordinates_volume N,
    Measure.map_map (hF.comp (measurable_canonicalGapSquaredSpectrum N))
      (measurable_takagiMatrixOfRealCoordinates N)]
  rfl

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
