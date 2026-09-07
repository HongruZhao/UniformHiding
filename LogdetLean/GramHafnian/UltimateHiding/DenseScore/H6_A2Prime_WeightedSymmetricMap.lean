import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Literature.H6_A2Prime_TakagiWeylSymmetricIntegration

/-!
# Weighted symmetric-map consequences of A2-prime

This module derives the density-weighted form of the invariant Takagi--Weyl
formula.  The key device is to apply A2' to the joint symmetric statistic
`lambda |-> (w lambda, F lambda)`.  Consequently no full unordered-spectrum
pushforward law is introduced or assumed.
-/

open scoped ENNReal
open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open H6CoordinateAlgebra H6RadialMeasureAdapters

/-- Pairing two permutation-invariant spectral tests preserves invariance. -/
theorem IsPermutationInvariantSpectralTest.prodMk
    {N : ℕ} {γ δ : Type}
    {F : (Fin N → ℝ) → γ} {G : (Fin N → ℝ) → δ}
    (hF : IsPermutationInvariantSpectralTest F)
    (hG : IsPermutationInvariantSpectralTest G) :
    IsPermutationInvariantSpectralTest (fun lambda ↦ (F lambda, G lambda)) := by
  intro sigma lambda
  change (F (lambda ∘ sigma), G (lambda ∘ sigma)) = (F lambda, G lambda)
  rw [hF sigma lambda, hG sigma lambda]

/-- Density-weighted, permutation-invariant pushforward form of A2'.

The density `w` and reported statistic `F` are both symmetric.  This is the
general adapter needed to insert the COE boundary density while retaining
only the trace-vector statistic downstream. -/
theorem TakagiWeylSymmetricIntegrationLaw.weighted_symmetric_map_law
    {N : ℕ} (h : TakagiWeylSymmetricIntegrationLaw N)
    {γ : Type} [MeasurableSpace γ]
    (F : (Fin N → ℝ) → γ) (w : (Fin N → ℝ) → ℝ≥0∞)
    (hF : Measurable F) (hFsym : IsPermutationInvariantSpectralTest F)
    (hw : Measurable w) (hwsym : IsPermutationInvariantSpectralTest w) :
    Measure.map (F ∘ canonicalGapSquaredSpectrum N)
        ((complexSymmetricMatrixVolume N).withDensity
          (w ∘ canonicalGapSquaredSpectrum N)) =
      (h.orbitConstant : ℝ≥0∞) •
        Measure.map F
          ((takagiFlatEigenvalueRadialMeasure N).withDensity w) := by
  let J : (Fin N → ℝ) → ℝ≥0∞ × γ := fun lambda ↦ (w lambda, F lambda)
  have hJ : Measurable J := hw.prodMk hF
  have hJsym : IsPermutationInvariantSpectralTest J :=
    hwsym.prodMk hFsym
  have hJspec : Measurable (J ∘ canonicalGapSquaredSpectrum N) :=
    hJ.comp h.measurable_spectrum
  have hFspec : Measurable (F ∘ canonicalGapSquaredSpectrum N) :=
    hF.comp h.measurable_spectrum
  have hwJ : (Prod.fst : ℝ≥0∞ × γ → ℝ≥0∞) ∘ J = w := by
    rfl
  have hFJ : (Prod.snd : ℝ≥0∞ × γ → γ) ∘ J = F := by
    rfl
  have hwJspec :
      (Prod.fst : ℝ≥0∞ × γ → ℝ≥0∞) ∘
          (J ∘ canonicalGapSquaredSpectrum N) =
        w ∘ canonicalGapSquaredSpectrum N := by
    rfl
  have hFJspec :
      (Prod.snd : ℝ≥0∞ × γ → γ) ∘
          (J ∘ canonicalGapSquaredSpectrum N) =
        F ∘ canonicalGapSquaredSpectrum N := by
    rfl
  calc
    Measure.map (F ∘ canonicalGapSquaredSpectrum N)
        ((complexSymmetricMatrixVolume N).withDensity
          (w ∘ canonicalGapSquaredSpectrum N)) =
      Measure.map Prod.snd
        (Measure.map (J ∘ canonicalGapSquaredSpectrum N)
          ((complexSymmetricMatrixVolume N).withDensity
            (w ∘ canonicalGapSquaredSpectrum N))) := by
        rw [Measure.map_map measurable_snd hJspec, hFJspec]
    _ = Measure.map Prod.snd
        ((Measure.map (J ∘ canonicalGapSquaredSpectrum N)
            (complexSymmetricMatrixVolume N)).withDensity Prod.fst) := by
      congr 1
      rw [← hwJspec]
      exact H6RadialMeasureAdapters.map_withDensity_comp
        (complexSymmetricMatrixVolume N)
        (J ∘ canonicalGapSquaredSpectrum N) Prod.fst hJspec
        measurable_fst.aemeasurable
    _ = Measure.map Prod.snd
        (((h.orbitConstant : ℝ≥0∞) •
            Measure.map J (takagiFlatEigenvalueRadialMeasure N)).withDensity
          Prod.fst) := by
      rw [h.symmetric_flat_radial_law J hJ hJsym]
    _ = Measure.map Prod.snd
        ((h.orbitConstant : ℝ≥0∞) •
          (Measure.map J (takagiFlatEigenvalueRadialMeasure N)).withDensity
            Prod.fst) := by
      rw [withDensity_smul_measure]
    _ = (h.orbitConstant : ℝ≥0∞) •
        Measure.map Prod.snd
          ((Measure.map J (takagiFlatEigenvalueRadialMeasure N)).withDensity
            Prod.fst) := by
      rw [Measure.map_smul]
    _ = (h.orbitConstant : ℝ≥0∞) •
        Measure.map Prod.snd
          (Measure.map J
            ((takagiFlatEigenvalueRadialMeasure N).withDensity w)) := by
      congr 1
      congr 1
      rw [← hwJ]
      exact (H6RadialMeasureAdapters.map_withDensity_comp
        (takagiFlatEigenvalueRadialMeasure N) J Prod.fst hJ
        measurable_fst.aemeasurable).symm
    _ = (h.orbitConstant : ℝ≥0∞) •
        Measure.map F
          ((takagiFlatEigenvalueRadialMeasure N).withDensity w) := by
      rw [Measure.map_map measurable_snd hJ, hFJ]

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
