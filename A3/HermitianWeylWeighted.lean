import A3.HermitianWeylProof

open MeasureTheory MeasureTheory.Measure
open scoped BigOperators ENNReal

noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

namespace A3Research

variable {n : ℕ} {K : Type*} [RCLike K] [MeasureSpace K] [BorelSpace K]

/-- Spectral weighting commutes with the actual symmetric-test Weyl law.
The weight is arbitrary measurable and permutation invariant. -/
theorem HermitianWeylSymmetricIntegrationLaw.map_spectral_withDensity
    (h : HermitianWeylSymmetricIntegrationLaw n K)
    {Y : Type} [MeasurableSpace Y] (F : (Fin n → ℝ) → Y)
    (hF : Measurable F)
    (hperm : LogdetLean.GramHafnian.UltimateHiding.DenseScore.IsA2SymmetricTest F)
    (g : (Fin n → ℝ) → ℝ≥0∞) (hg : Measurable g)
    (hgperm : LogdetLean.GramHafnian.UltimateHiding.DenseScore.IsA2SymmetricTest g) :
    Measure.map (F ∘ canonicalHermitianSpectrum)
      ((hermitianCoordinateVolume n K).withDensity (g ∘ canonicalHermitianSpectrum)) =
      (h.orbitConstant : ℝ≥0∞) • Measure.map F
        ((hermitianFlatEigenvalueRadialMeasure n K).withDensity g) := by
  let G : (Fin n → ℝ) → Y × ℝ≥0∞ := fun lambda ↦ (F lambda, g lambda)
  have hG : Measurable G := hF.prodMk hg
  have hGperm : LogdetLean.GramHafnian.UltimateHiding.DenseScore.IsA2SymmetricTest G := by
    intro sigma lambda
    exact Prod.ext (hperm sigma lambda) (hgperm sigma lambda)
  have hleft : Measure.map Prod.fst
      ((Measure.map (G ∘ canonicalHermitianSpectrum) (hermitianCoordinateVolume n K)).withDensity
        Prod.snd) =
      Measure.map (F ∘ canonicalHermitianSpectrum)
        ((hermitianCoordinateVolume n K).withDensity (g ∘ canonicalHermitianSpectrum)) := by
    rw [← map_withDensity_comp _ _ (hG.comp h.measurable_spectrum) Prod.snd measurable_snd,
      Measure.map_map measurable_fst (hG.comp h.measurable_spectrum)]
    rfl
  have hright : Measure.map Prod.fst
      ((Measure.map G (hermitianFlatEigenvalueRadialMeasure n K)).withDensity Prod.snd) =
      Measure.map F ((hermitianFlatEigenvalueRadialMeasure n K).withDensity g) := by
    rw [← map_withDensity_comp _ G hG Prod.snd measurable_snd,
      Measure.map_map measurable_fst hG]
    rfl
  have hw := congrArg (fun nu : Measure (Y × ℝ≥0∞) ↦
    Measure.map Prod.fst (nu.withDensity Prod.snd)) (h.symmetric_flat_radial_law G hG hGperm)
  rw [withDensity_smul_measure, Measure.map_smul, hleft, hright] at hw
  exact hw

theorem hermitianWeyl_map_spectral_withDensity
    [PolishSpace K] [IsAddHaarMeasure (volume : Measure K)]
    {Y : Type} [MeasurableSpace Y] (F : (Fin n → ℝ) → Y)
    (hF : Measurable F)
    (hperm : LogdetLean.GramHafnian.UltimateHiding.DenseScore.IsA2SymmetricTest F)
    (g : (Fin n → ℝ) → ℝ≥0∞) (hg : Measurable g)
    (hgperm : LogdetLean.GramHafnian.UltimateHiding.DenseScore.IsA2SymmetricTest g) :
    Measure.map (F ∘ canonicalHermitianSpectrum)
      ((hermitianCoordinateVolume n K).withDensity (g ∘ canonicalHermitianSpectrum)) =
      ((hermitianWeylSymmetricIntegrationLaw n K).orbitConstant : ℝ≥0∞) • Measure.map F
        ((hermitianFlatEigenvalueRadialMeasure n K).withDensity g) :=
  (hermitianWeylSymmetricIntegrationLaw n K).map_spectral_withDensity F hF hperm g hg hgperm

end A3Research
