import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16DirectGaussGreenReduction
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16_Proof
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ConcreteScaledCOECornerProbability
import Mathlib.Tactic

/-!
# H16 fourth radial integrability from exact H5

This module discharges the sharp determinant-kernel `L1` input at order four
directly from the exact H5 density theorem, used at the shifted parameter
`K - 8`.  It does not use a separate Weyl--Takagi theorem.  The key point is
that exact H5 identifies the canonically normalized determinant measure with
an actual probability law, so its unnormalized mass cannot be infinite.

The fourth radial kernel is exactly the real-valued version of the determinant
weight at `K - 8`, because its exponent is shifted down by four.  No boundary
value or pointwise fourth-jet dominator is introduced.
-/

open MeasureTheory Set
open scoped ENNReal

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.LocalAnticoncentration

/-- Unscaling preserves the total mass of the canonical scaled COE law. -/
theorem h16_concreteUnscaledCOECornerLaw_apply_univ
    {N K : ℕ} (hNK : N ≤ K) :
    concreteUnscaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K Set.univ = 1 := by
  letI : IsProbabilityMeasure
      (concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K) :=
    canonicalScaledCOECornerLaw_isProbability hNK
  unfold concreteUnscaledCOECornerLaw
  rw [Measure.map_apply_of_aemeasurable
    (measurable_unscaleCOECorner N K).aemeasurable MeasurableSet.univ]
  simp

/-- The total mass of the raw determinant measure is the integral of its
coordinate density. -/
theorem h16_coeCornerRawDeterminantDensityMeasure_apply_univ
    (N K : ℕ) :
    coeCornerRawDeterminantDensityMeasure N K Set.univ =
      ∫⁻ x, coeCornerDeterminantWeight N K x
        ∂(complexSymmetricCoordinateVolume N) := by
  unfold coeCornerRawDeterminantDensityMeasure
  rw [Measure.map_apply_of_aemeasurable
    (measurable_complexSymmetricMatrixOfCoordinates N).aemeasurable
      MeasurableSet.univ]
  simp [withDensity_apply]

/-- Exact H5 forces the raw determinant mass to be finite.  This uses only
normalization and the probability character of the concrete COE law. -/
theorem h16_coeCornerRawDeterminantDensityMeasure_univ_ne_top_of_exactH5
    (hH5 : H16ExactH5Family) {N K : ℕ}
    (hN : 1 ≤ N) (h2NK : 2 * N ≤ K) :
    coeCornerRawDeterminantDensityMeasure N K Set.univ ≠ ∞ := by
  let μ := coeCornerRawDeterminantDensityMeasure N K
  have hprob :
      concreteUnscaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K Set.univ = 1 :=
    h16_concreteUnscaledCOECornerLaw_apply_univ (by omega)
  have heq := hH5 (n := N) (k := K) hN h2NK
  have hnormalized :
      coeCornerDeterminantDensityProbabilityMeasure N K Set.univ = 1 := by
    rw [← heq]
    exact hprob
  intro htop
  have hzero : coeCornerDeterminantDensityProbabilityMeasure N K = 0 := by
    unfold coeCornerDeterminantDensityProbabilityMeasure
    change (μ Set.univ)⁻¹ • μ = 0
    rw [htop]
    simp
  rw [hzero] at hnormalized
  simp at hnormalized

/-- The determinant weight has finite integral whenever exact H5 applies. -/
theorem h16_lintegral_coeCornerDeterminantWeight_ne_top_of_exactH5
    (hH5 : H16ExactH5Family) {N K : ℕ}
    (hN : 1 ≤ N) (h2NK : 2 * N ≤ K) :
    ∫⁻ x, coeCornerDeterminantWeight N K x
        ∂(complexSymmetricCoordinateVolume N) ≠ ∞ := by
  rw [← h16_coeCornerRawDeterminantDensityMeasure_apply_univ]
  exact h16_coeCornerRawDeterminantDensityMeasure_univ_ne_top_of_exactH5
    hH5 hN h2NK

/-- Subtracting eight ambient COE dimensions lowers the determinant exponent
by exactly four. -/
theorem h16_coeCornerDensityExponent_sub_eight
    {N K : ℕ} (hK : 8 ≤ K) :
    coeCornerDensityExponent N (K - 8) =
      coeCornerDensityExponent N K - 4 := by
  unfold coeCornerDensityExponent
  rw [Nat.cast_sub hK]
  push_cast
  ring

/-- Pointwise identification of the sharp fourth-order radial kernel with the
shifted determinant density. -/
theorem h16COEFourthRadialKernel_eq_shiftedWeight_toReal
    {N K : ℕ} (hK : 8 ≤ K)
    (x : ComplexSymmetricCoordinates N) :
    h16COEFourthRadialKernel N K x =
      (coeCornerDeterminantWeight N (K - 8) x).toReal := by
  classical
  unfold h16COEFourthRadialKernel coeCornerDeterminantWeight
  dsimp only
  split_ifs with hsupport
  · rw [h16_coeCornerDensityExponent_sub_eight hK]
    rw [ENNReal.toReal_ofReal]
    · rfl
    · exact Real.rpow_nonneg
        (h16COECoordinateGapDeterminant_pos hsupport).le _
  · simp

/-- The determinant-specific fourth radial kernel is genuinely integrable
under the exact H5 family and the sharp order-four boundary range. -/
theorem h16COEFourthRadialIntegrability_of_exactH5
    (hH5 : H16ExactH5Family) {N K : ℕ}
    (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K) :
    H16COEFourthRadialIntegrability N K := by
  have hK : 8 ≤ K := by omega
  have hshift : 2 * N ≤ K - 8 := by omega
  have hfinite :=
    h16_lintegral_coeCornerDeterminantWeight_ne_top_of_exactH5
      hH5 hN hshift
  have hint : Integrable
      (fun x ↦ (coeCornerDeterminantWeight N (K - 8) x).toReal)
      (complexSymmetricCoordinateVolume N) :=
    integrable_toReal_of_lintegral_ne_top
      (measurable_coeCornerDeterminantWeight N (K - 8)).aemeasurable hfinite
  have hfun : h16COEFourthRadialKernel N K =
      fun x ↦ (coeCornerDeterminantWeight N (K - 8) x).toReal :=
    funext (h16COEFourthRadialKernel_eq_shiftedWeight_toReal hK)
  change Integrable (h16COEFourthRadialKernel N K)
    (complexSymmetricCoordinateVolume N)
  rw [hfun]
  exact hint

/-- Exact H5 plus the literal algebraic radial estimate yields the genuine
determinant-specific fourth base-jet `L1` theorem. -/
theorem h16CenteredBaseJetFourIntegrable_of_exactH5
    (hH5 : H16ExactH5Family) {N K : ℕ}
    (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (hjet : H16CenteredFourthJetRadialEstimate N K) :
    H16CenteredBaseJetFourIntegrable N K :=
  h16CenteredBaseJetFourIntegrable_of_radial
    (h16COEFourthRadialIntegrability_of_exactH5 hH5 hN hboundary) hjet

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
