import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16CoordinateProbabilityLawFromExactH5
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16WeakFactsProjectiveEnvelope
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# Scaled-law score `L1` from corrected weak facts

The exact-H5 coordinate law and the time-zero jet/score identity transfer the
coordinate `L1` jets to the literal zero-extended scores under the actual
scaled COE law.  The pulled-back envelope yields a bound uniform in the
projective direction.

The final product-space theorem isolates only joint a.e. strong measurability
as an explicit input.  Its remaining integrability and uniform control are
proved here; no moment or event-derivative declaration is used.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.CurrentPRL

theorem continuous_h16ScaledSymmetricCoordinateEmbedding (N K : ℕ) :
    Continuous (h16ScaledSymmetricCoordinateEmbedding N K) := by
  unfold h16ScaledSymmetricCoordinateEmbedding h16ScaleCOECorner
  fun_prop

theorem injective_h16ScaledSymmetricCoordinateEmbedding
    {N K : ℕ} (hK : 0 < K) :
    Function.Injective (h16ScaledSymmetricCoordinateEmbedding N K) := by
  intro x y hxy
  have hunscaled := congrArg (unscaleCOECorner K) hxy
  simp only [h16ScaledSymmetricCoordinateEmbedding,
    unscaleCOECorner_h16ScaleCOECorner hK] at hunscaled
  have hcoordinates :=
    congrArg complexSymmetricCoordinatesOfMatrix hunscaled
  simpa only [complexSymmetricCoordinatesOfMatrix_matrixOfCoordinates]
    using hcoordinates

theorem range_h16ScaledSymmetricCoordinateEmbedding
    {N K : ℕ} (hK : 0 < K) :
    Set.range (h16ScaledSymmetricCoordinateEmbedding N K) =
      {A : ConcreteMatrixState N | A.IsSymm} := by
  ext A
  constructor
  · rintro ⟨x, rfl⟩
    exact (complexSymmetricMatrixOfCoordinates_isSymm x).smul _
  · intro hA
    have hunscaled : (unscaleCOECorner K A).IsSymm := by
      exact hA.smul _
    refine ⟨complexSymmetricCoordinatesOfMatrix (unscaleCOECorner K A), ?_⟩
    unfold h16ScaledSymmetricCoordinateEmbedding
    rw [complexSymmetricMatrixOfCoordinates_coordinatesOfMatrix _ hunscaled]
    exact h16ScaleCOECorner_unscaleCOECorner hK A

theorem measurableEmbedding_h16ScaledSymmetricCoordinateEmbedding
    {N K : ℕ} (hK : 0 < K) :
    MeasurableEmbedding (h16ScaledSymmetricCoordinateEmbedding N K) := by
  apply MeasurableEmbedding.of_measurable_inverse
    (measurable_h16ScaledSymmetricCoordinateEmbedding N K)
  · rw [range_h16ScaledSymmetricCoordinateEmbedding hK]
    exact measurableSet_concreteMatrix_isSymm N
  · exact (measurable_complexSymmetricCoordinatesOfMatrix N).comp
      (measurable_unscaleCOECorner N K)
  · intro x
    change complexSymmetricCoordinatesOfMatrix
        (unscaleCOECorner K
          (h16ScaleCOECorner K
            (complexSymmetricMatrixOfCoordinates x))) = x
    rw [unscaleCOECorner_h16ScaleCOECorner hK,
      complexSymmetricCoordinatesOfMatrix_matrixOfCoordinates]

/-- Every zero-extended literal score section through order four is genuinely
`L1` under the scaled COE law. -/
theorem integrable_h16ZeroExtendedConcreteCenteredDensityScore_of_weakFacts
    (hH5 : H16ExactH5Family) {N K : ℕ}
    {hN : 1 ≤ N} {hboundary : 2 * N + 8 ≤ K}
    (W : COECenteredOrderFourWeakGeneratorFacts N K hN hboundary)
    (r : Fin 5) (v : ComplexUnitSphere N) :
    Integrable
      (h16ZeroExtendedConcreteCenteredDensityScore (r : ℕ) N K v)
      (concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K) := by
  have hK : 0 < K := by omega
  rw [h16_scaledLaw_eq_map_coordinateProbabilityDensity_of_exactH5
    hH5 hN (by omega : 2 * N ≤ K)]
  rw [(measurableEmbedding_h16ScaledSymmetricCoordinateEmbedding hK).integrable_map_iff]
  change Integrable
    (fun x ↦ h16ZeroExtendedConcreteCenteredDensityScore
      (r : ℕ) N K v (h16ScaledSymmetricCoordinateEmbedding N K x))
    ((complexSymmetricCoordinateVolume N).withDensity
      (fun x ↦ (h16COECoordinateProbabilityWeight N K x : ℝ≥0∞)))
  rw [integrable_withDensity_iff_integrable_coe_smul
    (measurable_h16COECoordinateProbabilityWeight N K)]
  exact (W.jet_integrable r v 0).congr <| by
    filter_upwards [W.jet_at_zero_score r v] with x hx
    simp only [smul_eq_mul,
      h16COECoordinateProbabilityWeight_coe_real]
    rw [hx]
    rw [W.density_zero_eq_probabilityDensity v 0 x]
    simp only [neg_zero, h16CenteredCoordinateFlow_zero]
    ring

/-- Exact equality between the scaled-law absolute score integral and the
coordinate `L1` norm of the corresponding base jet. -/
theorem integral_norm_h16ZeroExtendedScore_eq_norm_centeredJetLp
    (hH5 : H16ExactH5Family) {N K : ℕ}
    {hN : 1 ≤ N} {hboundary : 2 * N + 8 ≤ K}
    (W : COECenteredOrderFourWeakGeneratorFacts N K hN hboundary)
    (r : Fin 5) (v : ComplexUnitSphere N) :
    (∫ A, ‖h16ZeroExtendedConcreteCenteredDensityScore
          (r : ℕ) N K v A‖
        ∂(concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K)) =
      ‖h16CenteredJetLpOfWeak W r v 0‖ := by
  have hK : 0 < K := by omega
  rw [h16_scaledLaw_eq_map_coordinateProbabilityDensity_of_exactH5
    hH5 hN (by omega : 2 * N ≤ K)]
  rw [(measurableEmbedding_h16ScaledSymmetricCoordinateEmbedding hK).integral_map]
  rw [integral_withDensity_eq_integral_smul
    (measurable_h16COECoordinateProbabilityWeight N K)]
  rw [L1.norm_eq_integral_norm]
  apply integral_congr_ae
  filter_upwards [W.jet_at_zero_score r v,
    h16CenteredJetLpOfWeak_coeFn_ae W r v 0] with x hx hLp
  rw [hLp, hx]
  simp only [NNReal.smul_def,
    h16COECoordinateProbabilityWeight_coe_real, norm_mul]
  rw [W.density_zero_eq_probabilityDensity v 0 x]
  simp only [neg_zero, h16CenteredCoordinateFlow_zero]
  simp only [smul_eq_mul, Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ h16COECoordinateProbabilityDensity N K x by
      rw [← h16COECoordinateProbabilityWeight_coe_real]
      exact NNReal.zero_le_coe)]
  ring

/-- One finite constant bounds the absolute score integral for every
projective direction. -/
theorem exists_uniform_scaledScore_L1_bound_of_weakFacts
    (hH5 : H16ExactH5Family) {N K : ℕ}
    {hN : 1 ≤ N} {hboundary : 2 * N + 8 ≤ K}
    (W : COECenteredOrderFourWeakGeneratorFacts N K hN hboundary)
    (r : Fin 5) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ v : ComplexUnitSphere N,
      (∫ A, ‖h16ZeroExtendedConcreteCenteredDensityScore
            (r : ℕ) N K v A‖
          ∂(concreteScaledCOECornerLaw
            canonicalUnitaryHaarProbabilityFamily N K)) ≤ B := by
  obtain ⟨b, hb, hbound⟩ := W.pulledBack_L1_envelope
  let B : ℝ := ∫ x, b r x ∂(complexSymmetricCoordinateVolume N)
  refine ⟨B, integral_nonneg (hb r).1, ?_⟩
  intro v
  rw [integral_norm_h16ZeroExtendedScore_eq_norm_centeredJetLp
    hH5 W r v]
  exact h16CenteredJetLp_norm_le_pulledBackEnvelopeIntegral
    W b hb hbound r v 0

/-- Joint a.e. strong measurability is the only extra ingredient needed to
promote the proved section bounds to product-`L1` over matrix and direction. -/
theorem integrable_h16ZeroExtendedScore_product_of_weakFacts
    (hH5 : H16ExactH5Family) {N K : ℕ}
    {hN : 1 ≤ N} {hboundary : 2 * N + 8 ≤ K}
    (W : COECenteredOrderFourWeakGeneratorFacts N K hN hboundary)
    (r : Fin 5)
    (hjoint : AEStronglyMeasurable
      (fun Av : ConcreteMatrixState N × ComplexUnitSphere N ↦
        h16ZeroExtendedConcreteCenteredDensityScore
          (r : ℕ) N K Av.2 Av.1)
      ((concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K).prod
        (complexUnitSphereProbabilityMeasure N))) :
    Integrable
      (fun Av : ConcreteMatrixState N × ComplexUnitSphere N ↦
        h16ZeroExtendedConcreteCenteredDensityScore
          (r : ℕ) N K Av.2 Av.1)
      ((concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K).prod
        (complexUnitSphereProbabilityMeasure N)) := by
  let mu := concreteScaledCOECornerLaw
    canonicalUnitaryHaarProbabilityFamily N K
  let sphere := complexUnitSphereProbabilityMeasure N
  let score : ConcreteMatrixState N × ComplexUnitSphere N → ℝ :=
    fun Av ↦ h16ZeroExtendedConcreteCenteredDensityScore
      (r : ℕ) N K Av.2 Av.1
  letI : IsProbabilityMeasure mu :=
    canonicalScaledCOECornerLaw_isProbability (by omega : N ≤ K)
  letI : IsProbabilityMeasure sphere :=
    complexUnitSphereProbabilityMeasure_isProbability hN
  obtain ⟨B, hB, hbound⟩ :=
    exists_uniform_scaledScore_L1_bound_of_weakFacts hH5 W r
  rw [integrable_prod_iff' hjoint]
  constructor
  · filter_upwards [] with v
    exact integrable_h16ZeroExtendedConcreteCenteredDensityScore_of_weakFacts
      hH5 W r v
  · have hmeas : AEStronglyMeasurable
        (fun v : ComplexUnitSphere N ↦
          ∫ A : ConcreteMatrixState N, ‖score (A, v)‖ ∂mu) sphere :=
      by
        simpa [score] using
          hjoint.norm.prod_swap.integral_prod_right'
    exact (integrable_const B).mono' hmeas <| by
      filter_upwards [] with v
      have hnonneg : 0 ≤
          ∫ A : ConcreteMatrixState N, ‖score (A, v)‖ ∂mu :=
        integral_nonneg fun _ ↦ norm_nonneg _
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      simpa only [score, mu] using hbound v

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
