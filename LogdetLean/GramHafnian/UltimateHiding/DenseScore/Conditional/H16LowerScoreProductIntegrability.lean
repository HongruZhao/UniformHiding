import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16ScoreJointMeasurability
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16LowerJetEnvelope
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16DeterminantLocalLowerJetContinuity
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16ZeroExtensionDownstreamAssembly
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CenteredScoreProductLaw
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# Product integrability of the lower literal centered scores

Orders zero through three do not need the weak-generator or Gauss--Green
step.  Their zero-extended coordinate density jets are jointly continuous
and are supported in the closed unit coordinate ball.  Compactness therefore
gives one integrable envelope, uniform in the projective direction.  Exact H5
then transports this elementary coordinate estimate to the literal scaled
COE score under the matrix-law/projective product measure.

The order-three specialization removes the separate product-`L1` scientific
input formerly used only to justify projective Fubini.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.CurrentPRL

/-- The matrix-coordinate jet proxy is measurable at every lower order,
directly from joint continuity; no weak-generator package is involved. -/
theorem measurable_h16CenteredTransportJet_scoreCoordinate_lower
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (r : Fin 4) :
    Measurable (h16CenteredTransportJetScoreCoordinate r.castSucc N K) := by
  unfold h16CenteredTransportJetScoreCoordinate
  exact (continuous_h16CenteredTransportJet_through_three
      hN hboundary r).measurable.comp
    (measurable_h16ScoreJetParameterMap N K)

/-- The quotient proxy for the literal lower score is globally measurable. -/
theorem measurable_h16ZeroExtendedScoreMeasurableProxy_lower
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (r : Fin 4) :
    Measurable (h16ZeroExtendedScoreMeasurableProxy r.castSucc N K) := by
  classical
  unfold h16ZeroExtendedScoreMeasurableProxy
  exact Measurable.ite
    ((measurableSet_h16ScaledMatrix_openCOESupport N K).preimage
      measurable_fst)
    ((measurable_h16CenteredTransportJet_scoreCoordinate_lower
        hN hboundary r).div
      (measurable_h16CenteredTransportJet_scoreCoordinate_lower
        hN hboundary 0))
    measurable_const

/-- Under exact H5, the literal (unextended) lower score agrees almost
everywhere with the measurable jet quotient. -/
theorem h16ConcreteCenteredDensityScore_lower_ae_eq_measurableProxy
    (hH5 : H16ExactH5Family) {N K : ℕ}
    (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (r : Fin 4) :
    (fun Av : ConcreteMatrixState N × ComplexUnitSphere N ↦
      concreteCenteredDensityScore (r : ℕ) N K Av.2 Av.1) =ᵐ[
      (concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K).prod
        (complexUnitSphereProbabilityMeasure N)]
      h16ZeroExtendedScoreMeasurableProxy r.castSucc N K := by
  classical
  let mu := concreteScaledCOECornerLaw
    canonicalUnitaryHaarProbabilityFamily N K
  let sphere := complexUnitSphereProbabilityMeasure N
  letI : IsProbabilityMeasure mu :=
    canonicalScaledCOECornerLaw_isProbability (by omega : N ≤ K)
  letI : IsProbabilityMeasure sphere :=
    complexUnitSphereProbabilityMeasure_isProbability hN
  have hscaledSupport :
      ∀ᵐ Av ∂(mu.prod sphere),
        (unscaleCOECorner K Av.1).IsSymm ∧
          coeCornerSupport (unscaleCOECorner K Av.1) :=
    Measure.quasiMeasurePreserving_fst.ae
      (h16_scaledCOECorner_ae_support_of_exactH5
        hH5 hN (by omega : 2 * N ≤ K))
  filter_upwards [hscaledSupport] with Av hAv
  let x : ComplexSymmetricCoordinates N :=
    h16ScoreCoordinateOfMatrix K Av.1
  have hxmatrix : complexSymmetricMatrixOfCoordinates x =
      unscaleCOECorner K Av.1 := by
    exact complexSymmetricMatrixOfCoordinates_coordinatesOfMatrix
      (unscaleCOECorner K Av.1) hAv.1
  have hx : coeCornerSupport (complexSymmetricMatrixOfCoordinates x) := by
    rw [hxmatrix]
    exact hAv.2
  have hK : 0 < K := by omega
  have hembed : h16ScaledSymmetricCoordinateEmbedding N K x = Av.1 := by
    unfold h16ScaledSymmetricCoordinateEmbedding
    rw [hxmatrix, h16ScaleCOECorner_unscaleCOECorner hK]
  have hpoint :=
    h16CenteredTransportJet_zero_eq_score_mul_probabilityDensity
      hN hK r.castSucc Av.2 x
  rw [hembed] at hpoint
  have hzero := h16CenteredTransportJet_zero_eq_probabilityDensity
    (N := N) (K := K) Av.2 0 x
  simp only [neg_zero, h16CenteredCoordinateFlow_zero] at hzero
  have hzeroPos : 0 < h16CenteredTransportJet N K 0 Av.2 0 x := by
    rw [hzero]
    exact h16COECoordinateProbabilityDensity_pos_of_exactH5
      hH5 hN (by omega : 2 * N ≤ K) x hx
  have hzeroNe : h16CenteredTransportJet N K 0 Av.2 0 x ≠ 0 :=
    ne_of_gt hzeroPos
  change concreteCenteredDensityScore (r : ℕ) N K Av.2 Av.1 =
    h16ZeroExtendedScoreMeasurableProxy r.castSucc N K Av
  simp only [h16ZeroExtendedScoreMeasurableProxy,
    h16CenteredTransportJetScoreCoordinate, Function.comp_apply,
    hAv.2, if_true]
  change concreteCenteredDensityScore (r : ℕ) N K Av.2 Av.1 =
    h16CenteredTransportJet N K r.castSucc Av.2 0 x /
      h16CenteredTransportJet N K 0 Av.2 0 x
  have hpoint' :
      h16CenteredTransportJet N K r.castSucc Av.2 0 x =
        concreteCenteredDensityScore (r : ℕ) N K Av.2 Av.1 *
          h16COECoordinateProbabilityDensity N K x := by
    simpa only [Fin.val_castSucc] using hpoint
  rw [← hzero] at hpoint'
  rw [hpoint']
  exact (mul_div_cancel_right₀ _ hzeroNe).symm

/-- Joint a.e. strong measurability of every literal lower score. -/
theorem aestronglyMeasurable_h16ConcreteCenteredDensityScore_lower_joint
    (hH5 : H16ExactH5Family) {N K : ℕ}
    (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (r : Fin 4) :
    AEStronglyMeasurable
      (fun Av : ConcreteMatrixState N × ComplexUnitSphere N ↦
        concreteCenteredDensityScore (r : ℕ) N K Av.2 Av.1)
      ((concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K).prod
        (complexUnitSphereProbabilityMeasure N)) := by
  exact
    (measurable_h16ZeroExtendedScoreMeasurableProxy_lower
      hN hboundary r).aestronglyMeasurable.congr
        (h16ConcreteCenteredDensityScore_lower_ae_eq_measurableProxy
          hH5 hN hboundary r).symm

/-- One compactly supported integrable coordinate envelope controls a fixed
lower jet, uniformly in the projective direction. -/
theorem exists_h16CenteredBaseJetLowerEnvelope_proved
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (r : Fin 4) :
    ∃ b : ComplexSymmetricCoordinates N → ℝ,
      (∀ x, 0 ≤ b x) ∧
      Integrable b (complexSymmetricCoordinateVolume N) ∧
      ∀ (v : ComplexUnitSphere N) (x : ComplexSymmetricCoordinates N),
        ‖h16CenteredTransportJet N K r.castSucc v 0 x‖ ≤ b x := by
  exact exists_h16CenteredBaseJetLowerEnvelope_of_continuous
    (fun s ↦ continuous_h16CenteredTransportJet_through_three
      hN hboundary s)
    (fun s v t x hx ↦
      h16CenteredTransportJet_zero_off_support s v t x hx)
    r

/-- Every fixed-direction lower base jet is integrable in flat coordinates. -/
theorem integrable_h16CenteredBaseJet_lower
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (r : Fin 4) (v : ComplexUnitSphere N) :
    Integrable (h16CenteredTransportJet N K r.castSucc v 0)
      (complexSymmetricCoordinateVolume N) := by
  obtain ⟨b, _hbnonneg, hbint, hbound⟩ :=
    exists_h16CenteredBaseJetLowerEnvelope_proved hN hboundary r
  have hparam : Continuous
      (fun x : ComplexSymmetricCoordinates N ↦ ((v, (0 : ℝ)), x)) := by
    fun_prop
  have hmeas : AEStronglyMeasurable
      (h16CenteredTransportJet N K r.castSucc v 0)
      (complexSymmetricCoordinateVolume N) :=
    ((continuous_h16CenteredTransportJet_through_three
      hN hboundary r).comp hparam).aestronglyMeasurable
  exact hbint.mono' hmeas (ae_of_all _ (hbound v))

/-- Exact H5 transports lower-jet integrability to a literal fixed-direction
score under the scaled COE law. -/
theorem integrable_concreteCenteredDensityScore_lower_of_exactH5
    (hH5 : H16ExactH5Family) {N K : ℕ}
    (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (r : Fin 4) (v : ComplexUnitSphere N) :
    Integrable (concreteCenteredDensityScore (r : ℕ) N K v)
      (concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K) := by
  have hK : 0 < K := by omega
  rw [h16_scaledLaw_eq_map_coordinateProbabilityDensity_of_exactH5
    hH5 hN (by omega : 2 * N ≤ K)]
  rw [(measurableEmbedding_h16ScaledSymmetricCoordinateEmbedding hK).integrable_map_iff]
  change Integrable
    (fun x ↦ concreteCenteredDensityScore (r : ℕ) N K v
      (h16ScaledSymmetricCoordinateEmbedding N K x))
    ((complexSymmetricCoordinateVolume N).withDensity
      (fun x ↦ (h16COECoordinateProbabilityWeight N K x : ℝ≥0∞)))
  rw [integrable_withDensity_iff_integrable_coe_smul
    (measurable_h16COECoordinateProbabilityWeight N K)]
  exact (integrable_h16CenteredBaseJet_lower hN hboundary r v).congr <| by
    filter_upwards [] with x
    simp only [NNReal.smul_def,
      h16COECoordinateProbabilityWeight_coe_real, smul_eq_mul]
    have hfactor :
        h16CenteredTransportJet N K r.castSucc v 0 x =
          concreteCenteredDensityScore (r : ℕ) N K v
              (h16ScaledSymmetricCoordinateEmbedding N K x) *
            h16COECoordinateProbabilityDensity N K x := by
      simpa only [Fin.val_castSucc] using
        (h16CenteredTransportJet_zero_eq_score_mul_probabilityDensity
          hN hK r.castSucc v x)
    rw [hfactor]
    ring

/-- The lower coordinate envelope bounds the absolute score integral under
the actual scaled law, uniformly in the projective direction. -/
theorem exists_uniform_concreteCenteredDensityScore_lower_L1_bound
    (hH5 : H16ExactH5Family) {N K : ℕ}
    (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (r : Fin 4) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ v : ComplexUnitSphere N,
      (∫ A, ‖concreteCenteredDensityScore (r : ℕ) N K v A‖
        ∂(concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K)) ≤ B := by
  obtain ⟨b, hbnonneg, hbint, hbound⟩ :=
    exists_h16CenteredBaseJetLowerEnvelope_proved hN hboundary r
  let B : ℝ := ∫ x, b x ∂(complexSymmetricCoordinateVolume N)
  refine ⟨B, integral_nonneg hbnonneg, ?_⟩
  intro v
  have hK : 0 < K := by omega
  rw [h16_scaledLaw_eq_map_coordinateProbabilityDensity_of_exactH5
    hH5 hN (by omega : 2 * N ≤ K)]
  rw [(measurableEmbedding_h16ScaledSymmetricCoordinateEmbedding hK).integral_map]
  rw [integral_withDensity_eq_integral_smul
    (measurable_h16COECoordinateProbabilityWeight N K)]
  calc
    (∫ x,
        (h16COECoordinateProbabilityWeight N K x : ℝ) •
          ‖concreteCenteredDensityScore (r : ℕ) N K v
            (h16ScaledSymmetricCoordinateEmbedding N K x)‖
        ∂(complexSymmetricCoordinateVolume N)) =
        ∫ x, ‖h16CenteredTransportJet N K r.castSucc v 0 x‖
          ∂(complexSymmetricCoordinateVolume N) := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [smul_eq_mul,
        h16COECoordinateProbabilityWeight_coe_real]
      have hfactor :
          h16CenteredTransportJet N K r.castSucc v 0 x =
            concreteCenteredDensityScore (r : ℕ) N K v
                (h16ScaledSymmetricCoordinateEmbedding N K x) *
              h16COECoordinateProbabilityDensity N K x := by
        simpa only [Fin.val_castSucc] using
          (h16CenteredTransportJet_zero_eq_score_mul_probabilityDensity
            hN hK r.castSucc v x)
      rw [hfactor, norm_mul]
      simp only [Real.norm_eq_abs]
      rw [abs_of_nonneg
        (show 0 ≤ h16COECoordinateProbabilityDensity N K x by
          rw [← h16COECoordinateProbabilityWeight_coe_real]
          exact NNReal.zero_le_coe)]
      ring
    _ ≤ ∫ x, b x ∂(complexSymmetricCoordinateVolume N) := by
      apply integral_mono_ae
        (integrable_h16CenteredBaseJet_lower hN hboundary r v).norm hbint
      exact ae_of_all _ (hbound v)

/-- All literal lower scores are integrable on the matrix/projective product
law.  This statement is independent of the weak-generator identity. -/
theorem integrable_concreteCenteredDensityScore_lower_product_of_exactH5
    (hH5 : H16ExactH5Family) {N K : ℕ}
    (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (r : Fin 4) :
    Integrable
      (fun Av : ConcreteMatrixState N × ComplexUnitSphere N ↦
        concreteCenteredDensityScore (r : ℕ) N K Av.2 Av.1)
      ((concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K).prod
        (complexUnitSphereProbabilityMeasure N)) := by
  let mu := concreteScaledCOECornerLaw
    canonicalUnitaryHaarProbabilityFamily N K
  let sphere := complexUnitSphereProbabilityMeasure N
  let score : ConcreteMatrixState N × ComplexUnitSphere N → ℝ :=
    fun Av ↦ concreteCenteredDensityScore (r : ℕ) N K Av.2 Av.1
  letI : IsProbabilityMeasure mu :=
    canonicalScaledCOECornerLaw_isProbability (by omega : N ≤ K)
  letI : IsProbabilityMeasure sphere :=
    complexUnitSphereProbabilityMeasure_isProbability hN
  have hjoint : AEStronglyMeasurable score (mu.prod sphere) := by
    simpa only [score, mu, sphere] using
      aestronglyMeasurable_h16ConcreteCenteredDensityScore_lower_joint
        hH5 hN hboundary r
  obtain ⟨B, _hB, hbound⟩ :=
    exists_uniform_concreteCenteredDensityScore_lower_L1_bound
      hH5 hN hboundary r
  rw [integrable_prod_iff' hjoint]
  constructor
  · filter_upwards [] with v
    exact integrable_concreteCenteredDensityScore_lower_of_exactH5
      hH5 hN hboundary r v
  · have hmeas : AEStronglyMeasurable
        (fun v : ComplexUnitSphere N ↦
          ∫ A : ConcreteMatrixState N, ‖score (A, v)‖ ∂mu) sphere := by
      simpa [score] using
        hjoint.norm.prod_swap.integral_prod_right'
    exact (integrable_const B).mono' hmeas <| by
      filter_upwards [] with v
      have hnonneg : 0 ≤
          ∫ A : ConcreteMatrixState N, ‖score (A, v)‖ ∂mu :=
        integral_nonneg fun _ ↦ norm_nonneg _
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      simpa only [score, mu] using hbound v

/-- The exact order-three product-`L1` theorem that replaces the former
standalone scientific interface. -/
theorem concreteCenteredDensityScoreThreeProduct_memLp_one_of_exactH5
    (hH5 : H16ExactH5Family) {N K : ℕ}
    (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp
      (fun Av : ConcreteMatrixState N × ComplexUnitSphere N ↦
        concreteCenteredDensityScore 3 N K Av.2 Av.1) 1
      (concreteCenteredScoreProductLaw N K) := by
  rw [memLp_one_iff_integrable]
  simpa only [concreteCenteredScoreProductLaw] using
    integrable_concreteCenteredDensityScore_lower_product_of_exactH5
      hH5 hN hgap (⟨3, by omega⟩ : Fin 4)

/-- Approved A1 supplies exact H5, so the literal third score needs no
independent scientific product-integrability declaration. -/
theorem concreteCenteredDensityScoreThreeProduct_memLp_one_internal
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp
      (fun Av : ConcreteMatrixState N × ComplexUnitSphere N ↦
        concreteCenteredDensityScore 3 N K Av.2 Av.1) 1
      (concreteCenteredScoreProductLaw N K) := by
  apply concreteCenteredDensityScoreThreeProduct_memLp_one_of_exactH5
    (hN := hN) (hgap := hgap)
  intro n k hn h2nk
  exact
    friedmanMello1985_unscaledCOECornerLaw_eq_determinantDensity_of_A1
      hn h2nk

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
