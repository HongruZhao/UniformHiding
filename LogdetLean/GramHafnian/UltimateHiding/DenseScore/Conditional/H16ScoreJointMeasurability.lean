import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16ScorePointwiseIdentification
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16DownstreamZeroExtEnvelopeFromWeakFacts
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# Joint measurability of the literal zero-extended scores

The jointly measurable coordinate jets provide a measurable quotient
representative for the literal scores.  The pointwise interior factorization
identifies that quotient on the almost-sure scaled COE support supplied by
exact H5.  This removes joint score measurability as a downstream premise.
-/

open MeasureTheory Filter
open scoped ENNReal

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.LocalAnticoncentration

theorem h16COECoordinateProbabilityDensity_pos_of_exactH5
    (hH5 : H16ExactH5Family) {N K : ℕ}
    (hN : 1 ≤ N) (h2NK : 2 * N ≤ K)
    (x : ComplexSymmetricCoordinates N)
    (hx : coeCornerSupport (complexSymmetricMatrixOfCoordinates x)) :
    0 < h16COECoordinateProbabilityDensity N K x := by
  have hmass0 : h16COECoordinateRawMass N K ≠ 0 :=
    h16COECoordinateRawMass_ne_zero_of_exactH5 hH5 hN h2NK
  have hmassTop : h16COECoordinateRawMass N K ≠ ∞ :=
    h16COECoordinateRawMass_ne_top_of_exactH5 hH5 hN h2NK
  have hinvPos : 0 < (h16COECoordinateRawMass N K)⁻¹.toReal :=
    ENNReal.toReal_pos
      (ENNReal.inv_ne_zero.mpr hmassTop)
      (ENNReal.inv_ne_top.mpr hmass0)
  have hgap : 0 < h16COECoordinateGapDeterminant N x :=
    h16COECoordinateGapDeterminant_pos hx
  have hrpow : 0 <
      (h16COECoordinateGapDeterminant N x) ^
        coeCornerDensityExponent N K :=
    Real.rpow_pos_of_pos hgap _
  have hweight :
      (coeCornerDeterminantWeight N K x).toReal =
        (h16COECoordinateGapDeterminant N x) ^
          coeCornerDensityExponent N K := by
    unfold coeCornerDeterminantWeight
    dsimp only
    rw [if_pos hx]
    have hnonneg : 0 ≤
        Real.rpow
          (Matrix.det
            (1 - (complexSymmetricMatrixOfCoordinates x).conjTranspose *
              complexSymmetricMatrixOfCoordinates x)).re
          (coeCornerDensityExponent N K) :=
      Real.rpow_nonneg
      (show 0 ≤
          (Matrix.det
            (1 - (complexSymmetricMatrixOfCoordinates x).conjTranspose *
              complexSymmetricMatrixOfCoordinates x)).re by
        exact (RCLike.lt_iff_re_im.mp hx.det_pos).1.le) _
    rw [ENNReal.toReal_ofReal hnonneg]
    rfl
  unfold h16COECoordinateProbabilityDensity
  rw [hweight]
  exact mul_pos hinvPos hrpow

def h16ScoreCoordinateOfMatrix {N : ℕ} (K : ℕ)
    (A : ConcreteMatrixState N) : ComplexSymmetricCoordinates N :=
  complexSymmetricCoordinatesOfMatrix (unscaleCOECorner K A)

def h16CenteredTransportJetScoreCoordinate
    (r : Fin 5) (N K : ℕ) :
    ConcreteMatrixState N × ComplexUnitSphere N → ℝ :=
  (fun p : (ComplexUnitSphere N × ℝ) × ComplexSymmetricCoordinates N ↦
      h16CenteredTransportJet N K r p.1.1 p.1.2 p.2) ∘
    fun Av ↦ ((Av.2, (0 : ℝ)), h16ScoreCoordinateOfMatrix K Av.1)

def h16ZeroExtendedScoreMeasurableProxy
    (r : Fin 5) (N K : ℕ) :
    ConcreteMatrixState N × ComplexUnitSphere N → ℝ := by
  classical
  exact fun Av ↦ if coeCornerSupport (unscaleCOECorner K Av.1) then
    h16CenteredTransportJetScoreCoordinate r N K Av /
      h16CenteredTransportJetScoreCoordinate 0 N K Av
  else 0

theorem measurable_h16ScoreCoordinateOfMatrix (N K : ℕ) :
    Measurable (h16ScoreCoordinateOfMatrix (N := N) K) :=
  (measurable_complexSymmetricCoordinatesOfMatrix N).comp
    (measurable_unscaleCOECorner N K)

theorem measurable_h16DirectionZeroParameter (N : ℕ) :
    Measurable
      (fun Av : ConcreteMatrixState N × ComplexUnitSphere N ↦
        (Av.2, (0 : ℝ))) :=
  measurable_snd.prodMk measurable_const

theorem measurable_h16ScoreCoordinateOnProduct (N K : ℕ) :
    Measurable
      (fun Av : ConcreteMatrixState N × ComplexUnitSphere N ↦
        h16ScoreCoordinateOfMatrix K Av.1) :=
  (measurable_h16ScoreCoordinateOfMatrix N K).comp measurable_fst

theorem measurable_h16ScoreJetParameterMap (N K : ℕ) :
    Measurable
      (fun Av : ConcreteMatrixState N × ComplexUnitSphere N ↦
        ((Av.2, (0 : ℝ)), h16ScoreCoordinateOfMatrix K Av.1)) :=
  (measurable_h16DirectionZeroParameter N).prodMk
    (measurable_h16ScoreCoordinateOnProduct N K)

set_option maxHeartbeats 500000 in
theorem measurable_h16CenteredTransportJet_scoreCoordinate
    {N K : ℕ} {hN : 1 ≤ N} {hboundary : 2 * N + 8 ≤ K}
    (W : COECenteredOrderFourWeakGeneratorFacts N K hN hboundary)
    (r : Fin 5) :
    Measurable (h16CenteredTransportJetScoreCoordinate r N K) := by
  unfold h16CenteredTransportJetScoreCoordinate
  exact (W.jet_joint_measurable r).comp
    (measurable_h16ScoreJetParameterMap N K)

theorem measurableSet_h16ScaledMatrix_openCOESupport (N K : ℕ) :
    MeasurableSet
      {A : ConcreteMatrixState N | coeCornerSupport (unscaleCOECorner K A)} :=
  (measurableSet_coeCornerSupport N).preimage
    (measurable_unscaleCOECorner N K)

set_option maxHeartbeats 350000 in
theorem measurable_h16ZeroExtendedScoreMeasurableProxy
    {N K : ℕ} {hN : 1 ≤ N} {hboundary : 2 * N + 8 ≤ K}
    (W : COECenteredOrderFourWeakGeneratorFacts N K hN hboundary)
    (r : Fin 5) :
    Measurable (h16ZeroExtendedScoreMeasurableProxy r N K) := by
  classical
  unfold h16ZeroExtendedScoreMeasurableProxy
  exact Measurable.ite
    ((measurableSet_h16ScaledMatrix_openCOESupport N K).preimage
      measurable_fst)
    ((measurable_h16CenteredTransportJet_scoreCoordinate W r).div
      (measurable_h16CenteredTransportJet_scoreCoordinate W 0))
    measurable_const

set_option maxHeartbeats 750000 in
theorem h16ZeroExtendedScore_ae_eq_measurableProxy
    (hH5 : H16ExactH5Family) {N K : ℕ}
    {hN : 1 ≤ N} {hboundary : 2 * N + 8 ≤ K}
    (W : COECenteredOrderFourWeakGeneratorFacts N K hN hboundary)
    (r : Fin 5) :
    (fun Av : ConcreteMatrixState N × ComplexUnitSphere N ↦
      h16ZeroExtendedConcreteCenteredDensityScore
        (r : ℕ) N K Av.2 Av.1) =ᵐ[
      (concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K).prod
        (complexUnitSphereProbabilityMeasure N)]
      h16ZeroExtendedScoreMeasurableProxy r N K := by
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
    h16CenteredTransportJet_zero_eq_score_mul_density_pointwise
      hN hK r Av.2 x hx
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
  change h16ZeroExtendedConcreteCenteredDensityScore
      (r : ℕ) N K Av.2 Av.1 =
    h16ZeroExtendedScoreMeasurableProxy r N K Av
  simp only [h16ZeroExtendedScoreMeasurableProxy,
    h16CenteredTransportJetScoreCoordinate, Function.comp_apply,
    hAv.2, if_true]
  change h16ZeroExtendedConcreteCenteredDensityScore
      (r : ℕ) N K Av.2 Av.1 =
    h16CenteredTransportJet N K r Av.2 0 x /
      h16CenteredTransportJet N K 0 Av.2 0 x
  rw [hpoint]
  exact (mul_div_cancel_right₀ _ hzeroNe).symm

/-- The literal zero-extended score is jointly a.e. strongly measurable on
the actual scaled-law/projective product. -/
theorem aestronglyMeasurable_h16ZeroExtendedScore_joint_of_weakFacts
    (hH5 : H16ExactH5Family) {N K : ℕ}
    {hN : 1 ≤ N} {hboundary : 2 * N + 8 ≤ K}
    (W : COECenteredOrderFourWeakGeneratorFacts N K hN hboundary)
    (r : Fin 5) :
    AEStronglyMeasurable
      (fun Av : ConcreteMatrixState N × ComplexUnitSphere N ↦
        h16ZeroExtendedConcreteCenteredDensityScore
          (r : ℕ) N K Av.2 Av.1)
      ((concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K).prod
        (complexUnitSphereProbabilityMeasure N)) := by
  exact
    (measurable_h16ZeroExtendedScoreMeasurableProxy W r).aestronglyMeasurable.congr
      (h16ZeroExtendedScore_ae_eq_measurableProxy hH5 W r).symm

/-- Universally quantified joint-measurability family, now derived rather
than assumed. -/
theorem h16ZeroExtendedScoreJointAEStrongMeasurability_of_weakFacts
    (hH5 : H16ExactH5Family)
    (W : ∀ {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K),
      COECenteredOrderFourWeakGeneratorFacts N K hN hboundary) :
    H16ZeroExtendedScoreJointAEStrongMeasurabilityFamily := by
  intro N K hN hboundary r
  exact aestronglyMeasurable_h16ZeroExtendedScore_joint_of_weakFacts
    hH5 (W hN hboundary) r

/-- Exact H5 and corrected weak facts alone now discharge U07's entire
compact zero-extension envelope input. -/
theorem h16DownstreamCompactZeroExtL1Envelope_of_weakFacts_exactH5
    (hH5 : H16ExactH5Family)
    (W : ∀ {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K),
      COECenteredOrderFourWeakGeneratorFacts N K hN hboundary) :
    H16DownstreamCompactZeroExtL1EnvelopeContract :=
  h16DownstreamCompactZeroExtL1Envelope_of_weakFacts hH5 W
    (h16ZeroExtendedScoreJointAEStrongMeasurability_of_weakFacts hH5 W)

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
