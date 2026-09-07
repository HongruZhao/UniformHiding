import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16CenteredJetBasic
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CenteredLikelihoodBellCalculus
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic

/-!
# Pointwise identification of the coordinate base jets with literal scores

On the open determinant support, the moving coordinate density is locally
the time-zero density times the literal centered likelihood.  Differentiating
this local identity gives the exact base-jet/score factorization for every
order through four.  No boundary value is asserted.
-/

open MeasureTheory Filter
open scoped Topology

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

theorem h16CenteredTransportGapDeterminant_eq_concreteInverse
    {N K : ℕ} (hK : 0 < K) (v : ComplexUnitSphere N) (t : ℝ)
    (x : ComplexSymmetricCoordinates N) :
    h16CenteredTransportGapDeterminant v t x =
      concreteCOECenteredInverseDeterminant K v t
        (h16ScaledSymmetricCoordinateEmbedding N K x) := by
  unfold h16CenteredTransportGapDeterminant
    concreteCOECenteredInverseDeterminant
  dsimp only
  unfold h16ScaledSymmetricCoordinateEmbedding
  rw [unscaleCOECorner_h16ScaleCOECorner hK]
  have hmatrix :
      complexSymmetricMatrixOfCoordinates
          (h16CenteredCoordinateFlow v (-t) x) =
        transposeCongruenceFlow (concreteCenteredOrbitalDirection N v) (-t)
          (complexSymmetricMatrixOfCoordinates x) := by
    simpa only [h16CenteredCoordinateFlow] using
      (transposeCongruenceFlowCoordinates_matrix
        (concreteCenteredOrbitalDirection N v) (-t) x)
  rw [hmatrix]

theorem h16ScaledEmbedding_mem_openSupport
    {N K : ℕ} (hK : 0 < K) (x : ComplexSymmetricCoordinates N)
    (hx : coeCornerSupport (complexSymmetricMatrixOfCoordinates x)) :
    h16ScaledSymmetricCoordinateEmbedding N K x ∈
      h16ScaledCOEOpenSupport N K := by
  constructor
  · simpa only [h16ScaledSymmetricCoordinateEmbedding,
      unscaleCOECorner_h16ScaleCOECorner hK] using
      complexSymmetricMatrixOfCoordinates_isSymm x
  · simpa only [h16ScaledSymmetricCoordinateEmbedding,
      unscaleCOECorner_h16ScaleCOECorner hK] using hx

theorem h16CenteredTransportInteriorDensity_eventually_eq_probability_mul_likelihood
    {N K : ℕ} (hN : 1 ≤ N) (hK : 0 < K)
    (v : ComplexUnitSphere N) (x : ComplexSymmetricCoordinates N)
    (hx : coeCornerSupport (complexSymmetricMatrixOfCoordinates x)) :
    (fun t : ℝ ↦ h16CenteredTransportInteriorDensity N K v t x) =ᶠ[𝓝 0]
      fun t ↦ h16COECoordinateProbabilityDensity N K x *
        concreteCenteredLikelihoodCore K v t
          (h16ScaledSymmetricCoordinateEmbedding N K x) := by
  let A := h16ScaledSymmetricCoordinateEmbedding N K x
  let gap : ℝ → ℝ := fun t ↦ h16CenteredTransportGapDeterminant v t x
  have hgap_eq : ∀ t, gap t = concreteCOECenteredInverseDeterminant K v t A :=
    fun t ↦ h16CenteredTransportGapDeterminant_eq_concreteInverse hK v t x
  have hbase_eq : concreteCOEBaseDeterminant K A = gap 0 := by
    unfold concreteCOEBaseDeterminant A gap
    rw [h16ScaledSymmetricCoordinateEmbedding,
      unscaleCOECorner_h16ScaleCOECorner hK]
    unfold h16CenteredTransportGapDeterminant h16CenteredCoordinateFlow
    rw [show (-0 : ℝ) = 0 by norm_num,
      transposeCongruenceFlowCoordinates_zero]
  have hbase : 0 < gap 0 := by
    unfold gap h16CenteredTransportGapDeterminant h16CenteredCoordinateFlow
    rw [show (-0 : ℝ) = 0 by norm_num,
      transposeCongruenceFlowCoordinates_zero]
    exact (RCLike.lt_iff_re_im.mp hx.det_pos).1
  have hgap_cont : Continuous gap := by
    apply Continuous.congr
      (show Continuous (fun t : ℝ ↦
          concreteCOECenteredInverseDeterminant K v t A) by
        simp only [concreteCOECenteredInverseDeterminant]
        simp_rw [transposeCongruenceFlow_centered_eq_concreteOrbitalMatrixUpdate
          hN]
        simp only [concreteOrbitalMatrixUpdate, concreteOrbitalFactor,
          Matrix.det_apply, Matrix.sub_apply, Matrix.mul_apply,
          Matrix.conjTranspose_apply, Matrix.transpose_apply,
          Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply]
        fun_prop)
    exact fun t ↦ (hgap_eq t).symm
  have hgap_pos : ∀ᶠ t in 𝓝 0, 0 < gap t :=
    continuousAt_const.eventually_lt hgap_cont.continuousAt hbase
  have hprob : h16COECoordinateProbabilityDensity N K x =
      h16CenteredTransportInteriorDensity N K v 0 x := by
    have hsupport0 : x ∈ h16CenteredTransportSupport v 0 := by
      simpa [h16CenteredTransportSupport] using hx
    have hzero := h16CenteredTransportJet_zero_eq_probabilityDensity
      (N := N) (K := K) v 0 x
    rw [h16CenteredTransportJet, if_pos hsupport0] at hzero
    change h16CenteredTransportInteriorDensity N K v 0 x =
      h16COECoordinateProbabilityDensity N K
        (h16CenteredCoordinateFlow v (-0) x) at hzero
    simpa only [neg_zero, h16CenteredCoordinateFlow_zero] using hzero.symm
  filter_upwards [hgap_pos] with t ht
  rw [hprob]
  unfold h16CenteredTransportInteriorDensity
  change
    (h16COECoordinateRawMass N K)⁻¹.toReal *
        gap t ^ coeCornerDensityExponent N K =
      ((h16COECoordinateRawMass N K)⁻¹.toReal *
          gap 0 ^ coeCornerDensityExponent N K) *
        concreteCenteredLikelihoodCore K v t A
  unfold concreteCenteredLikelihoodCore
  rw [if_neg (hbase_eq.trans_ne hbase.ne')]
  rw [hbase_eq]
  rw [← hgap_eq t]
  calc
    (h16COECoordinateRawMass N K)⁻¹.toReal *
        gap t ^ coeCornerDensityExponent N K =
      (h16COECoordinateRawMass N K)⁻¹.toReal *
        (gap 0 * (gap t / gap 0)) ^
          coeCornerDensityExponent N K := by
            rw [mul_div_cancel₀ (gap t) hbase.ne']
    _ = (h16COECoordinateRawMass N K)⁻¹.toReal *
          gap 0 ^ coeCornerDensityExponent N K *
        (gap t / gap 0) ^ coeCornerDensityExponent N K := by
      rw [Real.mul_rpow hbase.le (div_nonneg ht.le hbase.le)]
      ring

/-- Pointwise base-jet factorization on the open support.  In particular,
the fourth identity is interior-only and makes no boundary-continuity claim. -/
theorem h16CenteredTransportJet_zero_eq_score_mul_density_pointwise
    {N K : ℕ} (hN : 1 ≤ N) (hK : 0 < K)
    (r : Fin 5) (v : ComplexUnitSphere N)
    (x : ComplexSymmetricCoordinates N)
    (hx : coeCornerSupport (complexSymmetricMatrixOfCoordinates x)) :
    h16CenteredTransportJet N K r v 0 x =
      h16ZeroExtendedConcreteCenteredDensityScore
          (r : ℕ) N K v
          (h16ScaledSymmetricCoordinateEmbedding N K x) *
        h16CenteredTransportJet N K 0 v 0 x := by
  have hsupport0 : x ∈ h16CenteredTransportSupport v 0 := by
    simpa [h16CenteredTransportSupport] using hx
  have hlocal :=
    h16CenteredTransportInteriorDensity_eventually_eq_probability_mul_likelihood
      hN hK v x hx
  have hderiv := hlocal.iteratedDeriv_eq (r : ℕ)
  rw [iteratedDeriv_const_mul_field] at hderiv
  have hscoreSupport := h16ScaledEmbedding_mem_openSupport hK x hx
  have hzero := h16CenteredTransportJet_zero_eq_probabilityDensity
    (N := N) (K := K) v 0 x
  simp only [h16CenteredTransportJet, hsupport0, if_true,
    h16ZeroExtendedConcreteCenteredDensityScore,
    Set.indicator_of_mem hscoreSupport] at ⊢ hzero
  rw [hderiv]
  rw [hzero]
  simp only [concreteCenteredDensityScore, neg_zero,
    h16CenteredCoordinateFlow_zero]
  ring

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
