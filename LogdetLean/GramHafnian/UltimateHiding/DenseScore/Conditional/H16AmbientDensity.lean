import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ConcreteCenteredLikelihood
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.FriedmanMelloSupportFromDensity
import Mathlib.MeasureTheory.Measure.WithDensityFinite
import Mathlib.Tactic

/-!
# H16: an explicit common ambient determinant density

This module works strictly below the event-differentiation layer.  It defines
flat independent complex-symmetric coordinates, the scaled coordinate
embedding, and the zero-extended determinant weights for the time-zero COE
law and for the inverse centered flow.

The exact H5 density identity is always a theorem parameter.  No H16 event
derivative declaration (centered or uncentered) is imported or used.  The
last theorem isolates the remaining geometric input as preservation of the
explicit ambient coordinate measure by the centered congruence flow.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.CurrentPRL

/-! ## Exact H5 parameter and scaled coordinates -/

/-- Exact H5, stated locally so this density module remains independent of
the conditional event-derivative module. -/
abbrev H16AmbientExactH5Family : Prop :=
  ∀ {n k : ℕ}, 1 ≤ n → 2 * n ≤ k →
    concreteUnscaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily n k =
      coeCornerDeterminantDensityProbabilityMeasure n k

/-- Multiplication by the paper scale `sqrt K`. -/
def h16ScaleCOECorner {N : ℕ} (K : ℕ) (C : ConcreteMatrixState N) :
    ConcreteMatrixState N :=
  (((Real.sqrt (K : ℝ) : ℝ) : ℂ)) • C

theorem measurable_h16ScaleCOECorner (N K : ℕ) :
    Measurable (h16ScaleCOECorner (N := N) K) := by
  refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
  simp only [h16ScaleCOECorner, Matrix.smul_apply]
  fun_prop

theorem unscaleCOECorner_h16ScaleCOECorner {N K : ℕ}
    (hK : 0 < K) (C : ConcreteMatrixState N) :
    unscaleCOECorner K (h16ScaleCOECorner K C) = C := by
  have hsqrtR : Real.sqrt (K : ℝ) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast hK))
  have hsqrtC : ((Real.sqrt (K : ℝ) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hsqrtR
  unfold unscaleCOECorner h16ScaleCOECorner
  rw [smul_smul, Complex.ofReal_inv, inv_mul_cancel₀ hsqrtC, one_smul]

theorem h16ScaleCOECorner_unscaleCOECorner {N K : ℕ}
    (hK : 0 < K) (A : ConcreteMatrixState N) :
    h16ScaleCOECorner K (unscaleCOECorner K A) = A := by
  have hsqrtR : Real.sqrt (K : ℝ) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast hK))
  have hsqrtC : ((Real.sqrt (K : ℝ) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hsqrtR
  unfold unscaleCOECorner h16ScaleCOECorner
  rw [smul_smul, Complex.ofReal_inv, mul_inv_cancel₀ hsqrtC, one_smul]

/-- Independent symmetric coordinates embedded at the paper scale. -/
def h16ScaledSymmetricCoordinateEmbedding (N K : ℕ) :
    ComplexSymmetricCoordinates N → ConcreteMatrixState N :=
  fun x ↦ h16ScaleCOECorner K (complexSymmetricMatrixOfCoordinates x)

theorem measurable_h16ScaledSymmetricCoordinateEmbedding (N K : ℕ) :
    Measurable (h16ScaledSymmetricCoordinateEmbedding N K) :=
  (measurable_h16ScaleCOECorner N K).comp
    (measurable_complexSymmetricMatrixOfCoordinates N)

/-- The flat symmetric-coordinate measure, pushed to paper-scaled matrices. -/
def h16ScaledSymmetricCoordinateVolume (N K : ℕ) :
    Measure (ConcreteMatrixState N) :=
  Measure.map (h16ScaledSymmetricCoordinateEmbedding N K)
    (complexSymmetricCoordinateVolume N)

/-! ## Zero-extended determinant weights -/

/-- The unscaled determinant power, extended by zero outside the open matrix
ball.  It is a real-valued version of `coeCornerDeterminantWeight`. -/
def h16ZeroExtendedDeterminantWeightReal (N K : ℕ)
    (C : ConcreteMatrixState N) : ℝ := by
  classical
  exact if coeCornerSupport C then
    Real.rpow (Matrix.det (1 - C.conjTranspose * C)).re
      (coeCornerDensityExponent N K)
  else 0

theorem h16ZeroExtendedDeterminantWeightReal_nonneg (N K : ℕ)
    (C : ConcreteMatrixState N) :
    0 ≤ h16ZeroExtendedDeterminantWeightReal N K C := by
  unfold h16ZeroExtendedDeterminantWeightReal
  split_ifs with hsupport
  · exact Real.rpow_nonneg
      ((RCLike.lt_iff_re_im.mp hsupport.det_pos).1.le) _
  · exact le_rfl

theorem measurable_h16ZeroExtendedDeterminantWeightReal (N K : ℕ) :
    Measurable (h16ZeroExtendedDeterminantWeightReal N K) := by
  letI : OpensMeasurableSpace (ConcreteMatrixState N) :=
    Pi.opensMeasurableSpace
  have hden : Continuous (fun C : ConcreteMatrixState N ↦
      1 - C.conjTranspose * C) :=
    continuous_const.sub
      (continuous_id.matrix_conjTranspose.matrix_mul continuous_id)
  have hdetComplex : Measurable (fun C : ConcreteMatrixState N ↦
      Matrix.det (1 - C.conjTranspose * C)) :=
    hden.matrix_det.measurable
  have hdet : Measurable (fun C : ConcreteMatrixState N ↦
      (Matrix.det (1 - C.conjTranspose * C)).re) :=
    Complex.measurable_re.comp hdetComplex
  have hrpow : Measurable (fun z : ℝ ↦
      Real.rpow z (coeCornerDensityExponent N K)) := by
    refine measurable_of_continuousOn_compl_singleton 0 ?_
    exact continuousOn_id.rpow_const fun z hz ↦
      Or.inl (by simpa using hz)
  unfold h16ZeroExtendedDeterminantWeightReal
  exact Measurable.ite (measurableSet_coeCornerSupport N)
    (hrpow.comp hdet) measurable_const

/-- The time-zero determinant weight on paper-scaled matrices. -/
def h16ScaledZeroExtendedDeterminantWeightReal (N K : ℕ)
    (A : ConcreteMatrixState N) : ℝ :=
  h16ZeroExtendedDeterminantWeightReal N K (unscaleCOECorner K A)

theorem h16ScaledZeroExtendedDeterminantWeightReal_nonneg (N K : ℕ)
    (A : ConcreteMatrixState N) :
    0 ≤ h16ScaledZeroExtendedDeterminantWeightReal N K A :=
  h16ZeroExtendedDeterminantWeightReal_nonneg N K _

theorem measurable_h16ScaledZeroExtendedDeterminantWeightReal (N K : ℕ) :
    Measurable (h16ScaledZeroExtendedDeterminantWeightReal N K) :=
  (measurable_h16ZeroExtendedDeterminantWeightReal N K).comp
    (measurable_unscaleCOECorner N K)

/-- The time-zero determinant weight as the nonnegative density required by
`Measure.withDensity`. -/
def h16ScaledZeroExtendedDeterminantWeight (N K : ℕ)
    (A : ConcreteMatrixState N) : ℝ≥0 :=
  ⟨h16ScaledZeroExtendedDeterminantWeightReal N K A,
    h16ScaledZeroExtendedDeterminantWeightReal_nonneg N K A⟩

theorem measurable_h16ScaledZeroExtendedDeterminantWeight (N K : ℕ) :
    Measurable (h16ScaledZeroExtendedDeterminantWeight N K) := by
  apply measurable_coe_nnreal_real_iff.mp
  exact measurable_h16ScaledZeroExtendedDeterminantWeightReal N K

/-- Zero-extended determinant weight evaluated at the inverse centered flow.
This is the correct common-ambient moving weight; it remains meaningful when
the support crosses a fixed target matrix. -/
def h16CenteredInverseZeroExtendedDeterminantWeightReal {N : ℕ}
    (K : ℕ) (v : ComplexUnitSphere N) (t : ℝ)
    (A : ConcreteMatrixState N) : ℝ :=
  h16ScaledZeroExtendedDeterminantWeightReal N K <|
    transposeCongruenceFlow
      (concreteCenteredOrbitalDirection N v) (-t) A

theorem h16CenteredInverseZeroExtendedDeterminantWeightReal_nonneg
    {N K : ℕ} (v : ComplexUnitSphere N) (t : ℝ)
    (A : ConcreteMatrixState N) :
    0 ≤ h16CenteredInverseZeroExtendedDeterminantWeightReal K v t A :=
  h16ScaledZeroExtendedDeterminantWeightReal_nonneg N K _

theorem measurable_h16CenteredInverseZeroExtendedDeterminantWeightReal
    {N K : ℕ} (v : ComplexUnitSphere N) (t : ℝ) :
    Measurable (h16CenteredInverseZeroExtendedDeterminantWeightReal K v t) :=
  (measurable_h16ScaledZeroExtendedDeterminantWeightReal N K).comp
    (measurable_transposeCongruence _)

/-- Nonnegative version of the inverse-flow ambient weight. -/
def h16CenteredInverseZeroExtendedDeterminantWeight {N : ℕ}
    (K : ℕ) (v : ComplexUnitSphere N) (t : ℝ)
    (A : ConcreteMatrixState N) : ℝ≥0 :=
  ⟨h16CenteredInverseZeroExtendedDeterminantWeightReal K v t A,
    h16CenteredInverseZeroExtendedDeterminantWeightReal_nonneg v t A⟩

theorem measurable_h16CenteredInverseZeroExtendedDeterminantWeight
    {N K : ℕ} (v : ComplexUnitSphere N) (t : ℝ) :
    Measurable (h16CenteredInverseZeroExtendedDeterminantWeight K v t) := by
  apply measurable_coe_nnreal_real_iff.mp
  exact measurable_h16CenteredInverseZeroExtendedDeterminantWeightReal v t

/-- Pulling the inverse-flow weight forward by the same flow recovers the
time-zero weight pointwise. -/
@[simp]
theorem h16CenteredInverseZeroExtendedDeterminantWeightReal_flow
    {N K : ℕ} (v : ComplexUnitSphere N) (t : ℝ)
    (A : ConcreteMatrixState N) :
    h16CenteredInverseZeroExtendedDeterminantWeightReal K v t
        (transposeCongruenceFlow
          (concreteCenteredOrbitalDirection N v) t A) =
      h16ScaledZeroExtendedDeterminantWeightReal N K A := by
  unfold h16CenteredInverseZeroExtendedDeterminantWeightReal
  rw [transposeCongruenceFlow_neg_left]

@[simp]
theorem h16CenteredInverseZeroExtendedDeterminantWeight_flow
    {N K : ℕ} (v : ComplexUnitSphere N) (t : ℝ)
    (A : ConcreteMatrixState N) :
    h16CenteredInverseZeroExtendedDeterminantWeight K v t
        (transposeCongruenceFlow
          (concreteCenteredOrbitalDirection N v) t A) =
      h16ScaledZeroExtendedDeterminantWeight N K A := by
  apply NNReal.eq
  exact h16CenteredInverseZeroExtendedDeterminantWeightReal_flow v t A

@[simp] theorem h16CenteredInverseZeroExtendedDeterminantWeightReal_zero
    {N K : ℕ} (v : ComplexUnitSphere N) (A : ConcreteMatrixState N) :
    h16CenteredInverseZeroExtendedDeterminantWeightReal K v 0 A =
      h16ScaledZeroExtendedDeterminantWeightReal N K A := by
  simp [h16CenteredInverseZeroExtendedDeterminantWeightReal]

@[simp] theorem h16CenteredInverseZeroExtendedDeterminantWeight_zero
    {N K : ℕ} (v : ComplexUnitSphere N) (A : ConcreteMatrixState N) :
    h16CenteredInverseZeroExtendedDeterminantWeight K v 0 A =
      h16ScaledZeroExtendedDeterminantWeight N K A := by
  apply NNReal.eq
  exact h16CenteredInverseZeroExtendedDeterminantWeightReal_zero v A

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
