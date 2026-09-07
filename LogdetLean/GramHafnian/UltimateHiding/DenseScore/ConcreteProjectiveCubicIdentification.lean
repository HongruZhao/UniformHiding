import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ProjectiveThirdTraceMoment
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ProjectiveTracePairHermitian
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ConcreteCubicNonWDefinitions
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.COESupportAlgebra
import Mathlib.Tactic

/-!
# Concrete projective cubic identification

This file connects the proved low-order projective trace moments to
the literal centered COE matrix

`S = Y - (N+1) I`.

The three projective moments of `s_v = Tr(P_v S)` are identified exactly
with the closed trace polynomials used by the cubic score estimates.  No
COE density differentiation, moment estimate, total variation, or hiding
statement occurs here.
-/

open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- The literal centered beta-prime matrix `S=Y-(N+1)I`. -/
def concreteCOECenteredMatrix (N K : ℕ) (A : ConcreteMatrixState N) :
    ConcreteMatrixState N :=
  concreteCOEY N K A - ((((N : ℝ) + 1 : ℝ) : ℂ)) • 1

/-- The literal projective scalar `s_v=Tr(P_v S)`.  On the COE support it is
real; the total definition takes the real part. -/
def concreteCenteredProjectiveTrace (N K : ℕ)
    (v : ComplexUnitSphere N) (A : ConcreteMatrixState N) : ℝ :=
  (complexProjectiveTracePair v (concreteCOECenteredMatrix N K A)).re

private theorem trace_im_eq_zero_of_isHermitian {N : ℕ}
    (A : ConcreteMatrixState N) (hA : A.IsHermitian) :
    (Matrix.trace A).im = 0 := by
  have ht := congrArg Matrix.trace hA
  rw [Matrix.trace_conjTranspose] at ht
  have hstar : star (Matrix.trace A) = Matrix.trace A := ht
  exact Complex.conj_eq_iff_im.mp hstar

theorem concreteCOECenteredMatrix_isHermitian_of_support
    {N K : ℕ} (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    (concreteCOECenteredMatrix N K A).IsHermitian := by
  have hY := concreteCOEY_isHermitian_of_support A hsupport
  have hI : (((((N : ℝ) + 1 : ℝ) : ℂ)) •
      (1 : ConcreteMatrixState N)).IsHermitian := by
    exact Matrix.isHermitian_one.smul (by simp [IsSelfAdjoint])
  exact hY.sub hI

theorem concreteCOECenteredMatrix_trace_re
    (N K : ℕ) (A : ConcreteMatrixState N) :
    (Matrix.trace (concreteCOECenteredMatrix N K A)).re =
      concreteCOECenteredMatrixTraceOne N K A := by
  simp [concreteCOECenteredMatrix, concreteCOECenteredMatrixTraceOne,
    concreteCOETraceOne, concreteRealTrace, Matrix.trace_sub,
    Matrix.trace_smul, Matrix.trace_one]
  ring

theorem concreteCOECenteredMatrix_sq_trace_re
    (N K : ℕ) (A : ConcreteMatrixState N) :
    (Matrix.trace
      (concreteCOECenteredMatrix N K A *
        concreteCOECenteredMatrix N K A)).re =
      concreteCOECenteredMatrixTraceTwo N K A := by
  let Y := concreteCOEY N K A
  let c : ℂ := (((N : ℝ) + 1 : ℝ) : ℂ)
  have hmat : (Y - c • (1 : ConcreteMatrixState N)) *
        (Y - c • (1 : ConcreteMatrixState N)) =
      Y * Y - (2 * c) • Y + (c ^ 2) • 1 := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.one_mul,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    module
  change (Matrix.trace ((Y - c • 1) * (Y - c • 1))).re = _
  rw [hmat, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul,
    Matrix.trace_smul, Matrix.trace_one]
  simp only [Complex.sub_re, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero,
    concreteCOECenteredMatrixTraceTwo, concreteCOETraceOne,
    concreteCOETraceTwo, concreteRealTrace, Y, c]
  simp only [Fintype.card_fin]
  norm_num [Complex.add_re, Complex.mul_re, pow_two]
  ring

theorem concreteCOECenteredMatrix_cube_trace_re
    (N K : ℕ) (A : ConcreteMatrixState N) :
    (Matrix.trace
      (concreteCOECenteredMatrix N K A *
        concreteCOECenteredMatrix N K A *
        concreteCOECenteredMatrix N K A)).re =
      concreteCOECenteredMatrixTraceThree N K A := by
  let Y := concreteCOEY N K A
  let c : ℂ := (((N : ℝ) + 1 : ℝ) : ℂ)
  have hmat : (Y - c • (1 : ConcreteMatrixState N)) *
        (Y - c • (1 : ConcreteMatrixState N)) *
        (Y - c • (1 : ConcreteMatrixState N)) =
      Y * Y * Y - (3 * c) • (Y * Y) + (3 * c ^ 2) • Y -
        (c ^ 3) • 1 := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.one_mul,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    module
  change (Matrix.trace ((Y - c • 1) * (Y - c • 1) * (Y - c • 1))).re = _
  rw [hmat, Matrix.trace_sub, Matrix.trace_add, Matrix.trace_sub,
    Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_one]
  simp only [Complex.sub_re, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero,
    concreteCOECenteredMatrixTraceThree, concreteCOETraceOne,
    concreteCOETraceTwo, concreteCOETraceThree, concreteRealTrace, Y, c]
  simp only [Fintype.card_fin]
  norm_num [Complex.add_re, Complex.mul_re, pow_two, pow_three]
  ring

theorem concreteCOECenteredMatrix_trace_im_eq_zero_of_support
    {N K : ℕ} (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    (Matrix.trace (concreteCOECenteredMatrix N K A)).im = 0 :=
  trace_im_eq_zero_of_isHermitian _
    (concreteCOECenteredMatrix_isHermitian_of_support A hsupport)

theorem concreteCOECenteredMatrix_sq_trace_im_eq_zero_of_support
    {N K : ℕ} (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    (Matrix.trace
      (concreteCOECenteredMatrix N K A *
        concreteCOECenteredMatrix N K A)).im = 0 := by
  apply trace_im_eq_zero_of_isHermitian
  have hS := concreteCOECenteredMatrix_isHermitian_of_support A hsupport
  rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, hS]

theorem concreteCOECenteredMatrix_cube_trace_im_eq_zero_of_support
    {N K : ℕ} (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    (Matrix.trace
      (concreteCOECenteredMatrix N K A *
        concreteCOECenteredMatrix N K A *
        concreteCOECenteredMatrix N K A)).im = 0 := by
  apply trace_im_eq_zero_of_isHermitian
  have hS := concreteCOECenteredMatrix_isHermitian_of_support A hsupport
  rw [Matrix.IsHermitian, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_mul, hS]
  simp only [Matrix.mul_assoc]

theorem integrable_concreteCenteredProjectiveTrace
    {N K : ℕ} (hN : 1 ≤ N) (A : ConcreteMatrixState N) :
    Integrable (concreteCenteredProjectiveTrace N K · A)
      (complexUnitSphereProbabilityMeasure N) := by
  change Integrable (fun v : ComplexUnitSphere N ↦
    RCLike.re (complexProjectiveTracePair v
      (concreteCOECenteredMatrix N K A))) _
  exact (integrable_complexProjectiveTracePair hN
    (concreteCOECenteredMatrix N K A)).re

theorem integral_concreteCenteredProjectiveTrace
    {N K : ℕ} (hN : 1 ≤ N) (A : ConcreteMatrixState N) :
    (∫ v : ComplexUnitSphere N,
      concreteCenteredProjectiveTrace N K v A
      ∂(complexUnitSphereProbabilityMeasure N)) =
      concreteProjectiveMeanS N K A := by
  have hint := integrable_complexProjectiveTracePair hN
    (concreteCOECenteredMatrix N K A)
  unfold concreteCenteredProjectiveTrace
  change (∫ v : ComplexUnitSphere N,
    RCLike.re (complexProjectiveTracePair v
      (concreteCOECenteredMatrix N K A))
      ∂(complexUnitSphereProbabilityMeasure N)) = _
  rw [integral_re hint, integral_complexProjectiveTracePair hN]
  change Complex.re
    (((((N : ℝ)⁻¹ : ℝ) : ℂ) *
      Matrix.trace (concreteCOECenteredMatrix N K A))) = _
  rw [Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    concreteCOECenteredMatrix_trace_re]
  unfold concreteProjectiveMeanS
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  field_simp [hNr]

theorem integrable_concreteCenteredProjectiveTrace_sq
    {N K : ℕ} (hN : 1 ≤ N) (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    Integrable (fun v : ComplexUnitSphere N ↦
      concreteCenteredProjectiveTrace N K v A ^ 2)
      (complexUnitSphereProbabilityMeasure N) := by
  have hmul := integrable_complexProjectiveTracePair_mul hN
    (concreteCOECenteredMatrix N K A) (concreteCOECenteredMatrix N K A)
  have hre := hmul.re
  have hS := concreteCOECenteredMatrix_isHermitian_of_support A hsupport
  apply hre.congr
  filter_upwards [] with v
  have him := complexProjectiveTracePair_im_eq_zero_of_isHermitian v _ hS
  change Complex.re
    (complexProjectiveTracePair v (concreteCOECenteredMatrix N K A) *
      complexProjectiveTracePair v (concreteCOECenteredMatrix N K A)) = _
  simp only [concreteCenteredProjectiveTrace, pow_two]
  rw [Complex.mul_re]
  rw [him]
  ring

theorem integral_concreteCenteredProjectiveTrace_sq
    {N K : ℕ} (hN : 1 ≤ N) (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    (∫ v : ComplexUnitSphere N,
      concreteCenteredProjectiveTrace N K v A ^ 2
      ∂(complexUnitSphereProbabilityMeasure N)) =
      concreteProjectiveMeanSSquare N K A := by
  let S := concreteCOECenteredMatrix N K A
  have hS := concreteCOECenteredMatrix_isHermitian_of_support A hsupport
  have hmul := integrable_complexProjectiveTracePair_mul hN S S
  have hfun : (fun v : ComplexUnitSphere N ↦
      concreteCenteredProjectiveTrace N K v A ^ 2) =
      fun v ↦ (complexProjectiveTracePair v S *
        complexProjectiveTracePair v S).re := by
    funext v
    have him := complexProjectiveTracePair_im_eq_zero_of_isHermitian v S hS
    simp only [concreteCenteredProjectiveTrace, S, pow_two, Complex.mul_re,
      him, mul_zero, sub_zero]
  rw [hfun]
  change (∫ v : ComplexUnitSphere N,
    RCLike.re (complexProjectiveTracePair v S *
      complexProjectiveTracePair v S)
      ∂(complexUnitSphereProbabilityMeasure N)) = _
  rw [integral_re hmul, integral_complexProjectiveTracePair_mul hN]
  change Complex.re
    (((((N : ℝ) * ((N : ℝ) + 1))⁻¹ : ℝ) : ℂ) *
      (Matrix.trace S * Matrix.trace S + Matrix.trace (S * S))) = _
  rw [Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.add_re, concreteCOECenteredMatrix_trace_re,
    concreteCOECenteredMatrix_sq_trace_re]
  unfold concreteProjectiveMeanSSquare
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hNp : (N : ℝ) + 1 ≠ 0 := by positivity
  have htRe := concreteCOECenteredMatrix_trace_re N K A
  have htIm :=
    concreteCOECenteredMatrix_trace_im_eq_zero_of_support A hsupport
  have hsqRe : (Matrix.trace S ^ 2).re =
      concreteCOECenteredMatrixTraceOne N K A ^ 2 := by
    dsimp only [S]
    rw [pow_two, Complex.mul_re, htRe, htIm]
    ring
  have htTwoRe := concreteCOECenteredMatrix_sq_trace_re N K A
  field_simp [hNr, hNp]
  rw [hsqRe]
  rw [show (Matrix.trace (S * S)).re =
      concreteCOECenteredMatrixTraceTwo N K A by
    simpa only [S] using htTwoRe]

theorem integrable_concreteCenteredProjectiveTrace_cube
    {N K : ℕ} (hN : 1 ≤ N) (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    Integrable (fun v : ComplexUnitSphere N ↦
      concreteCenteredProjectiveTrace N K v A ^ 3)
      (complexUnitSphereProbabilityMeasure N) := by
  have hcub := integrable_complexProjectiveTracePair_cube hN
    (concreteCOECenteredMatrix N K A)
  have hre := hcub.re
  have hS := concreteCOECenteredMatrix_isHermitian_of_support A hsupport
  apply hre.congr
  filter_upwards [] with v
  have him := complexProjectiveTracePair_im_eq_zero_of_isHermitian v _ hS
  change Complex.re
    (complexProjectiveTracePair v (concreteCOECenteredMatrix N K A) ^ 3) = _
  simp only [concreteCenteredProjectiveTrace, pow_three]
  rw [Complex.mul_re, Complex.mul_re, him]
  ring

/-- Exact concrete cubic contraction from the internally proved order-three
projective tensor identity. -/
theorem integral_concreteCenteredProjectiveTrace_cube
    {N K : ℕ} (hN : 1 ≤ N) (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    (∫ v : ComplexUnitSphere N,
      concreteCenteredProjectiveTrace N K v A ^ 3
      ∂(complexUnitSphereProbabilityMeasure N)) =
      concreteProjectiveMeanSCube N K A := by
  let S := concreteCOECenteredMatrix N K A
  have hS := concreteCOECenteredMatrix_isHermitian_of_support A hsupport
  have hcub := integrable_complexProjectiveTracePair_cube hN S
  have hfun : (fun v : ComplexUnitSphere N ↦
      concreteCenteredProjectiveTrace N K v A ^ 3) =
      fun v ↦ (complexProjectiveTracePair v S ^ 3).re := by
    funext v
    have him := complexProjectiveTracePair_im_eq_zero_of_isHermitian v S hS
    change _ = (complexProjectiveTracePair v S ^ 3).re
    simp only [concreteCenteredProjectiveTrace, S, pow_three]
    rw [Complex.mul_re, Complex.mul_re, him]
    ring
  rw [hfun]
  change (∫ v : ComplexUnitSphere N,
    RCLike.re (complexProjectiveTracePair v S ^ 3)
      ∂(complexUnitSphereProbabilityMeasure N)) = _
  rw [integral_re hcub, integral_complexProjectiveTracePair_cube hN]
  change Complex.re
    (((((N : ℝ) * ((N : ℝ) + 1) * ((N : ℝ) + 2))⁻¹ : ℝ) : ℂ) *
      (Matrix.trace S ^ 3 +
        3 * Matrix.trace S * Matrix.trace (S * S) +
        2 * Matrix.trace (S * S * S))) = _
  rw [Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.add_re, concreteCOECenteredMatrix_trace_re,
    concreteCOECenteredMatrix_sq_trace_re,
    concreteCOECenteredMatrix_cube_trace_re]
  unfold concreteProjectiveMeanSCube
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hNpOne : (N : ℝ) + 1 ≠ 0 := by positivity
  have hNpTwo : (N : ℝ) + 2 ≠ 0 := by positivity
  have htRe := concreteCOECenteredMatrix_trace_re N K A
  have htIm :=
    concreteCOECenteredMatrix_trace_im_eq_zero_of_support A hsupport
  have htTwoRe := concreteCOECenteredMatrix_sq_trace_re N K A
  have htTwoIm :=
    concreteCOECenteredMatrix_sq_trace_im_eq_zero_of_support A hsupport
  have htThreeRe := concreteCOECenteredMatrix_cube_trace_re N K A
  have hcubeRe : (Matrix.trace S ^ 3).re =
      concreteCOECenteredMatrixTraceOne N K A ^ 3 := by
    dsimp only [S]
    simp only [pow_three, Complex.mul_re, htRe, htIm]
    ring
  have hcrossRe : (Matrix.trace S * 3 * Matrix.trace (S * S)).re =
      3 * concreteCOECenteredMatrixTraceOne N K A *
        concreteCOECenteredMatrixTraceTwo N K A := by
    dsimp only [S]
    rw [Complex.mul_re, Complex.mul_re]
    norm_num
    rw [htRe, htIm, htTwoRe, htTwoIm]
    ring
  have hthreeRe : (2 * Matrix.trace (S * S * S)).re =
      2 * concreteCOECenteredMatrixTraceThree N K A := by
    dsimp only [S]
    simp only [Complex.mul_re, htThreeRe]
    norm_num
  field_simp [hNr, hNpOne, hNpTwo]
  rw [hcubeRe, hcrossRe, hthreeRe]
  ring

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
