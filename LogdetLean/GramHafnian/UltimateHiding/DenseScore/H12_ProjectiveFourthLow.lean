import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ProjectiveFourthTraceMoment
import Mathlib.Tactic

/-!
# Low Hermitian projective fourth-moment adapter for H12

This file converts the already proved complex projective fourth moment to its
real Hermitian form.  It intentionally sits below the H14 separated-score
machinery, so the A1--A4 H12 endpoint can be imported by low score consumers
without a cycle.
-/

open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

private theorem complexRankOneProjection_isHermitian_h12_low
    {N : ℕ} (v : ComplexUnitSphere N) :
    (complexRankOneProjection v).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  simp [Matrix.conjTranspose_apply, complexRankOneProjection]
  ring

/-- A projective quadratic form of a Hermitian matrix is real. -/
theorem complexProjectiveTracePair_im_eq_zero_of_isHermitian_h12_low
    {N : ℕ} (v : ComplexUnitSphere N) (A : ConcreteMatrixState N)
    (hA : A.IsHermitian) :
    (complexProjectiveTracePair v A).im = 0 := by
  rw [complexProjectiveTracePair_eq_trace]
  apply Complex.conj_eq_iff_im.mp
  calc
    star (Matrix.trace (complexRankOneProjection v * A)) =
        Matrix.trace ((complexRankOneProjection v * A).conjTranspose) := by
          rw [Matrix.trace_conjTranspose]
    _ = Matrix.trace (A * complexRankOneProjection v) := by
          rw [Matrix.conjTranspose_mul, hA,
            complexRankOneProjection_isHermitian_h12_low]
    _ = Matrix.trace (complexRankOneProjection v * A) :=
          Matrix.trace_mul_comm _ _

private theorem trace_im_eq_zero_of_isHermitian_h12_low
    {N : ℕ} {A : ConcreteMatrixState N} (hA : A.IsHermitian) :
    (Matrix.trace A).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  have ht := congrArg Matrix.trace hA.eq
  rw [Matrix.trace_conjTranspose] at ht
  exact ht

/-- Real form of the exact complex-projective fourth trace moment. -/
theorem integral_complexProjectiveTracePair_re_fourth_eq_h12_low
    {N : ℕ} (hN : 1 ≤ N) (A : ConcreteMatrixState N)
    (hA : A.IsHermitian) :
    (∫ v : ComplexUnitSphere N,
      (complexProjectiveTracePair v A).re ^ 4
        ∂(complexUnitSphereProbabilityMeasure N)) =
      ((N : ℝ) * ((N : ℝ) + 1) * ((N : ℝ) + 2) *
        ((N : ℝ) + 3))⁻¹ *
        ((Matrix.trace A).re ^ 4 +
          6 * ((Matrix.trace A).re ^ 2 * (Matrix.trace (A * A)).re) +
          3 * (Matrix.trace (A * A)).re ^ 2 +
          8 * ((Matrix.trace A).re * (Matrix.trace (A * A * A)).re) +
          6 * (Matrix.trace (A * A * A * A)).re) := by
  have hint := integrable_complexProjectiveTracePair_fourth hN A
  have htr1 : (Matrix.trace A).im = 0 :=
    trace_im_eq_zero_of_isHermitian_h12_low hA
  have hA2 : (A * A).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, hA]
  have hA3 : (A * A * A).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_mul, hA]
    simp only [Matrix.mul_assoc]
  have hA4 : (A * A * A * A).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hA]
    simp only [Matrix.mul_assoc]
  have htr2 : (Matrix.trace (A * A)).im = 0 :=
    trace_im_eq_zero_of_isHermitian_h12_low hA2
  have htr3 : (Matrix.trace (A * A * A)).im = 0 :=
    trace_im_eq_zero_of_isHermitian_h12_low hA3
  have htr4 : (Matrix.trace (A * A * A * A)).im = 0 :=
    trace_im_eq_zero_of_isHermitian_h12_low hA4
  rw [show (fun v : ComplexUnitSphere N ↦
      (complexProjectiveTracePair v A).re ^ 4) =
      fun v ↦ (complexProjectiveTracePair v A ^ 4).re by
    funext v
    have him :=
      complexProjectiveTracePair_im_eq_zero_of_isHermitian_h12_low v A hA
    simp only [pow_succ, pow_zero, one_mul, Complex.mul_re, him,
      mul_zero, sub_zero]]
  change (∫ v : ComplexUnitSphere N,
      RCLike.re (complexProjectiveTracePair v A ^ 4)
        ∂(complexUnitSphereProbabilityMeasure N)) = _
  rw [integral_re hint, integral_complexProjectiveTracePair_fourth hN]
  let d : ℝ := ((N : ℝ) * ((N : ℝ) + 1) * ((N : ℝ) + 2) *
    ((N : ℝ) + 3))⁻¹
  change ((((d : ℝ) : ℂ) *
      (Matrix.trace A ^ 4 +
        6 * (Matrix.trace A ^ 2 * Matrix.trace (A * A)) +
        3 * Matrix.trace (A * A) ^ 2 +
        8 * (Matrix.trace A * Matrix.trace (A * A * A)) +
        6 * Matrix.trace (A * A * A * A))).re) =
    d * ((Matrix.trace A).re ^ 4 +
      6 * ((Matrix.trace A).re ^ 2 * (Matrix.trace (A * A)).re) +
      3 * (Matrix.trace (A * A)).re ^ 2 +
      8 * ((Matrix.trace A).re * (Matrix.trace (A * A * A)).re) +
      6 * (Matrix.trace (A * A * A * A)).re)
  have hEq : (((d : ℝ) : ℂ) *
      (Matrix.trace A ^ 4 +
        6 * (Matrix.trace A ^ 2 * Matrix.trace (A * A)) +
        3 * Matrix.trace (A * A) ^ 2 +
        8 * (Matrix.trace A * Matrix.trace (A * A * A)) +
        6 * Matrix.trace (A * A * A * A))) =
      ((d * ((Matrix.trace A).re ^ 4 +
        6 * ((Matrix.trace A).re ^ 2 * (Matrix.trace (A * A)).re) +
        3 * (Matrix.trace (A * A)).re ^ 2 +
        8 * ((Matrix.trace A).re * (Matrix.trace (A * A * A)).re) +
        6 * (Matrix.trace (A * A * A * A)).re) : ℝ) : ℂ) := by
    apply Complex.ext
    · norm_num [pow_succ, Complex.mul_re, Complex.add_re,
        htr1, htr2, htr3, htr4]
    · norm_num [pow_succ, Complex.mul_im, Complex.add_im,
        htr1, htr2, htr3, htr4]
  rw [hEq]
  exact Complex.ofReal_re _

end


end LogdetLean.GramHafnian.UltimateHiding.DenseScore
