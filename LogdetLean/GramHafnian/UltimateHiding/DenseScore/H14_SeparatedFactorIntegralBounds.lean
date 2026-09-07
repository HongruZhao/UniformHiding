import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H14_CenteredEllTwoProjectiveContraction
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ProjectiveTracePairHermitian
import Mathlib.Tactic

/-!
# Separated finite-projective second-moment bounds for H14

This module is strictly below the literal H14 endpoint.  It proves the two
fixed-matrix sphere-integral inequalities isolated in
`H14CenteredEllTwoSeparatedFactorIntegralBoundsContract`.  No beta-prime or
radial law is used here.
-/

open scoped BigOperators ComplexConjugate ComplexOrder InnerProductSpace
open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open Matrix
open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep

set_option maxHeartbeats 1800000

private theorem trace_im_eq_zero_of_isHermitian_h14_bounds
    {N : ℕ} {A : ConcreteMatrixState N} (hA : A.IsHermitian) :
    (Matrix.trace A).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  have ht := congrArg Matrix.trace hA.eq
  rw [Matrix.trace_conjTranspose] at ht
  exact ht

theorem complexProjectiveTracePair_eq_star_dotProduct_mulVec_h14
    {N : ℕ} (v : ComplexUnitSphere N) (A : ConcreteMatrixState N) :
    complexProjectiveTracePair v A =
      star (fun i : Fin N ↦ v.1 i) ⬝ᵥ (A *ᵥ fun i ↦ v.1 i) := by
  unfold complexProjectiveTracePair complexRankOneProjection
    Matrix.mulVec dotProduct
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Pi.star_apply]
  ring

theorem complexProjectiveTracePair_re_nonneg_of_posSemidef_h14
    {N : ℕ} (v : ComplexUnitSphere N) (A : ConcreteMatrixState N)
    (hA : A.PosSemidef) :
    0 ≤ (complexProjectiveTracePair v A).re := by
  rw [complexProjectiveTracePair_eq_star_dotProduct_mulVec_h14]
  exact hA.re_dotProduct_nonneg (fun i : Fin N ↦ v.1 i)

/-- The coordinate bilinear contraction is the squared norm of the scalar
`v† R conjugate(v)`.  This identity does not require symmetry. -/
theorem complexProjectiveBilinearNormSq_eq_normSq_bilinear_h14
    {N : ℕ} (v : ComplexUnitSphere N) (R : ConcreteMatrixState N) :
    complexProjectiveBilinearNormSq v R =
      ((Complex.normSq (∑ i, ∑ j,
        star (v.1 i) * R i j * star (v.1 j)) : ℝ) : ℂ) := by
  rw [Complex.normSq_eq_conj_mul_self]
  change complexProjectiveBilinearNormSq v R =
    star (∑ i, ∑ j, star (v.1 i) * R i j * star (v.1 j)) *
      (∑ i, ∑ j, star (v.1 i) * R i j * star (v.1 j))
  rw [show star (∑ i, ∑ j,
        star (v.1 i) * R i j * star (v.1 j)) =
      ∑ a, ∑ d, v.1 a * star (R a d) * v.1 d by
    simp only [star_sum, star_mul, star_star]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro d _
    ring]
  unfold complexProjectiveBilinearNormSq complexRankOneProjection
  simp only [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro d _
  ring

/-- For a symmetric matrix, the projective quadratic form of `R R†` is
the squared Euclidean norm of `R conjugate(v)`. -/
theorem complexProjectiveTracePair_mul_conjTranspose_eq_sum_normSq_h14
    {N : ℕ} (v : ComplexUnitSphere N) (R : ConcreteMatrixState N)
    (hR : R.IsSymm) :
    complexProjectiveTracePair v (R * R.conjTranspose) =
      ((∑ i, Complex.normSq (∑ j, R i j * star (v.1 j)) : ℝ) : ℂ) := by
  classical
  have hsymm : ∀ i j, R j i = R i j := Matrix.IsSymm.ext_iff.mp hR
  unfold complexProjectiveTracePair complexRankOneProjection
  rw [Complex.ofReal_sum]
  simp_rw [Complex.normSq_eq_conj_mul_self]
  change (∑ i, ∑ j, v.1 i * star (v.1 j) *
      (∑ k, R j k * star (R i k))) =
    ∑ i, star (∑ j, R i j * star (v.1 j)) *
      (∑ j, R i j * star (v.1 j))
  have hstar : ∀ i, star (∑ j, R i j * star (v.1 j)) =
      ∑ j, v.1 j * star (R i j) := by
    intro i
    simp only [star_sum, star_mul, star_star]
  simp_rw [hstar]
  simp only [Finset.sum_mul, Finset.mul_sum]
  calc
    (∑ i, ∑ j, ∑ k,
        v.1 i * star (v.1 j) * (R j k * star (R i k))) =
        ∑ i, ∑ j, ∑ k,
          v.1 i * star (R k i) * (R k j * star (v.1 j)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      rw [hsymm i k, hsymm j k]
      ring
    _ = ∑ i, ∑ k, ∑ j,
          v.1 i * star (R k i) * (R k j * star (v.1 j)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ j,
          v.1 i * star (R k i) * (R k j * star (v.1 j)) :=
      Finset.sum_comm
    _ = ∑ k, ∑ j, ∑ i,
          (v.1 i * star (R k i)) * (R k j * star (v.1 j)) := by
      apply Finset.sum_congr rfl
      intro k _
      exact Finset.sum_comm

/-- Pointwise projective Cauchy--Schwarz: for symmetric `R`, the bilinear
norm-square is dominated by the quadratic form of `R R†`. -/
theorem complexProjectiveBilinearNormSq_re_le_tracePair_mul_conjTranspose_re_h14
    {N : ℕ} (v : ComplexUnitSphere N) (R : ConcreteMatrixState N)
    (hR : R.IsSymm) :
    (complexProjectiveBilinearNormSq v R).re ≤
      (complexProjectiveTracePair v (R * R.conjTranspose)).re := by
  let x : EuclideanSpace ℂ (Fin N) :=
    WithLp.toLp 2 (fun i ↦ ∑ j, R i j * star (v.1 j))
  let B : ℂ := ∑ i, ∑ j,
    star (v.1 i) * R i j * star (v.1 j)
  have hinner : ⟪v.1, x⟫_ℂ = B := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    dsimp only [x, B, dotProduct, WithLp.ofLp_toLp]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Pi.star_apply]
    ring
  have hvnorm : ‖v.1‖ = 1 := mem_sphere_zero_iff_norm.mp v.2
  have hcs : ‖⟪v.1, x⟫_ℂ‖ ≤ ‖v.1‖ * ‖x‖ :=
    norm_inner_le_norm v.1 x
  rw [hinner, hvnorm, one_mul] at hcs
  have hsq : ‖B‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    simpa only [pow_two] using
      (mul_self_le_mul_self (norm_nonneg B) hcs)
  have htrace := congrArg Complex.re
    (complexProjectiveTracePair_mul_conjTranspose_eq_sum_normSq_h14
      v R hR)
  simp only [Complex.ofReal_re] at htrace
  have hx : ‖x‖ ^ 2 =
      (complexProjectiveTracePair v (R * R.conjTranspose)).re := by
    calc
      ‖x‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 := EuclideanSpace.norm_sq_eq x
      _ = ∑ i, Complex.normSq (∑ j, R i j * star (v.1 j)) := by
        apply Finset.sum_congr rfl
        intro i _
        change ‖∑ j, R i j * star (v.1 j)‖ ^ 2 =
          Complex.normSq (∑ j, R i j * star (v.1 j))
        exact (Complex.normSq_eq_norm_sq _).symm
      _ = _ := htrace.symm
  have hw : (complexProjectiveBilinearNormSq v R).re = ‖B‖ ^ 2 := by
    rw [complexProjectiveBilinearNormSq_eq_normSq_bilinear_h14]
    simp only [Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    rfl
  calc
    (complexProjectiveBilinearNormSq v R).re = ‖B‖ ^ 2 := hw
    _ ≤ ‖x‖ ^ 2 := hsq
    _ = (complexProjectiveTracePair v (R * R.conjTranspose)).re := hx

theorem posSemidef_trace_four_re_le_trace_square_re_sq_h14
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.PosSemidef) :
    (Matrix.trace (A * A * A * A)).re ≤
      (Matrix.trace (A * A)).re ^ 2 := by
  have hA2 : (A ^ 2).PosSemidef := hA.pow 2
  have h := posSemidef_trace_square_re_le_trace_re_sq (A ^ 2) hA2
  simpa only [pow_two, Matrix.mul_assoc] using h

theorem posSemidef_trace_four_re_le_trace_re_four_h14
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.PosSemidef) :
    (Matrix.trace (A * A * A * A)).re ≤ (Matrix.trace A).re ^ 4 := by
  have hfour := posSemidef_trace_four_re_le_trace_square_re_sq_h14 A hA
  have htwo := posSemidef_trace_square_re_le_trace_re_sq A hA
  have ht20 : 0 ≤ (Matrix.trace (A * A)).re := by
    have htr := (hA.pow 2).trace_nonneg
    simpa only [pow_two] using (Complex.nonneg_iff.mp htr).1
  have ht10 : 0 ≤ (Matrix.trace A).re :=
    (Complex.nonneg_iff.mp hA.trace_nonneg).1
  have htwo' : (Matrix.trace (A * A)).re ≤
      (Matrix.trace A).re ^ 2 := by
    simpa only [pow_two] using htwo
  have hsq := mul_self_le_mul_self ht20 htwo'
  nlinarith

theorem integral_complexProjectiveTracePair_re_sq_eq_h14
    {N : ℕ} (hN : 1 ≤ N) (A : ConcreteMatrixState N)
    (hA : A.IsHermitian) :
    (∫ v : ComplexUnitSphere N,
      (complexProjectiveTracePair v A).re ^ 2
        ∂(complexUnitSphereProbabilityMeasure N)) =
      ((N : ℝ) * ((N : ℝ) + 1))⁻¹ *
        ((Matrix.trace A).re ^ 2 + (Matrix.trace (A * A)).re) := by
  have hint := integrable_complexProjectiveTracePair_mul hN A A
  have htr1 : (Matrix.trace A).im = 0 :=
    trace_im_eq_zero_of_isHermitian_h14_bounds hA
  have hAA : (A * A).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, hA]
  have htr2 : (Matrix.trace (A * A)).im = 0 :=
    trace_im_eq_zero_of_isHermitian_h14_bounds hAA
  rw [show (fun v : ComplexUnitSphere N ↦
      (complexProjectiveTracePair v A).re ^ 2) =
      fun v ↦ (complexProjectiveTracePair v A *
        complexProjectiveTracePair v A).re by
    funext v
    have him := complexProjectiveTracePair_im_eq_zero_of_isHermitian v A hA
    simp only [pow_two, Complex.mul_re, him, mul_zero, sub_zero]]
  change (∫ v : ComplexUnitSphere N,
      RCLike.re (complexProjectiveTracePair v A *
        complexProjectiveTracePair v A)
        ∂(complexUnitSphereProbabilityMeasure N)) = _
  rw [integral_re hint, integral_complexProjectiveTracePair_mul hN]
  let d : ℝ := ((N : ℝ) * ((N : ℝ) + 1))⁻¹
  change ((((d : ℝ) : ℂ) *
      (Matrix.trace A * Matrix.trace A + Matrix.trace (A * A))).re) =
    d * ((Matrix.trace A).re ^ 2 + (Matrix.trace (A * A)).re)
  have hEq : (((d : ℝ) : ℂ) *
      (Matrix.trace A * Matrix.trace A + Matrix.trace (A * A))) =
      ((d * ((Matrix.trace A).re ^ 2 +
        (Matrix.trace (A * A)).re) : ℝ) : ℂ) := by
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re,
        Complex.ofReal_im, htr1, htr2, zero_mul, mul_zero, sub_zero]
      ring
    · simp only [Complex.mul_im, Complex.add_im, Complex.ofReal_re,
        Complex.ofReal_im, htr1, htr2, zero_mul, mul_zero, add_zero]
  rw [hEq]
  exact Complex.ofReal_re _

theorem integral_complexProjectiveTracePair_re_fourth_eq_h14
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
    trace_im_eq_zero_of_isHermitian_h14_bounds hA
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
    trace_im_eq_zero_of_isHermitian_h14_bounds hA2
  have htr3 : (Matrix.trace (A * A * A)).im = 0 :=
    trace_im_eq_zero_of_isHermitian_h14_bounds hA3
  have htr4 : (Matrix.trace (A * A * A * A)).im = 0 :=
    trace_im_eq_zero_of_isHermitian_h14_bounds hA4
  rw [show (fun v : ComplexUnitSphere N ↦
      (complexProjectiveTracePair v A).re ^ 4) =
      fun v ↦ (complexProjectiveTracePair v A ^ 4).re by
    funext v
    have him := complexProjectiveTracePair_im_eq_zero_of_isHermitian v A hA
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

/-! ## Positive trace-pairing moment bounds -/

/-- A PSD matrix has projective quadratic-form second moment at most twice
the square of its trace divided by the ambient dimension squared. -/
theorem integral_posSemidef_complexProjectiveTracePair_re_sq_le_h14
    {N : ℕ} (hN : 1 ≤ N) (Z : ConcreteMatrixState N)
    (hZ : Z.PosSemidef) :
    (∫ v : ComplexUnitSphere N,
      (complexProjectiveTracePair v Z).re ^ 2
        ∂(complexUnitSphereProbabilityMeasure N)) ≤
      2 * (Matrix.trace Z).re ^ 2 / (N : ℝ) ^ 2 := by
  let n : ℝ := N
  let t : ℝ := (Matrix.trace Z).re
  let t2 : ℝ := (Matrix.trace (Z * Z)).re
  have hn : 0 < n := by
    dsimp only [n]
    exact_mod_cast (Nat.zero_lt_of_lt hN)
  have ht : 0 ≤ t := by
    exact (Complex.nonneg_iff.mp hZ.trace_nonneg).1
  have ht2 : 0 ≤ t2 := by
    have htr := (hZ.pow 2).trace_nonneg
    simpa only [t2, pow_two] using (Complex.nonneg_iff.mp htr).1
  have ht2le : t2 ≤ t ^ 2 := by
    simpa only [t, t2, pow_two] using
      posSemidef_trace_square_re_le_trace_re_sq Z hZ
  have hnum : 0 ≤ t ^ 2 + t2 := add_nonneg (sq_nonneg _) ht2
  have hnumle : t ^ 2 + t2 ≤ 2 * t ^ 2 := by linarith
  have hden : n ^ 2 ≤ n * (n + 1) := by nlinarith
  rw [integral_complexProjectiveTracePair_re_sq_eq_h14 hN Z hZ.isHermitian]
  change (n * (n + 1))⁻¹ * (t ^ 2 + t2) ≤ 2 * t ^ 2 / n ^ 2
  rw [inv_mul_eq_div]
  calc
    (t ^ 2 + t2) / (n * (n + 1)) ≤
        (2 * t ^ 2) / (n * (n + 1)) :=
      div_le_div_of_nonneg_right hnumle (by positivity)
    _ ≤ (2 * t ^ 2) / n ^ 2 :=
      div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hn) hden

theorem integral_concreteCOEY_tracePair_re_sq_le_h14
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    (∫ v : ComplexUnitSphere N,
      (complexProjectiveTracePair v (concreteCOEY N K A)).re ^ 2
        ∂(complexUnitSphereProbabilityMeasure N)) ≤
      (concreteCOETraceOne N K A ^ 2 + concreteCOETraceTwo N K A) /
        (N : ℝ) ^ 2 := by
  let Y := concreteCOEY N K A
  let n : ℝ := N
  have hY := concreteCOEY_posSemidef_of_support hgap A hsupport
  have hn : 0 < n := by
    dsimp only [n]
    exact_mod_cast (Nat.zero_lt_of_lt hN)
  have ht2 : 0 ≤ concreteCOETraceTwo N K A :=
    concreteCOETraceTwo_nonneg_of_support hgap A hsupport
  have hnum : 0 ≤
      concreteCOETraceOne N K A ^ 2 + concreteCOETraceTwo N K A :=
    add_nonneg (sq_nonneg _) ht2
  have hden : n ^ 2 ≤ n * (n + 1) := by nlinarith
  rw [integral_complexProjectiveTracePair_re_sq_eq_h14 hN Y hY.isHermitian]
  change (n * (n + 1))⁻¹ *
      (concreteCOETraceOne N K A ^ 2 + concreteCOETraceTwo N K A) ≤ _
  rw [inv_mul_eq_div]
  exact div_le_div_of_nonneg_left hnum (sq_pos_of_pos hn) hden

theorem integral_concreteCOEY_sq_tracePair_re_sq_le_h14
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    (∫ v : ComplexUnitSphere N,
      (complexProjectiveTracePair v
        (concreteCOEY N K A * concreteCOEY N K A)).re ^ 2
        ∂(complexUnitSphereProbabilityMeasure N)) ≤
      2 * concreteCOETraceTwo N K A ^ 2 / (N : ℝ) ^ 2 := by
  let Y := concreteCOEY N K A
  let Y2 := Y * Y
  let n : ℝ := N
  have hY := concreteCOEY_posSemidef_of_support hgap A hsupport
  have hY2 : Y2.PosSemidef := by
    simpa only [Y2, pow_two] using hY.pow 2
  have hn : 0 < n := by
    dsimp only [n]
    exact_mod_cast (Nat.zero_lt_of_lt hN)
  have ht2 : 0 ≤ concreteCOETraceTwo N K A :=
    concreteCOETraceTwo_nonneg_of_support hgap A hsupport
  have ht2eq : (Matrix.trace (Y * Y)).re =
      concreteCOETraceTwo N K A := by rfl
  have hfour : (Matrix.trace (Y * Y * Y * Y)).re ≤
      concreteCOETraceTwo N K A ^ 2 := by
    have hraw :=
      posSemidef_trace_four_re_le_trace_square_re_sq_h14 Y hY
    rw [ht2eq] at hraw
    exact hraw
  have hfour0 : 0 ≤ (Matrix.trace (Y * Y * Y * Y)).re := by
    have htr := (hY.pow 4).trace_nonneg
    simpa only [pow_succ, pow_two, pow_zero, one_mul, Matrix.mul_assoc] using
      (Complex.nonneg_iff.mp htr).1
  have hnum : 0 ≤ concreteCOETraceTwo N K A ^ 2 +
      (Matrix.trace (Y * Y * Y * Y)).re :=
    add_nonneg (sq_nonneg _) hfour0
  have hnumle : concreteCOETraceTwo N K A ^ 2 +
      (Matrix.trace (Y * Y * Y * Y)).re ≤
      2 * concreteCOETraceTwo N K A ^ 2 := by nlinarith
  have hden : n ^ 2 ≤ n * (n + 1) := by nlinarith
  rw [show concreteCOEY N K A * concreteCOEY N K A = Y2 by rfl]
  rw [integral_complexProjectiveTracePair_re_sq_eq_h14 hN Y2 hY2.isHermitian]
  have hY2trace : (Matrix.trace Y2).re =
      concreteCOETraceTwo N K A := by rfl
  have hY2sq : (Matrix.trace (Y2 * Y2)).re =
      (Matrix.trace (Y * Y * Y * Y)).re := by
    congr 2
    simp only [Y2, Matrix.mul_assoc]
  rw [hY2trace, hY2sq]
  change (n * (n + 1))⁻¹ *
      (concreteCOETraceTwo N K A ^ 2 +
        (Matrix.trace (Y * Y * Y * Y)).re) ≤ _
  rw [inv_mul_eq_div]
  calc
    _ ≤ (2 * concreteCOETraceTwo N K A ^ 2) / (n * (n + 1)) :=
      div_le_div_of_nonneg_right hnumle (by positivity)
    _ ≤ (2 * concreteCOETraceTwo N K A ^ 2) / n ^ 2 :=
      div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hn) hden

theorem integral_concreteCOEY_tracePair_re_fourth_le_h14
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    (∫ v : ComplexUnitSphere N,
      (complexProjectiveTracePair v (concreteCOEY N K A)).re ^ 4
        ∂(complexUnitSphereProbabilityMeasure N)) ≤
      24 * concreteCOETraceOne N K A ^ 4 / (N : ℝ) ^ 4 := by
  let Y := concreteCOEY N K A
  let n : ℝ := N
  let t1 := concreteCOETraceOne N K A
  let t2 := concreteCOETraceTwo N K A
  let t3 := concreteCOETraceThree N K A
  let t4 := (Matrix.trace (Y * Y * Y * Y)).re
  have hY := concreteCOEY_posSemidef_of_support hgap A hsupport
  have hn : 0 < n := by
    dsimp only [n]
    exact_mod_cast (Nat.zero_lt_of_lt hN)
  have ht1 : 0 ≤ t1 := by
    exact (Complex.nonneg_iff.mp hY.trace_nonneg).1
  have ht2 : 0 ≤ t2 := by
    exact concreteCOETraceTwo_nonneg_of_support hgap A hsupport
  have ht3 : 0 ≤ t3 := by
    exact concreteCOETraceThree_nonneg_of_support hgap A hsupport
  have ht4 : 0 ≤ t4 := by
    have htr := (hY.pow 4).trace_nonneg
    simpa only [t4, Y, pow_succ, pow_two, pow_zero, one_mul,
      Matrix.mul_assoc] using (Complex.nonneg_iff.mp htr).1
  have ht2le : t2 ≤ t1 ^ 2 := by
    exact concreteCOETraceTwo_le_traceOne_sq_of_support hgap A hsupport
  have ht3le : t3 ≤ t1 ^ 3 := by
    exact concreteCOETraceThree_le_traceOne_cube_of_support hgap A hsupport
  have ht1eq : (Matrix.trace Y).re = t1 := by rfl
  have ht4le : t4 ≤ t1 ^ 4 := by
    have hraw := posSemidef_trace_four_re_le_trace_re_four_h14 Y hY
    rw [ht1eq] at hraw
    exact hraw
  have ht1t2 : t1 ^ 2 * t2 ≤ t1 ^ 4 := by
    have := mul_le_mul_of_nonneg_left ht2le (sq_nonneg t1)
    nlinarith
  have ht2sq : t2 ^ 2 ≤ t1 ^ 4 := by
    have := mul_self_le_mul_self ht2 ht2le
    nlinarith
  have ht1t3 : t1 * t3 ≤ t1 ^ 4 := by
    have := mul_le_mul_of_nonneg_left ht3le ht1
    nlinarith
  have hnum0 : 0 ≤ t1 ^ 4 + 6 * (t1 ^ 2 * t2) + 3 * t2 ^ 2 +
      8 * (t1 * t3) + 6 * t4 := by positivity
  have hnumle : t1 ^ 4 + 6 * (t1 ^ 2 * t2) + 3 * t2 ^ 2 +
      8 * (t1 * t3) + 6 * t4 ≤ 24 * t1 ^ 4 := by
    nlinarith
  have hden : n ^ 4 ≤ n * (n + 1) * (n + 2) * (n + 3) := by
    have hn0 : 0 ≤ n := hn.le
    calc
      n ^ 4 = n * n * n * n := by ring
      _ ≤ n * (n + 1) * (n + 2) * (n + 3) := by
        gcongr <;> linarith
  rw [integral_complexProjectiveTracePair_re_fourth_eq_h14
    hN Y hY.isHermitian]
  change (n * (n + 1) * (n + 2) * (n + 3))⁻¹ *
      (t1 ^ 4 + 6 * (t1 ^ 2 * t2) + 3 * t2 ^ 2 +
        8 * (t1 * t3) + 6 * t4) ≤ _
  rw [inv_mul_eq_div]
  calc
    _ ≤ (24 * t1 ^ 4) / (n * (n + 1) * (n + 2) * (n + 3)) :=
      div_le_div_of_nonneg_right hnumle (by positivity)
    _ ≤ (24 * t1 ^ 4) / n ^ 4 :=
      div_le_div_of_nonneg_left (by positivity) (pow_pos hn 4) hden

/-! ## The separated sandwich factor -/

private theorem h14_sandwich_scalar_square_le
    (a s b e t1 t2 : ℝ)
    (ha0 : 0 ≤ a) (ha1 : 2 * a ≤ 1)
    (hb : 0 ≤ b) (he : 0 ≤ e) (ht2 : 0 ≤ t2) :
    ((1 - 2 * a) * b + a ^ 2 * t1 +
        s * (b ^ 2 - 2 * a * e + a ^ 2 * t2)) ^ 2 ≤
      4 * b ^ 2 + 4 * a ^ 4 * t1 ^ 2 +
        2 * s ^ 2 *
          (b ^ 4 + 4 * a ^ 2 * e ^ 2 + a ^ 4 * t2 ^ 2 +
            2 * a ^ 2 * b ^ 2 * t2) := by
  let L := (1 - 2 * a) * b + a ^ 2 * t1
  let Q := b ^ 2 - 2 * a * e + a ^ 2 * t2
  have hac : 0 ≤ 1 - 2 * a := by linarith
  have hacSq : (1 - 2 * a) ^ 2 ≤ 1 := by nlinarith
  have hcb : (1 - 2 * a) ^ 2 * b ^ 2 ≤ b ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha1) (sq_nonneg b),
      mul_le_mul_of_nonneg_right hacSq (sq_nonneg b)]
  have hL : L ^ 2 ≤ 2 * b ^ 2 + 2 * a ^ 4 * t1 ^ 2 := by
    dsimp only [L]
    nlinarith [sq_nonneg ((1 - 2 * a) * b - a ^ 2 * t1)]
  have hdrop1 : 0 ≤ a * b ^ 2 * e := by positivity
  have hdrop2 : 0 ≤ a ^ 3 * e * t2 := by positivity
  have hQ : Q ^ 2 ≤
      b ^ 4 + 4 * a ^ 2 * e ^ 2 + a ^ 4 * t2 ^ 2 +
        2 * a ^ 2 * b ^ 2 * t2 := by
    dsimp only [Q]
    nlinarith
  have hsQ := mul_le_mul_of_nonneg_left hQ (sq_nonneg s)
  dsimp only [L, Q] at hL ⊢
  nlinarith [sq_nonneg
    (((1 - 2 * a) * b + a ^ 2 * t1) -
      s * (b ^ 2 - 2 * a * e + a ^ 2 * t2))]

theorem complexCenteredProjectiveSandwich_re_expansion_h14
    {N K : ℕ} (v : ComplexUnitSphere N) (A : ConcreteMatrixState N)
    (hgap : 2 * N + 8 ≤ K)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    (complexCenteredProjectiveSandwich v
      (concreteCOEWMatrix N K A) (concreteCOEY N K A)).re =
      (1 - 2 * (N : ℝ)⁻¹) *
          (complexProjectiveTracePair v (concreteCOEY N K A)).re +
        (N : ℝ)⁻¹ ^ 2 * concreteCOETraceOne N K A +
        (concreteCOEExponent N K)⁻¹ *
          ((complexProjectiveTracePair v (concreteCOEY N K A)).re ^ 2 -
            2 * (N : ℝ)⁻¹ *
              (complexProjectiveTracePair v
                (concreteCOEY N K A * concreteCOEY N K A)).re +
            (N : ℝ)⁻¹ ^ 2 * concreteCOETraceTwo N K A) := by
  let Y := concreteCOEY N K A
  have hY := concreteCOEY_posSemidef_of_support hgap A hsupport
  have hY2 : (Y * Y).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, hY.isHermitian]
  have hbim : (complexProjectiveTracePair v Y).im = 0 :=
    complexProjectiveTracePair_im_eq_zero_of_isHermitian v Y hY.isHermitian
  have heim : (complexProjectiveTracePair v (Y * Y)).im = 0 :=
    complexProjectiveTracePair_im_eq_zero_of_isHermitian v (Y * Y) hY2
  have ht1im : (Matrix.trace Y).im = 0 :=
    trace_im_eq_zero_of_isHermitian_h14_bounds hY.isHermitian
  have ht2im : (Matrix.trace (Y * Y)).im = 0 :=
    trace_im_eq_zero_of_isHermitian_h14_bounds hY2
  rw [complexCenteredProjectiveSandwich_expansion_h14]
  change (h14ProjectiveSandwichExpansion K v Y).re =
    (1 - 2 * (N : ℝ)⁻¹) *
          (complexProjectiveTracePair v Y).re +
        (N : ℝ)⁻¹ ^ 2 * (Matrix.trace Y).re +
        (concreteCOEExponent N K)⁻¹ *
          ((complexProjectiveTracePair v Y).re ^ 2 -
            2 * (N : ℝ)⁻¹ *
              (complexProjectiveTracePair v (Y * Y)).re +
            (N : ℝ)⁻¹ ^ 2 * (Matrix.trace (Y * Y)).re)
  unfold h14ProjectiveSandwichExpansion
  simp [Complex.mul_re, pow_two, hbim, heim, ht1im, ht2im]

theorem complexCenteredProjectiveSandwich_re_sq_pointwise_le_h14
    {N K : ℕ} (hN : 2 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (v : ComplexUnitSphere N) (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    (complexCenteredProjectiveSandwich v
      (concreteCOEWMatrix N K A) (concreteCOEY N K A)).re ^ 2 ≤
      4 * (complexProjectiveTracePair v (concreteCOEY N K A)).re ^ 2 +
        4 * (N : ℝ)⁻¹ ^ 4 * concreteCOETraceOne N K A ^ 2 +
        2 * (concreteCOEExponent N K)⁻¹ ^ 2 *
          ((complexProjectiveTracePair v (concreteCOEY N K A)).re ^ 4 +
            4 * (N : ℝ)⁻¹ ^ 2 *
              (complexProjectiveTracePair v
                (concreteCOEY N K A * concreteCOEY N K A)).re ^ 2 +
            (N : ℝ)⁻¹ ^ 4 * concreteCOETraceTwo N K A ^ 2 +
            2 * (N : ℝ)⁻¹ ^ 2 *
              (complexProjectiveTracePair v
                (concreteCOEY N K A)).re ^ 2 *
              concreteCOETraceTwo N K A) := by
  let n : ℝ := N
  let a : ℝ := n⁻¹
  let s : ℝ := (concreteCOEExponent N K)⁻¹
  let b : ℝ := (complexProjectiveTracePair v
    (concreteCOEY N K A)).re
  let e : ℝ := (complexProjectiveTracePair v
    (concreteCOEY N K A * concreteCOEY N K A)).re
  let t1 : ℝ := concreteCOETraceOne N K A
  let t2 : ℝ := concreteCOETraceTwo N K A
  have hn : 0 < n := by
    dsimp only [n]
    exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hn2 : (2 : ℝ) ≤ n := by
    dsimp only [n]
    exact_mod_cast hN
  have ha0 : 0 ≤ a := inv_nonneg.mpr hn.le
  have ha1 : 2 * a ≤ 1 := by
    dsimp only [a]
    rw [← div_eq_mul_inv]
    exact (div_le_one hn).2 hn2
  have hY := concreteCOEY_posSemidef_of_support hgap A hsupport
  have hY2 : (concreteCOEY N K A * concreteCOEY N K A).PosSemidef := by
    simpa only [pow_two] using hY.pow 2
  have hb : 0 ≤ b := by
    exact complexProjectiveTracePair_re_nonneg_of_posSemidef_h14
      v _ hY
  have he : 0 ≤ e := by
    exact complexProjectiveTracePair_re_nonneg_of_posSemidef_h14
      v _ hY2
  have ht2 : 0 ≤ t2 :=
    concreteCOETraceTwo_nonneg_of_support hgap A hsupport
  rw [complexCenteredProjectiveSandwich_re_expansion_h14
    v A hgap hsupport]
  change ((1 - 2 * a) * b + a ^ 2 * t1 +
      s * (b ^ 2 - 2 * a * e + a ^ 2 * t2)) ^ 2 ≤
    4 * b ^ 2 + 4 * a ^ 4 * t1 ^ 2 +
      2 * s ^ 2 *
        (b ^ 4 + 4 * a ^ 2 * e ^ 2 + a ^ 4 * t2 ^ 2 +
          2 * a ^ 2 * b ^ 2 * t2)
  exact h14_sandwich_scalar_square_le a s b e t1 t2
    ha0 ha1 hb he ht2

/-- Real form of the exact centered conjugate-sandwich expansion. -/
theorem complexCenteredProjectiveConjugateSandwich_re_expansion_h14
    {N : ℕ} (v : ComplexUnitSphere N) (R : ConcreteMatrixState N)
    (hR : R.IsSymm) :
    (complexCenteredProjectiveConjugateSandwich v R).re =
      (complexProjectiveBilinearNormSq v R).re -
        2 * (N : ℝ)⁻¹ *
          (complexProjectiveTracePair v (R * R.conjTranspose)).re +
        (N : ℝ)⁻¹ ^ 2 *
          (Matrix.trace (R * R.conjTranspose)).re := by
  let Z := R * R.conjTranspose
  have hZ : Z.PosSemidef := Matrix.posSemidef_self_mul_conjTranspose R
  have hdim : (complexProjectiveTracePair v Z).im = 0 :=
    complexProjectiveTracePair_im_eq_zero_of_isHermitian v Z hZ.isHermitian
  have htim : (Matrix.trace Z).im = 0 :=
    trace_im_eq_zero_of_isHermitian_h14_bounds hZ.isHermitian
  rw [complexCenteredProjectiveConjugateSandwich_expansion_h14 v R hR]
  unfold h14ProjectiveConjugateSandwichExpansion
  rw [complexProjectiveBilinearNormSq_eq_normSq_bilinear_h14]
  change (_ - 2 * (((N : ℝ)⁻¹ : ℝ) : ℂ) *
      complexProjectiveTracePair v Z +
      (((N : ℝ)⁻¹ : ℝ) : ℂ) ^ 2 * Matrix.trace Z).re = _
  simp only [Complex.sub_re, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_apply,
    Complex.natCast_re, hdim, htim, zero_mul, mul_zero, sub_zero, pow_two]
  have htwo : Complex.re (2 : ℂ) = 2 := by norm_num
  rw [htwo]

private theorem h14_three_term_square_le
    (x y z : ℝ) : (x + y + z) ^ 2 ≤ 3 * (x ^ 2 + y ^ 2 + z ^ 2) := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z)]

/-- Pointwise bound for the centered conjugate factor.  The key input is
the projective Cauchy--Schwarz inequality above, applied before squaring. -/
theorem complexCenteredProjectiveConjugateSandwich_re_sq_pointwise_le_h14
    {N : ℕ} (v : ComplexUnitSphere N) (R : ConcreteMatrixState N)
    (hR : R.IsSymm) :
    (complexCenteredProjectiveConjugateSandwich v R).re ^ 2 ≤
      3 * ((1 + 4 * (N : ℝ)⁻¹ ^ 2) *
          (complexProjectiveTracePair v (R * R.conjTranspose)).re ^ 2 +
        (N : ℝ)⁻¹ ^ 4 *
          (Matrix.trace (R * R.conjTranspose)).re ^ 2) := by
  let a : ℝ := (N : ℝ)⁻¹
  let w : ℝ := (complexProjectiveBilinearNormSq v R).re
  let d : ℝ := (complexProjectiveTracePair v
    (R * R.conjTranspose)).re
  let t : ℝ := (Matrix.trace (R * R.conjTranspose)).re
  have hZ : (R * R.conjTranspose).PosSemidef :=
    Matrix.posSemidef_self_mul_conjTranspose R
  have hw0 : 0 ≤ w := by
    rw [show w = Complex.normSq (∑ i, ∑ j,
        star (v.1 i) * R i j * star (v.1 j)) by
      dsimp only [w]
      rw [complexProjectiveBilinearNormSq_eq_normSq_bilinear_h14]
      exact Complex.ofReal_re _]
    exact Complex.normSq_nonneg _
  have hd0 : 0 ≤ d := by
    exact complexProjectiveTracePair_re_nonneg_of_posSemidef_h14 v _ hZ
  have hwle : w ≤ d := by
    exact complexProjectiveBilinearNormSq_re_le_tracePair_mul_conjTranspose_re_h14
      v R hR
  have hw2le : w ^ 2 ≤ d ^ 2 := by
    simpa only [pow_two] using mul_self_le_mul_self hw0 hwle
  have hthree := h14_three_term_square_le w (-2 * a * d) (a ^ 2 * t)
  have hpieces :
      w ^ 2 + (-2 * a * d) ^ 2 + (a ^ 2 * t) ^ 2 ≤
        (1 + 4 * a ^ 2) * d ^ 2 + a ^ 4 * t ^ 2 := by
    nlinarith
  rw [complexCenteredProjectiveConjugateSandwich_re_expansion_h14 v R hR]
  change (w - 2 * a * d + a ^ 2 * t) ^ 2 ≤
    3 * ((1 + 4 * a ^ 2) * d ^ 2 + a ^ 4 * t ^ 2)
  nlinarith

private theorem integrable_complexProjectiveTracePair_re_sq_h14
    {N : ℕ} (hN : 1 ≤ N) (A : ConcreteMatrixState N)
    (hA : A.IsHermitian) :
    Integrable (fun v : ComplexUnitSphere N ↦
      (complexProjectiveTracePair v A).re ^ 2)
      (complexUnitSphereProbabilityMeasure N) := by
  have h := (integrable_complexProjectiveTracePair_mul hN A A).re
  apply h.congr
  filter_upwards [] with v
  have him := complexProjectiveTracePair_im_eq_zero_of_isHermitian v A hA
  simpa [RCLike.re_to_complex, pow_two, Complex.mul_re, him]

private theorem integrable_complexProjectiveTracePair_re_fourth_h14
    {N : ℕ} (hN : 1 ≤ N) (A : ConcreteMatrixState N)
    (hA : A.IsHermitian) :
    Integrable (fun v : ComplexUnitSphere N ↦
      (complexProjectiveTracePair v A).re ^ 4)
      (complexUnitSphereProbabilityMeasure N) := by
  have h := (integrable_complexProjectiveTracePair_fourth hN A).re
  apply h.congr
  filter_upwards [] with v
  have him := complexProjectiveTracePair_im_eq_zero_of_isHermitian v A hA
  simpa [RCLike.re_to_complex, pow_succ, Complex.mul_re,
    Complex.mul_im, him]

theorem integral_complexCenteredProjectiveSandwich_re_sq_le_h14
    {N K : ℕ} (hN : 2 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    (∫ v : ComplexUnitSphere N,
      (complexCenteredProjectiveSandwich v
        (concreteCOEWMatrix N K A) (concreteCOEY N K A)).re ^ 2
        ∂(complexUnitSphereProbabilityMeasure N)) ≤
      h14ProjectiveSandwichSecondMomentEnvelope N K A := by
  let μ := complexUnitSphereProbabilityMeasure N
  let Y := concreteCOEY N K A
  let n : ℝ := N
  let c : ℝ := concreteCOEExponent N K
  let a : ℝ := n⁻¹
  let s : ℝ := c⁻¹
  let t1 : ℝ := concreteCOETraceOne N K A
  let t2 : ℝ := concreteCOETraceTwo N K A
  let b : ComplexUnitSphere N → ℝ := fun v ↦
    (complexProjectiveTracePair v Y).re
  let e : ComplexUnitSphere N → ℝ := fun v ↦
    (complexProjectiveTracePair v (Y * Y)).re
  let M : ComplexUnitSphere N → ℝ := fun v ↦
    4 * b v ^ 2 + 4 * a ^ 4 * t1 ^ 2 +
      2 * s ^ 2 * b v ^ 4 +
      8 * s ^ 2 * a ^ 2 * e v ^ 2 +
      2 * s ^ 2 * a ^ 4 * t2 ^ 2 +
      4 * s ^ 2 * a ^ 2 * t2 * b v ^ 2
  have hN1 : 1 ≤ N := le_trans (by omega) hN
  have hn : 0 < n := by
    dsimp only [n]
    exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hn2 : (2 : ℝ) ≤ n := by
    dsimp only [n]
    exact_mod_cast hN
  have hc : 0 < c := by
    dsimp only [c, concreteCOEExponent]
    have hg : (2 : ℝ) * (N : ℝ) + 8 ≤ (K : ℝ) := by
      exact_mod_cast hgap
    linarith
  have ha0 : 0 ≤ a := inv_nonneg.mpr hn.le
  have ha1 : 2 * a ≤ 1 := by
    dsimp only [a]
    rw [← div_eq_mul_inv]
    exact (div_le_one hn).2 hn2
  have ha_le : a ≤ 1 := by linarith
  have hs0 : 0 ≤ s := inv_nonneg.mpr hc.le
  have hY := concreteCOEY_posSemidef_of_support hgap A hsupport
  have hY2 : (Y * Y).PosSemidef := by
    simpa only [Y, pow_two] using hY.pow 2
  have ht1 : 0 ≤ t1 := by
    exact (Complex.nonneg_iff.mp hY.trace_nonneg).1
  have ht2 : 0 ≤ t2 :=
    concreteCOETraceTwo_nonneg_of_support hgap A hsupport
  have ht2le : t2 ≤ t1 ^ 2 :=
    concreteCOETraceTwo_le_traceOne_sq_of_support hgap A hsupport
  have hb2int : Integrable (fun v ↦ b v ^ 2) μ := by
    simpa only [b, μ] using
      integrable_complexProjectiveTracePair_re_sq_h14 hN1 Y hY.isHermitian
  have he2int : Integrable (fun v ↦ e v ^ 2) μ := by
    simpa only [e, μ] using
      integrable_complexProjectiveTracePair_re_sq_h14 hN1 (Y * Y)
        hY2.isHermitian
  have hb4int : Integrable (fun v ↦ b v ^ 4) μ := by
    simpa only [b, μ] using
      integrable_complexProjectiveTracePair_re_fourth_h14 hN1 Y hY.isHermitian
  letI : IsProbabilityMeasure μ := by
    dsimp only [μ]
    exact complexUnitSphereProbabilityMeasure_isProbability hN1
  have hm1 : Integrable (fun v ↦ 4 * b v ^ 2) μ := hb2int.const_mul 4
  have hm2 : Integrable (fun _ : ComplexUnitSphere N ↦
      4 * a ^ 4 * t1 ^ 2) μ := integrable_const _
  have hm3 : Integrable (fun v ↦ 2 * s ^ 2 * b v ^ 4) μ :=
    hb4int.const_mul (2 * s ^ 2)
  have hm4 : Integrable (fun v ↦ 8 * s ^ 2 * a ^ 2 * e v ^ 2) μ := by
    convert he2int.const_mul (8 * s ^ 2 * a ^ 2) using 1 <;> ring
  have hm5 : Integrable (fun _ : ComplexUnitSphere N ↦
      2 * s ^ 2 * a ^ 4 * t2 ^ 2) μ := integrable_const _
  have hm6 : Integrable (fun v ↦
      4 * s ^ 2 * a ^ 2 * t2 * b v ^ 2) μ := by
    convert hb2int.const_mul (4 * s ^ 2 * a ^ 2 * t2) using 1 <;> ring
  have hMInt : Integrable M μ := by
    dsimp only [M]
    exact ((((hm1.add hm2).add hm3).add hm4).add hm5).add hm6
  have hSInt : Integrable (fun v : ComplexUnitSphere N ↦
      (complexCenteredProjectiveSandwich v
        (concreteCOEWMatrix N K A) Y).re ^ 2) μ := by
    simpa only [μ] using
      integrable_complexCenteredProjectiveSandwich_re_sq_h14 hN1
        (concreteCOEWMatrix N K A) Y
  have hpoint : ∀ v : ComplexUnitSphere N,
      (complexCenteredProjectiveSandwich v
        (concreteCOEWMatrix N K A) Y).re ^ 2 ≤ M v := by
    intro v
    calc
      _ ≤ 4 * b v ^ 2 + 4 * a ^ 4 * t1 ^ 2 +
          2 * s ^ 2 *
            (b v ^ 4 + 4 * a ^ 2 * e v ^ 2 + a ^ 4 * t2 ^ 2 +
              2 * a ^ 2 * b v ^ 2 * t2) := by
        simpa only [Y, b, e, a, s, n, c, t1, t2] using
          complexCenteredProjectiveSandwich_re_sq_pointwise_le_h14
            hN hgap v A hsupport
      _ = M v := by dsimp only [M]; ring
  have hMain : (∫ v,
      (complexCenteredProjectiveSandwich v
        (concreteCOEWMatrix N K A) Y).re ^ 2 ∂μ) ≤ ∫ v, M v ∂μ :=
    integral_mono hSInt hMInt hpoint
  have hMIntegral : (∫ v, M v ∂μ) =
      4 * (∫ v, b v ^ 2 ∂μ) + 4 * a ^ 4 * t1 ^ 2 +
        2 * s ^ 2 * (∫ v, b v ^ 4 ∂μ) +
        8 * s ^ 2 * a ^ 2 * (∫ v, e v ^ 2 ∂μ) +
        2 * s ^ 2 * a ^ 4 * t2 ^ 2 +
        4 * s ^ 2 * a ^ 2 * t2 * (∫ v, b v ^ 2 ∂μ) := by
    calc
      (∫ v, M v ∂μ) =
          ∫ v, (((((4 * b v ^ 2 + 4 * a ^ 4 * t1 ^ 2) +
            2 * s ^ 2 * b v ^ 4) +
            8 * s ^ 2 * a ^ 2 * e v ^ 2) +
            2 * s ^ 2 * a ^ 4 * t2 ^ 2) +
            4 * s ^ 2 * a ^ 2 * t2 * b v ^ 2) ∂μ := by
          apply integral_congr_ae
          filter_upwards [] with v
          dsimp only [M]
      _ = (∫ v, ((((4 * b v ^ 2 + 4 * a ^ 4 * t1 ^ 2) +
            2 * s ^ 2 * b v ^ 4) +
            8 * s ^ 2 * a ^ 2 * e v ^ 2) +
            2 * s ^ 2 * a ^ 4 * t2 ^ 2) ∂μ) +
          ∫ v, 4 * s ^ 2 * a ^ 2 * t2 * b v ^ 2 ∂μ :=
        integral_add ((((hm1.add hm2).add hm3).add hm4).add hm5) hm6
      _ = ((∫ v, (((4 * b v ^ 2 + 4 * a ^ 4 * t1 ^ 2) +
            2 * s ^ 2 * b v ^ 4) +
            8 * s ^ 2 * a ^ 2 * e v ^ 2) ∂μ) +
          ∫ _v, 2 * s ^ 2 * a ^ 4 * t2 ^ 2 ∂μ) +
          ∫ v, 4 * s ^ 2 * a ^ 2 * t2 * b v ^ 2 ∂μ := by
        congr 1
        exact integral_add (((hm1.add hm2).add hm3).add hm4) hm5
      _ = (((∫ v, ((4 * b v ^ 2 + 4 * a ^ 4 * t1 ^ 2) +
            2 * s ^ 2 * b v ^ 4) ∂μ) +
          ∫ v, 8 * s ^ 2 * a ^ 2 * e v ^ 2 ∂μ) +
          ∫ _v, 2 * s ^ 2 * a ^ 4 * t2 ^ 2 ∂μ) +
          ∫ v, 4 * s ^ 2 * a ^ 2 * t2 * b v ^ 2 ∂μ := by
        congr 2
        exact integral_add ((hm1.add hm2).add hm3) hm4
      _ = ((((∫ v, (4 * b v ^ 2 + 4 * a ^ 4 * t1 ^ 2) ∂μ) +
          ∫ v, 2 * s ^ 2 * b v ^ 4 ∂μ) +
          ∫ v, 8 * s ^ 2 * a ^ 2 * e v ^ 2 ∂μ) +
          ∫ _v, 2 * s ^ 2 * a ^ 4 * t2 ^ 2 ∂μ) +
          ∫ v, 4 * s ^ 2 * a ^ 2 * t2 * b v ^ 2 ∂μ := by
        congr 3
        exact integral_add (hm1.add hm2) hm3
      _ = (((((∫ v, 4 * b v ^ 2 ∂μ) +
          ∫ _v, 4 * a ^ 4 * t1 ^ 2 ∂μ) +
          ∫ v, 2 * s ^ 2 * b v ^ 4 ∂μ) +
          ∫ v, 8 * s ^ 2 * a ^ 2 * e v ^ 2 ∂μ) +
          ∫ _v, 2 * s ^ 2 * a ^ 4 * t2 ^ 2 ∂μ) +
          ∫ v, 4 * s ^ 2 * a ^ 2 * t2 * b v ^ 2 ∂μ := by
        congr 4
        exact integral_add hm1 hm2
      _ = 4 * (∫ v, b v ^ 2 ∂μ) + 4 * a ^ 4 * t1 ^ 2 +
          2 * s ^ 2 * (∫ v, b v ^ 4 ∂μ) +
          8 * s ^ 2 * a ^ 2 * (∫ v, e v ^ 2 ∂μ) +
          2 * s ^ 2 * a ^ 4 * t2 ^ 2 +
          4 * s ^ 2 * a ^ 2 * t2 * (∫ v, b v ^ 2 ∂μ) := by
        simp only [integral_const_mul, integral_const, probReal_univ, one_smul]
  have hb2bound : (∫ v, b v ^ 2 ∂μ) ≤ (t1 ^ 2 + t2) * a ^ 2 := by
    simpa only [b, μ, Y, t1, t2, n, a, div_eq_mul_inv, inv_pow] using
      integral_concreteCOEY_tracePair_re_sq_le_h14 hN1 hgap A hsupport
  have he2bound : (∫ v, e v ^ 2 ∂μ) ≤ 2 * t2 ^ 2 * a ^ 2 := by
    simpa only [e, μ, Y, t2, n, a, div_eq_mul_inv, inv_pow] using
      integral_concreteCOEY_sq_tracePair_re_sq_le_h14 hN1 hgap A hsupport
  have hb4bound : (∫ v, b v ^ 4 ∂μ) ≤ 24 * t1 ^ 4 * a ^ 4 := by
    simpa only [b, μ, Y, t1, n, a, div_eq_mul_inv, inv_pow] using
      integral_concreteCOEY_tracePair_re_fourth_le_h14 hN1 hgap A hsupport
  have hMbound : (∫ v, M v ∂μ) ≤
      4 * ((t1 ^ 2 + t2) * a ^ 2) + 4 * a ^ 4 * t1 ^ 2 +
        2 * s ^ 2 * (24 * t1 ^ 4 * a ^ 4) +
        8 * s ^ 2 * a ^ 2 * (2 * t2 ^ 2 * a ^ 2) +
        2 * s ^ 2 * a ^ 4 * t2 ^ 2 +
        4 * s ^ 2 * a ^ 2 * t2 * ((t1 ^ 2 + t2) * a ^ 2) := by
    rw [hMIntegral]
    have h1 := mul_le_mul_of_nonneg_left hb2bound (by norm_num : (0 : ℝ) ≤ 4)
    have h3 := mul_le_mul_of_nonneg_left hb4bound (by positivity : 0 ≤ 2 * s ^ 2)
    have h4 := mul_le_mul_of_nonneg_left he2bound
      (by positivity : 0 ≤ 8 * s ^ 2 * a ^ 2)
    have h6 := mul_le_mul_of_nonneg_left hb2bound
      (by positivity : 0 ≤ 4 * s ^ 2 * a ^ 2 * t2)
    nlinarith
  have ha4le : a ^ 4 ≤ a ^ 2 := by
    have ha2le : a ^ 2 ≤ 1 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right ha2le (sq_nonneg a)]
  have ha4t1 : a ^ 4 * t1 ^ 2 ≤ a ^ 2 * t1 ^ 2 :=
    mul_le_mul_of_nonneg_right ha4le (sq_nonneg t1)
  have ht2sq : t2 ^ 2 ≤ t1 ^ 4 := by
    have h := mul_self_le_mul_self ht2 ht2le
    nlinarith
  have ht1t2 : t1 ^ 2 * t2 ≤ t1 ^ 4 := by
    have h := mul_le_mul_of_nonneg_left ht2le (sq_nonneg t1)
    nlinarith
  have hradial :
      2 * s ^ 2 * (24 * t1 ^ 4 * a ^ 4) +
          8 * s ^ 2 * a ^ 2 * (2 * t2 ^ 2 * a ^ 2) +
          2 * s ^ 2 * a ^ 4 * t2 ^ 2 +
          4 * s ^ 2 * a ^ 2 * t2 * ((t1 ^ 2 + t2) * a ^ 2) ≤
        74 * s ^ 2 * a ^ 4 * t1 ^ 4 := by
    have hsqScaled := mul_le_mul_of_nonneg_left ht2sq
      (by positivity : 0 ≤ s ^ 2 * a ^ 4)
    have hmixScaled := mul_le_mul_of_nonneg_left ht1t2
      (by positivity : 0 ≤ s ^ 2 * a ^ 4)
    nlinarith
  have hfinal :
      4 * ((t1 ^ 2 + t2) * a ^ 2) + 4 * a ^ 4 * t1 ^ 2 +
          2 * s ^ 2 * (24 * t1 ^ 4 * a ^ 4) +
          8 * s ^ 2 * a ^ 2 * (2 * t2 ^ 2 * a ^ 2) +
          2 * s ^ 2 * a ^ 4 * t2 ^ 2 +
          4 * s ^ 2 * a ^ 2 * t2 * ((t1 ^ 2 + t2) * a ^ 2) ≤
        8 * t1 ^ 2 * a ^ 2 + 4 * t2 * a ^ 2 +
          96 * t1 ^ 4 * a ^ 4 * s ^ 2 +
          4 * t2 ^ 2 * a ^ 2 * s ^ 2 := by
    have hnonradial :
        4 * ((t1 ^ 2 + t2) * a ^ 2) + 4 * a ^ 4 * t1 ^ 2 ≤
          8 * t1 ^ 2 * a ^ 2 + 4 * t2 * a ^ 2 := by
      nlinarith [ha4t1]
    have hradialFinal :
        2 * s ^ 2 * (24 * t1 ^ 4 * a ^ 4) +
            8 * s ^ 2 * a ^ 2 * (2 * t2 ^ 2 * a ^ 2) +
            2 * s ^ 2 * a ^ 4 * t2 ^ 2 +
            4 * s ^ 2 * a ^ 2 * t2 * ((t1 ^ 2 + t2) * a ^ 2) ≤
          96 * t1 ^ 4 * a ^ 4 * s ^ 2 +
            4 * t2 ^ 2 * a ^ 2 * s ^ 2 := by
      have hpos1 : 0 ≤ s ^ 2 * a ^ 4 * t1 ^ 4 := by positivity
      have hpos2 : 0 ≤ t2 ^ 2 * a ^ 2 * s ^ 2 := by positivity
      nlinarith [hradial]
    nlinarith
  calc
    (∫ v : ComplexUnitSphere N,
      (complexCenteredProjectiveSandwich v
        (concreteCOEWMatrix N K A) (concreteCOEY N K A)).re ^ 2
        ∂(complexUnitSphereProbabilityMeasure N)) =
        ∫ v, (complexCenteredProjectiveSandwich v
          (concreteCOEWMatrix N K A) Y).re ^ 2 ∂μ := by rfl
    _ ≤ ∫ v, M v ∂μ := hMain
    _ ≤ _ := hMbound.trans hfinal
    _ = h14ProjectiveSandwichSecondMomentEnvelope N K A := by
      unfold h14ProjectiveSandwichSecondMomentEnvelope
      simp only [t1, t2, a, s, n, c, div_eq_mul_inv, inv_pow]
      ring

/-! ## The separated conjugate-sandwich factor -/

/-- A dimension-uniform centered projective second-moment bound for an
arbitrary symmetric matrix.  This is the finite-projective input for the
concrete `R R† = YW` specialization below. -/
theorem integral_complexCenteredProjectiveConjugateSandwich_re_sq_le_trace_sq_h14
    {N : ℕ} (hN : 2 ≤ N) (R : ConcreteMatrixState N) (hR : R.IsSymm) :
    (∫ v : ComplexUnitSphere N,
      (complexCenteredProjectiveConjugateSandwich v R).re ^ 2
        ∂(complexUnitSphereProbabilityMeasure N)) ≤
      14 * (Matrix.trace (R * R.conjTranspose)).re ^ 2 / (N : ℝ) ^ 2 := by
  let μ := complexUnitSphereProbabilityMeasure N
  let Z := R * R.conjTranspose
  let n : ℝ := N
  let a : ℝ := n⁻¹
  let T : ℝ := (Matrix.trace Z).re
  let d : ComplexUnitSphere N → ℝ := fun v ↦
    (complexProjectiveTracePair v Z).re
  let M : ComplexUnitSphere N → ℝ := fun v ↦
    3 * (1 + 4 * a ^ 2) * d v ^ 2 + 3 * a ^ 4 * T ^ 2
  have hN1 : 1 ≤ N := le_trans (by omega) hN
  have hn : 0 < n := by
    dsimp only [n]
    exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hn2 : (2 : ℝ) ≤ n := by
    dsimp only [n]
    exact_mod_cast hN
  have ha0 : 0 ≤ a := inv_nonneg.mpr hn.le
  have haHalf : a ≤ (2 : ℝ)⁻¹ := by
    dsimp only [a]
    exact inv_anti₀ (by norm_num) hn2
  have ha2le : a ^ 2 ≤ (4 : ℝ)⁻¹ := by
    norm_num at haHalf ⊢
    nlinarith [sq_nonneg a]
  have hZ : Z.PosSemidef := Matrix.posSemidef_self_mul_conjTranspose R
  have hdInt : Integrable (fun v ↦ d v ^ 2) μ := by
    simpa only [d, μ, Z] using
      integrable_complexProjectiveTracePair_re_sq_h14 hN1 Z hZ.isHermitian
  have hCInt : Integrable (fun v : ComplexUnitSphere N ↦
      (complexCenteredProjectiveConjugateSandwich v R).re ^ 2) μ := by
    simpa only [μ] using
      integrable_complexCenteredProjectiveConjugateSandwich_re_sq_h14 hN1 R
  letI : IsProbabilityMeasure μ := by
    dsimp only [μ]
    exact complexUnitSphereProbabilityMeasure_isProbability hN1
  have hm1 : Integrable (fun v ↦
      3 * (1 + 4 * a ^ 2) * d v ^ 2) μ :=
    hdInt.const_mul (3 * (1 + 4 * a ^ 2))
  have hm2 : Integrable (fun _ : ComplexUnitSphere N ↦
      3 * a ^ 4 * T ^ 2) μ := integrable_const _
  have hMInt : Integrable M μ := by
    dsimp only [M]
    exact hm1.add hm2
  have hpoint : ∀ v : ComplexUnitSphere N,
      (complexCenteredProjectiveConjugateSandwich v R).re ^ 2 ≤ M v := by
    intro v
    calc
      _ ≤ 3 * ((1 + 4 * (N : ℝ)⁻¹ ^ 2) *
          (complexProjectiveTracePair v (R * R.conjTranspose)).re ^ 2 +
          (N : ℝ)⁻¹ ^ 4 *
            (Matrix.trace (R * R.conjTranspose)).re ^ 2) :=
        complexCenteredProjectiveConjugateSandwich_re_sq_pointwise_le_h14
          v R hR
      _ = M v := by
        dsimp only [M, d, T, Z, a, n]
        ring
  have hMain : (∫ v,
      (complexCenteredProjectiveConjugateSandwich v R).re ^ 2 ∂μ) ≤
      ∫ v, M v ∂μ := integral_mono hCInt hMInt hpoint
  have hMIntegral : (∫ v, M v ∂μ) =
      3 * (1 + 4 * a ^ 2) * (∫ v, d v ^ 2 ∂μ) +
        3 * a ^ 4 * T ^ 2 := by
    dsimp only [M]
    rw [integral_add hm1 hm2, integral_const_mul, integral_const]
    simp only [probReal_univ, one_smul]
  have hdBound : (∫ v, d v ^ 2 ∂μ) ≤ 2 * T ^ 2 * a ^ 2 := by
    simpa only [d, μ, Z, T, a, n, div_eq_mul_inv, inv_pow] using
      integral_posSemidef_complexProjectiveTracePair_re_sq_le_h14 hN1 Z hZ
  have hcoef0 : 0 ≤ 3 * (1 + 4 * a ^ 2) := by positivity
  have hMbound : (∫ v, M v ∂μ) ≤
      3 * (1 + 4 * a ^ 2) * (2 * T ^ 2 * a ^ 2) +
        3 * a ^ 4 * T ^ 2 := by
    rw [hMIntegral]
    exact add_le_add (mul_le_mul_of_nonneg_left hdBound hcoef0) le_rfl
  have hcoef : 6 * (1 + 4 * a ^ 2) + 3 * a ^ 2 ≤ 14 := by
    nlinarith
  have hscale0 : 0 ≤ a ^ 2 * T ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  calc
    (∫ v : ComplexUnitSphere N,
      (complexCenteredProjectiveConjugateSandwich v R).re ^ 2
        ∂(complexUnitSphereProbabilityMeasure N)) =
        ∫ v, (complexCenteredProjectiveConjugateSandwich v R).re ^ 2 ∂μ := by
          rfl
    _ ≤ ∫ v, M v ∂μ := hMain
    _ ≤ 3 * (1 + 4 * a ^ 2) * (2 * T ^ 2 * a ^ 2) +
        3 * a ^ 4 * T ^ 2 := hMbound
    _ = (6 * (1 + 4 * a ^ 2) + 3 * a ^ 2) * (a ^ 2 * T ^ 2) := by ring
    _ ≤ 14 * (a ^ 2 * T ^ 2) :=
      mul_le_mul_of_nonneg_right hcoef hscale0
    _ = 14 * (Matrix.trace (R * R.conjTranspose)).re ^ 2 /
        (N : ℝ) ^ 2 := by
      simp only [a, n, T, Z, div_eq_mul_inv, inv_pow]
      ring

/-- Concrete specialization of the conjugate-sandwich factor bound, using
`R R† = YW` only through its exact trace identity. -/
theorem integral_concreteCOERMatrix_centeredConjugateSandwich_re_sq_le_h14
    {N K : ℕ} (hN : 2 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (A : ConcreteMatrixState N)
    (hsymm : (unscaleCOECorner K A).IsSymm)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    (∫ v : ComplexUnitSphere N,
      (complexCenteredProjectiveConjugateSandwich v
        (concreteCOERMatrix N K A)).re ^ 2
        ∂(complexUnitSphereProbabilityMeasure N)) ≤
      h14ProjectiveConjugateSecondMomentEnvelope N K A := by
  let R := concreteCOERMatrix N K A
  let n : ℝ := N
  let c : ℝ := concreteCOEExponent N K
  let a : ℝ := n⁻¹
  let s : ℝ := c⁻¹
  let t1 : ℝ := concreteCOETraceOne N K A
  let t2 : ℝ := concreteCOETraceTwo N K A
  let T : ℝ := (Matrix.trace (R * R.conjTranspose)).re
  have hn : 0 < n := by
    dsimp only [n]
    exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hc : 0 < c := by
    dsimp only [c, concreteCOEExponent]
    have hg : (2 : ℝ) * (N : ℝ) + 8 ≤ (K : ℝ) := by
      exact_mod_cast hgap
    linarith
  have ha0 : 0 ≤ a := inv_nonneg.mpr hn.le
  have hs0 : 0 ≤ s := inv_nonneg.mpr hc.le
  have ht2 : 0 ≤ t2 :=
    concreteCOETraceTwo_nonneg_of_support hgap A hsupport
  have hR : R.IsSymm := by
    simpa only [R] using
      concreteCOERMatrix_isSymm_of_support A hsymm hsupport
  have hraw :
      (∫ v : ComplexUnitSphere N,
        (complexCenteredProjectiveConjugateSandwich v R).re ^ 2
          ∂(complexUnitSphereProbabilityMeasure N)) ≤
        14 * T ^ 2 * a ^ 2 := by
    simpa only [R, T, a, n, div_eq_mul_inv, inv_pow] using
      integral_complexCenteredProjectiveConjugateSandwich_re_sq_le_trace_sq_h14
        hN R hR
  have hT : T = t1 + t2 * s := by
    have htrace := concreteCOERMatrix_sq_trace_re A hc hsupport
    simpa only [T, R, t1, t2, s, c, div_eq_mul_inv] using htrace
  have hTsq : T ^ 2 ≤ 2 * t1 ^ 2 + 2 * t2 ^ 2 * s ^ 2 := by
    rw [hT]
    nlinarith [sq_nonneg (t1 - t2 * s)]
  have hscale := mul_le_mul_of_nonneg_left hTsq
    (by positivity : 0 ≤ 14 * a ^ 2)
  have htraceBound : 14 * T ^ 2 * a ^ 2 ≤
      28 * t1 ^ 2 * a ^ 2 + 28 * t2 ^ 2 * a ^ 2 * s ^ 2 := by
    nlinarith
  have hpos1 : 0 ≤ t1 ^ 2 * a ^ 2 := by positivity
  have hpos2 : 0 ≤ t2 * a ^ 2 := mul_nonneg ht2 (sq_nonneg _)
  have hpos3 : 0 ≤ t2 ^ 2 * a ^ 2 * s ^ 2 := by positivity
  calc
    (∫ v : ComplexUnitSphere N,
      (complexCenteredProjectiveConjugateSandwich v
        (concreteCOERMatrix N K A)).re ^ 2
        ∂(complexUnitSphereProbabilityMeasure N)) =
        ∫ v, (complexCenteredProjectiveConjugateSandwich v R).re ^ 2
          ∂(complexUnitSphereProbabilityMeasure N) := by rfl
    _ ≤ 14 * T ^ 2 * a ^ 2 := hraw
    _ ≤ 28 * t1 ^ 2 * a ^ 2 + 28 * t2 ^ 2 * a ^ 2 * s ^ 2 :=
      htraceBound
    _ ≤ 40 * t1 ^ 2 * a ^ 2 + 36 * t2 * a ^ 2 +
        76 * t2 ^ 2 * a ^ 2 * s ^ 2 := by nlinarith
    _ = h14ProjectiveConjugateSecondMomentEnvelope N K A := by
      unfold h14ProjectiveConjugateSecondMomentEnvelope
      simp only [t1, t2, a, s, n, c, div_eq_mul_inv, inv_pow]
      ring

/-! ## The one-dimensional centered case and exact contract closure -/

theorem complexCenteredProjectiveSandwich_fin_one_eq_zero_h14
    (v : ComplexUnitSphere 1) (W Y : ConcreteMatrixState 1) :
    complexCenteredProjectiveSandwich v W Y = 0 := by
  rw [complexCenteredProjectiveSandwich_eq_trace_h14,
    concreteCenteredOrbitalDirection_fin_one_eq_zero]
  simp

theorem complexCenteredProjectiveConjugateSandwich_fin_one_eq_zero_h14
    (v : ComplexUnitSphere 1) (R : ConcreteMatrixState 1) :
    complexCenteredProjectiveConjugateSandwich v R = 0 := by
  rw [complexCenteredProjectiveConjugateSandwich_eq_trace_h14,
    concreteCenteredOrbitalDirection_fin_one_eq_zero]
  simp

theorem integral_complexCenteredProjectiveSandwich_re_sq_fin_one_eq_zero_h14
    (W Y : ConcreteMatrixState 1) :
    (∫ v : ComplexUnitSphere 1,
      (complexCenteredProjectiveSandwich v W Y).re ^ 2
        ∂(complexUnitSphereProbabilityMeasure 1)) = 0 := by
  simp_rw [complexCenteredProjectiveSandwich_fin_one_eq_zero_h14]
  simp

theorem integral_complexCenteredProjectiveConjugateSandwich_re_sq_fin_one_eq_zero_h14
    (R : ConcreteMatrixState 1) :
    (∫ v : ComplexUnitSphere 1,
      (complexCenteredProjectiveConjugateSandwich v R).re ^ 2
        ∂(complexUnitSphereProbabilityMeasure 1)) = 0 := by
  simp_rw [complexCenteredProjectiveConjugateSandwich_fin_one_eq_zero_h14]
  simp

/-- PROVED non-endpoint producer: both separated finite-projective integral
bounds, with the exact quantifiers and constants of the formerly conditional
contract.  This theorem contains no beta-prime or radial-law input. -/
theorem h14_centeredEllTwoSeparatedFactorIntegralBounds_internal
    (N K : ℕ) :
    H14CenteredEllTwoSeparatedFactorIntegralBoundsContract N K := by
  intro hN hgap A hsymm hsupport
  by_cases hOne : N = 1
  · subst N
    have ht2 : 0 ≤ concreteCOETraceTwo 1 K A :=
      concreteCOETraceTwo_nonneg_of_support hgap A hsupport
    constructor
    · rw [integral_complexCenteredProjectiveSandwich_re_sq_fin_one_eq_zero_h14]
      unfold h14ProjectiveSandwichSecondMomentEnvelope
      positivity
    · rw [integral_complexCenteredProjectiveConjugateSandwich_re_sq_fin_one_eq_zero_h14]
      unfold h14ProjectiveConjugateSecondMomentEnvelope
      positivity
  · have hN2 : 2 ≤ N := by omega
    exact ⟨
      integral_complexCenteredProjectiveSandwich_re_sq_le_h14
        hN2 hgap A hsupport,
      integral_concreteCOERMatrix_centeredConjugateSandwich_re_sq_le_h14
        hN2 hgap A hsymm hsupport⟩

/-- PROVED non-endpoint fixed-matrix contraction, obtained by feeding the
now-internal separated factor bounds into the checked polarization ledger. -/
theorem h14_centeredEllTwoProjectiveContraction_internal (N K : ℕ) :
    H14CenteredEllTwoProjectiveContractionContract N K :=
  h14_centeredEllTwoProjectiveContraction_of_integralBounds
    (h14_centeredEllTwoSeparatedFactorIntegralBounds_internal N K)

/-- PROVED non-endpoint package with the positive projective-cancellation
envelope.  No beta-prime averaging is performed in this module. -/
theorem h14_fixedMatrix_projectiveCancellation_package_internal
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (A : ConcreteMatrixState N)
    (hsymm : (unscaleCOECorner K A).IsSymm)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    Integrable (h14CenteredSandwichSecondSquare N K A)
        (complexUnitSphereProbabilityMeasure N) ∧
      (∫ v, ‖h14CenteredSandwichSecondSquare N K A v‖
          ∂(complexUnitSphereProbabilityMeasure N)) ≤
        h14ProjectiveCancellationEnvelope N K A :=
  h14_fixedMatrix_projectiveCancellation_package_conditional
    (h14_centeredEllTwoProjectiveContraction_internal N K)
    hN hgap A hsymm hsupport

#print axioms complexProjectiveTracePair_eq_star_dotProduct_mulVec_h14
#print axioms complexProjectiveTracePair_re_nonneg_of_posSemidef_h14
#print axioms posSemidef_trace_four_re_le_trace_square_re_sq_h14
#print axioms posSemidef_trace_four_re_le_trace_re_four_h14
#print axioms integral_complexProjectiveTracePair_re_sq_eq_h14
#print axioms integral_complexProjectiveTracePair_re_fourth_eq_h14
#print axioms integral_concreteCOEY_tracePair_re_sq_le_h14
#print axioms integral_concreteCOEY_sq_tracePair_re_sq_le_h14
#print axioms integral_concreteCOEY_tracePair_re_fourth_le_h14
#print axioms complexCenteredProjectiveSandwich_re_expansion_h14
#print axioms complexCenteredProjectiveSandwich_re_sq_pointwise_le_h14
#print axioms integral_complexCenteredProjectiveSandwich_re_sq_le_h14
#print axioms complexProjectiveBilinearNormSq_eq_normSq_bilinear_h14
#print axioms complexProjectiveTracePair_mul_conjTranspose_eq_sum_normSq_h14
#print axioms complexProjectiveBilinearNormSq_re_le_tracePair_mul_conjTranspose_re_h14
#print axioms integral_posSemidef_complexProjectiveTracePair_re_sq_le_h14
#print axioms complexCenteredProjectiveConjugateSandwich_re_expansion_h14
#print axioms complexCenteredProjectiveConjugateSandwich_re_sq_pointwise_le_h14
#print axioms integral_complexCenteredProjectiveConjugateSandwich_re_sq_le_trace_sq_h14
#print axioms integral_concreteCOERMatrix_centeredConjugateSandwich_re_sq_le_h14
#print axioms complexCenteredProjectiveSandwich_fin_one_eq_zero_h14
#print axioms complexCenteredProjectiveConjugateSandwich_fin_one_eq_zero_h14
#print axioms h14_centeredEllTwoSeparatedFactorIntegralBounds_internal
#print axioms h14_centeredEllTwoProjectiveContraction_internal
#print axioms h14_fixedMatrix_projectiveCancellation_package_internal

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
