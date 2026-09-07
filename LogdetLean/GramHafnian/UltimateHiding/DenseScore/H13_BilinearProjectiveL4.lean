import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H13_MixedPairBilinearFactorization
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H13_PosSemidefProjectiveL4
import Mathlib.Tactic

/-!
# Sharp projective L4 bound for the H13 bilinear factors

For a symmetric matrix `R`, projective Cauchy--Schwarz gives

`|v^* R conjugate(v)|^2 <= Tr(P_v R R^*)`.

Combining this with the exact projective second moment proves the dimension-
sharp bound

`||v^* R conjugate(v)||_4^2 <= 2 Tr(R R^*) / N`.

This is the quantitative input needed to feed the scalar factorization of the
H13 polynomial into four-factor Holder.
-/

open MeasureTheory
open scoped ComplexOrder MatrixOrder

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open U08

set_option maxHeartbeats 2400000
set_option linter.style.haveILetI false

/-- The conjugate-bilinear projective factor is measurable. -/
theorem measurable_complexProjectiveConjugateBilinearPair_h13
    {N : ℕ} (R : ConcreteMatrixState N) :
    Measurable (fun v : ComplexUnitSphere N =>
      complexProjectiveConjugateBilinearPair v R) := by
  unfold complexProjectiveConjugateBilinearPair
  fun_prop

/-- A coordinate of a unit vector has norm at most one. -/
private theorem complexUnitSphere_coordinate_norm_le_one_h13
    {N : ℕ} (v : ComplexUnitSphere N) (i : Fin N) :
    ‖v.1 i‖ ≤ 1 := by
  have hi := PiLp.norm_apply_le v.1 i
  rw [mem_sphere_zero_iff_norm.mp v.2] at hi
  exact hi

/-- Finite-dimensional boundedness supplies `L4` membership independently
of the quantitative estimate. -/
theorem memLp_complexProjectiveConjugateBilinearPair_four_h13
    {N : ℕ} (hN : 1 ≤ N) (R : ConcreteMatrixState N) :
    MemLp (fun v : ComplexUnitSphere N =>
      complexProjectiveConjugateBilinearPair v R) 4
      (complexUnitSphereProbabilityMeasure N) := by
  letI : IsProbabilityMeasure (complexUnitSphereProbabilityMeasure N) :=
    complexUnitSphereProbabilityMeasure_isProbability hN
  let M : ℝ := ∑ i, ∑ j, ‖R i j‖
  have hmeas : AEStronglyMeasurable
      (fun v : ComplexUnitSphere N =>
        complexProjectiveConjugateBilinearPair v R)
      (complexUnitSphereProbabilityMeasure N) :=
    (measurable_complexProjectiveConjugateBilinearPair_h13 R).aestronglyMeasurable
  apply MemLp.of_bound hmeas M
  filter_upwards [] with v
  unfold complexProjectiveConjugateBilinearPair
  calc
    ‖∑ i, ∑ j, star (v.1 i) * R i j * star (v.1 j)‖ ≤
        ∑ i, ‖∑ j, star (v.1 i) * R i j * star (v.1 j)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i, ∑ j, ‖star (v.1 i) * R i j * star (v.1 j)‖ := by
      apply Finset.sum_le_sum
      intro i _
      exact norm_sum_le _ _
    _ ≤ ∑ i, ∑ j, ‖R i j‖ := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul, norm_mul, norm_star, norm_star]
      have hi := complexUnitSphere_coordinate_norm_le_one_h13 v i
      have hj := complexUnitSphere_coordinate_norm_le_one_h13 v j
      calc
        ‖v.1 i‖ * ‖R i j‖ * ‖v.1 j‖ ≤
            1 * ‖R i j‖ * 1 := by gcongr
        _ = ‖R i j‖ := by ring
    _ = M := rfl

/-- Pointwise fourth-power domination by the square of a positive projective
quadratic form. -/
theorem norm_conjugateBilinearPair_four_le_tracePair_sq_h13
    {N : ℕ} (v : ComplexUnitSphere N) (R : ConcreteMatrixState N)
    (hR : R.IsSymm) :
    ‖complexProjectiveConjugateBilinearPair v R‖ ^ 4 ≤
      (complexProjectiveTracePair v (R * R.conjTranspose)).re ^ 2 := by
  let b := complexProjectiveConjugateBilinearPair v R
  let w := complexProjectiveBilinearNormSq v R
  let q := (complexProjectiveTracePair v (R * R.conjTranspose)).re
  have hw : w.re = ‖b‖ ^ 2 := by
    unfold w b complexProjectiveConjugateBilinearPair
    rw [complexProjectiveBilinearNormSq_eq_normSq_bilinear_h14]
    simp only [Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have hw0 : 0 ≤ w.re := by rw [hw]; positivity
  have hwq : w.re ≤ q := by
    simpa only [w, q] using
      complexProjectiveBilinearNormSq_re_le_tracePair_mul_conjTranspose_re_h14
        v R hR
  have hq0 : 0 ≤ q := hw0.trans hwq
  have hsq := mul_self_le_mul_self hw0 hwq
  change ‖b‖ ^ 4 ≤ q ^ 2
  calc
    ‖b‖ ^ 4 = (w.re) ^ 2 := by rw [hw]; ring
    _ ≤ q ^ 2 := by simpa only [pow_two] using hsq

/-- Exact fourth-power comparison at the `lpNorm` level. -/
theorem lpNorm_conjugateBilinearPair_four_pow_four_le_h13
    {N : ℕ} (hN : 1 ≤ N) (R : ConcreteMatrixState N)
    (hR : R.IsSymm) :
    lpNorm (fun v : ComplexUnitSphere N =>
      complexProjectiveConjugateBilinearPair v R) 4
        (complexUnitSphereProbabilityMeasure N) ^ 4 ≤
      2 * (Matrix.trace (R * R.conjTranspose)).re ^ 2 / (N : ℝ) ^ 2 := by
  let μ := complexUnitSphereProbabilityMeasure N
  let b : ComplexUnitSphere N → ℂ := fun v =>
    complexProjectiveConjugateBilinearPair v R
  let H : ConcreteMatrixState N := R * R.conjTranspose
  let t : ℝ := (Matrix.trace H).re
  let s : ℝ := (Matrix.trace (H * H)).re
  let n : ℝ := N
  letI : IsProbabilityMeasure μ := by
    simpa only [μ] using complexUnitSphereProbabilityMeasure_isProbability hN
  have hb : MemLp b 4 μ := by
    simpa only [b, μ] using
      memLp_complexProjectiveConjugateBilinearPair_four_h13 hN R
  have hnormInt : Integrable (fun v => ‖b v‖ ^ 4) μ := by
    have h := hb.integrable_norm_rpow (by norm_num) (by norm_num)
    norm_num at h
    exact h
  have hH : H.PosSemidef := by
    simpa only [H] using Matrix.posSemidef_self_mul_conjTranspose R
  have hp4 := memLp_posSemidef_projectiveTracePair_re_four_h13 hN H hH
  have hp2 : MemLp (fun v : ComplexUnitSphere N =>
      (complexProjectiveTracePair v H).re) 2 μ := by
    simpa only [μ] using hp4.mono_exponent (p := (2 : ENNReal)) (by norm_num)
  have hpSqInt : Integrable (fun v : ComplexUnitSphere N =>
      (complexProjectiveTracePair v H).re ^ 2) μ := by
    have h := hp2.integrable_norm_rpow (by norm_num) (by norm_num)
    norm_num at h
    apply h.congr
    filter_upwards [] with v
    have hq0 := complexProjectiveTracePair_re_nonneg_of_posSemidef_h14 v H hH
    rfl
  have hpoint : ∀ v : ComplexUnitSphere N,
      ‖b v‖ ^ 4 ≤ (complexProjectiveTracePair v H).re ^ 2 := by
    intro v
    simpa only [b, H] using
      norm_conjugateBilinearPair_four_le_tracePair_sq_h13 v R hR
  have hint : (∫ v, ‖b v‖ ^ 4 ∂μ) ≤
      ∫ v, (complexProjectiveTracePair v H).re ^ 2 ∂μ :=
    integral_mono hnormInt hpSqInt hpoint
  have hn : 0 < n := by
    dsimp only [n]
    exact_mod_cast (Nat.zero_lt_of_lt hN)
  have ht : 0 ≤ t := by
    exact (Complex.nonneg_iff.mp hH.trace_nonneg).1
  have hsle : s ≤ t ^ 2 := by
    simpa only [s, t, pow_two] using
      posSemidef_trace_square_re_le_trace_re_sq H hH
  have hden : n ^ 2 ≤ n * (n + 1) := by nlinarith
  have hmoment :
      (∫ v, (complexProjectiveTracePair v H).re ^ 2 ∂μ) ≤
        2 * t ^ 2 / n ^ 2 := by
    rw [show (∫ v, (complexProjectiveTracePair v H).re ^ 2 ∂μ) =
        (n * (n + 1))⁻¹ * (t ^ 2 + s) by
      simpa only [μ, n, t, s, inv_mul_eq_div] using
        integral_complexProjectiveTracePair_re_sq_eq_h14 hN H hH.isHermitian]
    rw [inv_mul_eq_div]
    calc
      (t ^ 2 + s) / (n * (n + 1)) ≤
          (2 * t ^ 2) / (n * (n + 1)) := by
        apply div_le_div_of_nonneg_right (by nlinarith) (by positivity)
      _ ≤ (2 * t ^ 2) / n ^ 2 :=
        div_le_div_of_nonneg_left (by positivity) (pow_pos hn 2) hden
  have hnormEq : lpNorm b 4 μ ^ 4 = ∫ v, ‖b v‖ ^ 4 ∂μ := by
    rw [← lpNorm_norm hb.aestronglyMeasurable 4]
    exact lpNorm_four_pow_four_eq_integral_pow_four_h9 hb.norm
  rw [show (fun v : ComplexUnitSphere N =>
      complexProjectiveConjugateBilinearPair v R) = b by rfl]
  rw [hnormEq]
  calc
    (∫ v, ‖b v‖ ^ 4 ∂μ) ≤
        ∫ v, (complexProjectiveTracePair v H).re ^ 2 ∂μ := hint
    _ ≤ 2 * t ^ 2 / n ^ 2 := hmoment
    _ = 2 * (Matrix.trace (R * R.conjTranspose)).re ^ 2 /
        (N : ℝ) ^ 2 := rfl

/-- Dimension-sharp linearized form: the squared `L4` norm is controlled by
twice the trace-over-dimension of the Gram matrix. -/
theorem lpNorm_conjugateBilinearPair_four_sq_le_h13
    {N : ℕ} (hN : 1 ≤ N) (R : ConcreteMatrixState N)
    (hR : R.IsSymm) :
    lpNorm (fun v : ComplexUnitSphere N =>
      complexProjectiveConjugateBilinearPair v R) 4
        (complexUnitSphereProbabilityMeasure N) ^ 2 ≤
      2 * (Matrix.trace (R * R.conjTranspose)).re / (N : ℝ) := by
  let x := lpNorm (fun v : ComplexUnitSphere N =>
    complexProjectiveConjugateBilinearPair v R) 4
      (complexUnitSphereProbabilityMeasure N)
  let t := (Matrix.trace (R * R.conjTranspose)).re
  let n : ℝ := N
  have hfour := lpNorm_conjugateBilinearPair_four_pow_four_le_h13
    hN R hR
  have hGram : (R * R.conjTranspose).PosSemidef :=
    Matrix.posSemidef_self_mul_conjTranspose R
  have ht : 0 ≤ t := by
    exact (Complex.nonneg_iff.mp hGram.trace_nonneg).1
  have hn : 0 < n := by
    dsimp only [n]
    exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hx : 0 ≤ x := lpNorm_nonneg
  change x ^ 2 ≤ 2 * t / n
  change x ^ 4 ≤ 2 * t ^ 2 / n ^ 2 at hfour
  have hratio : 0 ≤ t / n := div_nonneg ht hn.le
  have hrelax : 2 * t ^ 2 / n ^ 2 ≤ (2 * t / n) ^ 2 := by
    rw [div_pow]
    have hn2 : 0 < n ^ 2 := pow_pos hn 2
    apply (div_le_div_iff_of_pos_right hn2).2
    nlinarith [sq_nonneg t]
  have hsquare : (x ^ 2) ^ 2 ≤ (2 * t / n) ^ 2 := by
    calc
      (x ^ 2) ^ 2 = x ^ 4 := by ring
      _ ≤ 2 * t ^ 2 / n ^ 2 := hfour
      _ ≤ (2 * t / n) ^ 2 := hrelax
  have hrhs : 0 ≤ 2 * t / n := by positivity
  exact (sq_le_sq₀ (sq_nonneg x) hrhs).mp hsquare

/-- The conjugate transpose factor has the same `L4` membership. -/
theorem memLp_complexProjectiveTransposeBilinearPair_conjTranspose_four_h13
    {N : ℕ} (hN : 1 ≤ N) (R : ConcreteMatrixState N) :
    MemLp (fun v : ComplexUnitSphere N =>
      complexProjectiveTransposeBilinearPair v R.conjTranspose) 4
      (complexUnitSphereProbabilityMeasure N) := by
  have h := memLp_complexProjectiveConjugateBilinearPair_four_h13 hN R
  let f : ComplexUnitSphere N → ℂ := fun v =>
    complexProjectiveConjugateBilinearPair v R
  have heq : (fun v : ComplexUnitSphere N =>
      complexProjectiveTransposeBilinearPair v R.conjTranspose) = star f := by
    funext v
    exact complexProjectiveTransposeBilinearPair_conjTranspose_eq_star_h13 v R
  rw [heq]
  simpa only [f] using h.star

/-- The conjugate transpose factor has the identical quantitative bound. -/
theorem lpNorm_transposeBilinearPair_conjTranspose_four_sq_le_h13
    {N : ℕ} (hN : 1 ≤ N) (R : ConcreteMatrixState N)
    (hR : R.IsSymm) :
    lpNorm (fun v : ComplexUnitSphere N =>
      complexProjectiveTransposeBilinearPair v R.conjTranspose) 4
        (complexUnitSphereProbabilityMeasure N) ^ 2 ≤
      2 * (Matrix.trace (R * R.conjTranspose)).re / (N : ℝ) := by
  have h := lpNorm_conjugateBilinearPair_four_sq_le_h13 hN R hR
  let f : ComplexUnitSphere N → ℂ := fun v =>
    complexProjectiveConjugateBilinearPair v R
  have heq : (fun v : ComplexUnitSphere N =>
      complexProjectiveTransposeBilinearPair v R.conjTranspose) = star f := by
    funext v
    exact complexProjectiveTransposeBilinearPair_conjTranspose_eq_star_h13 v R
  rw [heq]
  change lpNorm (star f) 4 (complexUnitSphereProbabilityMeasure N) ^ 2 ≤ _
  have hstar : lpNorm (star f) 4 (complexUnitSphereProbabilityMeasure N) =
      lpNorm f 4 (complexUnitSphereProbabilityMeasure N) := by
    have hfMeas : AEStronglyMeasurable f
        (complexUnitSphereProbabilityMeasure N) := by
      dsimp only [f]
      exact (measurable_complexProjectiveConjugateBilinearPair_h13 R).aestronglyMeasurable
    have hstarMeas : AEStronglyMeasurable (star f)
        (complexUnitSphereProbabilityMeasure N) := hfMeas.star
    calc
      lpNorm (star f) 4 (complexUnitSphereProbabilityMeasure N) =
          lpNorm (fun v => ‖(star f) v‖) 4
            (complexUnitSphereProbabilityMeasure N) :=
        (lpNorm_norm hstarMeas 4).symm
      _ = lpNorm (fun v => ‖f v‖) 4
          (complexUnitSphereProbabilityMeasure N) := by
        congr 1
        funext v
        simp
      _ = lpNorm f 4 (complexUnitSphereProbabilityMeasure N) :=
        lpNorm_norm hfMeas 4
  rw [hstar]
  simpa only [f] using h

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
