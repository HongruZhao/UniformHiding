import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H14_SeparatedFactorIntegralBounds
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.PositiveTraceMomentInternal
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.H9CenteredTraceSteinClosure
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H13_ProjectiveMixedHolder
import Mathlib.Tactic

/-!
# Positive-matrix projective L4 package for H13

The H13 rank-one expansion contains projective quadratic forms of positive
products of the commuting support matrices `W=I+Z` and `Z`.  This module
packages the exact order-four sphere identity as a reusable `L^4` estimate.
-/

open MeasureTheory
open scoped ComplexOrder MatrixOrder

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open U08

/-- A positive-semidefinite quadratic form has fourth projective moment at
most `24 (Tr A)^4 / N^4`. -/
theorem integral_posSemidef_projectiveTracePair_re_fourth_le_h13
    {N : ℕ} (hN : 1 ≤ N) (A : ConcreteMatrixState N)
    (hA : A.PosSemidef) :
    (∫ v : ComplexUnitSphere N,
      (complexProjectiveTracePair v A).re ^ 4
        ∂(complexUnitSphereProbabilityMeasure N)) ≤
      24 * (Matrix.trace A).re ^ 4 / (N : ℝ) ^ 4 := by
  let n : ℝ := N
  let t1 : ℝ := (Matrix.trace A).re
  let t2 : ℝ := (Matrix.trace (A * A)).re
  let t3 : ℝ := (Matrix.trace (A * A * A)).re
  let t4 : ℝ := (Matrix.trace (A * A * A * A)).re
  have hn : 0 < n := by
    dsimp only [n]
    exact_mod_cast (Nat.zero_lt_of_lt hN)
  have ht1 : 0 ≤ t1 := by
    exact (Complex.nonneg_iff.mp hA.trace_nonneg).1
  have ht2 : 0 ≤ t2 := by
    have htr := (hA.pow 2).trace_nonneg
    simpa only [t2, pow_two] using (Complex.nonneg_iff.mp htr).1
  have ht3 : 0 ≤ t3 := by
    have htr := (hA.pow 3).trace_nonneg
    simpa [t3, pow_succ, Matrix.mul_assoc] using
      (Complex.nonneg_iff.mp htr).1
  have ht4 : 0 ≤ t4 := by
    have htr := (hA.pow 4).trace_nonneg
    simpa [t4, pow_succ, Matrix.mul_assoc] using
      (Complex.nonneg_iff.mp htr).1
  have ht2le : t2 ≤ t1 ^ 2 := by
    simpa only [t1, t2, pow_two] using
      posSemidef_trace_square_re_le_trace_re_sq A hA
  have ht3le : t3 ≤ t1 ^ 3 := by
    simpa [t1, t3, pow_succ, Matrix.mul_assoc] using
      posSemidef_trace_cube_re_le_trace_re_cube A hA
  have ht4le : t4 ≤ t1 ^ 4 := by
    simpa only [t1, t4] using
      posSemidef_trace_four_re_le_trace_re_four_h14 A hA
  have ht1t2 : t1 ^ 2 * t2 ≤ t1 ^ 4 := by
    have h := mul_le_mul_of_nonneg_left ht2le (sq_nonneg t1)
    nlinarith
  have ht2sq : t2 ^ 2 ≤ t1 ^ 4 := by
    have h := mul_self_le_mul_self ht2 ht2le
    nlinarith
  have ht1t3 : t1 * t3 ≤ t1 ^ 4 := by
    have h := mul_le_mul_of_nonneg_left ht3le ht1
    nlinarith
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
    hN A hA.isHermitian]
  change (n * (n + 1) * (n + 2) * (n + 3))⁻¹ *
      (t1 ^ 4 + 6 * (t1 ^ 2 * t2) + 3 * t2 ^ 2 +
        8 * (t1 * t3) + 6 * t4) ≤ 24 * t1 ^ 4 / n ^ 4
  rw [inv_mul_eq_div]
  calc
    _ ≤ (24 * t1 ^ 4) / (n * (n + 1) * (n + 2) * (n + 3)) :=
      div_le_div_of_nonneg_right hnumle (by positivity)
    _ ≤ (24 * t1 ^ 4) / n ^ 4 :=
      div_le_div_of_nonneg_left (by positivity) (pow_pos hn 4) hden

/-- The real projective quadratic form of a PSD matrix belongs to `L^4`. -/
theorem memLp_posSemidef_projectiveTracePair_re_four_h13
    {N : ℕ} (hN : 1 ≤ N) (A : ConcreteMatrixState N)
    (hA : A.PosSemidef) :
    MemLp (fun v : ComplexUnitSphere N =>
      (complexProjectiveTracePair v A).re) 4
      (complexUnitSphereProbabilityMeasure N) := by
  let f : ComplexUnitSphere N → ℝ := fun v =>
    (complexProjectiveTracePair v A).re
  have hmeas : AEStronglyMeasurable f
      (complexUnitSphereProbabilityMeasure N) := by
    dsimp only [f]
    change AEStronglyMeasurable
      (fun v : ComplexUnitSphere N =>
        RCLike.re (complexProjectiveTracePair v A))
      (complexUnitSphereProbabilityMeasure N)
    exact (integrable_complexProjectiveTracePair hN A).re.aestronglyMeasurable
  apply (integrable_norm_rpow_iff hmeas (by norm_num) (by norm_num)).mp
  have hfour : Integrable (fun v : ComplexUnitSphere N => f v ^ 4)
      (complexUnitSphereProbabilityMeasure N) := by
    have h := (integrable_complexProjectiveTracePair_fourth hN A).re
    apply h.congr
    filter_upwards [] with v
    have him :=
      complexProjectiveTracePair_im_eq_zero_of_isHermitian_h12_low v A
        hA.isHermitian
    simp only [f, pow_succ, pow_zero, one_mul, Complex.mul_re,
      him, mul_zero, sub_zero, RCLike.re_to_complex]
  simpa [Real.rpow_natCast, norm_pow] using hfour.norm

/-- Convenient linearized `L^4` norm bound for a PSD projective quadratic
form.  The constant `3` is a clean relaxation of `24^(1/4)`. -/
theorem lpNorm_posSemidef_projectiveTracePair_re_four_le_h13
    {N : ℕ} (hN : 1 ≤ N) (A : ConcreteMatrixState N)
    (hA : A.PosSemidef) :
    lpNorm (fun v : ComplexUnitSphere N =>
      (complexProjectiveTracePair v A).re) 4
        (complexUnitSphereProbabilityMeasure N) ≤
      3 * (Matrix.trace A).re / (N : ℝ) := by
  let f : ComplexUnitSphere N → ℝ := fun v =>
    (complexProjectiveTracePair v A).re
  let n : ℝ := N
  let t : ℝ := (Matrix.trace A).re
  have hf : MemLp f 4 (complexUnitSphereProbabilityMeasure N) := by
    simpa only [f] using
      memLp_posSemidef_projectiveTracePair_re_four_h13 hN A hA
  have hn : 0 < n := by
    dsimp only [n]
    exact_mod_cast (Nat.zero_lt_of_lt hN)
  have ht : 0 ≤ t := by
    exact (Complex.nonneg_iff.mp hA.trace_nonneg).1
  apply le_of_pow_le_pow_left₀ (by norm_num : (4 : ℕ) ≠ 0) (by positivity)
  rw [lpNorm_four_pow_four_eq_integral_pow_four_h9 hf]
  calc
    (∫ v, f v ^ 4 ∂(complexUnitSphereProbabilityMeasure N)) ≤
        24 * t ^ 4 / n ^ 4 := by
      simpa only [f, t, n] using
        integral_posSemidef_projectiveTracePair_re_fourth_le_h13 hN A hA
    _ ≤ (3 * t / n) ^ 4 := by
      have hn4 : 0 < n ^ 4 := pow_pos hn 4
      rw [div_pow]
      apply (div_le_div_iff_of_pos_right hn4).2
      nlinarith [pow_nonneg ht 4]

/-- The centered real projective pairing of a PSD matrix is in `L^4`. -/
theorem memLp_posSemidef_centeredProjectiveTracePair_re_four_h13
    {N : ℕ} (hN : 1 ≤ N) (A : ConcreteMatrixState N)
    (hA : A.PosSemidef) :
    MemLp (fun v : ComplexUnitSphere N =>
      (complexCenteredProjectiveTracePair v A).re) 4
      (complexUnitSphereProbabilityMeasure N) := by
  letI : IsProbabilityMeasure (complexUnitSphereProbabilityMeasure N) :=
    complexUnitSphereProbabilityMeasure_isProbability hN
  have hp := memLp_posSemidef_projectiveTracePair_re_four_h13 hN A hA
  have hc : MemLp (fun _ : ComplexUnitSphere N =>
      (N : ℝ)⁻¹ * (Matrix.trace A).re) 4
      (complexUnitSphereProbabilityMeasure N) := memLp_const _
  convert hp.sub hc using 1
  funext v
  unfold complexCenteredProjectiveTracePair
  norm_num [Complex.mul_re]

/-- Centering costs at most one further trace-over-dimension term. -/
theorem lpNorm_posSemidef_centeredProjectiveTracePair_re_four_le_h13
    {N : ℕ} (hN : 1 ≤ N) (A : ConcreteMatrixState N)
    (hA : A.PosSemidef) :
    lpNorm (fun v : ComplexUnitSphere N =>
      (complexCenteredProjectiveTracePair v A).re) 4
        (complexUnitSphereProbabilityMeasure N) ≤
      4 * (Matrix.trace A).re / (N : ℝ) := by
  let μ := complexUnitSphereProbabilityMeasure N
  let t : ℝ := (Matrix.trace A).re
  let c : ℝ := (N : ℝ)⁻¹ * t
  letI : IsProbabilityMeasure μ :=
    complexUnitSphereProbabilityMeasure_isProbability hN
  have hp := memLp_posSemidef_projectiveTracePair_re_four_h13 hN A hA
  have hpμ : MemLp (fun v : ComplexUnitSphere N =>
      (complexProjectiveTracePair v A).re) 4 μ := by
    simpa only [μ] using hp
  have hc : MemLp (fun _ : ComplexUnitSphere N => c) 4 μ := memLp_const _
  have ht : 0 ≤ t := (Complex.nonneg_iff.mp hA.trace_nonneg).1
  have hn : 0 < (N : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hc0 : 0 ≤ c := by dsimp only [c]; positivity
  have hconstNorm : lpNorm (fun _ : ComplexUnitSphere N => c) 4 μ = c := by
    rw [lpNorm_const (p := (4 : ENNReal)) (by norm_num)
      (IsProbabilityMeasure.ne_zero μ) c]
    simp [Real.norm_eq_abs, abs_of_nonneg hc0]
  have htri := lpNorm_sub_le hpμ (p := (4 : ENNReal))
    (g := fun _ : ComplexUnitSphere N => c) (by norm_num)
  rw [show (fun v : ComplexUnitSphere N =>
      (complexCenteredProjectiveTracePair v A).re) =
      (fun v => (complexProjectiveTracePair v A).re) -
        (fun _ => c) by
    funext v
    unfold complexCenteredProjectiveTracePair
    dsimp only [c, t]
    norm_num [Complex.mul_re]]
  calc
    lpNorm ((fun v : ComplexUnitSphere N =>
        (complexProjectiveTracePair v A).re) - (fun _ => c)) 4 μ ≤
        lpNorm (fun v : ComplexUnitSphere N =>
          (complexProjectiveTracePair v A).re) 4 μ +
          lpNorm (fun _ : ComplexUnitSphere N => c) 4 μ := htri
    _ ≤ 3 * t / (N : ℝ) + c := by
      rw [hconstNorm]
      gcongr
      simpa only [t, μ] using
        lpNorm_posSemidef_projectiveTracePair_re_four_le_h13 hN A hA
    _ = 4 * t / (N : ℝ) := by
      dsimp only [c]
      field_simp [ne_of_gt hn]
      ring

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
