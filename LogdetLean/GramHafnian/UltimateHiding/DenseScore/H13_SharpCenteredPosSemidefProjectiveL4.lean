import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H13_ProjectiveBilinearHolderConsumption
import Mathlib.Tactic

/-!
# Sharp centered positive-semidefinite projective L4 bound

This module improves the triangle-inequality constant for a centered
positive projective quadratic form.  It uses the exact trace-zero fourth
moment, before taking absolute values, and proves the dimension-sharp clean
bound `2 * Re (Tr A) / N`.
-/

open MeasureTheory
open scoped ComplexOrder MatrixOrder

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open U08

set_option maxHeartbeats 2400000

private theorem trace_im_eq_zero_of_isHermitian_h13_sharp
    {N : ℕ} {A : ConcreteMatrixState N} (hA : A.IsHermitian) :
    (Matrix.trace A).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  have ht := congrArg Matrix.trace hA.eq
  rw [Matrix.trace_conjTranspose] at ht
  exact ht

private theorem traceZeroPart_isHermitian_h13_sharp
    {N : ℕ} (A : ConcreteMatrixState N) (hA : A.IsHermitian) :
    (h14ProjectiveTraceZeroPart A).IsHermitian := by
  have htim : (Matrix.trace A).im = 0 :=
    trace_im_eq_zero_of_isHermitian_h13_sharp hA
  have hc : IsSelfAdjoint
      (((((N : ℝ)⁻¹ : ℝ) : ℂ) * Matrix.trace A)) := by
    rw [isSelfAdjoint_iff]
    apply Complex.ext
    · simp [htim]
    · simp [htim]
  unfold h14ProjectiveTraceZeroPart
  exact hA.sub (Matrix.isHermitian_one.smul hc)

private theorem traceZeroPart_sq_posSemidef_h13_sharp
    {N : ℕ} (A : ConcreteMatrixState N) (hA : A.IsHermitian) :
    (h14ProjectiveTraceZeroPart A *
      h14ProjectiveTraceZeroPart A).PosSemidef := by
  let A0 := h14ProjectiveTraceZeroPart A
  have hA0 : A0.IsHermitian := by
    simpa only [A0] using traceZeroPart_isHermitian_h13_sharp A hA
  have hpos := Matrix.posSemidef_conjTranspose_mul_self A0
  rw [hA0.eq] at hpos
  simpa only [A0] using hpos

/-- For a Hermitian matrix, the fourth trace of its trace-zero part is at
most the square of the second trace. -/
theorem trace_traceZeroPart_four_re_le_traceZeroPart_two_re_sq_h13
    {N : ℕ} (A : ConcreteMatrixState N) (hA : A.IsHermitian) :
    (Matrix.trace
      (h14ProjectiveTraceZeroPart A * h14ProjectiveTraceZeroPart A *
        h14ProjectiveTraceZeroPart A * h14ProjectiveTraceZeroPart A)).re ≤
      (Matrix.trace
        (h14ProjectiveTraceZeroPart A *
          h14ProjectiveTraceZeroPart A)).re ^ 2 := by
  let H := h14ProjectiveTraceZeroPart A * h14ProjectiveTraceZeroPart A
  have hH : H.PosSemidef := by
    simpa only [H] using traceZeroPart_sq_posSemidef_h13_sharp A hA
  have h := posSemidef_trace_square_re_le_trace_re_sq H hH
  simpa only [H, pow_two, Matrix.mul_assoc] using h

/-- Removing the scalar trace part can only decrease the squared
Hilbert--Schmidt trace of a positive-semidefinite matrix. -/
theorem trace_traceZeroPart_two_re_le_trace_square_re_h13
    {N : ℕ} (hN : 1 ≤ N) (A : ConcreteMatrixState N)
    (hA : A.PosSemidef) :
    (Matrix.trace
      (h14ProjectiveTraceZeroPart A *
        h14ProjectiveTraceZeroPart A)).re ≤
      (Matrix.trace (A * A)).re := by
  let a : ℂ := (((N : ℝ)⁻¹ : ℝ) : ℂ)
  have hn : (N : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hN)
  have htim : (Matrix.trace A).im = 0 :=
    trace_im_eq_zero_of_isHermitian_h13_sharp hA.isHermitian
  have haN : a * (N : ℂ) = 1 := by
    dsimp only [a]
    exact_mod_cast inv_mul_cancel₀ hn
  have htrace :
      (Matrix.trace
        (h14ProjectiveTraceZeroPart A *
          h14ProjectiveTraceZeroPart A)).re =
        (Matrix.trace (A * A)).re -
          (N : ℝ)⁻¹ * (Matrix.trace A).re ^ 2 := by
    unfold h14ProjectiveTraceZeroPart
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, Matrix.trace_sub,
      Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
    change
      (Matrix.trace (A * A) -
        a * Matrix.trace A * Matrix.trace A -
        a * Matrix.trace A *
          (Matrix.trace A - a * Matrix.trace A * (N : ℂ))).re = _
    have htrace0 :
        Matrix.trace A - a * Matrix.trace A * (N : ℂ) = 0 := by
      calc
        Matrix.trace A - a * Matrix.trace A * (N : ℂ) =
            Matrix.trace A - Matrix.trace A * (a * (N : ℂ)) := by ring
        _ = 0 := by rw [haN]; ring
    rw [htrace0, mul_zero, sub_zero]
    dsimp only [a]
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, htim, zero_mul, mul_zero, sub_zero, add_zero]
    ring
  rw [htrace]
  have hinv : 0 ≤ (N : ℝ)⁻¹ := by positivity
  have hsq : 0 ≤ (Matrix.trace A).re ^ 2 := sq_nonneg _
  nlinarith

/-- The second trace of the trace-zero part is controlled just by the square
of the positive trace. -/
theorem trace_traceZeroPart_two_re_le_trace_re_sq_h13
    {N : ℕ} (hN : 1 ≤ N) (A : ConcreteMatrixState N)
    (hA : A.PosSemidef) :
    (Matrix.trace
      (h14ProjectiveTraceZeroPart A *
        h14ProjectiveTraceZeroPart A)).re ≤
      (Matrix.trace A).re ^ 2 := by
  calc
    _ ≤ (Matrix.trace (A * A)).re :=
      trace_traceZeroPart_two_re_le_trace_square_re_h13 hN A hA
    _ ≤ (Matrix.trace A).re ^ 2 := by
      simpa only [pow_two] using
        posSemidef_trace_square_re_le_trace_re_sq A hA

private theorem centeredProjectiveTracePair_im_eq_zero_h13_sharp
    {N : ℕ} (v : ComplexUnitSphere N) (A : ConcreteMatrixState N)
    (hA : A.IsHermitian) :
    (complexCenteredProjectiveTracePair v A).im = 0 := by
  unfold complexCenteredProjectiveTracePair
  have hpim :=
    complexProjectiveTracePair_im_eq_zero_of_isHermitian_h12_low v A hA
  have htim := trace_im_eq_zero_of_isHermitian_h13_sharp hA
  simp [Complex.mul_im, hpim, htim]

/-- Exact real fourth moment of the centered pairing, in trace-zero form. -/
theorem integral_centeredProjectiveTracePair_re_fourth_eq_traceZero_h13
    {N : ℕ} (hN : 1 ≤ N) (A : ConcreteMatrixState N)
    (hA : A.IsHermitian) :
    (∫ v : ComplexUnitSphere N,
      (complexCenteredProjectiveTracePair v A).re ^ 4
        ∂(complexUnitSphereProbabilityMeasure N)) =
      ((N : ℝ) * ((N : ℝ) + 1) * ((N : ℝ) + 2) *
        ((N : ℝ) + 3))⁻¹ *
        (3 * (Matrix.trace
            (h14ProjectiveTraceZeroPart A *
              h14ProjectiveTraceZeroPart A)).re ^ 2 +
          6 * (Matrix.trace
            (h14ProjectiveTraceZeroPart A *
              h14ProjectiveTraceZeroPart A *
              h14ProjectiveTraceZeroPart A *
              h14ProjectiveTraceZeroPart A)).re) := by
  let A0 := h14ProjectiveTraceZeroPart A
  have hA0 : A0.IsHermitian := by
    simpa only [A0] using traceZeroPart_isHermitian_h13_sharp A hA
  have hA02 : (A0 * A0).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, hA0.eq]
  have hA04 : (A0 * A0 * A0 * A0).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hA0.eq]
    simp only [Matrix.mul_assoc]
  have htr2im : (Matrix.trace (A0 * A0)).im = 0 :=
    trace_im_eq_zero_of_isHermitian_h13_sharp hA02
  have htr4im : (Matrix.trace (A0 * A0 * A0 * A0)).im = 0 :=
    trace_im_eq_zero_of_isHermitian_h13_sharp hA04
  have hint := integrable_complexCenteredProjectiveTracePair_fourth_h14 hN A
  rw [show (fun v : ComplexUnitSphere N ↦
      (complexCenteredProjectiveTracePair v A).re ^ 4) =
      fun v ↦ (complexCenteredProjectiveTracePair v A ^ 4).re by
    funext v
    have him := centeredProjectiveTracePair_im_eq_zero_h13_sharp v A hA
    simp only [pow_succ, pow_zero, one_mul, Complex.mul_re, him,
      mul_zero, sub_zero]]
  change (∫ v : ComplexUnitSphere N,
      RCLike.re (complexCenteredProjectiveTracePair v A ^ 4)
        ∂(complexUnitSphereProbabilityMeasure N)) = _
  rw [integral_re hint,
    integral_complexCenteredProjectiveTracePair_fourth_eq_traceZero_h14 hN A]
  let d : ℝ := ((N : ℝ) * ((N : ℝ) + 1) * ((N : ℝ) + 2) *
    ((N : ℝ) + 3))⁻¹
  change
    ((((d : ℝ) : ℂ) *
      (3 * Matrix.trace (A0 * A0) ^ 2 +
        6 * Matrix.trace (A0 * A0 * A0 * A0))).re) =
      d * (3 * (Matrix.trace (A0 * A0)).re ^ 2 +
        6 * (Matrix.trace (A0 * A0 * A0 * A0)).re)
  have hEq : (((d : ℝ) : ℂ) *
      (3 * Matrix.trace (A0 * A0) ^ 2 +
        6 * Matrix.trace (A0 * A0 * A0 * A0))) =
      ((d * (3 * (Matrix.trace (A0 * A0)).re ^ 2 +
        6 * (Matrix.trace (A0 * A0 * A0 * A0)).re) : ℝ) : ℂ) := by
    apply Complex.ext
    · norm_num [pow_two, Complex.mul_re, Complex.add_re,
        htr2im, htr4im]
    · norm_num [pow_two, Complex.mul_im, Complex.add_im,
        htr2im, htr4im]
  rw [hEq]
  exact Complex.ofReal_re _

/-- The centered fourth projective moment of a PSD matrix has the clean
dimension-sharp bound needed by H13. -/
theorem integral_posSemidef_centeredProjectiveTracePair_re_fourth_le_sharp_h13
    {N : ℕ} (hN : 1 ≤ N) (A : ConcreteMatrixState N)
    (hA : A.PosSemidef) :
    (∫ v : ComplexUnitSphere N,
      (complexCenteredProjectiveTracePair v A).re ^ 4
        ∂(complexUnitSphereProbabilityMeasure N)) ≤
      (2 * (Matrix.trace A).re / (N : ℝ)) ^ 4 := by
  let n : ℝ := N
  let t : ℝ := (Matrix.trace A).re
  let t2 : ℝ := (Matrix.trace
    (h14ProjectiveTraceZeroPart A * h14ProjectiveTraceZeroPart A)).re
  let t4 : ℝ := (Matrix.trace
    (h14ProjectiveTraceZeroPart A * h14ProjectiveTraceZeroPart A *
      h14ProjectiveTraceZeroPart A * h14ProjectiveTraceZeroPart A)).re
  have hn : 0 < n := by
    dsimp only [n]
    exact_mod_cast (Nat.zero_lt_of_lt hN)
  have ht : 0 ≤ t := by
    exact (Complex.nonneg_iff.mp hA.trace_nonneg).1
  have ht2nonneg : 0 ≤ t2 := by
    have hpos := traceZeroPart_sq_posSemidef_h13_sharp A hA.isHermitian
    exact (Complex.nonneg_iff.mp hpos.trace_nonneg).1
  have ht4le : t4 ≤ t2 ^ 2 := by
    simpa only [t4, t2] using
      trace_traceZeroPart_four_re_le_traceZeroPart_two_re_sq_h13
        A hA.isHermitian
  have ht2le : t2 ≤ t ^ 2 := by
    simpa only [t2, t] using
      trace_traceZeroPart_two_re_le_trace_re_sq_h13 hN A hA
  have ht2sqle : t2 ^ 2 ≤ t ^ 4 := by
    have h := mul_self_le_mul_self ht2nonneg ht2le
    nlinarith
  rw [integral_centeredProjectiveTracePair_re_fourth_eq_traceZero_h13
    hN A hA.isHermitian]
  change
    (n * (n + 1) * (n + 2) * (n + 3))⁻¹ * (3 * t2 ^ 2 + 6 * t4) ≤
      (2 * t / n) ^ 4
  have hnum : 3 * t2 ^ 2 + 6 * t4 ≤ 9 * t ^ 4 := by
    nlinarith
  have hden : n ^ 4 ≤ n * (n + 1) * (n + 2) * (n + 3) := by
    calc
      n ^ 4 = n * n * n * n := by ring
      _ ≤ n * (n + 1) * (n + 2) * (n + 3) := by
        gcongr <;> linarith
  rw [inv_mul_eq_div]
  calc
    (3 * t2 ^ 2 + 6 * t4) /
        (n * (n + 1) * (n + 2) * (n + 3)) ≤
      (9 * t ^ 4) / (n * (n + 1) * (n + 2) * (n + 3)) :=
        div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ (9 * t ^ 4) / n ^ 4 :=
      div_le_div_of_nonneg_left (by positivity) (pow_pos hn 4) hden
    _ ≤ (2 * t / n) ^ 4 := by
      rw [div_pow]
      apply (div_le_div_iff_of_pos_right (pow_pos hn 4)).2
      nlinarith [pow_nonneg ht 4]

/-- Sharp clean `L4` estimate for the centered complex projective pairing of
a positive-semidefinite matrix. -/
theorem lpNorm_posSemidef_centeredProjectiveTracePair_complex_four_le_sharp_h13
    {N : ℕ} (hN : 1 ≤ N) (A : ConcreteMatrixState N)
    (hA : A.PosSemidef) :
    lpNorm (fun v : ComplexUnitSphere N ↦
      complexCenteredProjectiveTracePair v A) 4
        (complexUnitSphereProbabilityMeasure N) ≤
      2 * (Matrix.trace A).re / (N : ℝ) := by
  let μ := complexUnitSphereProbabilityMeasure N
  let f : ComplexUnitSphere N → ℝ := fun v ↦
    (complexCenteredProjectiveTracePair v A).re
  let fc : ComplexUnitSphere N → ℂ := fun v ↦ (f v : ℂ)
  have hf : MemLp f 4 μ := by
    simpa only [f, μ] using
      memLp_posSemidef_centeredProjectiveTracePair_re_four_h13 hN A hA
  have hfc : MemLp fc 4 μ := by
    change MemLp (fun v ↦ (f v : ℂ)) 4 μ
    exact hf.ofReal
  have heq : (fun v : ComplexUnitSphere N ↦
      complexCenteredProjectiveTracePair v A) = fc := by
    funext v
    apply Complex.ext
    · rfl
    · simp only [fc, f, Complex.ofReal_im]
      exact centeredProjectiveTracePair_im_eq_zero_h13_sharp
        v A hA.isHermitian
  have ht : 0 ≤ (Matrix.trace A).re :=
    (Complex.nonneg_iff.mp hA.trace_nonneg).1
  have hn : 0 < (N : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hN)
  rw [heq]
  have hnorm : lpNorm fc 4 μ = lpNorm f 4 μ := by
    calc
      lpNorm fc 4 μ = lpNorm (fun v ↦ ‖fc v‖) 4 μ :=
        (lpNorm_norm hfc.aestronglyMeasurable 4).symm
      _ = lpNorm (fun v ↦ ‖f v‖) 4 μ := by
        congr 1
        funext v
        simp only [fc, Complex.norm_real]
      _ = lpNorm f 4 μ := lpNorm_norm hf.aestronglyMeasurable 4
  rw [hnorm]
  apply le_of_pow_le_pow_left₀ (by norm_num : (4 : ℕ) ≠ 0) (by positivity)
  rw [lpNorm_four_pow_four_eq_integral_pow_four_h9 hf]
  simpa only [f, μ] using
    integral_posSemidef_centeredProjectiveTracePair_re_fourth_le_sharp_h13
      hN A hA

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
