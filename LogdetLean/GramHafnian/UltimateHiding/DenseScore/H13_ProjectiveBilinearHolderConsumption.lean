import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H13_BilinearProjectiveL4
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H13_BilinearSupportGram
import Mathlib.Tactic

/-!
# Four-factor Holder consumption for the H13 bilinear words

This module turns the real positive-projective and complex bilinear `L4`
packages into bounds for the exact scalar factors occurring in the H13
rank-one expansion.  The important dimensional gain is retained before any
matrix-law expectation is taken.
-/

open MeasureTheory
open scoped ComplexOrder MatrixOrder

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open U08

set_option maxHeartbeats 2400000

private theorem trace_im_eq_zero_of_isHermitian_h13_consume
    {N : ℕ} {A : ConcreteMatrixState N} (hA : A.IsHermitian) :
    (Matrix.trace A).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  have ht := congrArg Matrix.trace hA.eq
  rw [Matrix.trace_conjTranspose] at ht
  exact ht

/-- A positive projective trace pairing, regarded as complex-valued, belongs
to `L4`. -/
theorem memLp_posSemidef_projectiveTracePair_complex_four_h13
    {N : ℕ} (hN : 1 ≤ N) (A : ConcreteMatrixState N)
    (hA : A.PosSemidef) :
    MemLp (fun v : ComplexUnitSphere N =>
      complexProjectiveTracePair v A) 4
      (complexUnitSphereProbabilityMeasure N) := by
  let f : ComplexUnitSphere N → ℝ := fun v =>
    (complexProjectiveTracePair v A).re
  have hf : MemLp f 4 (complexUnitSphereProbabilityMeasure N) := by
    simpa only [f] using
      memLp_posSemidef_projectiveTracePair_re_four_h13 hN A hA
  have hfc : MemLp (fun v : ComplexUnitSphere N => (f v : ℂ)) 4
      (complexUnitSphereProbabilityMeasure N) := by
    exact hf.ofReal
  apply hfc.ae_eq
  filter_upwards [] with v
  apply Complex.ext
  · rfl
  · simp only [f, Complex.ofReal_im]
    exact (complexProjectiveTracePair_im_eq_zero_of_isHermitian_h12_low
      v A hA.isHermitian).symm

/-- The complex-valued positive projective pairing has the same sharp `L4`
bound as its real part. -/
theorem lpNorm_posSemidef_projectiveTracePair_complex_four_le_h13
    {N : ℕ} (hN : 1 ≤ N) (A : ConcreteMatrixState N)
    (hA : A.PosSemidef) :
    lpNorm (fun v : ComplexUnitSphere N =>
      complexProjectiveTracePair v A) 4
        (complexUnitSphereProbabilityMeasure N) ≤
      3 * (Matrix.trace A).re / (N : ℝ) := by
  let μ := complexUnitSphereProbabilityMeasure N
  let f : ComplexUnitSphere N → ℝ := fun v =>
    (complexProjectiveTracePair v A).re
  let fc : ComplexUnitSphere N → ℂ := fun v => (f v : ℂ)
  have hf : MemLp f 4 μ := by
    simpa only [f, μ] using
      memLp_posSemidef_projectiveTracePair_re_four_h13 hN A hA
  have hfc : MemLp fc 4 μ := by
    change MemLp (fun x => (f x : ℂ)) 4 μ
    exact hf.ofReal
  have heq : (fun v : ComplexUnitSphere N =>
      complexProjectiveTracePair v A) = fc := by
    funext v
    apply Complex.ext
    · rfl
    · simp only [fc, f, Complex.ofReal_im]
      exact complexProjectiveTracePair_im_eq_zero_of_isHermitian_h12_low
        v A hA.isHermitian
  rw [heq]
  calc
    lpNorm fc 4 μ = lpNorm (fun v => ‖fc v‖) 4 μ :=
      (lpNorm_norm hfc.aestronglyMeasurable 4).symm
    _ = lpNorm (fun v => ‖f v‖) 4 μ := by
      congr 1
      funext v
      simp only [fc, Complex.norm_real]
    _ = lpNorm f 4 μ := lpNorm_norm hf.aestronglyMeasurable 4
    _ ≤ 3 * (Matrix.trace A).re / (N : ℝ) := by
      simpa only [f, μ] using
        lpNorm_posSemidef_projectiveTracePair_re_four_le_h13 hN A hA

/-- A centered positive projective trace pairing, regarded as complex-valued,
belongs to `L4`. -/
theorem memLp_posSemidef_centeredProjectiveTracePair_complex_four_h13
    {N : ℕ} (hN : 1 ≤ N) (A : ConcreteMatrixState N)
    (hA : A.PosSemidef) :
    MemLp (fun v : ComplexUnitSphere N =>
      complexCenteredProjectiveTracePair v A) 4
      (complexUnitSphereProbabilityMeasure N) := by
  let f : ComplexUnitSphere N → ℝ := fun v =>
    (complexCenteredProjectiveTracePair v A).re
  have hf : MemLp f 4 (complexUnitSphereProbabilityMeasure N) := by
    simpa only [f] using
      memLp_posSemidef_centeredProjectiveTracePair_re_four_h13 hN A hA
  have hfc : MemLp (fun v : ComplexUnitSphere N => (f v : ℂ)) 4
      (complexUnitSphereProbabilityMeasure N) := hf.ofReal
  apply hfc.ae_eq
  filter_upwards [] with v
  unfold complexCenteredProjectiveTracePair
  have hpim := complexProjectiveTracePair_im_eq_zero_of_isHermitian_h12_low
    v A hA.isHermitian
  have htim := trace_im_eq_zero_of_isHermitian_h13_consume hA.isHermitian
  apply Complex.ext
  · rfl
  · simp only [f, Complex.ofReal_im]
    simp [Complex.mul_im, hpim, htim]

/-- Centering costs the same single trace-over-dimension term in the complex
form. -/
theorem lpNorm_posSemidef_centeredProjectiveTracePair_complex_four_le_h13
    {N : ℕ} (hN : 1 ≤ N) (A : ConcreteMatrixState N)
    (hA : A.PosSemidef) :
    lpNorm (fun v : ComplexUnitSphere N =>
      complexCenteredProjectiveTracePair v A) 4
        (complexUnitSphereProbabilityMeasure N) ≤
      4 * (Matrix.trace A).re / (N : ℝ) := by
  let μ := complexUnitSphereProbabilityMeasure N
  let f : ComplexUnitSphere N → ℝ := fun v =>
    (complexCenteredProjectiveTracePair v A).re
  let fc : ComplexUnitSphere N → ℂ := fun v => (f v : ℂ)
  have hf : MemLp f 4 μ := by
    simpa only [f, μ] using
      memLp_posSemidef_centeredProjectiveTracePair_re_four_h13 hN A hA
  have hfc : MemLp fc 4 μ := by
    change MemLp (fun x => (f x : ℂ)) 4 μ
    exact hf.ofReal
  have heq : (fun v : ComplexUnitSphere N =>
      complexCenteredProjectiveTracePair v A) = fc := by
    funext v
    unfold complexCenteredProjectiveTracePair
    have hpim := complexProjectiveTracePair_im_eq_zero_of_isHermitian_h12_low
      v A hA.isHermitian
    have htim := trace_im_eq_zero_of_isHermitian_h13_consume hA.isHermitian
    apply Complex.ext
    · rfl
    · simp only [fc, f, Complex.ofReal_im]
      simp [Complex.mul_im, hpim, htim]
  rw [heq]
  calc
    lpNorm fc 4 μ = lpNorm (fun v => ‖fc v‖) 4 μ :=
      (lpNorm_norm hfc.aestronglyMeasurable 4).symm
    _ = lpNorm (fun v => ‖f v‖) 4 μ := by
      congr 1
      funext v
      simp only [fc, Complex.norm_real]
    _ = lpNorm f 4 μ := lpNorm_norm hf.aestronglyMeasurable 4
    _ ≤ 4 * (Matrix.trace A).re / (N : ℝ) := by
      simpa only [f, μ] using
        lpNorm_posSemidef_centeredProjectiveTracePair_re_four_le_h13 hN A hA

/-- Four-factor Holder bound for the characteristic H13 monomial consisting
of one centered positive pairing, one positive pairing, and one factored
mixed-transpose pairing. -/
theorem integral_norm_centeredPair_mul_pair_mul_mixedPair_le_h13
    {N : ℕ} (hN : 1 ≤ N)
    (A B R S : ConcreteMatrixState N)
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hR : R.IsSymm) (hS : S.IsSymm) :
    (∫ v : ComplexUnitSphere N,
      ‖complexCenteredProjectiveTracePair v A *
        complexProjectiveTracePair v B *
        complexProjectiveMixedTransposePair v R S.conjTranspose‖
        ∂(complexUnitSphereProbabilityMeasure N)) ≤
      12 * (Matrix.trace A).re * (Matrix.trace B).re *
        ((Matrix.trace (R * R.conjTranspose)).re +
          (Matrix.trace (S * S.conjTranspose)).re) / (N : ℝ) ^ 3 := by
  let μ := complexUnitSphereProbabilityMeasure N
  let f1 : ComplexUnitSphere N → ℂ := fun v =>
    complexCenteredProjectiveTracePair v A
  let f2 : ComplexUnitSphere N → ℂ := fun v =>
    complexProjectiveTracePair v B
  let f3 : ComplexUnitSphere N → ℂ := fun v =>
    complexProjectiveConjugateBilinearPair v R
  let f4 : ComplexUnitSphere N → ℂ := fun v =>
    complexProjectiveTransposeBilinearPair v S.conjTranspose
  have h1 : MemLp f1 4 μ := by
    simpa only [f1, μ] using
      memLp_posSemidef_centeredProjectiveTracePair_complex_four_h13 hN A hA
  have h2 : MemLp f2 4 μ := by
    simpa only [f2, μ] using
      memLp_posSemidef_projectiveTracePair_complex_four_h13 hN B hB
  have h3 : MemLp f3 4 μ := by
    simpa only [f3, μ] using
      memLp_complexProjectiveConjugateBilinearPair_four_h13 hN R
  have h4 : MemLp f4 4 μ := by
    simpa only [f4, μ] using
      memLp_complexProjectiveTransposeBilinearPair_conjTranspose_four_h13 hN S
  have hholder := integral_norm_mul_four_complex_le_h13 h1 h2 h3 h4
  have hholder' :
      (∫ v : ComplexUnitSphere N,
        ‖complexCenteredProjectiveTracePair v A *
          complexProjectiveTracePair v B *
          complexProjectiveMixedTransposePair v R S.conjTranspose‖ ∂μ) ≤
        lpNorm f1 4 μ * lpNorm f2 4 μ *
          lpNorm f3 4 μ * lpNorm f4 4 μ := by
    convert hholder using 1
    congr 1
    funext v
    rw [complexProjectiveMixedTransposePair_eq_bilinearFactors_h13]
    dsimp only [f1, f2, f3, f4]
    congr 1
    ring
  have h1norm :=
    lpNorm_posSemidef_centeredProjectiveTracePair_complex_four_le_h13 hN A hA
  have h2norm :=
    lpNorm_posSemidef_projectiveTracePair_complex_four_le_h13 hN B hB
  have h3sq := lpNorm_conjugateBilinearPair_four_sq_le_h13 hN R hR
  have h4sq := lpNorm_transposeBilinearPair_conjTranspose_four_sq_le_h13
    hN S hS
  let x := lpNorm f3 4 μ
  let y := lpNorm f4 4 μ
  let r := (Matrix.trace (R * R.conjTranspose)).re
  let s := (Matrix.trace (S * S.conjTranspose)).re
  let n : ℝ := N
  have hn : 0 < n := by
    dsimp only [n]
    exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hxy : x * y ≤ (r + s) / n := by
    have hsq : 2 * x * y ≤ x ^ 2 + y ^ 2 := by
      nlinarith [sq_nonneg (x - y)]
    have hxsq : x ^ 2 ≤ 2 * r / n := by
      simpa only [x, r, n, f3, μ] using h3sq
    have hysq : y ^ 2 ≤ 2 * s / n := by
      simpa only [y, s, n, f4, μ] using h4sq
    have hn0 : 0 ≤ n := hn.le
    calc
      x * y ≤ (x ^ 2 + y ^ 2) / 2 := by linarith
      _ ≤ ((2 * r / n) + (2 * s / n)) / 2 := by gcongr
      _ = (r + s) / n := by field_simp [ne_of_gt hn]
  have hnonneg :
      0 ≤ lpNorm f1 4 μ ∧ 0 ≤ lpNorm f2 4 μ ∧
        0 ≤ x ∧ 0 ≤ y := by
    exact ⟨lpNorm_nonneg, lpNorm_nonneg, lpNorm_nonneg, lpNorm_nonneg⟩
  calc
    (∫ v : ComplexUnitSphere N,
      ‖complexCenteredProjectiveTracePair v A *
        complexProjectiveTracePair v B *
        complexProjectiveMixedTransposePair v R S.conjTranspose‖ ∂μ) ≤
        lpNorm f1 4 μ * lpNorm f2 4 μ * x * y := by
      simpa only [x, y] using hholder'
    _ ≤ (4 * (Matrix.trace A).re / n) *
        (3 * (Matrix.trace B).re / n) * ((r + s) / n) := by
      have htA : 0 ≤ (Matrix.trace A).re :=
        (Complex.nonneg_iff.mp hA.trace_nonneg).1
      have htB : 0 ≤ (Matrix.trace B).re :=
        (Complex.nonneg_iff.mp hB.trace_nonneg).1
      have h1norm' : lpNorm f1 4 μ ≤
          4 * (Matrix.trace A).re / n := by
        simpa only [f1, μ, n] using h1norm
      have h2norm' : lpNorm f2 4 μ ≤
          3 * (Matrix.trace B).re / n := by
        simpa only [f2, μ, n] using h2norm
      have hrs0 : 0 ≤ (r + s) / n := by
        have hr0 : 0 ≤ r := by
          exact (Complex.nonneg_iff.mp
            (Matrix.posSemidef_self_mul_conjTranspose R).trace_nonneg).1
        have hs0 : 0 ≤ s := by
          exact (Complex.nonneg_iff.mp
            (Matrix.posSemidef_self_mul_conjTranspose S).trace_nonneg).1
        positivity
      have hAcoef0 : 0 ≤ 4 * (Matrix.trace A).re / n := by positivity
      have hBcoef0 : 0 ≤ 3 * (Matrix.trace B).re / n := by positivity
      have hab : lpNorm f1 4 μ * lpNorm f2 4 μ ≤
          (4 * (Matrix.trace A).re / n) *
            (3 * (Matrix.trace B).re / n) :=
        mul_le_mul h1norm' h2norm' lpNorm_nonneg hAcoef0
      calc
        lpNorm f1 4 μ * lpNorm f2 4 μ * x * y =
            (lpNorm f1 4 μ * lpNorm f2 4 μ) * (x * y) := by ring
        _ ≤ (lpNorm f1 4 μ * lpNorm f2 4 μ) *
            ((r + s) / n) :=
          mul_le_mul_of_nonneg_left hxy
            (mul_nonneg lpNorm_nonneg lpNorm_nonneg)
        _ ≤ ((4 * (Matrix.trace A).re / n) *
            (3 * (Matrix.trace B).re / n)) * ((r + s) / n) :=
          mul_le_mul_of_nonneg_right hab hrs0
    _ = 12 * (Matrix.trace A).re * (Matrix.trace B).re * (r + s) /
        n ^ 3 := by field_simp [ne_of_gt hn]; ring
    _ = 12 * (Matrix.trace A).re * (Matrix.trace B).re *
        ((Matrix.trace (R * R.conjTranspose)).re +
          (Matrix.trace (S * S.conjTranspose)).re) / (N : ℝ) ^ 3 := rfl

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
