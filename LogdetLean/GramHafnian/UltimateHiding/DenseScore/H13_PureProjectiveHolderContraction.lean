import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H13_SixWordSupportSimplification
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H13_ProjectiveBilinearHolderConsumption
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H13_BilinearSupportGramComparison
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H13_SharpCenteredPosSemidefProjectiveL4
import Mathlib.Tactic

/-!
# Pure-word projective Holder contraction for H13

This module contracts the two pure six-word terms after their exact support
simplification to one centered triple trace.  The only analytic ingredients
are finite-dimensional complex-projective moments and Holder's inequality.
-/

open MeasureTheory
open scoped ComplexOrder MatrixOrder

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open Matrix Unitary
open LogdetLean.GramHafnian.UltimateHiding.Dense
open U08

set_option maxHeartbeats 2400000

/-! ## Sharper uncentered positive-projective L4 constant -/

/-- The exact fourth projective moment gives the convenient rational bound
`24^(1/4) < 9/4`. -/
theorem lpNorm_posSemidef_projectiveTracePair_re_four_le_nine_fourths_h13
    {N : ℕ} (hN : 1 ≤ N) (A : ConcreteMatrixState N)
    (hA : A.PosSemidef) :
    lpNorm (fun v : ComplexUnitSphere N ↦
      (complexProjectiveTracePair v A).re) 4
        (complexUnitSphereProbabilityMeasure N) ≤
      (9 / 4 : ℝ) * (Matrix.trace A).re / (N : ℝ) := by
  let f : ComplexUnitSphere N → ℝ := fun v ↦
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
    _ ≤ ((9 / 4 : ℝ) * t / n) ^ 4 := by
      have hn4 : 0 < n ^ 4 := pow_pos hn 4
      rw [div_pow]
      apply (div_le_div_iff_of_pos_right hn4).2
      norm_num
      nlinarith [pow_nonneg ht 4]

/-- Complex-valued version of the `9/4` positive-projective L4 bound. -/
theorem lpNorm_posSemidef_projectiveTracePair_complex_four_le_nine_fourths_h13
    {N : ℕ} (hN : 1 ≤ N) (A : ConcreteMatrixState N)
    (hA : A.PosSemidef) :
    lpNorm (fun v : ComplexUnitSphere N ↦
      complexProjectiveTracePair v A) 4
        (complexUnitSphereProbabilityMeasure N) ≤
      (9 / 4 : ℝ) * (Matrix.trace A).re / (N : ℝ) := by
  let μ := complexUnitSphereProbabilityMeasure N
  let f : ComplexUnitSphere N → ℝ := fun v ↦
    (complexProjectiveTracePair v A).re
  let fc : ComplexUnitSphere N → ℂ := fun v ↦ (f v : ℂ)
  have hf : MemLp f 4 μ := by
    simpa only [f, μ] using
      memLp_posSemidef_projectiveTracePair_re_four_h13 hN A hA
  have hfc : MemLp fc 4 μ := by
    change MemLp (fun x ↦ (f x : ℂ)) 4 μ
    exact hf.ofReal
  have heq : (fun v : ComplexUnitSphere N ↦
      complexProjectiveTracePair v A) = fc := by
    funext v
    apply Complex.ext
    · rfl
    · simp only [fc, f, Complex.ofReal_im]
      exact complexProjectiveTracePair_im_eq_zero_of_isHermitian_h12_low
        v A hA.isHermitian
  rw [heq]
  calc
    lpNorm fc 4 μ = lpNorm (fun v ↦ ‖fc v‖) 4 μ :=
      (lpNorm_norm hfc.aestronglyMeasurable 4).symm
    _ = lpNorm (fun v ↦ ‖f v‖) 4 μ := by
      congr 1
      funext v
      simp only [fc, Complex.norm_real]
    _ = lpNorm f 4 μ := lpNorm_norm hf.aestronglyMeasurable 4
    _ ≤ (9 / 4 : ℝ) * (Matrix.trace A).re / (N : ℝ) := by
      simpa only [f, μ] using
        lpNorm_posSemidef_projectiveTracePair_re_four_le_nine_fourths_h13
          hN A hA

/-- Dimension Cauchy--Schwarz for the first two trace powers of a complex
positive-semidefinite matrix. -/
theorem posSemidef_trace_re_sq_le_card_mul_trace_square_re_h13_pure
    {N : ℕ} (A : ConcreteMatrixState N) (hA : A.PosSemidef) :
    (Matrix.trace A).re ^ 2 ≤
      (N : ℝ) * (Matrix.trace (A * A)).re := by
  let hH : A.IsHermitian := hA.isHermitian
  have hspectral := hH.spectral_theorem
  have htrace : Matrix.trace A = ∑ i, (hH.eigenvalues i : ℂ) :=
    hH.trace_eq_sum_eigenvalues
  have htrace2 : Matrix.trace (A * A) =
      ∑ i, ((hH.eigenvalues i : ℂ) ^ 2) := by
    rw [show A * A = A ^ 2 by noncomm_ring]
    conv_lhs => rw [hspectral]
    rw [← map_pow, conjStarAlgAut_apply, Matrix.trace_mul_cycle,
      Unitary.coe_star_mul_self, one_mul]
    rw [Matrix.diagonal_pow, Matrix.trace_diagonal]
    rfl
  rw [htrace, htrace2]
  simp only [Complex.re_sum]
  norm_cast
  simpa only [Finset.card_univ, Fintype.card_fin] using
    (sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset (Fin N)))
      (f := fun i ↦ hH.eigenvalues i))

/-! ## Holder packages with probability-space padding -/

private theorem memLp_mul_three_complex_h13_pure
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ]
    {f₁ f₂ f₃ : Ω → ℂ}
    (h₁ : MemLp f₁ 4 μ) (h₂ : MemLp f₂ 4 μ) (h₃ : MemLp f₃ 4 μ) :
    MemLp (fun x ↦ f₁ x * f₂ x * f₃ x) 1 μ := by
  have h₄ : MemLp (fun _ : Ω ↦ (1 : ℂ)) 4 μ := memLp_const _
  simpa only [mul_one] using memLp_mul_four_complex_h13 h₁ h₂ h₃ h₄

private theorem memLp_mul_two_complex_h13_pure
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ]
    {f₁ f₂ : Ω → ℂ} (h₁ : MemLp f₁ 4 μ) (h₂ : MemLp f₂ 4 μ) :
    MemLp (fun x ↦ f₁ x * f₂ x) 1 μ := by
  have h₃ : MemLp (fun _ : Ω ↦ (1 : ℂ)) 4 μ := memLp_const _
  have h₄ : MemLp (fun _ : Ω ↦ (1 : ℂ)) 4 μ := memLp_const _
  simpa only [mul_one] using memLp_mul_four_complex_h13 h₁ h₂ h₃ h₄

private theorem memLp_one_factor_complex_h13_pure
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ]
    {f : Ω → ℂ} (hf : MemLp f 4 μ) : MemLp f 1 μ := by
  have h₂ : MemLp (fun _ : Ω ↦ (1 : ℂ)) 4 μ := memLp_const _
  have h₃ : MemLp (fun _ : Ω ↦ (1 : ℂ)) 4 μ := memLp_const _
  have h₄ : MemLp (fun _ : Ω ↦ (1 : ℂ)) 4 μ := memLp_const _
  simpa only [mul_one] using memLp_mul_four_complex_h13 hf h₂ h₃ h₄

private theorem integral_norm_mul_three_complex_le_h13_pure
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f₁ f₂ f₃ : Ω → ℂ}
    (h₁ : MemLp f₁ 4 μ) (h₂ : MemLp f₂ 4 μ) (h₃ : MemLp f₃ 4 μ) :
    (∫ x, ‖f₁ x * f₂ x * f₃ x‖ ∂μ) ≤
      lpNorm f₁ 4 μ * lpNorm f₂ 4 μ * lpNorm f₃ 4 μ := by
  let one : Ω → ℂ := fun _ ↦ 1
  have h₄ : MemLp one 4 μ := memLp_const _
  have H := integral_norm_mul_four_complex_le_h13 h₁ h₂ h₃ h₄
  have hone : lpNorm one 4 μ = 1 := by
    rw [lpNorm_const (p := (4 : ENNReal)) (by norm_num)
      (IsProbabilityMeasure.ne_zero μ) (1 : ℂ)]
    norm_num
  simpa only [one, mul_one, hone] using H

private theorem integral_norm_mul_two_complex_le_h13_pure
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f₁ f₂ : Ω → ℂ}
    (h₁ : MemLp f₁ 4 μ) (h₂ : MemLp f₂ 4 μ) :
    (∫ x, ‖f₁ x * f₂ x‖ ∂μ) ≤ lpNorm f₁ 4 μ * lpNorm f₂ 4 μ := by
  let one : Ω → ℂ := fun _ ↦ 1
  have h₃ : MemLp one 4 μ := memLp_const _
  have h₄ : MemLp one 4 μ := memLp_const _
  have H := integral_norm_mul_four_complex_le_h13 h₁ h₂ h₃ h₄
  have hone : lpNorm one 4 μ = 1 := by
    rw [lpNorm_const (p := (4 : ENNReal)) (by norm_num)
      (IsProbabilityMeasure.ne_zero μ) (1 : ℂ)]
    norm_num
  simpa only [one, mul_one, hone] using H

private theorem integral_norm_one_complex_le_h13_pure
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Ω → ℂ} (hf : MemLp f 4 μ) :
    (∫ x, ‖f x‖ ∂μ) ≤ lpNorm f 4 μ := by
  let one : Ω → ℂ := fun _ ↦ 1
  have h₂ : MemLp one 4 μ := memLp_const _
  have h₃ : MemLp one 4 μ := memLp_const _
  have h₄ : MemLp one 4 μ := memLp_const _
  have H := integral_norm_mul_four_complex_le_h13 hf h₂ h₃ h₄
  have hone : lpNorm one 4 μ = 1 := by
    rw [lpNorm_const (p := (4 : ENNReal)) (by norm_num)
      (IsProbabilityMeasure.ne_zero μ) (1 : ℂ)]
    norm_num
  simpa only [one, mul_one, hone] using H

/-! ## Positive-matrix specializations -/

/-- One centered and three positive projective pairings. -/
theorem integral_norm_centeredPair_mul_three_posPairs_le_h13_pure
    {N : ℕ} (hN : 1 ≤ N)
    (A B C D : ConcreteMatrixState N)
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hC : C.PosSemidef) (hD : D.PosSemidef) :
    (∫ v : ComplexUnitSphere N,
      ‖complexCenteredProjectiveTracePair v A *
        complexProjectiveTracePair v B *
        complexProjectiveTracePair v C *
        complexProjectiveTracePair v D‖
        ∂(complexUnitSphereProbabilityMeasure N)) ≤
      23 * (Matrix.trace A).re * (Matrix.trace B).re *
        (Matrix.trace C).re * (Matrix.trace D).re / (N : ℝ) ^ 4 := by
  let μ := complexUnitSphereProbabilityMeasure N
  let f₁ : ComplexUnitSphere N → ℂ := fun v ↦
    complexCenteredProjectiveTracePair v A
  let f₂ : ComplexUnitSphere N → ℂ := fun v ↦
    complexProjectiveTracePair v B
  let f₃ : ComplexUnitSphere N → ℂ := fun v ↦
    complexProjectiveTracePair v C
  let f₄ : ComplexUnitSphere N → ℂ := fun v ↦
    complexProjectiveTracePair v D
  letI : IsProbabilityMeasure μ :=
    complexUnitSphereProbabilityMeasure_isProbability hN
  have h₁ :=
    memLp_posSemidef_centeredProjectiveTracePair_complex_four_h13 hN A hA
  have h₂ := memLp_posSemidef_projectiveTracePair_complex_four_h13 hN B hB
  have h₃ := memLp_posSemidef_projectiveTracePair_complex_four_h13 hN C hC
  have h₄ := memLp_posSemidef_projectiveTracePair_complex_four_h13 hN D hD
  have H := integral_norm_mul_four_complex_le_h13 h₁ h₂ h₃ h₄
  have h₁n :=
    lpNorm_posSemidef_centeredProjectiveTracePair_complex_four_le_sharp_h13
      hN A hA
  have h₂n :=
    lpNorm_posSemidef_projectiveTracePair_complex_four_le_nine_fourths_h13
      hN B hB
  have h₃n :=
    lpNorm_posSemidef_projectiveTracePair_complex_four_le_nine_fourths_h13
      hN C hC
  have h₄n :=
    lpNorm_posSemidef_projectiveTracePair_complex_four_le_nine_fourths_h13
      hN D hD
  have hn : 0 < (N : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have htA : 0 ≤ (Matrix.trace A).re :=
    (Complex.nonneg_iff.mp hA.trace_nonneg).1
  have htB : 0 ≤ (Matrix.trace B).re :=
    (Complex.nonneg_iff.mp hB.trace_nonneg).1
  have htC : 0 ≤ (Matrix.trace C).re :=
    (Complex.nonneg_iff.mp hC.trace_nonneg).1
  have htD : 0 ≤ (Matrix.trace D).re :=
    (Complex.nonneg_iff.mp hD.trace_nonneg).1
  have hprod :
      lpNorm f₁ 4 μ * lpNorm f₂ 4 μ * lpNorm f₃ 4 μ * lpNorm f₄ 4 μ ≤
        (2 * (Matrix.trace A).re / (N : ℝ)) *
          ((9 / 4 : ℝ) * (Matrix.trace B).re / (N : ℝ)) *
          ((9 / 4 : ℝ) * (Matrix.trace C).re / (N : ℝ)) *
          ((9 / 4 : ℝ) * (Matrix.trace D).re / (N : ℝ)) := by
    dsimp only [f₁, f₂, f₃, f₄, μ]
    gcongr <;> exact lpNorm_nonneg
  calc
    _ ≤ lpNorm f₁ 4 μ * lpNorm f₂ 4 μ * lpNorm f₃ 4 μ *
        lpNorm f₄ 4 μ := by simpa only [f₁, f₂, f₃, f₄, μ] using H
    _ ≤ _ := hprod
    _ = (729 / 32 : ℝ) * (Matrix.trace A).re * (Matrix.trace B).re *
        (Matrix.trace C).re * (Matrix.trace D).re / (N : ℝ) ^ 4 := by ring
    _ ≤ 23 * (Matrix.trace A).re * (Matrix.trace B).re *
        (Matrix.trace C).re * (Matrix.trace D).re / (N : ℝ) ^ 4 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith [mul_nonneg (mul_nonneg (mul_nonneg htA htB) htC) htD]

/-- One centered and two positive projective pairings. -/
theorem integral_norm_centeredPair_mul_two_posPairs_le_h13_pure
    {N : ℕ} (hN : 1 ≤ N)
    (A B C : ConcreteMatrixState N)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hC : C.PosSemidef) :
    (∫ v : ComplexUnitSphere N,
      ‖complexCenteredProjectiveTracePair v A *
        complexProjectiveTracePair v B * complexProjectiveTracePair v C‖
        ∂(complexUnitSphereProbabilityMeasure N)) ≤
      11 * (Matrix.trace A).re * (Matrix.trace B).re *
        (Matrix.trace C).re / (N : ℝ) ^ 3 := by
  let μ := complexUnitSphereProbabilityMeasure N
  let f₁ : ComplexUnitSphere N → ℂ := fun v ↦
    complexCenteredProjectiveTracePair v A
  let f₂ : ComplexUnitSphere N → ℂ := fun v ↦ complexProjectiveTracePair v B
  let f₃ : ComplexUnitSphere N → ℂ := fun v ↦ complexProjectiveTracePair v C
  letI : IsProbabilityMeasure μ :=
    complexUnitSphereProbabilityMeasure_isProbability hN
  have h₁ :=
    memLp_posSemidef_centeredProjectiveTracePair_complex_four_h13 hN A hA
  have h₂ := memLp_posSemidef_projectiveTracePair_complex_four_h13 hN B hB
  have h₃ := memLp_posSemidef_projectiveTracePair_complex_four_h13 hN C hC
  have H := integral_norm_mul_three_complex_le_h13_pure h₁ h₂ h₃
  have h₁n :=
    lpNorm_posSemidef_centeredProjectiveTracePair_complex_four_le_sharp_h13
      hN A hA
  have h₂n :=
    lpNorm_posSemidef_projectiveTracePair_complex_four_le_nine_fourths_h13
      hN B hB
  have h₃n :=
    lpNorm_posSemidef_projectiveTracePair_complex_four_le_nine_fourths_h13
      hN C hC
  have htA : 0 ≤ (Matrix.trace A).re :=
    (Complex.nonneg_iff.mp hA.trace_nonneg).1
  have htB : 0 ≤ (Matrix.trace B).re :=
    (Complex.nonneg_iff.mp hB.trace_nonneg).1
  have htC : 0 ≤ (Matrix.trace C).re :=
    (Complex.nonneg_iff.mp hC.trace_nonneg).1
  have hprod : lpNorm f₁ 4 μ * lpNorm f₂ 4 μ * lpNorm f₃ 4 μ ≤
      (2 * (Matrix.trace A).re / (N : ℝ)) *
        ((9 / 4 : ℝ) * (Matrix.trace B).re / (N : ℝ)) *
        ((9 / 4 : ℝ) * (Matrix.trace C).re / (N : ℝ)) := by
    dsimp only [f₁, f₂, f₃, μ]
    gcongr <;> exact lpNorm_nonneg
  calc
    _ ≤ lpNorm f₁ 4 μ * lpNorm f₂ 4 μ * lpNorm f₃ 4 μ := by
      simpa only [f₁, f₂, f₃, μ] using H
    _ ≤ _ := hprod
    _ = (81 / 8 : ℝ) * (Matrix.trace A).re * (Matrix.trace B).re *
        (Matrix.trace C).re / (N : ℝ) ^ 3 := by ring
    _ ≤ 11 * (Matrix.trace A).re * (Matrix.trace B).re *
        (Matrix.trace C).re / (N : ℝ) ^ 3 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith [mul_nonneg (mul_nonneg htA htB) htC]

/-- One centered and one positive projective pairing, retaining the exact
constant supplied by the two sharp `L⁴` bounds. -/
theorem integral_norm_centeredPair_mul_posPair_le_nine_halves_h13_pure
    {N : ℕ} (hN : 1 ≤ N) (A B : ConcreteMatrixState N)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (∫ v : ComplexUnitSphere N,
      ‖complexCenteredProjectiveTracePair v A *
        complexProjectiveTracePair v B‖
        ∂(complexUnitSphereProbabilityMeasure N)) ≤
      (9 / 2 : ℝ) * (Matrix.trace A).re * (Matrix.trace B).re /
        (N : ℝ) ^ 2 := by
  let μ := complexUnitSphereProbabilityMeasure N
  let f₁ : ComplexUnitSphere N → ℂ := fun v ↦
    complexCenteredProjectiveTracePair v A
  let f₂ : ComplexUnitSphere N → ℂ := fun v ↦ complexProjectiveTracePair v B
  letI : IsProbabilityMeasure μ :=
    complexUnitSphereProbabilityMeasure_isProbability hN
  have h₁ :=
    memLp_posSemidef_centeredProjectiveTracePair_complex_four_h13 hN A hA
  have h₂ := memLp_posSemidef_projectiveTracePair_complex_four_h13 hN B hB
  have H := integral_norm_mul_two_complex_le_h13_pure h₁ h₂
  have h₁n :=
    lpNorm_posSemidef_centeredProjectiveTracePair_complex_four_le_sharp_h13
      hN A hA
  have h₂n :=
    lpNorm_posSemidef_projectiveTracePair_complex_four_le_nine_fourths_h13
      hN B hB
  have htA : 0 ≤ (Matrix.trace A).re :=
    (Complex.nonneg_iff.mp hA.trace_nonneg).1
  have htB : 0 ≤ (Matrix.trace B).re :=
    (Complex.nonneg_iff.mp hB.trace_nonneg).1
  have hprod : lpNorm f₁ 4 μ * lpNorm f₂ 4 μ ≤
      (2 * (Matrix.trace A).re / (N : ℝ)) *
        ((9 / 4 : ℝ) * (Matrix.trace B).re / (N : ℝ)) := by
    dsimp only [f₁, f₂, μ]
    gcongr <;> exact lpNorm_nonneg
  calc
    _ ≤ lpNorm f₁ 4 μ * lpNorm f₂ 4 μ := by
      simpa only [f₁, f₂, μ] using H
    _ ≤ _ := hprod
    _ = (9 / 2 : ℝ) * (Matrix.trace A).re * (Matrix.trace B).re /
        (N : ℝ) ^ 2 := by ring

/-- Rounded compatibility form of the one-centered/one-positive bound. -/
theorem integral_norm_centeredPair_mul_posPair_le_h13_pure
    {N : ℕ} (hN : 1 ≤ N) (A B : ConcreteMatrixState N)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (∫ v : ComplexUnitSphere N,
      ‖complexCenteredProjectiveTracePair v A *
        complexProjectiveTracePair v B‖
        ∂(complexUnitSphereProbabilityMeasure N)) ≤
      5 * (Matrix.trace A).re * (Matrix.trace B).re / (N : ℝ) ^ 2 := by
  have H := integral_norm_centeredPair_mul_posPair_le_nine_halves_h13_pure
    hN A B hA hB
  have htA : 0 ≤ (Matrix.trace A).re :=
    (Complex.nonneg_iff.mp hA.trace_nonneg).1
  have htB : 0 ≤ (Matrix.trace B).re :=
    (Complex.nonneg_iff.mp hB.trace_nonneg).1
  calc
    _ ≤ (9 / 2 : ℝ) * (Matrix.trace A).re * (Matrix.trace B).re /
        (N : ℝ) ^ 2 := H
    _ ≤ 5 * (Matrix.trace A).re * (Matrix.trace B).re / (N : ℝ) ^ 2 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith [mul_nonneg htA htB]

/-- L1 bound for one centered positive projective pairing. -/
theorem integral_norm_centeredPair_le_h13_pure
    {N : ℕ} (hN : 1 ≤ N) (A : ConcreteMatrixState N)
    (hA : A.PosSemidef) :
    (∫ v : ComplexUnitSphere N,
      ‖complexCenteredProjectiveTracePair v A‖
        ∂(complexUnitSphereProbabilityMeasure N)) ≤
      2 * (Matrix.trace A).re / (N : ℝ) := by
  let μ := complexUnitSphereProbabilityMeasure N
  let f : ComplexUnitSphere N → ℂ := fun v ↦
    complexCenteredProjectiveTracePair v A
  letI : IsProbabilityMeasure μ :=
    complexUnitSphereProbabilityMeasure_isProbability hN
  have hf :=
    memLp_posSemidef_centeredProjectiveTracePair_complex_four_h13 hN A hA
  have H := integral_norm_one_complex_le_h13_pure hf
  have hn :=
    lpNorm_posSemidef_centeredProjectiveTracePair_complex_four_le_sharp_h13
      hN A hA
  calc
    _ ≤ lpNorm f 4 μ := by simpa only [f, μ] using H
    _ ≤ 2 * (Matrix.trace A).re / (N : ℝ) := by
      simpa only [f, μ] using hn

/-! ## Exact pure-word scalar normal form -/

/-- For the support polynomials `W=I+Z`, `A=I+2Z`, all three cyclic cubic
products coincide. -/
theorem h13CenteredTripleTraceProjectiveExpansion_support_eq_h13_pure
    {N : ℕ} (v : ComplexUnitSphere N) (Z : ConcreteMatrixState N) :
    h13CenteredTripleTraceProjectiveExpansion v
        (1 + Z) (1 + 2 • Z) Z =
      let a : ℂ := (((N : ℝ)⁻¹ : ℝ) : ℂ)
      let p : ConcreteMatrixState N → ℂ := fun X ↦
        complexProjectiveTracePair v X
      let ZW : ConcreteMatrixState N := Z + Z ^ 2
      let WA : ConcreteMatrixState N := 1 + 3 • Z + 2 • Z ^ 2
      let AZ : ConcreteMatrixState N := Z + 2 • Z ^ 2
      let B : ConcreteMatrixState N := Z + 3 • Z ^ 2 + 2 • Z ^ 3
      p (1 + Z) * p (1 + 2 • Z) * p Z -
        a * (p (1 + 2 • Z) * p ZW + p WA * p Z +
          p (1 + Z) * p AZ) +
        3 * a ^ 2 * p B - a ^ 3 * Matrix.trace B := by
  let W : ConcreteMatrixState N := 1 + Z
  let A : ConcreteMatrixState N := 1 + 2 • Z
  let ZW : ConcreteMatrixState N := Z + Z ^ 2
  let WA : ConcreteMatrixState N := 1 + 3 • Z + 2 • Z ^ 2
  let AZ : ConcreteMatrixState N := Z + 2 • Z ^ 2
  let B : ConcreteMatrixState N := Z + 3 • Z ^ 2 + 2 • Z ^ 3
  have hZW : Z * W = ZW := by
    dsimp only [W, ZW]
    noncomm_ring
  have hWA : W * A = WA := by
    dsimp only [W, A, WA]
    simp only [two_nsmul, three_nsmul]
    noncomm_ring
  have hAZ : A * Z = AZ := by
    dsimp only [A, AZ]
    simp only [two_nsmul]
    noncomm_ring
  have hWAZ : W * A * Z = B := by
    dsimp only [W, A, B]
    simp only [two_nsmul, three_nsmul]
    noncomm_ring
  have hAZW : A * Z * W = B := by
    dsimp only [W, A, B]
    simp only [two_nsmul, three_nsmul]
    noncomm_ring
  have hZWA : Z * W * A = B := by
    dsimp only [W, A, B]
    simp only [two_nsmul, three_nsmul]
    noncomm_ring
  unfold h13CenteredTripleTraceProjectiveExpansion
  dsimp only
  change
    complexProjectiveTracePair v W * complexProjectiveTracePair v A *
          complexProjectiveTracePair v Z -
        (((((N : ℝ)⁻¹ : ℝ) : ℂ)) *
          (complexProjectiveTracePair v A *
              complexProjectiveTracePair v (Z * W) +
            complexProjectiveTracePair v (W * A) *
              complexProjectiveTracePair v Z +
            complexProjectiveTracePair v W *
              complexProjectiveTracePair v (A * Z))) +
        (((((N : ℝ)⁻¹ : ℝ) : ℂ)) ^ 2 *
          (complexProjectiveTracePair v (W * A * Z) +
            complexProjectiveTracePair v (A * Z * W) +
            complexProjectiveTracePair v (Z * W * A))) -
        (((((N : ℝ)⁻¹ : ℝ) : ℂ)) ^ 3 * Matrix.trace (W * A * Z)) = _
  rw [hWAZ, hAZW, hZWA, hZW, hWA, hAZ]
  dsimp only [W, A, ZW, WA, AZ, B]
  ring

private theorem norm_add_six_le_h13_pure
    (x₀ x₁ x₂ x₃ x₄ x₅ : ℂ) :
    ‖x₀ + x₁ + x₂ + x₃ + x₄ + x₅‖ ≤
      ‖x₀‖ + ‖x₁‖ + ‖x₂‖ + ‖x₃‖ + ‖x₄‖ + ‖x₅‖ := by
  calc
    ‖x₀ + x₁ + x₂ + x₃ + x₄ + x₅‖ ≤
        ‖x₀ + x₁ + x₂ + x₃ + x₄‖ + ‖x₅‖ := norm_add_le _ _
    _ ≤ (‖x₀ + x₁ + x₂ + x₃‖ + ‖x₄‖) + ‖x₅‖ := by
      gcongr
      exact norm_add_le _ _
    _ ≤ ((‖x₀ + x₁ + x₂‖ + ‖x₃‖) + ‖x₄‖) + ‖x₅‖ := by
      gcongr
      exact norm_add_le _ _
    _ ≤ (((‖x₀ + x₁‖ + ‖x₂‖) + ‖x₃‖) + ‖x₄‖) + ‖x₅‖ := by
      gcongr
      exact norm_add_le _ _
    _ ≤ ((((‖x₀‖ + ‖x₁‖) + ‖x₂‖) + ‖x₃‖) + ‖x₄‖) + ‖x₅‖ := by
      gcongr
      exact norm_add_le _ _
    _ = _ := by ring

/-! ## Integrated pure-word contraction -/

/- Integrability of the exact pure support word.  This is the public form of
the `L¹` fact used internally by the quantitative contraction below. -/
set_option maxHeartbeats 6000000 in
theorem integrable_centeredPair_mul_pureSixWord_h13
    {N : ℕ} (hN : 1 ≤ N) (Z : ConcreteMatrixState N)
    (hZ : Z.PosSemidef) :
    Integrable (fun v : ComplexUnitSphere N ↦
      complexCenteredProjectiveTracePair v Z *
        h13PureSixWordProjectiveExpansion v (1 + Z) Z)
      (complexUnitSphereProbabilityMeasure N) := by
  let μ := complexUnitSphereProbabilityMeasure N
  let n : ℝ := N
  let ar : ℝ := n⁻¹
  let a : ℂ := (ar : ℂ)
  let W : ConcreteMatrixState N := 1 + Z
  let A : ConcreteMatrixState N := 1 + 2 • Z
  let ZW : ConcreteMatrixState N := Z + Z ^ 2
  let WA : ConcreteMatrixState N := 1 + 3 • Z + 2 • Z ^ 2
  let AZ : ConcreteMatrixState N := Z + 2 • Z ^ 2
  let B : ConcreteMatrixState N := Z + 3 • Z ^ 2 + 2 • Z ^ 3
  let p : ComplexUnitSphere N → ConcreteMatrixState N → ℂ := fun x X ↦
    complexProjectiveTracePair x X
  let q : ComplexUnitSphere N → ℂ := fun x ↦
    complexCenteredProjectiveTracePair x Z
  let f₀ : ComplexUnitSphere N → ℂ := fun x ↦ q x * p x W * p x A * p x Z
  let f₁ : ComplexUnitSphere N → ℂ := fun x ↦ q x * p x A * p x ZW
  let f₂ : ComplexUnitSphere N → ℂ := fun x ↦ q x * p x WA * p x Z
  let f₃ : ComplexUnitSphere N → ℂ := fun x ↦ q x * p x W * p x AZ
  let f₄ : ComplexUnitSphere N → ℂ := fun x ↦ q x * p x B
  let f₅ : ComplexUnitSphere N → ℂ := q
  letI : IsProbabilityMeasure μ :=
    complexUnitSphereProbabilityMeasure_isProbability hN
  have hW : W.PosSemidef := by
    simpa only [W] using Matrix.PosSemidef.one.add hZ
  have hA : A.PosSemidef := by
    simpa only [A, two_nsmul] using Matrix.PosSemidef.one.add (hZ.add hZ)
  have hZW : ZW.PosSemidef := by
    simpa only [ZW] using hZ.add (hZ.pow 2)
  have hWA : WA.PosSemidef := by
    have h3 : (3 • Z).PosSemidef := by
      simpa only [three_nsmul] using hZ.add (hZ.add hZ)
    have h2 : (2 • Z ^ 2).PosSemidef := by
      simpa only [two_nsmul] using (hZ.pow 2).add (hZ.pow 2)
    simpa only [WA] using (Matrix.PosSemidef.one.add h3).add h2
  have hAZ : AZ.PosSemidef := by
    have h2 : (2 • Z ^ 2).PosSemidef := by
      simpa only [two_nsmul] using (hZ.pow 2).add (hZ.pow 2)
    simpa only [AZ] using hZ.add h2
  have hB : B.PosSemidef := by
    have h3 : (3 • Z ^ 2).PosSemidef := by
      simpa only [three_nsmul] using
        (hZ.pow 2).add ((hZ.pow 2).add (hZ.pow 2))
    have h2 : (2 • Z ^ 3).PosSemidef := by
      simpa only [two_nsmul] using (hZ.pow 3).add (hZ.pow 3)
    simpa only [B] using (hZ.add h3).add h2
  have hq4 : MemLp q 4 μ := by
    simpa only [q, μ] using
      memLp_posSemidef_centeredProjectiveTracePair_complex_four_h13 hN Z hZ
  have hpW4 : MemLp (fun x ↦ p x W) 4 μ := by
    simpa only [p, μ] using
      memLp_posSemidef_projectiveTracePair_complex_four_h13 hN W hW
  have hpA4 : MemLp (fun x ↦ p x A) 4 μ := by
    simpa only [p, μ] using
      memLp_posSemidef_projectiveTracePair_complex_four_h13 hN A hA
  have hpZ4 : MemLp (fun x ↦ p x Z) 4 μ := by
    simpa only [p, μ] using
      memLp_posSemidef_projectiveTracePair_complex_four_h13 hN Z hZ
  have hpZW4 : MemLp (fun x ↦ p x ZW) 4 μ := by
    simpa only [p, μ] using
      memLp_posSemidef_projectiveTracePair_complex_four_h13 hN ZW hZW
  have hpWA4 : MemLp (fun x ↦ p x WA) 4 μ := by
    simpa only [p, μ] using
      memLp_posSemidef_projectiveTracePair_complex_four_h13 hN WA hWA
  have hpAZ4 : MemLp (fun x ↦ p x AZ) 4 μ := by
    simpa only [p, μ] using
      memLp_posSemidef_projectiveTracePair_complex_four_h13 hN AZ hAZ
  have hpB4 : MemLp (fun x ↦ p x B) 4 μ := by
    simpa only [p, μ] using
      memLp_posSemidef_projectiveTracePair_complex_four_h13 hN B hB
  have hf₀ : MemLp f₀ 1 μ := by
    simpa only [f₀] using memLp_mul_four_complex_h13 hq4 hpW4 hpA4 hpZ4
  have hf₁ : MemLp f₁ 1 μ := by
    simpa only [f₁] using memLp_mul_three_complex_h13_pure hq4 hpA4 hpZW4
  have hf₂ : MemLp f₂ 1 μ := by
    simpa only [f₂] using memLp_mul_three_complex_h13_pure hq4 hpWA4 hpZ4
  have hf₃ : MemLp f₃ 1 μ := by
    simpa only [f₃] using memLp_mul_three_complex_h13_pure hq4 hpW4 hpAZ4
  have hf₄ : MemLp f₄ 1 μ := by
    simpa only [f₄] using memLp_mul_two_complex_h13_pure hq4 hpB4
  have hf₅ : MemLp f₅ 1 μ := by
    simpa only [f₅] using memLp_one_factor_complex_h13_pure hq4
  have hsumMem : MemLp (fun x : ComplexUnitSphere N ↦
      f₀ x + (-a) * f₁ x + (-a) * f₂ x + (-a) * f₃ x +
        (3 * a ^ 2) * f₄ x + (-(a ^ 3 * Matrix.trace B)) * f₅ x) 1 μ :=
    (((((hf₀.add (hf₁.const_smul (-a))).add
      (hf₂.const_smul (-a))).add (hf₃.const_smul (-a))).add
      (hf₄.const_smul (3 * a ^ 2))).add
      (hf₅.const_smul (-(a ^ 3 * Matrix.trace B))))
  have hkernelMem : MemLp (fun x : ComplexUnitSphere N ↦
      complexCenteredProjectiveTracePair x Z *
        h13PureSixWordProjectiveExpansion x (1 + Z) Z) 1 μ := by
    apply hsumMem.ae_eq
    filter_upwards [] with x
    rw [h13PureSixWordProjectiveExpansion_eq_single_h13,
      h13CenteredTripleTraceProjectiveExpansion_support_eq_h13_pure]
    dsimp only [f₀, f₁, f₂, f₃, f₄, f₅, q, p, W, A, ZW, WA, AZ, B,
      a, ar, n]
    ring
  simpa only [μ] using memLp_one_iff_integrable.mp hkernelMem

/-- The exact scalar polynomial produced by the pure-word Holder ledger. -/
def h13PureHolderRadialPolynomial (N : ℕ) (Z : ConcreteMatrixState N) : ℝ :=
  let n : ℝ := N
  let t : ℝ := (Matrix.trace Z).re
  let u : ℝ := (Matrix.trace (Z ^ 2)).re
  let v : ℝ := (Matrix.trace (Z ^ 3)).re
  (23 * t ^ 2 * (n + t) * (n + 2 * t) +
    11 * t *
      ((n + 2 * t) * (t + u) +
        (n + 3 * t + 2 * u) * t +
        (n + t) * (t + 2 * u)) +
    16 * t * (t + 3 * u + 2 * v)) / n ^ 4

/-- Actual integrated pure-word contraction, before the final scalar
collection into the common trace-one/trace-two envelope. -/
theorem integral_norm_centeredPair_mul_pureSixWord_le_holderPolynomial_h13
    {N : ℕ} (hN : 1 ≤ N) (Z : ConcreteMatrixState N)
    (hZ : Z.PosSemidef) :
    (∫ v : ComplexUnitSphere N,
      ‖complexCenteredProjectiveTracePair v Z *
        h13PureSixWordProjectiveExpansion v (1 + Z) Z‖
        ∂(complexUnitSphereProbabilityMeasure N)) ≤
      h13PureHolderRadialPolynomial N Z := by
  let μ := complexUnitSphereProbabilityMeasure N
  let n : ℝ := N
  let t : ℝ := (Matrix.trace Z).re
  let u : ℝ := (Matrix.trace (Z ^ 2)).re
  let v₃ : ℝ := (Matrix.trace (Z ^ 3)).re
  let ar : ℝ := n⁻¹
  let a : ℂ := (ar : ℂ)
  let W : ConcreteMatrixState N := 1 + Z
  let A : ConcreteMatrixState N := 1 + 2 • Z
  let ZW : ConcreteMatrixState N := Z + Z ^ 2
  let WA : ConcreteMatrixState N := 1 + 3 • Z + 2 • Z ^ 2
  let AZ : ConcreteMatrixState N := Z + 2 • Z ^ 2
  let B : ConcreteMatrixState N := Z + 3 • Z ^ 2 + 2 • Z ^ 3
  let p : ComplexUnitSphere N → ConcreteMatrixState N → ℂ := fun x X ↦
    complexProjectiveTracePair x X
  let q : ComplexUnitSphere N → ℂ := fun x ↦
    complexCenteredProjectiveTracePair x Z
  let f₀ : ComplexUnitSphere N → ℂ := fun x ↦ q x * p x W * p x A * p x Z
  let f₁ : ComplexUnitSphere N → ℂ := fun x ↦ q x * p x A * p x ZW
  let f₂ : ComplexUnitSphere N → ℂ := fun x ↦ q x * p x WA * p x Z
  let f₃ : ComplexUnitSphere N → ℂ := fun x ↦ q x * p x W * p x AZ
  let f₄ : ComplexUnitSphere N → ℂ := fun x ↦ q x * p x B
  let f₅ : ComplexUnitSphere N → ℂ := q
  letI : IsProbabilityMeasure μ :=
    complexUnitSphereProbabilityMeasure_isProbability hN
  have hn : 0 < n := by
    dsimp only [n]
    exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hn1 : 1 ≤ n := by
    dsimp only [n]
    exact_mod_cast hN
  have har : 0 ≤ ar := by dsimp only [ar]; positivity
  have ht : 0 ≤ t := (Complex.nonneg_iff.mp hZ.trace_nonneg).1
  have hu : 0 ≤ u := by
    exact (Complex.nonneg_iff.mp (hZ.pow 2).trace_nonneg).1
  have hv₃ : 0 ≤ v₃ := by
    exact (Complex.nonneg_iff.mp (hZ.pow 3).trace_nonneg).1
  have htlow : t ^ 2 ≤ n * u := by
    simpa only [t, u, n, pow_two] using
      posSemidef_trace_re_sq_le_card_mul_trace_square_re_h13_pure Z hZ
  have hv₃le : v₃ ≤ t * u := by
    simpa only [v₃, t, u] using
      posSemidef_trace_cube_re_le_trace_re_mul_trace_square_re_h13 Z hZ
  have hW : W.PosSemidef := by
    simpa only [W] using Matrix.PosSemidef.one.add hZ
  have hA : A.PosSemidef := by
    simpa only [A, two_nsmul] using Matrix.PosSemidef.one.add (hZ.add hZ)
  have hZW : ZW.PosSemidef := by
    simpa only [ZW] using hZ.add (hZ.pow 2)
  have hWA : WA.PosSemidef := by
    have h3 : (3 • Z).PosSemidef := by
      simpa only [three_nsmul] using hZ.add (hZ.add hZ)
    have h2 : (2 • Z ^ 2).PosSemidef := by
      simpa only [two_nsmul] using (hZ.pow 2).add (hZ.pow 2)
    simpa only [WA] using (Matrix.PosSemidef.one.add h3).add h2
  have hAZ : AZ.PosSemidef := by
    have h2 : (2 • Z ^ 2).PosSemidef := by
      simpa only [two_nsmul] using (hZ.pow 2).add (hZ.pow 2)
    simpa only [AZ] using hZ.add h2
  have hB : B.PosSemidef := by
    have h3 : (3 • Z ^ 2).PosSemidef := by
      simpa only [three_nsmul] using
        (hZ.pow 2).add ((hZ.pow 2).add (hZ.pow 2))
    have h2 : (2 • Z ^ 3).PosSemidef := by
      simpa only [two_nsmul] using (hZ.pow 3).add (hZ.pow 3)
    simpa only [B] using (hZ.add h3).add h2
  have htrW : (Matrix.trace W).re = n + t := by
    dsimp only [W, n, t]
    simp only [Matrix.trace_add, Matrix.trace_one, Fintype.card_fin,
      Complex.add_re, Complex.natCast_re]
  have htrA : (Matrix.trace A).re = n + 2 * t := by
    dsimp only [A, n, t]
    simp only [two_nsmul, Matrix.trace_add, Matrix.trace_one,
      Fintype.card_fin, Complex.add_re, Complex.natCast_re]
    ring
  have htrZW : (Matrix.trace ZW).re = t + u := by
    dsimp only [ZW, t, u]
    simp only [Matrix.trace_add, Complex.add_re]
  have htrWA : (Matrix.trace WA).re = n + 3 * t + 2 * u := by
    dsimp only [WA, n, t, u]
    simp only [two_nsmul, three_nsmul, Matrix.trace_add, Matrix.trace_one,
      Fintype.card_fin, Complex.add_re, Complex.natCast_re]
    ring
  have htrAZ : (Matrix.trace AZ).re = t + 2 * u := by
    dsimp only [AZ, t, u]
    simp only [two_nsmul, Matrix.trace_add, Complex.add_re]
    ring
  have htrB : (Matrix.trace B).re = t + 3 * u + 2 * v₃ := by
    dsimp only [B, t, u, v₃]
    simp only [two_nsmul, three_nsmul, Matrix.trace_add, Complex.add_re]
    ring
  have hnorma : ‖a‖ = ar := by
    dsimp only [a]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg har]
  have htrBnonneg := Complex.nonneg_iff.mp hB.trace_nonneg
  have htrBreal : Matrix.trace B = (((Matrix.trace B).re : ℝ) : ℂ) := by
    apply Complex.ext
    · rfl
    · simp only [Complex.ofReal_im, htrBnonneg.2]
  have hnormtrB : ‖Matrix.trace B‖ = (Matrix.trace B).re := by
    rw [Complex.norm_def, Complex.normSq_apply, ← htrBnonneg.2]
    simp only [zero_mul, add_zero]
    exact Real.sqrt_mul_self htrBnonneg.1
  have hq4 : MemLp q 4 μ := by
    simpa only [q, μ] using
      memLp_posSemidef_centeredProjectiveTracePair_complex_four_h13 hN Z hZ
  have hpW4 : MemLp (fun x ↦ p x W) 4 μ := by
    simpa only [p, μ] using
      memLp_posSemidef_projectiveTracePair_complex_four_h13 hN W hW
  have hpA4 : MemLp (fun x ↦ p x A) 4 μ := by
    simpa only [p, μ] using
      memLp_posSemidef_projectiveTracePair_complex_four_h13 hN A hA
  have hpZ4 : MemLp (fun x ↦ p x Z) 4 μ := by
    simpa only [p, μ] using
      memLp_posSemidef_projectiveTracePair_complex_four_h13 hN Z hZ
  have hpZW4 : MemLp (fun x ↦ p x ZW) 4 μ := by
    simpa only [p, μ] using
      memLp_posSemidef_projectiveTracePair_complex_four_h13 hN ZW hZW
  have hpWA4 : MemLp (fun x ↦ p x WA) 4 μ := by
    simpa only [p, μ] using
      memLp_posSemidef_projectiveTracePair_complex_four_h13 hN WA hWA
  have hpAZ4 : MemLp (fun x ↦ p x AZ) 4 μ := by
    simpa only [p, μ] using
      memLp_posSemidef_projectiveTracePair_complex_four_h13 hN AZ hAZ
  have hpB4 : MemLp (fun x ↦ p x B) 4 μ := by
    simpa only [p, μ] using
      memLp_posSemidef_projectiveTracePair_complex_four_h13 hN B hB
  have hf₀ : MemLp f₀ 1 μ := by
    simpa only [f₀] using memLp_mul_four_complex_h13 hq4 hpW4 hpA4 hpZ4
  have hf₁ : MemLp f₁ 1 μ := by
    simpa only [f₁] using memLp_mul_three_complex_h13_pure hq4 hpA4 hpZW4
  have hf₂ : MemLp f₂ 1 μ := by
    simpa only [f₂] using memLp_mul_three_complex_h13_pure hq4 hpWA4 hpZ4
  have hf₃ : MemLp f₃ 1 μ := by
    simpa only [f₃] using memLp_mul_three_complex_h13_pure hq4 hpW4 hpAZ4
  have hf₄ : MemLp f₄ 1 μ := by
    simpa only [f₄] using memLp_mul_two_complex_h13_pure hq4 hpB4
  have hf₅ : MemLp f₅ 1 μ := by
    simpa only [f₅] using memLp_one_factor_complex_h13_pure hq4
  have hkernel (x : ComplexUnitSphere N) :
      complexCenteredProjectiveTracePair x Z *
          h13PureSixWordProjectiveExpansion x (1 + Z) Z =
        f₀ x + (-a) * f₁ x + (-a) * f₂ x + (-a) * f₃ x +
          (3 * a ^ 2) * f₄ x +
          (-(a ^ 3 * Matrix.trace B)) * f₅ x := by
    rw [h13PureSixWordProjectiveExpansion_eq_single_h13,
      h13CenteredTripleTraceProjectiveExpansion_support_eq_h13_pure]
    dsimp only [f₀, f₁, f₂, f₃, f₄, f₅, q, p, W, A, ZW, WA, AZ, B,
      a, ar, n]
    ring
  have hsumMem : MemLp (fun x : ComplexUnitSphere N ↦
      f₀ x + (-a) * f₁ x + (-a) * f₂ x + (-a) * f₃ x +
        (3 * a ^ 2) * f₄ x + (-(a ^ 3 * Matrix.trace B)) * f₅ x) 1 μ := by
    exact (((((hf₀.add (hf₁.const_smul (-a))).add
      (hf₂.const_smul (-a))).add (hf₃.const_smul (-a))).add
      (hf₄.const_smul (3 * a ^ 2))).add
      (hf₅.const_smul (-(a ^ 3 * Matrix.trace B))))
  have hkernelMem : MemLp (fun x : ComplexUnitSphere N ↦
      complexCenteredProjectiveTracePair x Z *
        h13PureSixWordProjectiveExpansion x (1 + Z) Z) 1 μ := by
    apply hsumMem.ae_eq
    filter_upwards [] with x
    exact (hkernel x).symm
  have hi₀ : Integrable (fun x ↦ ‖f₀ x‖) μ :=
    (memLp_one_iff_integrable.mp hf₀).norm
  have hi₁ : Integrable (fun x ↦ ‖f₁ x‖) μ :=
    (memLp_one_iff_integrable.mp hf₁).norm
  have hi₂ : Integrable (fun x ↦ ‖f₂ x‖) μ :=
    (memLp_one_iff_integrable.mp hf₂).norm
  have hi₃ : Integrable (fun x ↦ ‖f₃ x‖) μ :=
    (memLp_one_iff_integrable.mp hf₃).norm
  have hi₄ : Integrable (fun x ↦ ‖f₄ x‖) μ :=
    (memLp_one_iff_integrable.mp hf₄).norm
  have hi₅ : Integrable (fun x ↦ ‖f₅ x‖) μ :=
    (memLp_one_iff_integrable.mp hf₅).norm
  let c₄ : ℝ := 3 * ar ^ 2
  let c₅ : ℝ := ar ^ 3 * (Matrix.trace B).re
  have hc₄ : 0 ≤ c₄ := by dsimp only [c₄]; positivity
  have hc₅ : 0 ≤ c₅ := by
    dsimp only [c₅]
    exact mul_nonneg (pow_nonneg har 3) htrBnonneg.1
  let R : ComplexUnitSphere N → ℝ := fun x ↦
    ‖f₀ x‖ + ar * ‖f₁ x‖ + ar * ‖f₂ x‖ + ar * ‖f₃ x‖ +
      c₄ * ‖f₄ x‖ + c₅ * ‖f₅ x‖
  have hRint : Integrable R μ := by
    dsimp only [R]
    exact (((((hi₀.add (hi₁.const_mul ar)).add (hi₂.const_mul ar)).add
      (hi₃.const_mul ar)).add (hi₄.const_mul c₄)).add
      (hi₅.const_mul c₅))
  have hpoint (x : ComplexUnitSphere N) :
      ‖complexCenteredProjectiveTracePair x Z *
        h13PureSixWordProjectiveExpansion x (1 + Z) Z‖ ≤ R x := by
    rw [hkernel x]
    have H := norm_add_six_le_h13_pure
      (f₀ x) ((-a) * f₁ x) ((-a) * f₂ x) ((-a) * f₃ x)
      ((3 * a ^ 2) * f₄ x) ((-(a ^ 3 * Matrix.trace B)) * f₅ x)
    dsimp only [R, c₄, c₅]
    have hnormthree : ‖(3 : ℂ)‖ = 3 := by norm_num
    simpa only [norm_mul, norm_neg, hnorma, norm_pow, hnormtrB,
      hnormthree] using H
  have hleftInt : Integrable (fun x : ComplexUnitSphere N ↦
      ‖complexCenteredProjectiveTracePair x Z *
        h13PureSixWordProjectiveExpansion x (1 + Z) Z‖) μ :=
    (memLp_one_iff_integrable.mp hkernelMem).norm
  have hmono :
      (∫ x : ComplexUnitSphere N,
        ‖complexCenteredProjectiveTracePair x Z *
          h13PureSixWordProjectiveExpansion x (1 + Z) Z‖ ∂μ) ≤
        ∫ x, R x ∂μ :=
    integral_mono hleftInt hRint hpoint
  have hRvalue :
      (∫ x, R x ∂μ) =
        (∫ x, ‖f₀ x‖ ∂μ) + ar * (∫ x, ‖f₁ x‖ ∂μ) +
          ar * (∫ x, ‖f₂ x‖ ∂μ) + ar * (∫ x, ‖f₃ x‖ ∂μ) +
          c₄ * (∫ x, ‖f₄ x‖ ∂μ) + c₅ * (∫ x, ‖f₅ x‖ ∂μ) := by
    rw [show R =
      (((((fun x ↦ ‖f₀ x‖) + (fun x ↦ ar * ‖f₁ x‖)) +
        (fun x ↦ ar * ‖f₂ x‖)) + (fun x ↦ ar * ‖f₃ x‖)) +
        (fun x ↦ c₄ * ‖f₄ x‖)) + (fun x ↦ c₅ * ‖f₅ x‖) by rfl]
    rw [integral_add'
      ((((hi₀.add (hi₁.const_mul ar)).add (hi₂.const_mul ar)).add
        (hi₃.const_mul ar)).add (hi₄.const_mul c₄))
      (hi₅.const_mul c₅)]
    rw [integral_add'
      (((hi₀.add (hi₁.const_mul ar)).add (hi₂.const_mul ar)).add
        (hi₃.const_mul ar)) (hi₄.const_mul c₄)]
    rw [integral_add' ((hi₀.add (hi₁.const_mul ar)).add
      (hi₂.const_mul ar)) (hi₃.const_mul ar)]
    rw [integral_add' (hi₀.add (hi₁.const_mul ar)) (hi₂.const_mul ar)]
    rw [integral_add' hi₀ (hi₁.const_mul ar)]
    simp only [integral_const_mul]
  have H₀ := integral_norm_centeredPair_mul_three_posPairs_le_h13_pure
    hN Z W A Z hZ hW hA hZ
  have H₁ := integral_norm_centeredPair_mul_two_posPairs_le_h13_pure
    hN Z A ZW hZ hA hZW
  have H₂ := integral_norm_centeredPair_mul_two_posPairs_le_h13_pure
    hN Z WA Z hZ hWA hZ
  have H₃ := integral_norm_centeredPair_mul_two_posPairs_le_h13_pure
    hN Z W AZ hZ hW hAZ
  have H₄ := integral_norm_centeredPair_mul_posPair_le_nine_halves_h13_pure
    hN Z B hZ hB
  have H₅ := integral_norm_centeredPair_le_h13_pure hN Z hZ
  have hRbound :
      (∫ x, R x ∂μ) ≤
        (23 * t ^ 2 * (n + t) * (n + 2 * t) +
          11 * t *
            ((n + 2 * t) * (t + u) +
              (n + 3 * t + 2 * u) * t +
              (n + t) * (t + 2 * u)) +
          16 * t * (t + 3 * u + 2 * v₃)) / n ^ 4 := by
    rw [hRvalue]
    have hn2 : 0 < n ^ 2 := pow_pos hn 2
    have hn3 : 0 < n ^ 3 := pow_pos hn 3
    have hn4 : 0 < n ^ 4 := pow_pos hn 4
    change (∫ x, ‖f₀ x‖ ∂μ) ≤ _ at H₀
    change (∫ x, ‖f₁ x‖ ∂μ) ≤ _ at H₁
    change (∫ x, ‖f₂ x‖ ∂μ) ≤ _ at H₂
    change (∫ x, ‖f₃ x‖ ∂μ) ≤ _ at H₃
    change (∫ x, ‖f₄ x‖ ∂μ) ≤ _ at H₄
    change (∫ x, ‖f₅ x‖ ∂μ) ≤ _ at H₅
    rw [htrW, htrA] at H₀
    rw [htrA, htrZW] at H₁
    rw [htrWA] at H₂
    rw [htrW, htrAZ] at H₃
    rw [htrB] at H₄
    dsimp only [ar, c₄, c₅]
    rw [htrB]
    field_simp [ne_of_gt hn] at H₀ H₁ H₂ H₃ H₄ H₅ ⊢
    nlinarith
  calc
    _ ≤ ∫ x, R x ∂μ := by simpa only [μ] using hmono
    _ ≤ (23 * t ^ 2 * (n + t) * (n + 2 * t) +
          11 * t *
            ((n + 2 * t) * (t + u) +
              (n + 3 * t + 2 * u) * t +
              (n + t) * (t + 2 * u)) +
          16 * t * (t + 3 * u + 2 * v₃)) / n ^ 4 := hRbound
    _ = h13PureHolderRadialPolynomial N Z := by
      rfl

/-! ## Scalar collection -/

/-- The scalar polynomial left by the sharp Holder estimates fits inside the
common H14 trace-one/trace-two envelope with coefficient `256`. -/
theorem h13PureHolderPolynomial_le_halfEnvelope
    (n t u v : ℝ) (hn : 1 ≤ n) (ht : 0 ≤ t) (hu : 0 ≤ u)
    (htlow : t ^ 2 ≤ n * u) (hv : v ≤ t * u) :
    23 * t ^ 2 * (n + t) * (n + 2 * t) +
        11 * t *
          ((n + 2 * t) * (t + u) +
            (n + 3 * t + 2 * u) * t +
            (n + t) * (t + 2 * u)) +
        16 * t * (t + 3 * u + 2 * v) ≤
      128 * (n ^ 2 * (t ^ 2 + u) + t ^ 4 + n ^ 2 * u ^ 2) := by
  have hn0 : 0 ≤ n := le_trans (by norm_num) hn
  have hn2 : 1 ≤ n ^ 2 := by nlinarith [sq_nonneg n]
  have hnt3 : 144 * (n * t ^ 3) ≤
      81 * (n ^ 2 * t ^ 2) + 64 * t ^ 4 := by
    nlinarith [sq_nonneg (9 * n * t - 8 * t ^ 2)]
  have hnt2 : n * t ^ 2 ≤ n ^ 2 * u := by
    have := mul_le_mul_of_nonneg_left htlow hn0
    nlinarith
  have hntu : 2 * (n * t * u) ≤ n ^ 2 * t ^ 2 + u ^ 2 := by
    nlinarith [sq_nonneg (n * t - u)]
  have ht3 : 2 * t ^ 3 ≤ t ^ 2 + t ^ 4 := by
    nlinarith [sq_nonneg (t - t ^ 2)]
  have ht2u : 2 * (t ^ 2 * u) ≤ t ^ 4 + u ^ 2 := by
    nlinarith [sq_nonneg (t ^ 2 - u)]
  have htu : 2 * (t * u) ≤ t ^ 2 + u ^ 2 := by
    nlinarith [sq_nonneg (t - u)]
  have htv : t * v ≤ t ^ 2 * u := by
    have := mul_le_mul_of_nonneg_left hv ht
    nlinarith
  have ht2lift : t ^ 2 ≤ n ^ 2 * u := by
    have hnu : n * u ≤ n ^ 2 * u := by
      nlinarith [mul_nonneg hu (sub_nonneg.mpr hn)]
    exact htlow.trans hnu
  have ht2liftA : t ^ 2 ≤ n ^ 2 * t ^ 2 := by
    nlinarith [sq_nonneg t,
      mul_nonneg (sub_nonneg.mpr hn2) (sq_nonneg t)]
  have hu2lift : u ^ 2 ≤ n ^ 2 * u ^ 2 := by
    nlinarith [sq_nonneg u, mul_nonneg (sub_nonneg.mpr hn2) (sq_nonneg u)]
  have ht2uLiftC : t ^ 2 * u ≤ n ^ 2 * u ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right htlow hu
    have hnu2 : n * u ^ 2 ≤ n ^ 2 * u ^ 2 := by
      nlinarith [mul_nonneg (sq_nonneg u) (sub_nonneg.mpr hn)]
    nlinarith
  have h69nt3 : 69 * (n * t ^ 3) ≤
      39 * (n ^ 2 * t ^ 2) + 31 * t ^ 4 := by
    nlinarith
  have h33ntu : 33 * (n * t * u) ≤
      17 * (n ^ 2 * t ^ 2) + 17 * (n ^ 2 * u ^ 2) := by
    nlinarith
  have h66t3 : 66 * t ^ 3 ≤
      33 * (n ^ 2 * t ^ 2) + 33 * t ^ 4 := by
    nlinarith
  have h66t2u : 66 * (t ^ 2 * u) ≤
      66 * (n ^ 2 * u ^ 2) := by
    nlinarith
  have h48tu : 48 * (t * u) ≤
      24 * (n ^ 2 * u) + 24 * (n ^ 2 * u ^ 2) := by
    nlinarith
  have h32tv : 32 * (t * v) ≤
      16 * t ^ 4 + 16 * (n ^ 2 * u ^ 2) := by
    nlinarith
  have hexpand :
      23 * t ^ 2 * (n + t) * (n + 2 * t) +
          11 * t *
            ((n + 2 * t) * (t + u) +
              (n + 3 * t + 2 * u) * t +
              (n + t) * (t + 2 * u)) +
          16 * t * (t + 3 * u + 2 * v) =
        23 * (n ^ 2 * t ^ 2) + 69 * (n * t ^ 3) + 46 * t ^ 4 +
          33 * (n * t ^ 2) + 33 * (n * t * u) + 66 * t ^ 3 +
          66 * (t ^ 2 * u) + 16 * t ^ 2 + 48 * (t * u) +
          32 * (t * v) := by
    ring
  have hcoarse :
      23 * t ^ 2 * (n + t) * (n + 2 * t) +
          11 * t *
            ((n + 2 * t) * (t + u) +
              (n + 3 * t + 2 * u) * t +
              (n + t) * (t + 2 * u)) +
          16 * t * (t + 3 * u + 2 * v) ≤
        112 * (n ^ 2 * t ^ 2) + 73 * (n ^ 2 * u) +
          126 * t ^ 4 + 123 * (n ^ 2 * u ^ 2) := by
    rw [hexpand]
    nlinarith only [h69nt3, hnt2, h33ntu, h66t3, h66t2u,
      ht2lift, h48tu, h32tv]
  calc
    _ ≤ 112 * (n ^ 2 * t ^ 2) + 73 * (n ^ 2 * u) +
        126 * t ^ 4 + 123 * (n ^ 2 * u ^ 2) := hcoarse
    _ ≤ 128 * (n ^ 2 * (t ^ 2 + u) + t ^ 4 + n ^ 2 * u ^ 2) := by
      nlinarith [mul_nonneg (sq_nonneg n) hu]

/-- The combined pure six-word contribution consumes one half of the common
fixed-sphere coefficient `256` in the H13 trace-one/trace-two envelope. -/
theorem integral_norm_centeredPair_mul_pureSixWord_le_halfEnvelope_h13
    {N : ℕ} (hN : 1 ≤ N) (Z : ConcreteMatrixState N)
    (hZ : Z.PosSemidef) :
    (∫ v : ComplexUnitSphere N,
      ‖complexCenteredProjectiveTracePair v Z *
        h13PureSixWordProjectiveExpansion v (1 + Z) Z‖
        ∂(complexUnitSphereProbabilityMeasure N)) ≤
      128 *
        (((Matrix.trace Z).re ^ 2 + (Matrix.trace (Z ^ 2)).re) /
            (N : ℝ) ^ 2 +
          (Matrix.trace Z).re ^ 4 / (N : ℝ) ^ 4 +
          (Matrix.trace (Z ^ 2)).re ^ 2 / (N : ℝ) ^ 2) := by
  let n : ℝ := N
  let t : ℝ := (Matrix.trace Z).re
  let u : ℝ := (Matrix.trace (Z ^ 2)).re
  let v₃ : ℝ := (Matrix.trace (Z ^ 3)).re
  have hn : 0 < n := by
    dsimp only [n]
    exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hn1 : 1 ≤ n := by
    dsimp only [n]
    exact_mod_cast hN
  have ht : 0 ≤ t := (Complex.nonneg_iff.mp hZ.trace_nonneg).1
  have hu : 0 ≤ u :=
    (Complex.nonneg_iff.mp (hZ.pow 2).trace_nonneg).1
  have htlow : t ^ 2 ≤ n * u := by
    simpa only [t, u, n, pow_two] using
      posSemidef_trace_re_sq_le_card_mul_trace_square_re_h13_pure Z hZ
  have hv₃le : v₃ ≤ t * u := by
    simpa only [v₃, t, u] using
      posSemidef_trace_cube_re_le_trace_re_mul_trace_square_re_h13 Z hZ
  have hbase :=
    integral_norm_centeredPair_mul_pureSixWord_le_holderPolynomial_h13
      hN Z hZ
  have hscalar :=
    h13PureHolderPolynomial_le_halfEnvelope n t u v₃ hn1 ht hu htlow hv₃le
  change
    (∫ v : ComplexUnitSphere N,
      ‖complexCenteredProjectiveTracePair v Z *
        h13PureSixWordProjectiveExpansion v (1 + Z) Z‖
        ∂(complexUnitSphereProbabilityMeasure N)) ≤
      128 * ((t ^ 2 + u) / n ^ 2 + t ^ 4 / n ^ 4 + u ^ 2 / n ^ 2)
  calc
    _ ≤ h13PureHolderRadialPolynomial N Z := hbase
    _ = (23 * t ^ 2 * (n + t) * (n + 2 * t) +
          11 * t *
            ((n + 2 * t) * (t + u) +
              (n + 3 * t + 2 * u) * t +
              (n + t) * (t + 2 * u)) +
          16 * t * (t + 3 * u + 2 * v₃)) / n ^ 4 := by
      rfl
    _ ≤ 128 * (n ^ 2 * (t ^ 2 + u) + t ^ 4 + n ^ 2 * u ^ 2) /
        n ^ 4 := by
      exact div_le_div_of_nonneg_right hscalar (by positivity)
    _ = 128 * ((t ^ 2 + u) / n ^ 2 + t ^ 4 / n ^ 4 +
        u ^ 2 / n ^ 2) := by
      field_simp [ne_of_gt hn]

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
