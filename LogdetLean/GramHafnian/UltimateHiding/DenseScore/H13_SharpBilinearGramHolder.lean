import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H13_SharpBilinearProjectiveL4
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H13_SharpCenteredPosSemidefProjectiveL4
import Mathlib.Tactic

/-!
# Gram-product Holder bounds for the H13 mixed word

The cross-bilinear terms pair `T` with `(I+2Z)T`.  A sum of their two Gram
traces would introduce a fifth radial degree.  The lemmas here retain the
geometric product: if `Tr(RR^*) Tr(SS^*) <= L^2 G^2`, the product of the two
bilinear `L4` norms is at most `(3/2) L G / N`.
-/

open MeasureTheory
open scoped ComplexOrder MatrixOrder

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

set_option maxHeartbeats 2400000

/-- Product form of the sharpened bilinear `L4` estimate. -/
theorem lpNorm_bilinearFactors_mul_le_of_gramProduct_h13
    {N : ℕ} (hN : 1 ≤ N)
    (R S : ConcreteMatrixState N) (hR : R.IsSymm) (hS : S.IsSymm)
    (L G : ℝ) (hL : 0 ≤ L) (hG : 0 ≤ G)
    (hgram :
      (Matrix.trace (R * R.conjTranspose)).re *
          (Matrix.trace (S * S.conjTranspose)).re ≤ L ^ 2 * G ^ 2) :
    lpNorm (fun v : ComplexUnitSphere N =>
        complexProjectiveConjugateBilinearPair v R) 4
          (complexUnitSphereProbabilityMeasure N) *
      lpNorm (fun v : ComplexUnitSphere N =>
        complexProjectiveTransposeBilinearPair v S.conjTranspose) 4
          (complexUnitSphereProbabilityMeasure N) ≤
      (3 / 2 : ℝ) * L * G / (N : ℝ) := by
  let μ := complexUnitSphereProbabilityMeasure N
  let x := lpNorm (fun v : ComplexUnitSphere N =>
    complexProjectiveConjugateBilinearPair v R) 4 μ
  let y := lpNorm (fun v : ComplexUnitSphere N =>
    complexProjectiveTransposeBilinearPair v S.conjTranspose) 4 μ
  let r := (Matrix.trace (R * R.conjTranspose)).re
  let s := (Matrix.trace (S * S.conjTranspose)).re
  let n : ℝ := N
  have hn : 0 < n := by
    dsimp only [n]
    exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hr : 0 ≤ r := by
    exact (Complex.nonneg_iff.mp
      (Matrix.posSemidef_self_mul_conjTranspose R).trace_nonneg).1
  have hs : 0 ≤ s := by
    exact (Complex.nonneg_iff.mp
      (Matrix.posSemidef_self_mul_conjTranspose S).trace_nonneg).1
  have hx : 0 ≤ x := lpNorm_nonneg
  have hy : 0 ≤ y := lpNorm_nonneg
  have hxsq : x ^ 2 ≤ (3 / 2 : ℝ) * r / n := by
    simpa only [x, r, n, μ] using
      lpNorm_conjugateBilinearPair_four_sq_le_three_halves_h13 hN R hR
  have hysq : y ^ 2 ≤ (3 / 2 : ℝ) * s / n := by
    simpa only [y, s, n, μ] using
      lpNorm_transposeBilinearPair_conjTranspose_four_sq_le_three_halves_h13
        hN S hS
  have hprodSq : x ^ 2 * y ^ 2 ≤
      ((3 / 2 : ℝ) * r / n) * ((3 / 2 : ℝ) * s / n) :=
    mul_le_mul hxsq hysq (sq_nonneg y) (by positivity)
  have hscaled :
      ((3 / 2 : ℝ) * r / n) * ((3 / 2 : ℝ) * s / n) ≤
        ((3 / 2 : ℝ) * L * G / n) ^ 2 := by
    calc
      ((3 / 2 : ℝ) * r / n) * ((3 / 2 : ℝ) * s / n) =
          (9 / 4 : ℝ) * (r * s) / n ^ 2 := by ring
      _ ≤ (9 / 4 : ℝ) * (L ^ 2 * G ^ 2) / n ^ 2 := by
        gcongr
      _ = ((3 / 2 : ℝ) * L * G / n) ^ 2 := by ring
  have hsquare : (x * y) ^ 2 ≤
      ((3 / 2 : ℝ) * L * G / n) ^ 2 := by
    calc
      (x * y) ^ 2 = x ^ 2 * y ^ 2 := by ring
      _ ≤ ((3 / 2 : ℝ) * r / n) * ((3 / 2 : ℝ) * s / n) := hprodSq
      _ ≤ ((3 / 2 : ℝ) * L * G / n) ^ 2 := hscaled
  have hrhs : 0 ≤ (3 / 2 : ℝ) * L * G / n := by positivity
  change x * y ≤ (3 / 2 : ℝ) * L * G / n
  exact (sq_le_sq₀ (mul_nonneg hx hy) hrhs).mp hsquare

/-- Four-factor Holder with the Gram product retained. -/
theorem integral_norm_centeredPair_mul_pair_mul_mixedPair_le_gramProduct_h13
    {N : ℕ} (hN : 1 ≤ N)
    (A B R S : ConcreteMatrixState N)
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hR : R.IsSymm) (hS : S.IsSymm)
    (L G : ℝ) (hL : 0 ≤ L) (hG : 0 ≤ G)
    (hgram :
      (Matrix.trace (R * R.conjTranspose)).re *
          (Matrix.trace (S * S.conjTranspose)).re ≤ L ^ 2 * G ^ 2) :
    (∫ v : ComplexUnitSphere N,
      ‖complexCenteredProjectiveTracePair v A *
        complexProjectiveTracePair v B *
        complexProjectiveMixedTransposePair v R S.conjTranspose‖
        ∂(complexUnitSphereProbabilityMeasure N)) ≤
      9 * (Matrix.trace A).re * (Matrix.trace B).re *
        L * G / (N : ℝ) ^ 3 := by
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
  have H := integral_norm_mul_four_complex_le_h13 h1 h2 h3 h4
  have H' :
      (∫ v : ComplexUnitSphere N,
        ‖complexCenteredProjectiveTracePair v A *
          complexProjectiveTracePair v B *
          complexProjectiveMixedTransposePair v R S.conjTranspose‖ ∂μ) ≤
        lpNorm f1 4 μ * lpNorm f2 4 μ *
          lpNorm f3 4 μ * lpNorm f4 4 μ := by
    convert H using 1
    congr 1
    funext v
    rw [complexProjectiveMixedTransposePair_eq_bilinearFactors_h13]
    dsimp only [f1, f2, f3, f4]
    congr 1
    ring
  have h1n :=
    lpNorm_posSemidef_centeredProjectiveTracePair_complex_four_le_sharp_h13
      hN A hA
  have h2n :=
    lpNorm_posSemidef_projectiveTracePair_complex_four_le_h13 hN B hB
  have h34 := lpNorm_bilinearFactors_mul_le_of_gramProduct_h13
    hN R S hR hS L G hL hG hgram
  have htA : 0 ≤ (Matrix.trace A).re :=
    (Complex.nonneg_iff.mp hA.trace_nonneg).1
  have htB : 0 ≤ (Matrix.trace B).re :=
    (Complex.nonneg_iff.mp hB.trace_nonneg).1
  have hn : 0 < (N : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  calc
    _ ≤ lpNorm f1 4 μ * lpNorm f2 4 μ *
        lpNorm f3 4 μ * lpNorm f4 4 μ := H'
    _ = (lpNorm f1 4 μ * lpNorm f2 4 μ) *
        (lpNorm f3 4 μ * lpNorm f4 4 μ) := by ring
    _ ≤ ((2 * (Matrix.trace A).re / (N : ℝ)) *
          (3 * (Matrix.trace B).re / (N : ℝ))) *
        ((3 / 2 : ℝ) * L * G / (N : ℝ)) := by
      have h12 : lpNorm f1 4 μ * lpNorm f2 4 μ ≤
            (2 * (Matrix.trace A).re / (N : ℝ)) *
            (3 * (Matrix.trace B).re / (N : ℝ)) := by
        dsimp only [f1, f2, μ] at h1n h2n ⊢
        exact mul_le_mul h1n h2n lpNorm_nonneg (by positivity)
      exact mul_le_mul h12 (by simpa only [f3, f4, μ] using h34)
        (mul_nonneg lpNorm_nonneg lpNorm_nonneg) (by positivity)
    _ = 9 * (Matrix.trace A).re * (Matrix.trace B).re *
        L * G / (N : ℝ) ^ 3 := by field_simp [ne_of_gt hn]; ring

/-- Three-factor Holder with the same Gram-product comparison. -/
theorem integral_norm_centeredPair_mul_mixedPair_le_gramProduct_h13
    {N : ℕ} (hN : 1 ≤ N)
    (A R S : ConcreteMatrixState N)
    (hA : A.PosSemidef) (hR : R.IsSymm) (hS : S.IsSymm)
    (L G : ℝ) (hL : 0 ≤ L) (hG : 0 ≤ G)
    (hgram :
      (Matrix.trace (R * R.conjTranspose)).re *
          (Matrix.trace (S * S.conjTranspose)).re ≤ L ^ 2 * G ^ 2) :
    (∫ v : ComplexUnitSphere N,
      ‖complexCenteredProjectiveTracePair v A *
        complexProjectiveMixedTransposePair v R S.conjTranspose‖
        ∂(complexUnitSphereProbabilityMeasure N)) ≤
      3 * (Matrix.trace A).re * L * G / (N : ℝ) ^ 2 := by
  let μ := complexUnitSphereProbabilityMeasure N
  let f1 : ComplexUnitSphere N → ℂ := fun v =>
    complexCenteredProjectiveTracePair v A
  let f2 : ComplexUnitSphere N → ℂ := fun v =>
    complexProjectiveConjugateBilinearPair v R
  let f3 : ComplexUnitSphere N → ℂ := fun v =>
    complexProjectiveTransposeBilinearPair v S.conjTranspose
  let f4 : ComplexUnitSphere N → ℂ := fun _ => 1
  letI : IsProbabilityMeasure μ :=
    complexUnitSphereProbabilityMeasure_isProbability hN
  have h1 : MemLp f1 4 μ := by
    simpa only [f1, μ] using
      memLp_posSemidef_centeredProjectiveTracePair_complex_four_h13 hN A hA
  have h2 : MemLp f2 4 μ := by
    simpa only [f2, μ] using
      memLp_complexProjectiveConjugateBilinearPair_four_h13 hN R
  have h3 : MemLp f3 4 μ := by
    simpa only [f3, μ] using
      memLp_complexProjectiveTransposeBilinearPair_conjTranspose_four_h13 hN S
  have h4 : MemLp f4 4 μ := memLp_const _
  have H := integral_norm_mul_four_complex_le_h13 h1 h2 h3 h4
  have hone : lpNorm f4 4 μ = 1 := by
    dsimp only [f4]
    rw [lpNorm_const (p := (4 : ENNReal)) (by norm_num)
      (IsProbabilityMeasure.ne_zero μ) (1 : ℂ)]
    norm_num
  have H' :
      (∫ v : ComplexUnitSphere N,
        ‖complexCenteredProjectiveTracePair v A *
          complexProjectiveMixedTransposePair v R S.conjTranspose‖ ∂μ) ≤
        lpNorm f1 4 μ * lpNorm f2 4 μ * lpNorm f3 4 μ := by
    have H0 := H
    rw [hone, mul_one] at H0
    convert H0 using 1
    congr 1
    funext v
    rw [complexProjectiveMixedTransposePair_eq_bilinearFactors_h13]
    dsimp only [f1, f2, f3, f4]
    congr 1
    ring
  have h1n :=
    lpNorm_posSemidef_centeredProjectiveTracePair_complex_four_le_sharp_h13
      hN A hA
  have h23 := lpNorm_bilinearFactors_mul_le_of_gramProduct_h13
    hN R S hR hS L G hL hG hgram
  have hn : 0 < (N : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have htA : 0 ≤ (Matrix.trace A).re :=
    (Complex.nonneg_iff.mp hA.trace_nonneg).1
  calc
    _ ≤ lpNorm f1 4 μ * lpNorm f2 4 μ * lpNorm f3 4 μ := H'
    _ = lpNorm f1 4 μ * (lpNorm f2 4 μ * lpNorm f3 4 μ) := by ring
    _ ≤ (2 * (Matrix.trace A).re / (N : ℝ)) *
        ((3 / 2 : ℝ) * L * G / (N : ℝ)) := by
      exact mul_le_mul (by simpa only [f1, μ] using h1n)
        (by simpa only [f2, f3, μ] using h23)
        (mul_nonneg lpNorm_nonneg lpNorm_nonneg) (by positivity)
    _ = 3 * (Matrix.trace A).re * L * G / (N : ℝ) ^ 2 := by
      field_simp [ne_of_gt hn]

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
