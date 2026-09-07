import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H13_MixedSupportProjectiveNormalForm
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H13_BilinearSupportGramComparison
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H13_PureProjectiveHolderContraction
import Mathlib.Tactic

/-!
# Fixed-sphere Holder contraction for the H13 mixed word

This file consumes the exact support normal form and the Gram-product Holder
bounds.  Its coefficient ledger is

`9 n t (n+2t)(t+u) + 6 n t (1+2t)(t+u)
 + 11 t(t+u)(n+2t) + 17 t(t+3u+2v)`.

The scalar certificate in `H13_MixedSupportProjectiveNormalForm` puts this
inside `128` times the common trace-one/trace-two radial basis.
-/

open MeasureTheory
open scoped ComplexOrder MatrixOrder

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

set_option maxHeartbeats 4800000
set_option linter.style.haveILetI false

private theorem norm_add_eight_le_h13_mixed
    (x0 x1 x2 x3 x4 x5 x6 x7 : ℂ) :
    ‖x0 + x1 + x2 + x3 + x4 + x5 + x6 + x7‖ ≤
      ‖x0‖ + ‖x1‖ + ‖x2‖ + ‖x3‖ + ‖x4‖ + ‖x5‖ + ‖x6‖ + ‖x7‖ := by
  calc
    _ ≤ ‖x0 + x1 + x2 + x3 + x4 + x5 + x6‖ + ‖x7‖ := norm_add_le _ _
    _ ≤ (‖x0 + x1 + x2 + x3 + x4 + x5‖ + ‖x6‖) + ‖x7‖ := by
      gcongr; exact norm_add_le _ _
    _ ≤ ((‖x0 + x1 + x2 + x3 + x4‖ + ‖x5‖) + ‖x6‖) + ‖x7‖ := by
      gcongr; exact norm_add_le _ _
    _ ≤ (((‖x0 + x1 + x2 + x3‖ + ‖x4‖) + ‖x5‖) + ‖x6‖) + ‖x7‖ := by
      gcongr; exact norm_add_le _ _
    _ ≤ ((((‖x0 + x1 + x2‖ + ‖x3‖) + ‖x4‖) + ‖x5‖) + ‖x6‖) + ‖x7‖ := by
      gcongr; exact norm_add_le _ _
    _ ≤ (((((‖x0 + x1‖ + ‖x2‖) + ‖x3‖) + ‖x4‖) + ‖x5‖) + ‖x6‖) + ‖x7‖ := by
      gcongr; exact norm_add_le _ _
    _ ≤ ((((((‖x0‖ + ‖x1‖) + ‖x2‖) + ‖x3‖) + ‖x4‖) + ‖x5‖) + ‖x6‖) + ‖x7‖ := by
      gcongr; exact norm_add_le _ _
    _ = _ := by ring

/-- The exact scalar polynomial produced by the mixed-word Holder ledger. -/
def h13MixedHolderRadialPolynomial
    (N : ℕ) (C : ConcreteMatrixState N) : ℝ :=
  let n : ℝ := N
  let Z := h13LedgerZ C
  let t := (Matrix.trace Z).re
  let u := (Matrix.trace (Z ^ 2)).re
  let v := (Matrix.trace (Z ^ 3)).re
  (9 * n * t * (n + 2 * t) * (t + u) +
    6 * n * t * (1 + 2 * t) * (t + u) +
    11 * t * (t + u) * (n + 2 * t) +
    17 * t * (t + 3 * u + 2 * v)) / n ^ 4

/-- Actual integrated mixed-word contraction, before the final scalar
collection into the common trace-one/trace-two envelope. -/
theorem centeredPair_mul_h13Mixed_support_package_raw
    {N : ℕ} (hN : 1 ≤ N) (C : ConcreteMatrixState N) (hC : C.IsSymm)
    (hsupport : coeCornerSupport C) :
    let Z := h13LedgerZ C
    Integrable (fun x : ComplexUnitSphere N ↦
        complexCenteredProjectiveTracePair x Z *
          h13CenteredTripleMixedTransposeExpansion x
            (h13LedgerT C) (h13LedgerT C).conjTranspose (1 + 2 • Z))
        (complexUnitSphereProbabilityMeasure N) ∧
      (∫ x : ComplexUnitSphere N,
        ‖complexCenteredProjectiveTracePair x Z *
          h13CenteredTripleMixedTransposeExpansion x
            (h13LedgerT C) (h13LedgerT C).conjTranspose (1 + 2 • Z)‖
          ∂(complexUnitSphereProbabilityMeasure N)) ≤
        h13MixedHolderRadialPolynomial N C := by
  let μ := complexUnitSphereProbabilityMeasure N
  let n : ℝ := N
  let Z := h13LedgerZ C
  let T := h13LedgerT C
  let A : ConcreteMatrixState N := 1 + 2 • Z
  let B : ConcreteMatrixState N := T * T.conjTranspose
  let R : ConcreteMatrixState N := A * T
  let P : ConcreteMatrixState N := A * B
  let G : ConcreteMatrixState N := T.conjTranspose * A * T
  let t : ℝ := (Matrix.trace Z).re
  let u : ℝ := (Matrix.trace (Z ^ 2)).re
  let v3 : ℝ := (Matrix.trace (Z ^ 3)).re
  let ar : ℝ := n⁻¹
  let a : ℂ := (ar : ℂ)
  let q : ComplexUnitSphere N → ℂ := fun x ↦
    complexCenteredProjectiveTracePair x Z
  let p : ComplexUnitSphere N → ConcreteMatrixState N → ℂ := fun x X ↦
    complexProjectiveTracePair x X
  let m : ComplexUnitSphere N → ConcreteMatrixState N →
      ConcreteMatrixState N → ℂ := fun x X Y ↦
    complexProjectiveMixedTransposePair x X Y
  let f0 : ComplexUnitSphere N → ℂ := fun x ↦ q x * p x A * m x T T.conjTranspose
  let f1 : ComplexUnitSphere N → ℂ := fun x ↦ q x * m x R T.conjTranspose
  let f2 : ComplexUnitSphere N → ℂ := fun x ↦ q x * p x B * p x A
  let f3 : ComplexUnitSphere N → ℂ := fun x ↦ q x * m x T R.conjTranspose
  let f4 : ComplexUnitSphere N → ℂ := fun x ↦ q x * p x P
  let f5 : ComplexUnitSphere N → ℂ := fun x ↦ q x * p x G.transpose
  let f6 : ComplexUnitSphere N → ℂ := fun x ↦ q x * p x P
  let f7 : ComplexUnitSphere N → ℂ := q
  letI : IsProbabilityMeasure μ :=
    complexUnitSphereProbabilityMeasure_isProbability hN
  have hn : 0 < n := by
    dsimp only [n]
    exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hn1 : 1 ≤ n := by
    dsimp only [n]
    exact_mod_cast hN
  have har : 0 ≤ ar := by dsimp only [ar]; positivity
  have hZ : Z.PosSemidef := by
    simpa only [Z] using h13LedgerZ_posSemidef C hsupport
  have hA : A.PosSemidef := by
    simpa only [A, Z] using h13LedgerOneAddTwoZ_posSemidef C hsupport
  have hB : B.PosSemidef := by
    simpa only [B, T] using h13LedgerTGram_posSemidef C
  have hP : P.PosSemidef := by
    simpa only [P, A, B, Z, T] using
      h13LedgerOneAddTwoZ_mul_TGram_posSemidef C hsupport
  have hG : G.PosSemidef := by
    simpa only [G, A, T, Z] using
      h13LedgerTStar_mul_oneAddTwoZ_mul_T_posSemidef C hsupport
  have hGt : G.transpose.PosSemidef := hG.transpose
  have hT : T.IsSymm := by
    simpa only [T] using h13LedgerT_isSymm C hC hsupport
  have hR : R.IsSymm := by
    simpa only [R, A, T, Z] using
      h13LedgerOneAddTwoZ_mul_T_isSymm C hC hsupport
  have ht : 0 ≤ t := (Complex.nonneg_iff.mp hZ.trace_nonneg).1
  have hu : 0 ≤ u := by
    exact (Complex.nonneg_iff.mp (hZ.pow 2).trace_nonneg).1
  have hv3 : 0 ≤ v3 := by
    exact (Complex.nonneg_iff.mp (hZ.pow 3).trace_nonneg).1
  have htlow : t ^ 2 ≤ n * u := by
    simpa only [t, u, n, pow_two] using
      posSemidef_trace_re_sq_le_card_mul_trace_square_re_h13_pure Z hZ
  have hv3le : v3 ≤ t * u := by
    simpa only [v3, t, u] using
      posSemidef_trace_cube_re_le_trace_re_mul_trace_square_re_h13 Z hZ
  have htrA : (Matrix.trace A).re = n + 2 * t := by
    dsimp only [A, n, t]
    simp only [two_nsmul, Matrix.trace_add, Matrix.trace_one,
      Fintype.card_fin, Complex.add_re, Complex.natCast_re]
    ring
  have htrB : (Matrix.trace B).re = t + u := by
    simpa only [B, T, Z, t, u] using
      trace_h13LedgerT_gram_re_eq C hsupport
  have htrP : (Matrix.trace P).re = t + 3 * u + 2 * v3 := by
    rw [show P = Z + 3 • Z ^ 2 + 2 • Z ^ 3 by
      simpa only [P, A, B, Z, T] using
        h13LedgerOneAddTwoZ_mul_TGram_eq_positivePolynomial C hsupport]
    dsimp only [t, u, v3]
    simp only [two_nsmul, three_nsmul, Matrix.trace_add, Complex.add_re]
    ring
  have htrGt : (Matrix.trace G.transpose).re = t + 3 * u + 2 * v3 := by
    rw [Matrix.trace_transpose]
    rw [show Matrix.trace G = Matrix.trace P by
      simpa only [G, P, A, B, T, Z] using
        trace_h13LedgerTStar_mul_oneAddTwoZ_mul_T_eq_outputProduct C]
    exact htrP
  have hnorma : ‖a‖ = ar := by
    dsimp only [a]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg har]
  have htrPnonneg := Complex.nonneg_iff.mp hP.trace_nonneg
  have hnormtrP : ‖Matrix.trace P‖ = (Matrix.trace P).re := by
    rw [Complex.norm_def, Complex.normSq_apply, ← htrPnonneg.2]
    simp only [zero_mul, add_zero]
    exact Real.sqrt_mul_self htrPnonneg.1
  have hq4 : MemLp q 4 μ := by
    simpa only [q, μ] using
      memLp_posSemidef_centeredProjectiveTracePair_complex_four_h13 hN Z hZ
  have hpA4 : MemLp (fun x ↦ p x A) 4 μ := by
    simpa only [p, μ] using
      memLp_posSemidef_projectiveTracePair_complex_four_h13 hN A hA
  have hpB4 : MemLp (fun x ↦ p x B) 4 μ := by
    simpa only [p, μ] using
      memLp_posSemidef_projectiveTracePair_complex_four_h13 hN B hB
  have hpP4 : MemLp (fun x ↦ p x P) 4 μ := by
    simpa only [p, μ] using
      memLp_posSemidef_projectiveTracePair_complex_four_h13 hN P hP
  have hpGt4 : MemLp (fun x ↦ p x G.transpose) 4 μ := by
    simpa only [p, μ] using
      memLp_posSemidef_projectiveTracePair_complex_four_h13 hN G.transpose hGt
  have hbT4 := memLp_complexProjectiveConjugateBilinearPair_four_h13 hN T
  have hbtT4 :=
    memLp_complexProjectiveTransposeBilinearPair_conjTranspose_four_h13 hN T
  have hbR4 := memLp_complexProjectiveConjugateBilinearPair_four_h13 hN R
  have hbtR4 :=
    memLp_complexProjectiveTransposeBilinearPair_conjTranspose_four_h13 hN R
  have hone4 : MemLp (fun _ : ComplexUnitSphere N ↦ (1 : ℂ)) 4 μ := memLp_const _
  have hf0 : MemLp f0 1 μ := by
    rw [show f0 = fun x ↦ q x * p x A *
        complexProjectiveConjugateBilinearPair x T *
        complexProjectiveTransposeBilinearPair x T.conjTranspose by
      funext x
      dsimp only [f0, m]
      rw [complexProjectiveMixedTransposePair_eq_bilinearFactors_h13]
      ring]
    exact memLp_mul_four_complex_h13 hq4 hpA4 hbT4 hbtT4
  have hf1 : MemLp f1 1 μ := by
    rw [show f1 = fun x ↦ q x *
        complexProjectiveConjugateBilinearPair x R *
        complexProjectiveTransposeBilinearPair x T.conjTranspose * 1 by
      funext x
      dsimp only [f1, m]
      rw [complexProjectiveMixedTransposePair_eq_bilinearFactors_h13]
      ring]
    exact memLp_mul_four_complex_h13 hq4 hbR4 hbtT4 hone4
  have hf2 : MemLp f2 1 μ := by
    simpa only [f2, mul_one] using
      memLp_mul_four_complex_h13 hq4 hpB4 hpA4 hone4
  have hf3 : MemLp f3 1 μ := by
    rw [show f3 = fun x ↦ q x *
        complexProjectiveConjugateBilinearPair x T *
        complexProjectiveTransposeBilinearPair x R.conjTranspose * 1 by
      funext x
      dsimp only [f3, m]
      rw [complexProjectiveMixedTransposePair_eq_bilinearFactors_h13]
      ring]
    exact memLp_mul_four_complex_h13 hq4 hbT4 hbtR4 hone4
  have hf4 : MemLp f4 1 μ := by
    simpa only [f4, mul_one] using
      memLp_mul_four_complex_h13 hq4 hpP4 hone4 hone4
  have hf5 : MemLp f5 1 μ := by
    simpa only [f5, mul_one] using
      memLp_mul_four_complex_h13 hq4 hpGt4 hone4 hone4
  have hf6 : MemLp f6 1 μ := by simpa only [f6] using hf4
  have hf7 : MemLp f7 1 μ := by
    simpa only [f7, mul_one] using
      memLp_mul_four_complex_h13 hq4 hone4 hone4 hone4
  have hkernel (x : ComplexUnitSphere N) :
      q x * h13CenteredTripleMixedTransposeExpansion x
          T T.conjTranspose A =
        f0 x + (-a) * f1 x + (-a) * f2 x + (-a) * f3 x +
          a ^ 2 * f4 x + a ^ 2 * f5 x + a ^ 2 * f6 x +
          (-(a ^ 3 * Matrix.trace P)) * f7 x := by
    rw [h13CenteredTripleMixedTransposeExpansion_support_normalForm x C hsupport]
    unfold h13MixedSupportProjectiveNormalForm
    dsimp only [f0, f1, f2, f3, f4, f5, f6, f7, q, p, m,
      Z, T, A, B, R, P, G, a, ar, n]
    ring
  have hsumMem : MemLp (fun x ↦
      f0 x + (-a) * f1 x + (-a) * f2 x + (-a) * f3 x +
        a ^ 2 * f4 x + a ^ 2 * f5 x + a ^ 2 * f6 x +
        (-(a ^ 3 * Matrix.trace P)) * f7 x) 1 μ :=
    (((((((hf0.add (hf1.const_smul (-a))).add
      (hf2.const_smul (-a))).add (hf3.const_smul (-a))).add
      (hf4.const_smul (a ^ 2))).add (hf5.const_smul (a ^ 2))).add
      (hf6.const_smul (a ^ 2))).add
      (hf7.const_smul (-(a ^ 3 * Matrix.trace P))))
  have hkernelMem : MemLp (fun x ↦ q x *
      h13CenteredTripleMixedTransposeExpansion x T T.conjTranspose A) 1 μ := by
    apply hsumMem.ae_eq
    filter_upwards [] with x
    exact (hkernel x).symm
  have hi0 := (memLp_one_iff_integrable.mp hf0).norm
  have hi1 := (memLp_one_iff_integrable.mp hf1).norm
  have hi2 := (memLp_one_iff_integrable.mp hf2).norm
  have hi3 := (memLp_one_iff_integrable.mp hf3).norm
  have hi4 := (memLp_one_iff_integrable.mp hf4).norm
  have hi5 := (memLp_one_iff_integrable.mp hf5).norm
  have hi6 := (memLp_one_iff_integrable.mp hf6).norm
  have hi7 := (memLp_one_iff_integrable.mp hf7).norm
  let c7 : ℝ := ar ^ 3 * (Matrix.trace P).re
  have hc7 : 0 ≤ c7 := by
    dsimp only [c7]
    exact mul_nonneg (pow_nonneg har 3) htrPnonneg.1
  let RR : ComplexUnitSphere N → ℝ := fun x ↦
    ‖f0 x‖ + ar * ‖f1 x‖ + ar * ‖f2 x‖ + ar * ‖f3 x‖ +
      ar ^ 2 * ‖f4 x‖ + ar ^ 2 * ‖f5 x‖ + ar ^ 2 * ‖f6 x‖ +
      c7 * ‖f7 x‖
  have hRRint : Integrable RR μ := by
    dsimp only [RR]
    exact (((((((hi0.add (hi1.const_mul ar)).add
      (hi2.const_mul ar)).add (hi3.const_mul ar)).add
      (hi4.const_mul (ar ^ 2))).add (hi5.const_mul (ar ^ 2))).add
      (hi6.const_mul (ar ^ 2))).add (hi7.const_mul c7))
  have hpoint (x : ComplexUnitSphere N) :
      ‖q x * h13CenteredTripleMixedTransposeExpansion x T T.conjTranspose A‖ ≤
        RR x := by
    rw [hkernel x]
    have H := norm_add_eight_le_h13_mixed
      (f0 x) ((-a) * f1 x) ((-a) * f2 x) ((-a) * f3 x)
      (a ^ 2 * f4 x) (a ^ 2 * f5 x) (a ^ 2 * f6 x)
      ((-(a ^ 3 * Matrix.trace P)) * f7 x)
    dsimp only [RR, c7]
    simpa only [norm_mul, norm_neg, hnorma, norm_pow, hnormtrP] using H
  have hleftInt : Integrable (fun x ↦
      ‖q x * h13CenteredTripleMixedTransposeExpansion x T T.conjTranspose A‖) μ :=
    (memLp_one_iff_integrable.mp hkernelMem).norm
  have hmono : (∫ x, ‖q x *
      h13CenteredTripleMixedTransposeExpansion x T T.conjTranspose A‖ ∂μ) ≤
      ∫ x, RR x ∂μ := integral_mono hleftInt hRRint hpoint
  have hRRvalue : (∫ x, RR x ∂μ) =
      (∫ x, ‖f0 x‖ ∂μ) + ar * (∫ x, ‖f1 x‖ ∂μ) +
        ar * (∫ x, ‖f2 x‖ ∂μ) + ar * (∫ x, ‖f3 x‖ ∂μ) +
        ar ^ 2 * (∫ x, ‖f4 x‖ ∂μ) + ar ^ 2 * (∫ x, ‖f5 x‖ ∂μ) +
        ar ^ 2 * (∫ x, ‖f6 x‖ ∂μ) + c7 * (∫ x, ‖f7 x‖ ∂μ) := by
    rw [show RR =
      (((((((fun y ↦ ‖f0 y‖) + (fun y ↦ ar * ‖f1 y‖)) +
        (fun y ↦ ar * ‖f2 y‖)) + (fun y ↦ ar * ‖f3 y‖)) +
        (fun y ↦ ar ^ 2 * ‖f4 y‖)) + (fun y ↦ ar ^ 2 * ‖f5 y‖)) +
        (fun y ↦ ar ^ 2 * ‖f6 y‖)) + (fun y ↦ c7 * ‖f7 y‖) by rfl]
    rw [integral_add'
      ((((((hi0.add (hi1.const_mul ar)).add (hi2.const_mul ar)).add
        (hi3.const_mul ar)).add (hi4.const_mul (ar ^ 2))).add
        (hi5.const_mul (ar ^ 2))).add (hi6.const_mul (ar ^ 2)))
      (hi7.const_mul c7)]
    rw [integral_add'
      (((((hi0.add (hi1.const_mul ar)).add (hi2.const_mul ar)).add
        (hi3.const_mul ar)).add (hi4.const_mul (ar ^ 2))).add
        (hi5.const_mul (ar ^ 2))) (hi6.const_mul (ar ^ 2))]
    rw [integral_add'
      ((((hi0.add (hi1.const_mul ar)).add (hi2.const_mul ar)).add
        (hi3.const_mul ar)).add (hi4.const_mul (ar ^ 2)))
      (hi5.const_mul (ar ^ 2))]
    rw [integral_add'
      (((hi0.add (hi1.const_mul ar)).add (hi2.const_mul ar)).add
        (hi3.const_mul ar)) (hi4.const_mul (ar ^ 2))]
    rw [integral_add' ((hi0.add (hi1.const_mul ar)).add
      (hi2.const_mul ar)) (hi3.const_mul ar)]
    rw [integral_add' (hi0.add (hi1.const_mul ar)) (hi2.const_mul ar)]
    rw [integral_add' hi0 (hi1.const_mul ar)]
    simp only [integral_const_mul]
  have hG0 : 0 ≤ t + u := add_nonneg ht hu
  have hL : 0 ≤ 1 + 2 * t := by positivity
  have hgramT :
      (Matrix.trace (T * T.conjTranspose)).re = t + u := htrB
  have hgram0 :
      (Matrix.trace (T * T.conjTranspose)).re *
          (Matrix.trace (T * T.conjTranspose)).re ≤
        (1 : ℝ) ^ 2 * (t + u) ^ 2 := by
    rw [hgramT]
    ring_nf
    exact le_rfl
  have hgramRT :
      (Matrix.trace (R * R.conjTranspose)).re *
          (Matrix.trace (T * T.conjTranspose)).re ≤
        (1 + 2 * t) ^ 2 * (t + u) ^ 2 := by
    have H := trace_h13LedgerOneAddTwoZMulT_gram_re_le_factor_mul_T_gram_h13
      C hsupport
    change (Matrix.trace (R * R.conjTranspose)).re ≤
      (1 + 2 * t) ^ 2 * (Matrix.trace (T * T.conjTranspose)).re at H
    rw [hgramT] at H ⊢
    nlinarith [hG0, sq_nonneg (1 + 2 * t)]
  have H0 := integral_norm_centeredPair_mul_pair_mul_mixedPair_le_gramProduct_h13
    hN Z A T T hZ hA hT hT 1 (t + u) (by norm_num) hG0 hgram0
  have H1 := integral_norm_centeredPair_mul_mixedPair_le_gramProduct_h13
    hN Z R T hZ hR hT (1 + 2 * t) (t + u) hL hG0 hgramRT
  have H2 := integral_norm_centeredPair_mul_two_posPairs_le_h13_pure
    hN Z B A hZ hB hA
  have H3 := integral_norm_centeredPair_mul_mixedPair_le_gramProduct_h13
    hN Z T R hZ hT hR (1 + 2 * t) (t + u) hL hG0 (by
      simpa only [mul_comm] using hgramRT)
  have H4 := integral_norm_centeredPair_mul_posPair_le_h13_pure hN Z P hZ hP
  have H5 := integral_norm_centeredPair_mul_posPair_le_h13_pure
    hN Z G.transpose hZ hGt
  have H6 := integral_norm_centeredPair_mul_posPair_le_h13_pure hN Z P hZ hP
  have H7 := integral_norm_centeredPair_le_h13_pure hN Z hZ
  change (∫ x, ‖f0 x‖ ∂μ) ≤ _ at H0
  change (∫ x, ‖f1 x‖ ∂μ) ≤ _ at H1
  change (∫ x, ‖f2 x‖ ∂μ) ≤ _ at H2
  change (∫ x, ‖f3 x‖ ∂μ) ≤ _ at H3
  change (∫ x, ‖f4 x‖ ∂μ) ≤ _ at H4
  change (∫ x, ‖f5 x‖ ∂μ) ≤ _ at H5
  change (∫ x, ‖f6 x‖ ∂μ) ≤ _ at H6
  change (∫ x, ‖f7 x‖ ∂μ) ≤ _ at H7
  rw [htrA] at H0 H2
  rw [htrB] at H2
  rw [htrP] at H4 H6
  rw [htrGt] at H5
  have hRRbound : (∫ x, RR x ∂μ) ≤
      (9 * n * t * (n + 2 * t) * (t + u) +
        6 * n * t * (1 + 2 * t) * (t + u) +
        11 * t * (t + u) * (n + 2 * t) +
        17 * t * (t + 3 * u + 2 * v3)) / n ^ 4 := by
    rw [hRRvalue]
    dsimp only [ar, c7]
    rw [htrP]
    field_simp [ne_of_gt hn] at H0 H1 H2 H3 H4 H5 H6 H7 ⊢
    nlinarith
  constructor
  · simpa only [Z, T, A, q, μ] using memLp_one_iff_integrable.mp hkernelMem
  · calc
      _ ≤ ∫ x, RR x ∂μ := by simpa only [Z, T, A, q, μ] using hmono
      _ ≤ _ := hRRbound
      _ = _ := by rfl

/-- The single mixed word consumes at most one half-envelope coefficient
`128`.  This compatibility wrapper preserves the original fixed-matrix
interface while exposing the exact Holder polynomial above. -/
theorem centeredPair_mul_h13Mixed_support_package
    {N : ℕ} (hN : 1 ≤ N) (C : ConcreteMatrixState N) (hC : C.IsSymm)
    (hsupport : coeCornerSupport C) :
    let Z := h13LedgerZ C
    let t := (Matrix.trace Z).re
    let u := (Matrix.trace (Z ^ 2)).re
    Integrable (fun x : ComplexUnitSphere N ↦
        complexCenteredProjectiveTracePair x Z *
          h13CenteredTripleMixedTransposeExpansion x
            (h13LedgerT C) (h13LedgerT C).conjTranspose (1 + 2 • Z))
        (complexUnitSphereProbabilityMeasure N) ∧
      (∫ x : ComplexUnitSphere N,
        ‖complexCenteredProjectiveTracePair x Z *
          h13CenteredTripleMixedTransposeExpansion x
            (h13LedgerT C) (h13LedgerT C).conjTranspose (1 + 2 • Z)‖
          ∂(complexUnitSphereProbabilityMeasure N)) ≤
        128 * ((t ^ 2 + u) / (N : ℝ) ^ 2 +
          t ^ 4 / (N : ℝ) ^ 4 + u ^ 2 / (N : ℝ) ^ 2) := by
  let n : ℝ := N
  let Z := h13LedgerZ C
  let t : ℝ := (Matrix.trace Z).re
  let u : ℝ := (Matrix.trace (Z ^ 2)).re
  let v3 : ℝ := (Matrix.trace (Z ^ 3)).re
  have hn : 0 < n := by
    dsimp only [n]
    exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hn1 : 1 ≤ n := by
    dsimp only [n]
    exact_mod_cast hN
  have hZ : Z.PosSemidef := by
    simpa only [Z] using h13LedgerZ_posSemidef C hsupport
  have ht : 0 ≤ t := (Complex.nonneg_iff.mp hZ.trace_nonneg).1
  have hu : 0 ≤ u :=
    (Complex.nonneg_iff.mp (hZ.pow 2).trace_nonneg).1
  have htlow : t ^ 2 ≤ n * u := by
    simpa only [t, u, n, pow_two] using
      posSemidef_trace_re_sq_le_card_mul_trace_square_re_h13_pure Z hZ
  have hv3le : v3 ≤ t * u := by
    simpa only [v3, t, u] using
      posSemidef_trace_cube_re_le_trace_re_mul_trace_square_re_h13 Z hZ
  have hraw := centeredPair_mul_h13Mixed_support_package_raw
    hN C hC hsupport
  dsimp only at hraw
  have hpoly := h13MixedHolderPolynomial_le_halfEnvelope
    n t u v3 hn1 ht hu htlow hv3le
  have hpolyDiv : h13MixedHolderRadialPolynomial N C ≤
      128 * ((t ^ 2 + u) / n ^ 2 + t ^ 4 / n ^ 4 + u ^ 2 / n ^ 2) := by
    unfold h13MixedHolderRadialPolynomial
    dsimp only [n, Z, t, u, v3]
    have hn4 : 0 < n ^ 4 := pow_pos hn 4
    apply (div_le_iff₀ hn4).2
    field_simp [ne_of_gt hn]
    nlinarith
  constructor
  · simpa only [Z] using hraw.1
  · calc
      _ ≤ h13MixedHolderRadialPolynomial N C := by
        simpa only [Z] using hraw.2
      _ ≤ _ := by simpa only [n, t, u] using hpolyDiv

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
