import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.InverseWishartThirdEntryStein
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.H9CenteredTraceSteinContractionProof
import Mathlib.Tactic

/-!
# H9 third trace-power Stein closure

This module contracts the internally proved third-entry inverse-Wishart
recursion, normalizes it, and transports it to the project's standard-real
Gaussian denominator.  It constructs the exact recurrence isolated by
`H9ThirdTracePowerSteinRecurrence` and hence the H9 centered-trace Stein
contraction without a new scientific assumption.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08

noncomputable section

open LogdetLean.GramHafnian
open LogdetLean.GramHafnian.Wishart
open LogdetLean.GramHafnian.UltimateHiding.DenseScore

set_option maxHeartbeats 3600000

private theorem trace_sq_eq_diagonalPairSum_third
    {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) :
    Matrix.trace A ^ 2 =
      ∑ a : Fin p, ∑ b : Fin p, A a a * A b b := by
  simp only [Matrix.trace, Matrix.diag_apply, pow_two, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]

private theorem trace_cube_eq_diagonalTripleSum_third
    {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) :
    Matrix.trace A ^ 3 =
      ∑ a : Fin p, ∑ b : Fin p, ∑ d : Fin p,
        A a a * A b b * A d d := by
  rw [show Matrix.trace A ^ 3 = Matrix.trace A ^ 2 * Matrix.trace A by ring,
    trace_sq_eq_diagonalPairSum_third, Finset.sum_mul]
  simp only [Matrix.trace, Matrix.diag_apply]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.mul_sum]

private theorem trace_matrix_sq_eq_entryPairSum_third
    {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) :
    Matrix.trace (A ^ 2) =
      ∑ b : Fin p, ∑ d : Fin p, A b d * A d b := by
  simp [Matrix.trace, Matrix.mul_apply, pow_two]

private theorem trace_mul_trace_matrix_sq_eq_entryTripleSum_third
    {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) :
    Matrix.trace A * Matrix.trace (A ^ 2) =
      ∑ a : Fin p, ∑ b : Fin p, ∑ d : Fin p,
        A a a * (A b d * A d b) := by
  rw [trace_matrix_sq_eq_entryPairSum_third]
  simp only [Matrix.trace, Matrix.diag_apply]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.mul_sum]

private theorem integral_fintype_sum_two_third
    {X : Type*} [MeasurableSpace X] {p : ℕ} (μ : Measure X)
    (f : Fin p → Fin p → X → ℝ)
    (hf : ∀ a b, Integrable (f a b) μ) :
    (∫ x, ∑ a : Fin p, ∑ b : Fin p, f a b x ∂μ) =
      ∑ a : Fin p, ∑ b : Fin p, ∫ x, f a b x ∂μ := by
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro a ha
    rw [integral_finsetSum]
    intro b hb
    exact hf a b
  · intro a ha
    exact integrable_finsetSum Finset.univ fun b hb ↦ hf a b

private theorem integral_fintype_sum_three_third
    {X : Type*} [MeasurableSpace X] {p : ℕ} (μ : Measure X)
    (f : Fin p → Fin p → Fin p → X → ℝ)
    (hf : ∀ a b d, Integrable (f a b d) μ) :
    (∫ x, ∑ a : Fin p, ∑ b : Fin p, ∑ d : Fin p, f a b d x ∂μ) =
      ∑ a : Fin p, ∑ b : Fin p, ∑ d : Fin p,
        ∫ x, f a b d x ∂μ := by
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro a ha
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro b hb
      rw [integral_finsetSum]
      intro d hd
      exact hf a b d
    · intro b hb
      exact integrable_finsetSum Finset.univ fun d hd ↦ hf a b d
  · intro a ha
    exact integrable_finsetSum Finset.univ fun b hb ↦
      integrable_finsetSum Finset.univ fun d hd ↦ hf a b d

private theorem integrable_halfGaussian_inverseWishart_entryProduct_three_third
    {k p : ℕ} (hgap : p + 6 ≤ k)
    (a b d e u v : Fin p) :
    Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        (realWishartGram R)⁻¹ a b * (realWishartGram R)⁻¹ d e *
          (realWishartGram R)⁻¹ u v)
      (halfGaussianMatrix k p) := by
  let indices : Fin 3 → Fin p × Fin p := ![(a, b), (d, e), (u, v)]
  have h := integrable_inverseWishartEntryProduct_halfGaussianMatrix
    (k := k) (p := p) (q := 3) hgap indices
  apply h.congr
  filter_upwards [] with R
  simp [indices, inverseWishartEntryProduct, Fin.prod_univ_three]

private theorem integrable_halfGaussian_inverseWishart_entryProduct_two_third
    {k p : ℕ} (hgap : p + 4 ≤ k)
    (a b d e : Fin p) :
    Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        (realWishartGram R)⁻¹ a b * (realWishartGram R)⁻¹ d e)
      (halfGaussianMatrix k p) := by
  let indices : Fin 2 → Fin p × Fin p := ![(a, b), (d, e)]
  have h := integrable_inverseWishartEntryProduct_halfGaussianMatrix
    (k := k) (p := p) (q := 2) hgap indices
  apply h.congr
  filter_upwards [] with R
  simp [indices, inverseWishartEntryProduct, Fin.prod_univ_two]

/-! ## Diagonal contraction -/

/-- Diagonal contraction of the proved third-entry recursion. -/
theorem halfGaussian_inverseWishart_traceCube_steinRecursion_internal
    {k p : ℕ} (hgap : p + 8 ≤ k) :
    inverseWishartEntryGap k p *
        (∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace (realWishartGram R)⁻¹ ^ 3
          ∂halfGaussianMatrix k p) =
      2 * (p : ℝ) *
        (∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace (realWishartGram R)⁻¹ ^ 2
          ∂halfGaussianMatrix k p) +
      4 * (∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace (realWishartGram R)⁻¹ *
          Matrix.trace ((realWishartGram R)⁻¹ ^ 2)
        ∂halfGaussianMatrix k p) := by
  let μ := halfGaussianMatrix k p
  let M2 := halfGaussianInverseWishartDoubleEntryIntegral k p
  let M3 := halfGaussianInverseWishartThirdEntryIntegral k p
  have hsum :
      (∑ a : Fin p, ∑ b : Fin p, ∑ d : Fin p,
        inverseWishartEntryGap k p * M3 a a b b d d) =
      ∑ a : Fin p, ∑ b : Fin p, ∑ d : Fin p,
        (2 * realKroneckerDelta d d * M2 a a b b +
          M3 a d d a b b + M3 a d d a b b +
          M3 a a b d d b + M3 a a b d d b) := by
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro d hd
    exact halfGaussian_inverseWishart_thirdEntry_steinRecursion
      hgap d d a a b b
  have hleft :
      (∑ a : Fin p, ∑ b : Fin p, ∑ d : Fin p, M3 a a b b d d) =
        ∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace (realWishartGram R)⁻¹ ^ 3 ∂μ := by
    dsimp only [M3, halfGaussianInverseWishartThirdEntryIntegral]
    rw [← integral_fintype_sum_three_third μ]
    · apply integral_congr_ae
      filter_upwards [] with R
      exact (trace_cube_eq_diagonalTripleSum_third
        (realWishartGram R)⁻¹).symm
    · intro a b d
      exact integrable_halfGaussian_inverseWishart_entryProduct_three_third
        (by omega) a a b b d d
  have hdelta :
      (∑ a : Fin p, ∑ b : Fin p, ∑ d : Fin p,
        2 * realKroneckerDelta d d * M2 a a b b) =
      2 * (p : ℝ) *
        (∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace (realWishartGram R)⁻¹ ^ 2 ∂μ) := by
    have hM2 :
        (∑ a : Fin p, ∑ b : Fin p, M2 a a b b) =
        ∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace (realWishartGram R)⁻¹ ^ 2 ∂μ := by
      dsimp only [M2, halfGaussianInverseWishartDoubleEntryIntegral]
      rw [← integral_fintype_sum_two_third μ]
      · apply integral_congr_ae
        filter_upwards [] with R
        exact (trace_sq_eq_diagonalPairSum_third
          (realWishartGram R)⁻¹).symm
      · intro a b
        exact integrable_halfGaussian_inverseWishart_entryProduct_two_third
          (by omega) a a b b
    rw [show (∑ a : Fin p, ∑ b : Fin p, ∑ d : Fin p,
        2 * realKroneckerDelta d d * M2 a a b b) =
        2 * (p : ℝ) * (∑ a : Fin p, ∑ b : Fin p, M2 a a b b) by
      simp [realKroneckerDelta, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      ring]
    rw [hM2]
  have hsplice1 :
      (∑ a : Fin p, ∑ b : Fin p, ∑ d : Fin p, M3 a d d a b b) =
        ∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace (realWishartGram R)⁻¹ *
            Matrix.trace ((realWishartGram R)⁻¹ ^ 2) ∂μ := by
    dsimp only [M3, halfGaussianInverseWishartThirdEntryIntegral]
    rw [← integral_fintype_sum_three_third μ]
    · apply integral_congr_ae
      filter_upwards [] with R
      rw [trace_mul_trace_matrix_sq_eq_entryTripleSum_third]
      rw [show (∑ a : Fin p, ∑ b : Fin p, ∑ d : Fin p,
          (realWishartGram R)⁻¹ a d * (realWishartGram R)⁻¹ d a *
            (realWishartGram R)⁻¹ b b) =
          ∑ b : Fin p, ∑ a : Fin p, ∑ d : Fin p,
            (realWishartGram R)⁻¹ b b *
              ((realWishartGram R)⁻¹ a d *
                (realWishartGram R)⁻¹ d a) by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro b hb
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro d hd
        ring]
    · intro a b d
      exact integrable_halfGaussian_inverseWishart_entryProduct_three_third
        (by omega) a d d a b b
  have hsplice2 :
      (∑ a : Fin p, ∑ b : Fin p, ∑ d : Fin p, M3 a a b d d b) =
        ∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace (realWishartGram R)⁻¹ *
            Matrix.trace ((realWishartGram R)⁻¹ ^ 2) ∂μ := by
    dsimp only [M3, halfGaussianInverseWishartThirdEntryIntegral]
    rw [← integral_fintype_sum_three_third μ]
    · apply integral_congr_ae
      filter_upwards [] with R
      simpa only [mul_assoc] using
        (trace_mul_trace_matrix_sq_eq_entryTripleSum_third
          (realWishartGram R)⁻¹).symm
    · intro a b d
      exact integrable_halfGaussian_inverseWishart_entryProduct_three_third
        (by omega) a a b d d b
  rw [← hleft]
  simp only [Finset.mul_sum]
  rw [hsum]
  simp only [Finset.sum_add_distrib]
  rw [hdelta, hsplice1, hsplice2]
  ring

/-! ## Normalization and project transport -/

private theorem trace_steinNormalizedInverseWishartMatrix_third
    (k p : ℕ) (R : Matrix (Fin k) (Fin p) ℝ) :
    Matrix.trace (steinNormalizedInverseWishartMatrix k p R) =
      (inverseWishartEntryGap k p / 2) *
        Matrix.trace (realWishartGram R)⁻¹ := by
  simp [steinNormalizedInverseWishartMatrix, Matrix.trace_smul,
    smul_eq_mul]

private theorem trace_sq_steinNormalizedInverseWishartMatrix_third
    (k p : ℕ) (R : Matrix (Fin k) (Fin p) ℝ) :
    Matrix.trace ((steinNormalizedInverseWishartMatrix k p R) ^ 2) =
      (inverseWishartEntryGap k p / 2) ^ 2 *
        Matrix.trace ((realWishartGram R)⁻¹ ^ 2) := by
  simp [steinNormalizedInverseWishartMatrix, smul_pow,
    Matrix.trace_smul, smul_eq_mul]

/-- Gap-normalized third trace-power recursion. -/
theorem halfGaussian_steinNormalized_traceCube_steinRecursion_internal
    {k p : ℕ} (hgap : p + 8 ≤ k) :
    inverseWishartEntryGap k p *
        (∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace (steinNormalizedInverseWishartMatrix k p R) ^ 3
          ∂halfGaussianMatrix k p) =
      (p : ℝ) * inverseWishartEntryGap k p *
        (∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace (steinNormalizedInverseWishartMatrix k p R) ^ 2
          ∂halfGaussianMatrix k p) +
      4 * (∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace (steinNormalizedInverseWishartMatrix k p R) *
          Matrix.trace ((steinNormalizedInverseWishartMatrix k p R) ^ 2)
        ∂halfGaussianMatrix k p) := by
  let c := inverseWishartEntryGap k p
  let g := c / 2
  have hraw := halfGaussian_inverseWishart_traceCube_steinRecursion_internal hgap
  have hthree :
      (∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace (steinNormalizedInverseWishartMatrix k p R) ^ 3
          ∂halfGaussianMatrix k p) =
      g ^ 3 * (∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace (realWishartGram R)⁻¹ ^ 3
          ∂halfGaussianMatrix k p) := by
    rw [show (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        Matrix.trace (steinNormalizedInverseWishartMatrix k p R) ^ 3) =
        fun R ↦ g ^ 3 * Matrix.trace (realWishartGram R)⁻¹ ^ 3 by
      funext R
      rw [trace_steinNormalizedInverseWishartMatrix_third]
      dsimp only [g, c]
      ring]
    rw [integral_const_mul]
  have htwo :
      (∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace (steinNormalizedInverseWishartMatrix k p R) ^ 2
          ∂halfGaussianMatrix k p) =
      g ^ 2 * (∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace (realWishartGram R)⁻¹ ^ 2
          ∂halfGaussianMatrix k p) := by
    rw [show (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        Matrix.trace (steinNormalizedInverseWishartMatrix k p R) ^ 2) =
        fun R ↦ g ^ 2 * Matrix.trace (realWishartGram R)⁻¹ ^ 2 by
      funext R
      rw [trace_steinNormalizedInverseWishartMatrix_third]
      dsimp only [g, c]
      ring]
    rw [integral_const_mul]
  have hmixed :
      (∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace (steinNormalizedInverseWishartMatrix k p R) *
          Matrix.trace ((steinNormalizedInverseWishartMatrix k p R) ^ 2)
          ∂halfGaussianMatrix k p) =
      g ^ 3 * (∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace (realWishartGram R)⁻¹ *
          Matrix.trace ((realWishartGram R)⁻¹ ^ 2)
          ∂halfGaussianMatrix k p) := by
    rw [show (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        Matrix.trace (steinNormalizedInverseWishartMatrix k p R) *
          Matrix.trace ((steinNormalizedInverseWishartMatrix k p R) ^ 2)) =
        fun R ↦ g ^ 3 *
          (Matrix.trace (realWishartGram R)⁻¹ *
            Matrix.trace ((realWishartGram R)⁻¹ ^ 2)) by
      funext R
      rw [trace_steinNormalizedInverseWishartMatrix_third,
        trace_sq_steinNormalizedInverseWishartMatrix_third]
      dsimp only [g, c]
      ring]
    rw [integral_const_mul]
  rw [hthree, htwo, hmixed]
  dsimp only [g, c] at *
  linear_combination (inverseWishartEntryGap k p / 2) ^ 3 * hraw

private theorem measurable_matrix_trace_third (p : ℕ) :
    Measurable (fun D : Matrix (Fin p) (Fin p) ℝ ↦ Matrix.trace D) := by
  unfold Matrix.trace
  exact Finset.measurable_sum _ fun i _ ↦
    (measurable_pi_apply i).comp (measurable_pi_apply i)

private theorem measurable_matrix_trace_sq_third (p : ℕ) :
    Measurable
      (fun D : Matrix (Fin p) (Fin p) ℝ ↦ Matrix.trace (D ^ 2)) := by
  unfold Matrix.trace
  simp only [Matrix.diag_apply, pow_two, Matrix.mul_apply]
  apply Finset.measurable_sum
  intro i hi
  apply Finset.measurable_sum
  intro j hj
  have hij : Measurable
      (fun D : Matrix (Fin p) (Fin p) ℝ ↦ D i j) :=
    (measurable_pi_apply j).comp (measurable_pi_apply i)
  have hji : Measurable
      (fun D : Matrix (Fin p) (Fin p) ℝ ↦ D j i) :=
    (measurable_pi_apply i).comp (measurable_pi_apply j)
  exact hij.mul hji

/-- Project-side third trace-power recursion under the dense hypotheses. -/
theorem h9ScaledInverseWishart_traceCube_steinRecursion_internal
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    concreteCOEExponent N K *
        (∫ B : H9InverseWishartSample N K,
          Matrix.trace (h9ScaledInverseWishart N K B) ^ 3
          ∂h9InverseWishartDenominatorLaw N K) =
      (N : ℝ) * concreteCOEExponent N K *
        (∫ B : H9InverseWishartSample N K,
          Matrix.trace (h9ScaledInverseWishart N K B) ^ 2
          ∂h9InverseWishartDenominatorLaw N K) +
      4 * (∫ B : H9InverseWishartSample N K,
        Matrix.trace (h9ScaledInverseWishart N K B) *
          Matrix.trace ((h9ScaledInverseWishart N K B) ^ 2)
        ∂h9InverseWishartDenominatorLaw N K) := by
  have hNK : N ≤ K := by omega
  have hpk : N ≤ K - N := by omega
  have hc := inverseWishartEntryGap_project_eq_concreteCOEExponent_h9 hNK
  have hhalf := halfGaussian_steinNormalized_traceCube_steinRecursion_internal
    (k := K - N) (p := N) (by omega : N + 8 ≤ K - N)
  have htraceSq := integral_steinNormalized_halfGaussian_eq_standardScaled_h9
    hpk (fun D : Matrix (Fin N) (Fin N) ℝ ↦ Matrix.trace D ^ 2)
      ((measurable_matrix_trace_third N).pow_const 2)
  have htraceCube := integral_steinNormalized_halfGaussian_eq_standardScaled_h9
    hpk (fun D : Matrix (Fin N) (Fin N) ℝ ↦ Matrix.trace D ^ 3)
      ((measurable_matrix_trace_third N).pow_const 3)
  have hmixed := integral_steinNormalized_halfGaussian_eq_standardScaled_h9
    hpk (fun D : Matrix (Fin N) (Fin N) ℝ ↦
      Matrix.trace D * Matrix.trace (D ^ 2))
      ((measurable_matrix_trace_third N).mul
        (measurable_matrix_trace_sq_third N))
  rw [htraceCube, htraceSq, hmixed] at hhalf
  simpa only [hc, h9InverseWishartDenominatorLaw,
    h9ScaledInverseWishart] using hhalf

/-- The previously isolated H9 order-three recurrence is now internal. -/
theorem h9ThirdTracePowerSteinRecurrence_internal
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    H9ThirdTracePowerSteinRecurrence N K := by
  refine ⟨?_⟩
  exact h9ScaledInverseWishart_traceCube_steinRecursion_internal hN hdense

/-- Internal construction of the centered H9 Stein contraction. -/
theorem h9CenteredTraceSteinContraction_internal
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    H9CenteredTraceSteinContraction N K :=
  h9CenteredTraceSteinContraction_of_thirdTracePowerRecurrence
    hN hdense (h9ThirdTracePowerSteinRecurrence_internal hN hdense)

/-- Internal dense-range denominator package for H9. -/
theorem h9InverseWishartDenominatorPackage_internal
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    H9InverseWishartDenominatorPackage N K := by
  have hgap : 2 * N + 8 ≤ K := by omega
  exact h9U08InverseWishartContract_of_steinContraction hN hgap
    (h9CenteredTraceSteinContraction_internal hN hdense)

/-- All-dimensional H9 denominator package in the literal moment range.
The qualitative fields use `hgap`; the new Stein contraction is invoked only
inside the dense-bound field, where its stronger analytic threshold follows. -/
theorem h9InverseWishartDenominatorPackage_internal_allDimensions
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    H9InverseWishartDenominatorPackage N K := by
  apply h9U08InverseWishartContract_of_centeredTraceFourthBound hN hgap
  refine ⟨?_⟩
  intro hdense
  exact h9CenteredInverseTrace_lpNorm_four_le_of_steinContraction hN hdense
    (h9CenteredTraceSteinContraction_internal hN hdense)

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08
