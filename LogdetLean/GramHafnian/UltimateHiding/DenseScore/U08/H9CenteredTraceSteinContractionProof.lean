import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.H9CenteredTraceSteinClosure
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.H14_DenominatorFourthTraceContraction
import Mathlib.Tactic

/-!
# H9 centered trace: contraction of the audited entrywise Stein recursions

This module contracts the already proved second- and fourth-entry
inverse-Wishart Stein recursions along diagonal indices.  It proves the raw
second- and fourth-power trace recurrences, transports them from the
half-Gaussian normalization to the project's variance-one denominator law,
and reduces the H9 centered fourth-moment identity to the single missing
third-power trace recurrence.

The remaining third-power recurrence is strictly below
`H9CenteredTraceSteinContraction`: it is the diagonal contraction of the
order-three entrywise Stein identity.  No endpoint or literature atom is
declared here.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08

noncomputable section

open LogdetLean.GramHafnian
open LogdetLean.GramHafnian.Wishart
open LogdetLean.GramHafnian.UltimateHiding.DenseScore

set_option maxHeartbeats 3600000

/-! ## Finite diagonal contractions -/

private theorem trace_sq_eq_diagonalPairSum
    {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) :
    Matrix.trace A ^ 2 =
      ∑ a : Fin p, ∑ b : Fin p, A a a * A b b := by
  simp only [Matrix.trace, Matrix.diag_apply, pow_two, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]

private theorem trace_cube_eq_diagonalTripleSum
    {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) :
    Matrix.trace A ^ 3 =
      ∑ a : Fin p, ∑ b : Fin p, ∑ d : Fin p,
        A a a * A b b * A d d := by
  rw [show Matrix.trace A ^ 3 = Matrix.trace A ^ 2 * Matrix.trace A by ring,
    trace_sq_eq_diagonalPairSum, Finset.sum_mul]
  simp only [Matrix.trace, Matrix.diag_apply]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.mul_sum]

private theorem trace_fourth_eq_diagonalQuadrupleSum
    {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) :
    Matrix.trace A ^ 4 =
      ∑ a : Fin p, ∑ b : Fin p, ∑ d : Fin p, ∑ e : Fin p,
        A a a * A b b * A d d * A e e := by
  rw [show Matrix.trace A ^ 4 = Matrix.trace A ^ 2 * Matrix.trace A ^ 2 by ring,
    trace_sq_eq_diagonalPairSum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  ring

private theorem trace_matrix_sq_eq_entryPairSum
    {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) :
    Matrix.trace (A ^ 2) =
      ∑ a : Fin p, ∑ b : Fin p, A a b * A b a := by
  simp [Matrix.trace, Matrix.mul_apply, pow_two]

private theorem trace_sq_mul_trace_matrix_sq_eq_entrySum
    {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) :
    Matrix.trace A ^ 2 * Matrix.trace (A ^ 2) =
      ∑ a : Fin p, ∑ b : Fin p, ∑ d : Fin p, ∑ e : Fin p,
        A a a * A b b * (A d e * A e d) := by
  rw [trace_sq_eq_diagonalPairSum, trace_matrix_sq_eq_entryPairSum,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mul_sum]

private theorem integral_fintype_sum_two
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

private theorem integral_fintype_sum_three
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

private theorem integral_fintype_sum_four_diag
    {X : Type*} [MeasurableSpace X] {p : ℕ} (μ : Measure X)
    (f : Fin p → Fin p → Fin p → Fin p → X → ℝ)
    (hf : ∀ a b d e, Integrable (f a b d e) μ) :
    (∫ x, ∑ a : Fin p, ∑ b : Fin p, ∑ d : Fin p, ∑ e : Fin p,
        f a b d e x ∂μ) =
      ∑ a : Fin p, ∑ b : Fin p, ∑ d : Fin p, ∑ e : Fin p,
        ∫ x, f a b d e x ∂μ := by
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro a ha
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro b hb
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro d hd
        rw [integral_finsetSum]
        intro e he
        exact hf a b d e
      · intro d hd
        exact integrable_finsetSum Finset.univ fun e he ↦ hf a b d e
    · intro b hb
      exact integrable_finsetSum Finset.univ fun d hd ↦
        integrable_finsetSum Finset.univ fun e he ↦ hf a b d e
  · intro a ha
    exact integrable_finsetSum Finset.univ fun b hb ↦
      integrable_finsetSum Finset.univ fun d hd ↦
        integrable_finsetSum Finset.univ fun e he ↦ hf a b d e

private theorem integrable_halfGaussian_inverseWishart_entryProduct_one_h9
    {k p : ℕ} (hgap : p + 2 ≤ k) (a b : Fin p) :
    Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦ (realWishartGram R)⁻¹ a b)
      (halfGaussianMatrix k p) := by
  let indices : Fin 1 → Fin p × Fin p := ![(a, b)]
  have h := integrable_inverseWishartEntryProduct_halfGaussianMatrix
    (k := k) (p := p) (q := 1) hgap indices
  apply h.congr
  filter_upwards [] with R
  simp [indices, inverseWishartEntryProduct, Fin.prod_univ_one]

private theorem integrable_halfGaussian_inverseWishart_entryProduct_two_h9
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

private theorem integrable_halfGaussian_inverseWishart_entryProduct_three_h9
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

private theorem integrable_halfGaussian_inverseWishart_entryProduct_four_h9
    {k p : ℕ} (hgap : p + 8 ≤ k)
    (a b d e u v x y : Fin p) :
    Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        (realWishartGram R)⁻¹ a b * (realWishartGram R)⁻¹ d e *
          (realWishartGram R)⁻¹ u v * (realWishartGram R)⁻¹ x y)
      (halfGaussianMatrix k p) := by
  let indices : Fin 4 → Fin p × Fin p :=
    ![(a, b), (d, e), (u, v), (x, y)]
  have h := integrable_inverseWishartEntryProduct_halfGaussianMatrix
    (k := k) (p := p) (q := 4) hgap indices
  apply h.congr
  filter_upwards [] with R
  simp [indices, inverseWishartEntryProduct, Fin.prod_univ_four]

/-! ## Raw half-Gaussian trace recurrences -/

/-- Diagonal contraction of the checked second-entry Stein recursion. -/
theorem halfGaussian_inverseWishart_traceSq_steinRecursion
    {k p : ℕ} (hgap : p + 8 ≤ k) :
    inverseWishartEntryGap k p *
        (∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace (realWishartGram R)⁻¹ ^ 2
          ∂halfGaussianMatrix k p) =
      2 * (p : ℝ) *
        (∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace (realWishartGram R)⁻¹
          ∂halfGaussianMatrix k p) +
      2 * (∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace ((realWishartGram R)⁻¹ ^ 2)
        ∂halfGaussianMatrix k p) := by
  let μ := halfGaussianMatrix k p
  let M1 := halfGaussianInverseWishartEntryMeanIntegral k p
  let M2 := halfGaussianInverseWishartSecondEntryIntegral k p
  have H := halfGaussian_inverseWishart_secondEntry_steinRecursion
    (k := k) (p := p) hgap
  have hsum :
      (∑ a : Fin p, ∑ b : Fin p,
        inverseWishartEntryGap k p * M2 a a b b) =
      ∑ a : Fin p, ∑ b : Fin p,
        (2 * M1 b b * realKroneckerDelta a a +
          M2 a b a b + M2 a b a b) := by
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    simpa only using H.entry_product_recursion a a b b
  have hleft :
      (∑ a : Fin p, ∑ b : Fin p, M2 a a b b) =
        ∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace (realWishartGram R)⁻¹ ^ 2 ∂μ := by
    dsimp only [M2, halfGaussianInverseWishartSecondEntryIntegral]
    rw [← integral_fintype_sum_two μ]
    · apply integral_congr_ae
      filter_upwards [] with R
      exact (trace_sq_eq_diagonalPairSum (realWishartGram R)⁻¹).symm
    · intro a b
      exact integrable_halfGaussian_inverseWishart_entryProduct_two_h9
        (by omega) a a b b
  have hmean :
      (∑ a : Fin p, ∑ b : Fin p,
        2 * M1 b b * realKroneckerDelta a a) =
      2 * (p : ℝ) *
        (∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace (realWishartGram R)⁻¹ ∂μ) := by
    have hM1 : (∑ b : Fin p, M1 b b) =
        ∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace (realWishartGram R)⁻¹ ∂μ := by
      dsimp only [M1, halfGaussianInverseWishartEntryMeanIntegral]
      rw [← integral_finsetSum]
      · apply integral_congr_ae
        filter_upwards [] with R
        simp [Matrix.trace]
      · intro b hb
        exact integrable_halfGaussian_inverseWishart_entryProduct_one_h9
          (by omega) b b
    rw [show (∑ a : Fin p, ∑ b : Fin p,
        2 * M1 b b * realKroneckerDelta a a) =
        2 * (p : ℝ) * ∑ b : Fin p, M1 b b by
      simp [realKroneckerDelta, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      ring]
    rw [hM1]
  have hsplice :
      (∑ a : Fin p, ∑ b : Fin p, M2 a b a b) =
        ∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace ((realWishartGram R)⁻¹ ^ 2) ∂μ := by
    dsimp only [M2, halfGaussianInverseWishartSecondEntryIntegral]
    rw [← integral_fintype_sum_two μ]
    · apply integral_congr_ae
      filter_upwards [] with R
      rw [trace_matrix_sq_eq_entryPairSum]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      rw [(realWishartGram_inv_isSymm R).apply b a]
    · intro a b
      exact integrable_halfGaussian_inverseWishart_entryProduct_two_h9
        (by omega) a b a b
  rw [← hleft]
  simp only [Finset.mul_sum]
  rw [hsum]
  simp only [Finset.sum_add_distrib]
  rw [hmean, hsplice]
  ring

/-- Diagonal contraction of the checked fourth-entry Stein recursion. -/
theorem halfGaussian_inverseWishart_traceFourthPower_steinRecursion
    {k p : ℕ} (hgap : p + 10 ≤ k) :
    inverseWishartEntryGap k p *
        (∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace (realWishartGram R)⁻¹ ^ 4
          ∂halfGaussianMatrix k p) =
      2 * (p : ℝ) *
        (∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace (realWishartGram R)⁻¹ ^ 3
          ∂halfGaussianMatrix k p) +
      6 * (∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace (realWishartGram R)⁻¹ ^ 2 *
          Matrix.trace ((realWishartGram R)⁻¹ ^ 2)
        ∂halfGaussianMatrix k p) := by
  let μ := halfGaussianMatrix k p
  let M3 := halfGaussianInverseWishartTripleEntryIntegral k p
  let M4 := halfGaussianInverseWishartFourthEntryIntegral k p
  have hsum :
      (∑ a : Fin p, ∑ b : Fin p, ∑ d : Fin p, ∑ e : Fin p,
        inverseWishartEntryGap k p * M4 a a b b d d e e) =
      ∑ a : Fin p, ∑ b : Fin p, ∑ d : Fin p, ∑ e : Fin p,
        (2 * realKroneckerDelta e e * M3 a a b b d d +
          M4 a e e a b b d d + M4 a e e a b b d d +
          M4 a a b e e b d d + M4 a a b e e b d d +
          M4 a a b b d e e d + M4 a a b b d e e d) := by
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro e he
    exact halfGaussian_inverseWishart_fourthEntry_steinRecursion
      hgap e e a a b b d d
  have hleft :
      (∑ a : Fin p, ∑ b : Fin p, ∑ d : Fin p, ∑ e : Fin p,
        M4 a a b b d d e e) =
        ∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace (realWishartGram R)⁻¹ ^ 4 ∂μ := by
    dsimp only [M4, halfGaussianInverseWishartFourthEntryIntegral]
    rw [← integral_fintype_sum_four_diag μ]
    · apply integral_congr_ae
      filter_upwards [] with R
      exact (trace_fourth_eq_diagonalQuadrupleSum
        (realWishartGram R)⁻¹).symm
    · intro a b d e
      exact integrable_halfGaussian_inverseWishart_entryProduct_four_h9
        (by omega) a a b b d d e e
  have hdelta :
      (∑ a : Fin p, ∑ b : Fin p, ∑ d : Fin p, ∑ e : Fin p,
        2 * realKroneckerDelta e e * M3 a a b b d d) =
      2 * (p : ℝ) *
        (∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace (realWishartGram R)⁻¹ ^ 3 ∂μ) := by
    have hM3 :
        (∑ a : Fin p, ∑ b : Fin p, ∑ d : Fin p,
          M3 a a b b d d) =
        ∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace (realWishartGram R)⁻¹ ^ 3 ∂μ := by
      dsimp only [M3, halfGaussianInverseWishartTripleEntryIntegral]
      rw [← integral_fintype_sum_three μ]
      · apply integral_congr_ae
        filter_upwards [] with R
        exact (trace_cube_eq_diagonalTripleSum
          (realWishartGram R)⁻¹).symm
      · intro a b d
        exact integrable_halfGaussian_inverseWishart_entryProduct_three_h9
          (by omega) a a b b d d
    rw [show (∑ a : Fin p, ∑ b : Fin p, ∑ d : Fin p, ∑ e : Fin p,
        2 * realKroneckerDelta e e * M3 a a b b d d) =
        2 * (p : ℝ) *
          (∑ a : Fin p, ∑ b : Fin p, ∑ d : Fin p,
            M3 a a b b d d) by
      simp [realKroneckerDelta, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro d hd
      ring]
    rw [hM3]
  have hsplice1 :
      (∑ a : Fin p, ∑ b : Fin p, ∑ d : Fin p, ∑ e : Fin p,
        M4 a e e a b b d d) =
        ∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace (realWishartGram R)⁻¹ ^ 2 *
            Matrix.trace ((realWishartGram R)⁻¹ ^ 2) ∂μ := by
    dsimp only [M4, halfGaussianInverseWishartFourthEntryIntegral]
    rw [← integral_fintype_sum_four_diag μ]
    · apply integral_congr_ae
      filter_upwards [] with R
      rw [trace_sq_mul_trace_matrix_sq_eq_entrySum]
      rw [show (∑ a : Fin p, ∑ b : Fin p, ∑ d : Fin p, ∑ e : Fin p,
          (realWishartGram R)⁻¹ a e * (realWishartGram R)⁻¹ e a *
            (realWishartGram R)⁻¹ b b * (realWishartGram R)⁻¹ d d) =
          ∑ b : Fin p, ∑ d : Fin p, ∑ a : Fin p, ∑ e : Fin p,
            (realWishartGram R)⁻¹ b b * (realWishartGram R)⁻¹ d d *
              ((realWishartGram R)⁻¹ a e * (realWishartGram R)⁻¹ e a) by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro b hb
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro d hd
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro e he
        ring]
    · intro a b d e
      exact integrable_halfGaussian_inverseWishart_entryProduct_four_h9
        (by omega) a e e a b b d d
  have hsplice2 :
      (∑ a : Fin p, ∑ b : Fin p, ∑ d : Fin p, ∑ e : Fin p,
        M4 a a b e e b d d) =
        ∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace (realWishartGram R)⁻¹ ^ 2 *
            Matrix.trace ((realWishartGram R)⁻¹ ^ 2) ∂μ := by
    dsimp only [M4, halfGaussianInverseWishartFourthEntryIntegral]
    rw [← integral_fintype_sum_four_diag μ]
    · apply integral_congr_ae
      filter_upwards [] with R
      rw [trace_sq_mul_trace_matrix_sq_eq_entrySum]
      rw [show (∑ a : Fin p, ∑ b : Fin p, ∑ d : Fin p, ∑ e : Fin p,
          (realWishartGram R)⁻¹ a a * (realWishartGram R)⁻¹ b e *
            (realWishartGram R)⁻¹ e b * (realWishartGram R)⁻¹ d d) =
          ∑ a : Fin p, ∑ d : Fin p, ∑ b : Fin p, ∑ e : Fin p,
            (realWishartGram R)⁻¹ a a * (realWishartGram R)⁻¹ d d *
              ((realWishartGram R)⁻¹ b e * (realWishartGram R)⁻¹ e b) by
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro d hd
        apply Finset.sum_congr rfl
        intro b hb
        apply Finset.sum_congr rfl
        intro e he
        ring]
    · intro a b d e
      exact integrable_halfGaussian_inverseWishart_entryProduct_four_h9
        (by omega) a a b e e b d d
  have hsplice3 :
      (∑ a : Fin p, ∑ b : Fin p, ∑ d : Fin p, ∑ e : Fin p,
        M4 a a b b d e e d) =
        ∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace (realWishartGram R)⁻¹ ^ 2 *
            Matrix.trace ((realWishartGram R)⁻¹ ^ 2) ∂μ := by
    dsimp only [M4, halfGaussianInverseWishartFourthEntryIntegral]
    rw [← integral_fintype_sum_four_diag μ]
    · apply integral_congr_ae
      filter_upwards [] with R
      simpa only [mul_assoc] using
        (trace_sq_mul_trace_matrix_sq_eq_entrySum
          (realWishartGram R)⁻¹).symm
    · intro a b d e
      exact integrable_halfGaussian_inverseWishart_entryProduct_four_h9
        (by omega) a a b b d e e d
  rw [← hleft]
  simp only [Finset.mul_sum]
  rw [hsum]
  simp only [Finset.sum_add_distrib]
  rw [hdelta, hsplice1, hsplice2, hsplice3]
  ring

/-! ## Gap-normalized recurrences -/

private theorem trace_steinNormalizedInverseWishartMatrix_h9
    (k p : ℕ) (R : Matrix (Fin k) (Fin p) ℝ) :
    Matrix.trace (steinNormalizedInverseWishartMatrix k p R) =
      (inverseWishartEntryGap k p / 2) *
        Matrix.trace (realWishartGram R)⁻¹ := by
  simp [steinNormalizedInverseWishartMatrix, Matrix.trace_smul,
    smul_eq_mul]

private theorem trace_sq_steinNormalizedInverseWishartMatrix_h9
    (k p : ℕ) (R : Matrix (Fin k) (Fin p) ℝ) :
    Matrix.trace ((steinNormalizedInverseWishartMatrix k p R) ^ 2) =
      (inverseWishartEntryGap k p / 2) ^ 2 *
        Matrix.trace ((realWishartGram R)⁻¹ ^ 2) := by
  simp [steinNormalizedInverseWishartMatrix, smul_pow,
    Matrix.trace_smul, smul_eq_mul]

/-- Gap-normalized second trace-power recursion. -/
theorem halfGaussian_steinNormalized_traceSq_steinRecursion_h9
    {k p : ℕ} (hgap : p + 8 ≤ k) :
    inverseWishartEntryGap k p *
        (∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace (steinNormalizedInverseWishartMatrix k p R) ^ 2
          ∂halfGaussianMatrix k p) =
      (p : ℝ) * inverseWishartEntryGap k p *
        (∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace (steinNormalizedInverseWishartMatrix k p R)
          ∂halfGaussianMatrix k p) +
      2 * (∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace ((steinNormalizedInverseWishartMatrix k p R) ^ 2)
        ∂halfGaussianMatrix k p) := by
  let c := inverseWishartEntryGap k p
  let g := c / 2
  have hraw := halfGaussian_inverseWishart_traceSq_steinRecursion hgap
  have hpow :
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
      rw [trace_steinNormalizedInverseWishartMatrix_h9]
      dsimp only [g, c]
      ring]
    rw [integral_const_mul]
  have hone :
      (∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace (steinNormalizedInverseWishartMatrix k p R)
          ∂halfGaussianMatrix k p) =
      g * (∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace (realWishartGram R)⁻¹
          ∂halfGaussianMatrix k p) := by
    simp_rw [trace_steinNormalizedInverseWishartMatrix_h9]
    rw [integral_const_mul]
  have htwo :
      (∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace ((steinNormalizedInverseWishartMatrix k p R) ^ 2)
          ∂halfGaussianMatrix k p) =
      g ^ 2 * (∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace ((realWishartGram R)⁻¹ ^ 2)
          ∂halfGaussianMatrix k p) := by
    simp_rw [trace_sq_steinNormalizedInverseWishartMatrix_h9]
    rw [integral_const_mul]
  rw [hpow, hone, htwo]
  dsimp only [g, c] at *
  linear_combination (inverseWishartEntryGap k p / 2) ^ 2 * hraw

/-- Gap-normalized fourth trace-power recursion. -/
theorem halfGaussian_steinNormalized_traceFourthPower_steinRecursion_h9
    {k p : ℕ} (hgap : p + 10 ≤ k) :
    inverseWishartEntryGap k p *
        (∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace (steinNormalizedInverseWishartMatrix k p R) ^ 4
          ∂halfGaussianMatrix k p) =
      (p : ℝ) * inverseWishartEntryGap k p *
        (∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace (steinNormalizedInverseWishartMatrix k p R) ^ 3
          ∂halfGaussianMatrix k p) +
      6 * (∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace (steinNormalizedInverseWishartMatrix k p R) ^ 2 *
          Matrix.trace ((steinNormalizedInverseWishartMatrix k p R) ^ 2)
        ∂halfGaussianMatrix k p) := by
  let c := inverseWishartEntryGap k p
  let g := c / 2
  have hraw := halfGaussian_inverseWishart_traceFourthPower_steinRecursion hgap
  have hfour :
      (∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace (steinNormalizedInverseWishartMatrix k p R) ^ 4
          ∂halfGaussianMatrix k p) =
      g ^ 4 * (∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace (realWishartGram R)⁻¹ ^ 4
          ∂halfGaussianMatrix k p) := by
    rw [show (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        Matrix.trace (steinNormalizedInverseWishartMatrix k p R) ^ 4) =
        fun R ↦ g ^ 4 * Matrix.trace (realWishartGram R)⁻¹ ^ 4 by
      funext R
      rw [trace_steinNormalizedInverseWishartMatrix_h9]
      dsimp only [g, c]
      ring]
    rw [integral_const_mul]
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
      rw [trace_steinNormalizedInverseWishartMatrix_h9]
      dsimp only [g, c]
      ring]
    rw [integral_const_mul]
  have hmixed :
      (∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace (steinNormalizedInverseWishartMatrix k p R) ^ 2 *
          Matrix.trace ((steinNormalizedInverseWishartMatrix k p R) ^ 2)
          ∂halfGaussianMatrix k p) =
      g ^ 4 * (∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace (realWishartGram R)⁻¹ ^ 2 *
          Matrix.trace ((realWishartGram R)⁻¹ ^ 2)
          ∂halfGaussianMatrix k p) := by
    rw [show (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        Matrix.trace (steinNormalizedInverseWishartMatrix k p R) ^ 2 *
          Matrix.trace ((steinNormalizedInverseWishartMatrix k p R) ^ 2)) =
        fun R ↦ g ^ 4 *
          (Matrix.trace (realWishartGram R)⁻¹ ^ 2 *
            Matrix.trace ((realWishartGram R)⁻¹ ^ 2)) by
      funext R
      rw [trace_steinNormalizedInverseWishartMatrix_h9,
        trace_sq_steinNormalizedInverseWishartMatrix_h9]
      ring]
    rw [integral_const_mul]
  rw [hfour, hthree, hmixed]
  dsimp only [g, c] at *
  linear_combination (inverseWishartEntryGap k p / 2) ^ 4 * hraw

/-! ## Transport to the variance-one denominator -/

theorem measurable_steinNormalizedInverseWishartMatrix_h9 (k p : ℕ) :
    Measurable (steinNormalizedInverseWishartMatrix k p) := by
  have hGram : Measurable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦ realWishartGram R) := by
    unfold realWishartGram
    refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    fun_prop
  have hInv : Measurable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦ (realWishartGram R)⁻¹) :=
    (measurable_realMatrix_inv p).comp hGram
  unfold steinNormalizedInverseWishartMatrix
  refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
  exact measurable_const.mul
    ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hInv))

private theorem measurable_matrix_trace_h9 (p : ℕ) :
    Measurable (fun D : Matrix (Fin p) (Fin p) ℝ ↦ Matrix.trace D) := by
  unfold Matrix.trace
  exact Finset.measurable_sum _ fun i _ ↦
    (measurable_pi_apply i).comp (measurable_pi_apply i)

private theorem measurable_matrix_trace_sq_h9 (p : ℕ) :
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

theorem steinNormalized_invSqrtTwoScaleMatrix_eq_standardScaled_h9
    {k p : ℕ} (R : Matrix (Fin k) (Fin p) ℝ)
    (hunit : IsUnit (realWishartGram R).det) :
    steinNormalizedInverseWishartMatrix k p
        (invSqrtTwoScaleMatrix k p R) =
      inverseWishartEntryGap k p • (realWishartGram R)⁻¹ := by
  have hinv :
      (realWishartGram (invSqrtTwoScaleMatrix k p R))⁻¹ =
        (2 : ℝ) • (realWishartGram R)⁻¹ := by
    rw [realWishartGram_invSqrtTwoScaleMatrix]
    letI : Invertible (1 / 2 : ℝ) :=
      invertibleOfNonzero (by norm_num)
    rw [Matrix.inv_smul (A := realWishartGram R) (1 / 2 : ℝ) hunit]
    change (⅟ (1 / 2 : ℝ)) • (realWishartGram R)⁻¹ =
      (2 : ℝ) • (realWishartGram R)⁻¹
    norm_num
  unfold steinNormalizedInverseWishartMatrix
  rw [hinv]
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul]
  ring

/-- A generic normalization transport for measurable scalar matrix
observables. -/
theorem integral_steinNormalized_halfGaussian_eq_standardScaled_h9
    {k p : ℕ} (hpk : p ≤ k)
    (F : Matrix (Fin p) (Fin p) ℝ → ℝ) (hF : Measurable F) :
    (∫ R : Matrix (Fin k) (Fin p) ℝ,
        F (steinNormalizedInverseWishartMatrix k p R)
        ∂halfGaussianMatrix k p) =
      ∫ R : Matrix (Fin k) (Fin p) ℝ,
        F (inverseWishartEntryGap k p • (realWishartGram R)⁻¹)
        ∂standardRealGaussianMatrixMeasure k p := by
  let G := invSqrtTwoScaleMatrix k p
  let μ := standardRealGaussianMatrixMeasure k p
  have hunit := ae_isUnit_det_realWishartGram_standardRealGaussianMatrixMeasure
    (k := k) (p := p) hpk
  have hpoint :
      (fun R ↦ F (steinNormalizedInverseWishartMatrix k p (G R))) =ᵐ[μ]
        fun R ↦ F (inverseWishartEntryGap k p • (realWishartGram R)⁻¹) := by
    filter_upwards [hunit] with R hR
    rw [steinNormalized_invSqrtTwoScaleMatrix_eq_standardScaled_h9 R hR]
  calc
    (∫ R : Matrix (Fin k) (Fin p) ℝ,
        F (steinNormalizedInverseWishartMatrix k p R)
        ∂halfGaussianMatrix k p) =
      ∫ R, F (steinNormalizedInverseWishartMatrix k p R)
        ∂Measure.map G μ := by
          rw [map_invSqrtTwoScaleMatrix_standardRealGaussianMatrixMeasure]
    _ = ∫ R, F (steinNormalizedInverseWishartMatrix k p (G R)) ∂μ := by
      change (∫ R, (F ∘ steinNormalizedInverseWishartMatrix k p) R
          ∂Measure.map G μ) = _
      rw [integral_map (measurable_invSqrtTwoScaleMatrix k p).aemeasurable
        (hF.comp (measurable_steinNormalizedInverseWishartMatrix_h9 k p)).aestronglyMeasurable]
      rfl
    _ = _ := integral_congr_ae hpoint

theorem inverseWishartEntryGap_project_eq_concreteCOEExponent_h9
    {N K : ℕ} (hNK : N ≤ K) :
    inverseWishartEntryGap (K - N) N = concreteCOEExponent N K := by
  unfold inverseWishartEntryGap concreteCOEExponent
  rw [Nat.cast_sub hNK]
  ring

/-- Project-side second trace-power recursion under the dense hypotheses. -/
theorem h9ScaledInverseWishart_traceSq_steinRecursion_internal
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    concreteCOEExponent N K *
        (∫ B : H9InverseWishartSample N K,
          Matrix.trace (h9ScaledInverseWishart N K B) ^ 2
          ∂h9InverseWishartDenominatorLaw N K) =
      (N : ℝ) * concreteCOEExponent N K *
        (∫ B : H9InverseWishartSample N K,
          Matrix.trace (h9ScaledInverseWishart N K B)
          ∂h9InverseWishartDenominatorLaw N K) +
      2 * (∫ B : H9InverseWishartSample N K,
        Matrix.trace ((h9ScaledInverseWishart N K B) ^ 2)
        ∂h9InverseWishartDenominatorLaw N K) := by
  have hNK : N ≤ K := by omega
  have hpk : N ≤ K - N := by omega
  have hc := inverseWishartEntryGap_project_eq_concreteCOEExponent_h9 hNK
  have hhalf := halfGaussian_steinNormalized_traceSq_steinRecursion_h9
    (k := K - N) (p := N) (by omega : N + 8 ≤ K - N)
  have htrace := integral_steinNormalized_halfGaussian_eq_standardScaled_h9
    hpk (fun D : Matrix (Fin N) (Fin N) ℝ ↦ Matrix.trace D)
      (measurable_matrix_trace_h9 N)
  have htraceSq := integral_steinNormalized_halfGaussian_eq_standardScaled_h9
    hpk (fun D : Matrix (Fin N) (Fin N) ℝ ↦ Matrix.trace D ^ 2)
      ((measurable_matrix_trace_h9 N).pow_const 2)
  have hmatrixSq := integral_steinNormalized_halfGaussian_eq_standardScaled_h9
    hpk (fun D : Matrix (Fin N) (Fin N) ℝ ↦ Matrix.trace (D ^ 2))
      (measurable_matrix_trace_sq_h9 N)
  rw [htraceSq, htrace, hmatrixSq] at hhalf
  simpa only [hc, h9InverseWishartDenominatorLaw,
    h9ScaledInverseWishart] using hhalf

/-- Project-side fourth trace-power recursion under the dense hypotheses. -/
theorem h9ScaledInverseWishart_traceFourthPower_steinRecursion_internal
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    concreteCOEExponent N K *
        (∫ B : H9InverseWishartSample N K,
          Matrix.trace (h9ScaledInverseWishart N K B) ^ 4
          ∂h9InverseWishartDenominatorLaw N K) =
      (N : ℝ) * concreteCOEExponent N K *
        (∫ B : H9InverseWishartSample N K,
          Matrix.trace (h9ScaledInverseWishart N K B) ^ 3
          ∂h9InverseWishartDenominatorLaw N K) +
      6 * (∫ B : H9InverseWishartSample N K,
        Matrix.trace (h9ScaledInverseWishart N K B) ^ 2 *
          Matrix.trace ((h9ScaledInverseWishart N K B) ^ 2)
        ∂h9InverseWishartDenominatorLaw N K) := by
  have hNK : N ≤ K := by omega
  have hpk : N ≤ K - N := by omega
  have hc := inverseWishartEntryGap_project_eq_concreteCOEExponent_h9 hNK
  have hhalf := halfGaussian_steinNormalized_traceFourthPower_steinRecursion_h9
    (k := K - N) (p := N) (by omega : N + 10 ≤ K - N)
  have htraceCube := integral_steinNormalized_halfGaussian_eq_standardScaled_h9
    hpk (fun D : Matrix (Fin N) (Fin N) ℝ ↦ Matrix.trace D ^ 3)
      ((measurable_matrix_trace_h9 N).pow_const 3)
  have htraceFourth := integral_steinNormalized_halfGaussian_eq_standardScaled_h9
    hpk (fun D : Matrix (Fin N) (Fin N) ℝ ↦ Matrix.trace D ^ 4)
      ((measurable_matrix_trace_h9 N).pow_const 4)
  have hmixed := integral_steinNormalized_halfGaussian_eq_standardScaled_h9
    hpk (fun D : Matrix (Fin N) (Fin N) ℝ ↦
      Matrix.trace D ^ 2 * Matrix.trace (D ^ 2))
      ((measurable_matrix_trace_h9 N).pow_const 2 |>.mul
        (measurable_matrix_trace_sq_h9 N))
  rw [htraceFourth, htraceCube, hmixed] at hhalf
  simpa only [hc, h9InverseWishartDenominatorLaw,
    h9ScaledInverseWishart] using hhalf

/-! ## Exact reduction to the third trace-power recurrence -/

/-- The sole order-three identity left after contracting the checked
second- and fourth-entry recursions.  This is the diagonal contraction of
the missing third-entry Stein recursion, not an endpoint or an axiom. -/
structure H9ThirdTracePowerSteinRecurrence (N K : ℕ) : Prop where
  traceCube_recursion :
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
        ∂h9InverseWishartDenominatorLaw N K)

private theorem integral_centered_four_expand_h9
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ] (x : X → ℝ) (n : ℝ)
    (hx1 : Integrable x μ)
    (hx2 : Integrable (fun w ↦ x w ^ 2) μ)
    (hx3 : Integrable (fun w ↦ x w ^ 3) μ)
    (hx4 : Integrable (fun w ↦ x w ^ 4) μ) :
    (∫ w, (x w - n) ^ 4 ∂μ) =
      (∫ w, x w ^ 4 ∂μ) -
        4 * n * (∫ w, x w ^ 3 ∂μ) +
        6 * n ^ 2 * (∫ w, x w ^ 2 ∂μ) -
        4 * n ^ 3 * (∫ w, x w ∂μ) + n ^ 4 := by
  let f4 : X → ℝ := fun w ↦ x w ^ 4
  let f3 : X → ℝ := fun w ↦ (4 * n) * x w ^ 3
  let f2 : X → ℝ := fun w ↦ (6 * n ^ 2) * x w ^ 2
  let f1 : X → ℝ := fun w ↦ (4 * n ^ 3) * x w
  let f0 : X → ℝ := fun _ ↦ n ^ 4
  have hf4 : Integrable f4 μ := by simpa only [f4] using hx4
  have hf3 : Integrable f3 μ := by
    simpa only [f3] using hx3.const_mul (4 * n)
  have hf2 : Integrable f2 μ := by
    simpa only [f2] using hx2.const_mul (6 * n ^ 2)
  have hf1 : Integrable f1 μ := by
    simpa only [f1] using hx1.const_mul (4 * n ^ 3)
  have hf0 : Integrable f0 μ := by
    exact integrable_const (n ^ 4)
  have hf43 : Integrable (fun w ↦ f4 w - f3 w) μ := hf4.sub hf3
  have hf432 : Integrable (fun w ↦ (f4 w - f3 w) + f2 w) μ :=
    hf43.add hf2
  have hf4321 : Integrable
      (fun w ↦ ((f4 w - f3 w) + f2 w) - f1 w) μ := hf432.sub hf1
  calc
    (∫ w, (x w - n) ^ 4 ∂μ) =
        ∫ w, (((f4 w - f3 w) + f2 w) - f1 w) + f0 w ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with w
      dsimp only [f4, f3, f2, f1, f0]
      ring
    _ = (∫ w, ((f4 w - f3 w) + f2 w) - f1 w ∂μ) +
          ∫ w, f0 w ∂μ := integral_add hf4321 hf0
    _ = (((∫ w, f4 w ∂μ) - (∫ w, f3 w ∂μ)) +
          (∫ w, f2 w ∂μ) - (∫ w, f1 w ∂μ)) +
          ∫ w, f0 w ∂μ := by
      rw [integral_sub hf432 hf1, integral_add hf43 hf2,
        integral_sub hf4 hf3]
    _ = _ := by
      dsimp only [f4, f3, f2, f1, f0]
      rw [integral_const_mul, integral_const_mul, integral_const_mul,
        integral_const, probReal_univ]
      simp only [one_smul]

private theorem integral_centered_sq_mul_expand_h9
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (x y : X → ℝ) (n : ℝ)
    (hy : Integrable y μ)
    (hxy : Integrable (fun w ↦ x w * y w) μ)
    (hx2y : Integrable (fun w ↦ x w ^ 2 * y w) μ) :
    (∫ w, (x w - n) ^ 2 * y w ∂μ) =
      (∫ w, x w ^ 2 * y w ∂μ) -
        2 * n * (∫ w, x w * y w ∂μ) +
        n ^ 2 * (∫ w, y w ∂μ) := by
  let f2 : X → ℝ := fun w ↦ x w ^ 2 * y w
  let f1 : X → ℝ := fun w ↦ (2 * n) * (x w * y w)
  let f0 : X → ℝ := fun w ↦ n ^ 2 * y w
  have hf2 : Integrable f2 μ := by simpa only [f2] using hx2y
  have hf1 : Integrable f1 μ := by
    simpa only [f1] using hxy.const_mul (2 * n)
  have hf0 : Integrable f0 μ := by
    simpa only [f0] using hy.const_mul (n ^ 2)
  have hf21 : Integrable (fun w ↦ f2 w - f1 w) μ := hf2.sub hf1
  calc
    (∫ w, (x w - n) ^ 2 * y w ∂μ) =
        ∫ w, (f2 w - f1 w) + f0 w ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with w
      dsimp only [f2, f1, f0]
      ring
    _ = (∫ w, f2 w - f1 w ∂μ) + ∫ w, f0 w ∂μ :=
      integral_add hf21 hf0
    _ = ((∫ w, f2 w ∂μ) - ∫ w, f1 w ∂μ) +
        ∫ w, f0 w ∂μ := by rw [integral_sub hf2 hf1]
    _ = _ := by
      dsimp only [f2, f1, f0]
      rw [integral_const_mul, integral_const_mul]

/-- Exact centered fourth-moment Stein identity from the single remaining
third trace-power recurrence. -/
theorem h9CenteredTraceSteinIdentity_of_thirdTracePowerRecurrence
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K)
    (H3 : H9ThirdTracePowerSteinRecurrence N K) :
    concreteCOEExponent N K *
        (∫ B : H9InverseWishartSample N K,
          h9CenteredInverseTrace N K B ^ 4
          ∂h9InverseWishartDenominatorLaw N K) =
      6 * (∫ B : H9InverseWishartSample N K,
        h9CenteredInverseTrace N K B ^ 2 *
          h9InverseTraceSquare N K B
        ∂h9InverseWishartDenominatorLaw N K) := by
  have hgap : 2 * N + 8 ≤ K := by omega
  let μ := h9InverseWishartDenominatorLaw N K
  let x : H9InverseWishartSample N K → ℝ := fun B ↦
    Matrix.trace (h9ScaledInverseWishart N K B)
  let y : H9InverseWishartSample N K → ℝ := fun B ↦
    Matrix.trace ((h9ScaledInverseWishart N K B) ^ 2)
  let z : H9InverseWishartSample N K → ℝ := fun B ↦ x B - (N : ℝ)
  let c := concreteCOEExponent N K
  let n : ℝ := (N : ℝ)
  letI : IsProbabilityMeasure μ :=
    h9InverseWishartDenominatorLaw_isProbability N K
  have hz : MemLp z 4 μ := by
    have hz_eq : z = h9CenteredInverseTrace N K := by
      funext B
      rfl
    rw [hz_eq]
    exact h9CenteredInverseTrace_memLp_four_internal hgap
  have hy : MemLp y 2 μ := by
    have hy_eq : y = h9InverseTraceSquare N K := by
      funext B
      simp only [y, h9InverseTraceSquare, pow_two]
    rw [hy_eq]
    exact h9InverseTraceSquare_memLp_two_internal hgap
  have hx : MemLp x 4 μ := by
    have hfun : x = z + (fun _ ↦ n) := by
      funext B
      dsimp only [x, z, n]
      change Matrix.trace (h9ScaledInverseWishart N K B) =
        (Matrix.trace (h9ScaledInverseWishart N K B) - (N : ℝ)) + (N : ℝ)
      ring
    rw [hfun]
    exact hz.add (memLp_const n)
  have hxTwo : MemLp x 2 μ := hx.mono_exponent (by norm_num)
  have hxSq : MemLp (fun B ↦ x B ^ 2) 2 μ :=
    memLp_sq_two_of_memLp_four hx
  have hzSq : MemLp (fun B ↦ z B ^ 2) 2 μ :=
    memLp_sq_two_of_memLp_four hz
  have hx1 : Integrable x μ :=
    memLp_one_iff_integrable.mp (hx.mono_exponent (by norm_num))
  have hx2 : Integrable (fun B ↦ x B ^ 2) μ :=
    memLp_one_iff_integrable.mp (hxSq.mono_exponent (by norm_num))
  have hx3 : Integrable (fun B ↦ x B ^ 3) μ := by
    have hprod : MemLp (fun B ↦ x B ^ 2 * x B) 1 μ :=
      hxTwo.mul' hxSq
    apply memLp_one_iff_integrable.mp
    apply hprod.ae_eq
    filter_upwards [] with B
    ring
  have hx4 : Integrable (fun B ↦ x B ^ 4) μ := by
    have hprod : MemLp (fun B ↦ x B ^ 2 * x B ^ 2) 1 μ :=
      hxSq.mul' hxSq
    apply memLp_one_iff_integrable.mp
    apply hprod.ae_eq
    filter_upwards [] with B
    ring
  have hy1 : Integrable y μ :=
    memLp_one_iff_integrable.mp (hy.mono_exponent (by norm_num))
  have hxy : Integrable (fun B ↦ x B * y B) μ := by
    exact memLp_one_iff_integrable.mp (hy.mul' hxTwo)
  have hx2y : Integrable (fun B ↦ x B ^ 2 * y B) μ := by
    exact memLp_one_iff_integrable.mp (hy.mul' hxSq)
  have hz2y : Integrable (fun B ↦ z B ^ 2 * y B) μ := by
    exact memLp_one_iff_integrable.mp (hy.mul' hzSq)
  have hz4 : Integrable (fun B ↦ z B ^ 4) μ := by
    have hprod : MemLp (fun B ↦ z B ^ 2 * z B ^ 2) 1 μ :=
      hzSq.mul' hzSq
    apply memLp_one_iff_integrable.mp
    apply hprod.ae_eq
    filter_upwards [] with B
    ring
  have hcenter4 := integral_centered_four_expand_h9 x n hx1 hx2 hx3 hx4
  have hcenterMixed := integral_centered_sq_mul_expand_h9 x y n hy1 hxy hx2y
  have hrec2 :
      c * (∫ B, x B ^ 2 ∂μ) =
        n * c * (∫ B, x B ∂μ) + 2 * (∫ B, y B ∂μ) := by
    simpa only [c, n, x, y, μ] using
      h9ScaledInverseWishart_traceSq_steinRecursion_internal hN hdense
  have hrec3 :
      c * (∫ B, x B ^ 3 ∂μ) =
        n * c * (∫ B, x B ^ 2 ∂μ) +
          4 * (∫ B, x B * y B ∂μ) := by
    simpa only [c, n, x, y, μ] using H3.traceCube_recursion
  have hrec4 :
      c * (∫ B, x B ^ 4 ∂μ) =
        n * c * (∫ B, x B ^ 3 ∂μ) +
          6 * (∫ B, x B ^ 2 * y B ∂μ) := by
    simpa only [c, n, x, y, μ] using
      h9ScaledInverseWishart_traceFourthPower_steinRecursion_internal hN hdense
  have hmean : (∫ B, x B ∂μ) = n := by
    simpa only [x, μ, n] using integral_h9ScaledInverseTrace hgap
  have hid : c * (∫ B, z B ^ 4 ∂μ) =
      6 * (∫ B, z B ^ 2 * y B ∂μ) := by
    rw [hcenter4, hcenterMixed]
    linear_combination hrec4 - 3 * n * hrec3 + 3 * n ^ 2 * hrec2 -
      n ^ 3 * c * hmean
  simpa only [c, z, x, y, μ, h9CenteredInverseTrace,
    h9InverseTraceSquare, pow_two] using hid

/-- The checked second/fourth contractions plus the smaller order-three
recurrence construct the former H9 scalar contraction. -/
theorem h9CenteredTraceSteinContraction_of_thirdTracePowerRecurrence
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K)
    (H3 : H9ThirdTracePowerSteinRecurrence N K) :
    H9CenteredTraceSteinContraction N K := by
  refine ⟨?_⟩
  exact (h9CenteredTraceSteinIdentity_of_thirdTracePowerRecurrence
    hN hdense H3).le

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08
