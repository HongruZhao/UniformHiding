import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.H9ThirdTracePowerSteinProof
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.H14_DenominatorFourthTraceContraction
import Mathlib.Tactic

/-!
# Mixed trace contractions for H8/H10

This foundations-only module contracts the already proved second-, third-,
and fourth-entry inverse-Wishart Stein recursions against the remaining trace
words needed by the H8/H10 scalar recurrence ledger.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08

noncomputable section

open LogdetLean.GramHafnian
open LogdetLean.GramHafnian.Wishart
open LogdetLean.GramHafnian.UltimateHiding.DenseScore

set_option maxHeartbeats 3600000
set_option maxRecDepth 100000

/-! ## Finite trace words -/

private theorem trace_one_entrySum_h8h10
    {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) :
    Matrix.trace A = ∑ a : Fin p, A a a := by
  rfl

private theorem trace_one_sq_entrySum_h8h10
    {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) :
    Matrix.trace A ^ 2 =
      ∑ a : Fin p, ∑ b : Fin p, A a a * A b b := by
  simp only [Matrix.trace, Matrix.diag_apply, pow_two, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]

private theorem trace_two_entrySum_h8h10
    {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) :
    Matrix.trace (A ^ 2) =
      ∑ a : Fin p, ∑ b : Fin p, A a b * A b a := by
  simp [Matrix.trace, Matrix.mul_apply, pow_two]

private theorem trace_three_entrySum_h8h10
    {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) :
    Matrix.trace (A ^ 3) =
      ∑ a : Fin p, ∑ b : Fin p, ∑ d : Fin p,
        A a b * A b d * A d a := by
  simp [Matrix.trace, Matrix.mul_apply, pow_succ, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  conv_lhs => rw [Finset.sum_comm]

private theorem trace_one_mul_trace_two_entrySum_h8h10
    {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) :
    Matrix.trace A * Matrix.trace (A ^ 2) =
      ∑ a : Fin p, ∑ b : Fin p, ∑ d : Fin p,
        A a a * (A b d * A d b) := by
  rw [trace_two_entrySum_h8h10]
  simp only [Matrix.trace, Matrix.diag_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.mul_sum]

private theorem trace_one_mul_trace_two_alt_entrySum_h8h10
    {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) :
    Matrix.trace A * Matrix.trace (A ^ 2) =
      ∑ a : Fin p, ∑ b : Fin p, ∑ d : Fin p,
        A a b * A b a * A d d := by
  rw [mul_comm, trace_two_entrySum_h8h10, trace_one_entrySum_h8h10]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.mul_sum]

/-! ## Finite integral interchange -/

private theorem integral_fintype_sum_one_h8h10
    {X : Type*} [MeasurableSpace X] {p : ℕ} (μ : Measure X)
    (f : Fin p → X → ℝ) (hf : ∀ a, Integrable (f a) μ) :
    (∫ x, ∑ a : Fin p, f a x ∂μ) =
      ∑ a : Fin p, ∫ x, f a x ∂μ := by
  exact integral_finsetSum Finset.univ (fun a _ ↦ hf a)

private theorem integral_fintype_sum_two_h8h10
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

private theorem integral_fintype_sum_three_h8h10
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

/-! ## Entry-product integrability -/

private theorem integrable_halfGaussian_inverseWishart_entry_one_h8h10
    {k p : ℕ} (hgap : p + 2 ≤ k) (a b : Fin p) :
    Integrable (fun R : Matrix (Fin k) (Fin p) ℝ ↦
      (realWishartGram R)⁻¹ a b) (halfGaussianMatrix k p) := by
  let indices : Fin 1 → Fin p × Fin p := ![(a, b)]
  have h := integrable_inverseWishartEntryProduct_halfGaussianMatrix
    (k := k) (p := p) (q := 1) hgap indices
  apply h.congr
  filter_upwards [] with R
  simp [indices, inverseWishartEntryProduct]

private theorem integrable_halfGaussian_inverseWishart_entry_two_h8h10
    {k p : ℕ} (hgap : p + 4 ≤ k) (a b d e : Fin p) :
    Integrable (fun R : Matrix (Fin k) (Fin p) ℝ ↦
      (realWishartGram R)⁻¹ a b * (realWishartGram R)⁻¹ d e)
      (halfGaussianMatrix k p) := by
  let indices : Fin 2 → Fin p × Fin p := ![(a, b), (d, e)]
  have h := integrable_inverseWishartEntryProduct_halfGaussianMatrix
    (k := k) (p := p) (q := 2) hgap indices
  apply h.congr
  filter_upwards [] with R
  simp [indices, inverseWishartEntryProduct, Fin.prod_univ_two]

private theorem integrable_halfGaussian_inverseWishart_entry_three_h8h10
    {k p : ℕ} (hgap : p + 6 ≤ k) (a b d e u v : Fin p) :
    Integrable (fun R : Matrix (Fin k) (Fin p) ℝ ↦
      (realWishartGram R)⁻¹ a b * (realWishartGram R)⁻¹ d e *
        (realWishartGram R)⁻¹ u v) (halfGaussianMatrix k p) := by
  let indices : Fin 3 → Fin p × Fin p := ![(a, b), (d, e), (u, v)]
  have h := integrable_inverseWishartEntryProduct_halfGaussianMatrix
    (k := k) (p := p) (q := 3) hgap indices
  apply h.congr
  filter_upwards [] with R
  simp [indices, inverseWishartEntryProduct, Fin.prod_univ_three]

/-! ## The cyclic second-order contraction -/

/-- The second-entry recursion contracted against `Tr(A²)`. -/
theorem halfGaussian_inverseWishart_traceTwo_steinRecursion_h8h10
    {k p : ℕ} (hgap : p + 8 ≤ k) :
    (inverseWishartEntryGap k p - 1) *
        (∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace ((realWishartGram R)⁻¹ ^ 2)
          ∂halfGaussianMatrix k p) =
      2 * (∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace (realWishartGram R)⁻¹ ∂halfGaussianMatrix k p) +
      (∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace (realWishartGram R)⁻¹ ^ 2
        ∂halfGaussianMatrix k p) := by
  let μ := halfGaussianMatrix k p
  let M1 := halfGaussianInverseWishartEntryMeanIntegral k p
  let M2 := halfGaussianInverseWishartSecondEntryIntegral k p
  have H := halfGaussian_inverseWishart_secondEntry_steinRecursion
    (k := k) (p := p) hgap
  have hsum :
      (∑ a : Fin p, ∑ b : Fin p,
        inverseWishartEntryGap k p * M2 a b b a) =
      ∑ a : Fin p, ∑ b : Fin p,
        (2 * M1 b a * realKroneckerDelta a b +
          M2 a b b a + M2 a a b b) := by
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    simpa only [add_comm] using H.entry_product_recursion a b b a
  have hcycle :
      (∑ a : Fin p, ∑ b : Fin p, M2 a b b a) =
      ∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace ((realWishartGram R)⁻¹ ^ 2) ∂μ := by
    dsimp only [M2, halfGaussianInverseWishartSecondEntryIntegral]
    rw [← integral_fintype_sum_two_h8h10 μ]
    · apply integral_congr_ae
      filter_upwards [] with R
      exact (trace_two_entrySum_h8h10 (realWishartGram R)⁻¹).symm
    · intro a b
      exact integrable_halfGaussian_inverseWishart_entry_two_h8h10
        (by omega) a b b a
  have hdiag :
      (∑ a : Fin p, ∑ b : Fin p, M2 a a b b) =
      ∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace (realWishartGram R)⁻¹ ^ 2 ∂μ := by
    dsimp only [M2, halfGaussianInverseWishartSecondEntryIntegral]
    rw [← integral_fintype_sum_two_h8h10 μ]
    · apply integral_congr_ae
      filter_upwards [] with R
      exact (trace_one_sq_entrySum_h8h10 (realWishartGram R)⁻¹).symm
    · intro a b
      exact integrable_halfGaussian_inverseWishart_entry_two_h8h10
        (by omega) a a b b
  have hdelta :
      (∑ a : Fin p, ∑ b : Fin p,
        2 * M1 b a * realKroneckerDelta a b) =
      2 * (∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace (realWishartGram R)⁻¹ ∂μ) := by
    have hone : (∑ a : Fin p, M1 a a) =
        ∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace (realWishartGram R)⁻¹ ∂μ := by
      dsimp only [M1, halfGaussianInverseWishartEntryMeanIntegral]
      rw [← integral_fintype_sum_one_h8h10 μ]
      · apply integral_congr_ae
        filter_upwards [] with R
        exact (trace_one_entrySum_h8h10 (realWishartGram R)⁻¹).symm
      · intro a
        exact integrable_halfGaussian_inverseWishart_entry_one_h8h10
          (by omega) a a
    rw [show (∑ a : Fin p, ∑ b : Fin p,
        2 * M1 b a * realKroneckerDelta a b) =
        2 * ∑ a : Fin p, M1 a a by
      simp [realKroneckerDelta, Finset.mul_sum]]
    rw [hone]
  have hrec :
      inverseWishartEntryGap k p *
          (∫ R : Matrix (Fin k) (Fin p) ℝ,
            Matrix.trace ((realWishartGram R)⁻¹ ^ 2) ∂μ) =
        2 * (∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace (realWishartGram R)⁻¹ ∂μ) +
        (∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace ((realWishartGram R)⁻¹ ^ 2) ∂μ) +
        (∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace (realWishartGram R)⁻¹ ^ 2 ∂μ) := by
    calc
      _ = ∑ a : Fin p, ∑ b : Fin p,
          inverseWishartEntryGap k p * M2 a b b a := by
        rw [← hcycle, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.mul_sum]
      _ = _ := by
        rw [hsum]
        simp_rw [Finset.sum_add_distrib]
        rw [hdelta, hcycle, hdiag]
  change (inverseWishartEntryGap k p - 1) * _ = _
  nlinarith [hrec]

/-! ## The two mixed third-order contractions -/

/-- The third-entry recursion contracted against `Tr(A) Tr(A²)`. -/
theorem halfGaussian_inverseWishart_traceOneTraceTwo_steinRecursion_h8h10
    {k p : ℕ} (hgap : p + 8 ≤ k) :
    inverseWishartEntryGap k p *
        (∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace (realWishartGram R)⁻¹ *
            Matrix.trace ((realWishartGram R)⁻¹ ^ 2)
          ∂halfGaussianMatrix k p) =
      2 * (p : ℝ) *
        (∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace ((realWishartGram R)⁻¹ ^ 2)
          ∂halfGaussianMatrix k p) +
      4 * (∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace ((realWishartGram R)⁻¹ ^ 3)
        ∂halfGaussianMatrix k p) := by
  let μ := halfGaussianMatrix k p
  let M2 := halfGaussianInverseWishartDoubleEntryIntegral k p
  let M3 := halfGaussianInverseWishartThirdEntryIntegral k p
  have hsum :
      (∑ a : Fin p, ∑ b : Fin p, ∑ d : Fin p,
        inverseWishartEntryGap k p * M3 b d d b a a) =
      ∑ a : Fin p, ∑ b : Fin p, ∑ d : Fin p,
        (2 * realKroneckerDelta a a * M2 b d d b +
          M3 b a a d d b + M3 b a a d d b +
          M3 b d d a a b + M3 b d d a a b) := by
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro d hd
    exact halfGaussian_inverseWishart_thirdEntry_steinRecursion
      hgap a a b d d b
  have hleft : (∑ a : Fin p, ∑ b : Fin p, ∑ d : Fin p,
      M3 b d d b a a) =
      ∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace (realWishartGram R)⁻¹ *
          Matrix.trace ((realWishartGram R)⁻¹ ^ 2) ∂μ := by
    dsimp only [M3, halfGaussianInverseWishartThirdEntryIntegral]
    rw [← integral_fintype_sum_three_h8h10 μ]
    · apply integral_congr_ae
      filter_upwards [] with R
      rw [trace_one_mul_trace_two_entrySum_h8h10]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro d hd
      ring
    · intro a b d
      exact integrable_halfGaussian_inverseWishart_entry_three_h8h10
        (by omega) b d d b a a
  have hdelta : (∑ a : Fin p, ∑ b : Fin p, ∑ d : Fin p,
      2 * realKroneckerDelta a a * M2 b d d b) =
      2 * (p : ℝ) * (∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace ((realWishartGram R)⁻¹ ^ 2) ∂μ) := by
    have hcycle : (∑ b : Fin p, ∑ d : Fin p, M2 b d d b) =
        ∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace ((realWishartGram R)⁻¹ ^ 2) ∂μ := by
      dsimp only [M2, halfGaussianInverseWishartDoubleEntryIntegral]
      rw [← integral_fintype_sum_two_h8h10 μ]
      · apply integral_congr_ae
        filter_upwards [] with R
        exact (trace_two_entrySum_h8h10 (realWishartGram R)⁻¹).symm
      · intro b d
        exact integrable_halfGaussian_inverseWishart_entry_two_h8h10
          (by omega) b d d b
    rw [show (∑ a : Fin p, ∑ b : Fin p, ∑ d : Fin p,
        2 * realKroneckerDelta a a * M2 b d d b) =
        2 * (p : ℝ) * (∑ b : Fin p, ∑ d : Fin p, M2 b d d b) by
      simp [realKroneckerDelta, Finset.mul_sum]
      ring]
    rw [hcycle]
  have hsplice1 : (∑ a : Fin p, ∑ b : Fin p, ∑ d : Fin p,
      M3 b a a d d b) =
      ∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace ((realWishartGram R)⁻¹ ^ 3) ∂μ := by
    dsimp only [M3, halfGaussianInverseWishartThirdEntryIntegral]
    rw [← integral_fintype_sum_three_h8h10 μ]
    · apply integral_congr_ae
      filter_upwards [] with R
      rw [trace_three_entrySum_h8h10]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro d hd
      rw [(realWishartGram_inv_isSymm R).apply b a,
        (realWishartGram_inv_isSymm R).apply d a,
        (realWishartGram_inv_isSymm R).apply b d]
      ring
    · intro a b d
      exact integrable_halfGaussian_inverseWishart_entry_three_h8h10
        (by omega) b a a d d b
  have hsplice2 : (∑ a : Fin p, ∑ b : Fin p, ∑ d : Fin p,
      M3 b d d a a b) =
      ∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace ((realWishartGram R)⁻¹ ^ 3) ∂μ := by
    dsimp only [M3, halfGaussianInverseWishartThirdEntryIntegral]
    rw [← integral_fintype_sum_three_h8h10 μ]
    · apply integral_congr_ae
      filter_upwards [] with R
      rw [trace_three_entrySum_h8h10]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro d hd
      ring
    · intro a b d
      exact integrable_halfGaussian_inverseWishart_entry_three_h8h10
        (by omega) b d d a a b
  rw [← hleft]
  simp only [Finset.mul_sum]
  rw [hsum]
  simp only [Finset.sum_add_distrib]
  rw [hdelta, hsplice1, hsplice2]
  ring

/-- The third-entry recursion contracted against `Tr(A³)`. -/
theorem halfGaussian_inverseWishart_traceThree_steinRecursion_h8h10
    {k p : ℕ} (hgap : p + 8 ≤ k) :
    (inverseWishartEntryGap k p - 2) *
        (∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace ((realWishartGram R)⁻¹ ^ 3)
          ∂halfGaussianMatrix k p) =
      2 * (∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace ((realWishartGram R)⁻¹ ^ 2)
        ∂halfGaussianMatrix k p) +
      2 * (∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace (realWishartGram R)⁻¹ *
          Matrix.trace ((realWishartGram R)⁻¹ ^ 2)
        ∂halfGaussianMatrix k p) := by
  let μ := halfGaussianMatrix k p
  let M2 := halfGaussianInverseWishartDoubleEntryIntegral k p
  let M3 := halfGaussianInverseWishartThirdEntryIntegral k p
  have hsum :
      (∑ a : Fin p, ∑ b : Fin p, ∑ d : Fin p,
        inverseWishartEntryGap k p * M3 a b b d d a) =
      ∑ a : Fin p, ∑ b : Fin p, ∑ d : Fin p,
        (2 * realKroneckerDelta d a * M2 a b b d +
          M3 a a d b b d + M3 a d a b b d +
          M3 a b b a d d + M3 a b b d a d) := by
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro d hd
    exact halfGaussian_inverseWishart_thirdEntry_steinRecursion
      hgap d a a b b d
  have hz : (∑ a : Fin p, ∑ b : Fin p, ∑ d : Fin p,
      M3 a b b d d a) =
      ∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace ((realWishartGram R)⁻¹ ^ 3) ∂μ := by
    dsimp only [M3, halfGaussianInverseWishartThirdEntryIntegral]
    rw [← integral_fintype_sum_three_h8h10 μ]
    · apply integral_congr_ae
      filter_upwards [] with R
      exact (trace_three_entrySum_h8h10 (realWishartGram R)⁻¹).symm
    · intro a b d
      exact integrable_halfGaussian_inverseWishart_entry_three_h8h10
        (by omega) a b b d d a
  have hy : (∑ a : Fin p, ∑ b : Fin p, ∑ d : Fin p,
      2 * realKroneckerDelta d a * M2 a b b d) =
      2 * (∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace ((realWishartGram R)⁻¹ ^ 2) ∂μ) := by
    have hcycle : (∑ a : Fin p, ∑ b : Fin p, M2 a b b a) =
        ∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace ((realWishartGram R)⁻¹ ^ 2) ∂μ := by
      dsimp only [M2, halfGaussianInverseWishartDoubleEntryIntegral]
      rw [← integral_fintype_sum_two_h8h10 μ]
      · apply integral_congr_ae
        filter_upwards [] with R
        exact (trace_two_entrySum_h8h10 (realWishartGram R)⁻¹).symm
      · intro a b
        exact integrable_halfGaussian_inverseWishart_entry_two_h8h10
          (by omega) a b b a
    rw [show (∑ a : Fin p, ∑ b : Fin p, ∑ d : Fin p,
        2 * realKroneckerDelta d a * M2 a b b d) =
        2 * (∑ a : Fin p, ∑ b : Fin p, M2 a b b a) by
      simp [realKroneckerDelta, Finset.mul_sum]]
    rw [hcycle]
  have hxy1 : (∑ a : Fin p, ∑ b : Fin p, ∑ d : Fin p,
      M3 a a d b b d) =
      ∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace (realWishartGram R)⁻¹ *
          Matrix.trace ((realWishartGram R)⁻¹ ^ 2) ∂μ := by
    dsimp only [M3, halfGaussianInverseWishartThirdEntryIntegral]
    rw [← integral_fintype_sum_three_h8h10 μ]
    · apply integral_congr_ae
      filter_upwards [] with R
      rw [trace_one_mul_trace_two_entrySum_h8h10]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro d hd
      ring
    · intro a b d
      exact integrable_halfGaussian_inverseWishart_entry_three_h8h10
        (by omega) a a d b b d
  have hxy2 : (∑ a : Fin p, ∑ b : Fin p, ∑ d : Fin p,
      M3 a b b a d d) =
      ∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace (realWishartGram R)⁻¹ *
          Matrix.trace ((realWishartGram R)⁻¹ ^ 2) ∂μ := by
    dsimp only [M3, halfGaussianInverseWishartThirdEntryIntegral]
    rw [← integral_fintype_sum_three_h8h10 μ]
    · apply integral_congr_ae
      filter_upwards [] with R
      exact (trace_one_mul_trace_two_alt_entrySum_h8h10
        (realWishartGram R)⁻¹).symm
    · intro a b d
      exact integrable_halfGaussian_inverseWishart_entry_three_h8h10
        (by omega) a b b a d d
  have hz1 : (∑ a : Fin p, ∑ b : Fin p, ∑ d : Fin p,
      M3 a d a b b d) =
      ∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace ((realWishartGram R)⁻¹ ^ 3) ∂μ := by
    dsimp only [M3, halfGaussianInverseWishartThirdEntryIntegral]
    rw [← integral_fintype_sum_three_h8h10 μ]
    · apply integral_congr_ae
      filter_upwards [] with R
      rw [trace_three_entrySum_h8h10]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro d hd
      rw [(realWishartGram_inv_isSymm R).apply d a]
      ring
    · intro a b d
      exact integrable_halfGaussian_inverseWishart_entry_three_h8h10
        (by omega) a d a b b d
  have hz2 : (∑ a : Fin p, ∑ b : Fin p, ∑ d : Fin p,
      M3 a b b d a d) =
      ∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace ((realWishartGram R)⁻¹ ^ 3) ∂μ := by
    dsimp only [M3, halfGaussianInverseWishartThirdEntryIntegral]
    rw [← integral_fintype_sum_three_h8h10 μ]
    · apply integral_congr_ae
      filter_upwards [] with R
      rw [trace_three_entrySum_h8h10]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro d hd
      rw [(realWishartGram_inv_isSymm R).apply a d]
    · intro a b d
      exact integrable_halfGaussian_inverseWishart_entry_three_h8h10
        (by omega) a b b d a d
  have hrec :
      inverseWishartEntryGap k p *
          (∫ R : Matrix (Fin k) (Fin p) ℝ,
            Matrix.trace ((realWishartGram R)⁻¹ ^ 3) ∂μ) =
        2 * (∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace ((realWishartGram R)⁻¹ ^ 2) ∂μ) +
        2 * (∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace (realWishartGram R)⁻¹ *
            Matrix.trace ((realWishartGram R)⁻¹ ^ 2) ∂μ) +
        2 * (∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace ((realWishartGram R)⁻¹ ^ 3) ∂μ) := by
    calc
      _ = ∑ a : Fin p, ∑ b : Fin p, ∑ d : Fin p,
          inverseWishartEntryGap k p * M3 a b b d d a := by
        rw [← hz, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b hb
        rw [Finset.mul_sum]
      _ = _ := by
        rw [hsum]
        simp_rw [Finset.sum_add_distrib]
        rw [hy, hxy1, hxy2, hz1, hz2]
        ring
  change (inverseWishartEntryGap k p - 2) * _ = _
  nlinarith [hrec]

/-! ## Degree-four trace words -/

private theorem trace_four_entrySum_h8h10
    {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) :
    Matrix.trace (A ^ 4) =
      ∑ a : Fin p, ∑ d : Fin p, ∑ c : Fin p, ∑ b : Fin p,
        A a b * A b c * A c d * A d a := by
  simp [Matrix.trace, Matrix.mul_apply, pow_succ, Finset.sum_mul]

private theorem trace_four_standard_entrySum_h8h10
    {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) :
    Matrix.trace (A ^ 4) =
      ∑ a : Fin p, ∑ b : Fin p, ∑ c : Fin p, ∑ d : Fin p,
        A a b * A b c * A c d * A d a := by
  rw [trace_four_entrySum_h8h10]
  apply Finset.sum_congr rfl
  intro a ha
  calc
    (∑ d : Fin p, ∑ c : Fin p, ∑ b : Fin p,
        A a b * A b c * A c d * A d a) =
      ∑ c : Fin p, ∑ d : Fin p, ∑ b : Fin p,
        A a b * A b c * A c d * A d a := by
        rw [Finset.sum_comm]
    _ = ∑ c : Fin p, ∑ b : Fin p, ∑ d : Fin p,
        A a b * A b c * A c d * A d a := by
        apply Finset.sum_congr rfl
        intro c hc
        rw [Finset.sum_comm]
    _ = ∑ b : Fin p, ∑ c : Fin p, ∑ d : Fin p,
        A a b * A b c * A c d * A d a := by
        rw [Finset.sum_comm]

private theorem trace_one_sq_mul_trace_two_entrySum_h8h10
    {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) :
    Matrix.trace A ^ 2 * Matrix.trace (A ^ 2) =
      ∑ a : Fin p, ∑ b : Fin p, ∑ d : Fin p, ∑ e : Fin p,
        A a a * A b b * (A d e * A e d) := by
  rw [trace_one_sq_entrySum_h8h10, trace_two_entrySum_h8h10,
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

private theorem trace_two_mul_trace_one_sq_alt_entrySum_h8h10
    {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) :
    Matrix.trace A ^ 2 * Matrix.trace (A ^ 2) =
      ∑ a : Fin p, ∑ b : Fin p, ∑ c : Fin p, ∑ d : Fin p,
        (A a b * A b a) * (A c c * A d d) := by
  rw [mul_comm, trace_two_entrySum_h8h10,
    trace_one_sq_entrySum_h8h10, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  rw [Finset.mul_sum]

private theorem trace_two_sq_entrySum_h8h10
    {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) :
    Matrix.trace (A ^ 2) ^ 2 =
      ∑ a : Fin p, ∑ b : Fin p, ∑ d : Fin p, ∑ e : Fin p,
        (A a b * A b a) * (A d e * A e d) := by
  rw [trace_two_entrySum_h8h10, pow_two, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mul_sum]

private theorem trace_one_mul_trace_three_entrySum_h8h10
    {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) :
    Matrix.trace A * Matrix.trace (A ^ 3) =
      ∑ a : Fin p, ∑ b : Fin p, ∑ d : Fin p, ∑ e : Fin p,
        A a a * (A b d * A d e * A e b) := by
  rw [trace_three_entrySum_h8h10]
  simp only [Matrix.trace, Matrix.diag_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mul_sum]

private theorem integral_fintype_sum_four_h8h10
    {X : Type*} [MeasurableSpace X] {p : ℕ} (mu : Measure X)
    (f : Fin p → Fin p → Fin p → Fin p → X → ℝ)
    (hf : ∀ a b d e, Integrable (f a b d e) mu) :
    (∫ x, ∑ a : Fin p, ∑ b : Fin p, ∑ d : Fin p, ∑ e : Fin p,
        f a b d e x ∂mu) =
      ∑ a : Fin p, ∑ b : Fin p, ∑ d : Fin p, ∑ e : Fin p,
        ∫ x, f a b d e x ∂mu := by
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

private theorem integrable_halfGaussian_inverseWishart_entry_four_h8h10
    {k p : ℕ} (hgap : p + 8 ≤ k)
    (a b d e u v x y : Fin p) :
    Integrable (fun R : Matrix (Fin k) (Fin p) ℝ ↦
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

/-! ## The three mixed fourth-order contractions -/

/-- The fourth-entry recursion contracted against
`Tr(A)^2 Tr(A^2)`. -/
theorem halfGaussian_inverseWishart_traceOneSqTraceTwo_steinRecursion_h8h10
    {k p : ℕ} (hgap : p + 10 ≤ k) :
    inverseWishartEntryGap k p *
        (∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace (realWishartGram R)⁻¹ ^ 2 *
            Matrix.trace ((realWishartGram R)⁻¹ ^ 2)
          ∂halfGaussianMatrix k p) =
      2 * (p : ℝ) *
        (∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace (realWishartGram R)⁻¹ *
            Matrix.trace ((realWishartGram R)⁻¹ ^ 2)
          ∂halfGaussianMatrix k p) +
      2 * (∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace ((realWishartGram R)⁻¹ ^ 2) ^ 2
        ∂halfGaussianMatrix k p) +
      4 * (∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace (realWishartGram R)⁻¹ *
          Matrix.trace ((realWishartGram R)⁻¹ ^ 3)
        ∂halfGaussianMatrix k p) := by
  let mu := halfGaussianMatrix k p
  let M3 := halfGaussianInverseWishartTripleEntryIntegral k p
  let M4 := halfGaussianInverseWishartFourthEntryIntegral k p
  have hsum :
      (∑ a : Fin p, ∑ b : Fin p, ∑ d : Fin p, ∑ e : Fin p,
        inverseWishartEntryGap k p * M4 b b d e e d a a) =
      ∑ a : Fin p, ∑ b : Fin p, ∑ d : Fin p, ∑ e : Fin p,
        (2 * realKroneckerDelta a a * M3 b b d e e d +
          M4 b a a b d e e d + M4 b a a b d e e d +
          M4 b b d a a e e d + M4 b b d a a e e d +
          M4 b b d e e a a d + M4 b b d e e a a d) := by
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro e he
    exact halfGaussian_inverseWishart_fourthEntry_steinRecursion
      hgap a a b b d e e d
  have hleft :
      (∑ a : Fin p, ∑ b : Fin p, ∑ d : Fin p, ∑ e : Fin p,
        M4 b b d e e d a a) =
      ∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace (realWishartGram R)⁻¹ ^ 2 *
          Matrix.trace ((realWishartGram R)⁻¹ ^ 2) ∂mu := by
    dsimp only [M4, halfGaussianInverseWishartFourthEntryIntegral]
    rw [← integral_fintype_sum_four_h8h10 mu]
    · apply integral_congr_ae
      filter_upwards [] with R
      rw [trace_one_sq_mul_trace_two_entrySum_h8h10]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro e he
      ring
    · intro a b d e
      exact integrable_halfGaussian_inverseWishart_entry_four_h8h10
        (by omega) b b d e e d a a
  have hxy :
      (∑ b : Fin p, ∑ d : Fin p, ∑ e : Fin p, M3 b b d e e d) =
      ∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace (realWishartGram R)⁻¹ *
          Matrix.trace ((realWishartGram R)⁻¹ ^ 2) ∂mu := by
    dsimp only [M3, halfGaussianInverseWishartTripleEntryIntegral]
    rw [← integral_fintype_sum_three_h8h10 mu]
    · apply integral_congr_ae
      filter_upwards [] with R
      rw [trace_one_mul_trace_two_entrySum_h8h10]
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro e he
      ring
    · intro b d e
      exact integrable_halfGaussian_inverseWishart_entry_three_h8h10
        (by omega) b b d e e d
  have hdelta :
      (∑ a : Fin p, ∑ b : Fin p, ∑ d : Fin p, ∑ e : Fin p,
        2 * realKroneckerDelta a a * M3 b b d e e d) =
      2 * (p : ℝ) * (∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace (realWishartGram R)⁻¹ *
          Matrix.trace ((realWishartGram R)⁻¹ ^ 2) ∂mu) := by
    rw [show (∑ a : Fin p, ∑ b : Fin p, ∑ d : Fin p, ∑ e : Fin p,
        2 * realKroneckerDelta a a * M3 b b d e e d) =
        2 * (p : ℝ) *
          (∑ b : Fin p, ∑ d : Fin p, ∑ e : Fin p, M3 b b d e e d) by
      simp [realKroneckerDelta, Finset.mul_sum]
      ring]
    rw [hxy]
  have hy2 :
      (∑ a : Fin p, ∑ b : Fin p, ∑ d : Fin p, ∑ e : Fin p,
        M4 b a a b d e e d) =
      ∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace ((realWishartGram R)⁻¹ ^ 2) ^ 2 ∂mu := by
    dsimp only [M4, halfGaussianInverseWishartFourthEntryIntegral]
    rw [← integral_fintype_sum_four_h8h10 mu]
    · apply integral_congr_ae
      filter_upwards [] with R
      rw [trace_two_sq_entrySum_h8h10, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro e he
      ring
    · intro a b d e
      exact integrable_halfGaussian_inverseWishart_entry_four_h8h10
        (by omega) b a a b d e e d
  have hxz1 :
      (∑ a : Fin p, ∑ b : Fin p, ∑ d : Fin p, ∑ e : Fin p,
        M4 b b d a a e e d) =
      ∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace (realWishartGram R)⁻¹ *
          Matrix.trace ((realWishartGram R)⁻¹ ^ 3) ∂mu := by
    dsimp only [M4, halfGaussianInverseWishartFourthEntryIntegral]
    rw [← integral_fintype_sum_four_h8h10 mu]
    · apply integral_congr_ae
      filter_upwards [] with R
      rw [trace_one_mul_trace_three_entrySum_h8h10, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro e he
      ring
    · intro a b d e
      exact integrable_halfGaussian_inverseWishart_entry_four_h8h10
        (by omega) b b d a a e e d
  have hxz2 :
      (∑ a : Fin p, ∑ b : Fin p, ∑ d : Fin p, ∑ e : Fin p,
        M4 b b d e e a a d) =
      ∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace (realWishartGram R)⁻¹ *
          Matrix.trace ((realWishartGram R)⁻¹ ^ 3) ∂mu := by
    dsimp only [M4, halfGaussianInverseWishartFourthEntryIntegral]
    rw [← integral_fintype_sum_four_h8h10 mu]
    · apply integral_congr_ae
      filter_upwards [] with R
      rw [trace_one_mul_trace_three_entrySum_h8h10, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b hb
      calc
        (∑ a : Fin p, ∑ d : Fin p, ∑ e : Fin p,
            (realWishartGram R)⁻¹ b b * (realWishartGram R)⁻¹ d e *
              (realWishartGram R)⁻¹ e a * (realWishartGram R)⁻¹ a d) =
          ∑ d : Fin p, ∑ a : Fin p, ∑ e : Fin p,
            (realWishartGram R)⁻¹ b b * (realWishartGram R)⁻¹ d e *
              (realWishartGram R)⁻¹ e a * (realWishartGram R)⁻¹ a d := by
            rw [Finset.sum_comm]
        _ = ∑ d : Fin p, ∑ e : Fin p, ∑ a : Fin p,
            (realWishartGram R)⁻¹ b b *
              ((realWishartGram R)⁻¹ d e *
                (realWishartGram R)⁻¹ e a *
                (realWishartGram R)⁻¹ a d) := by
            apply Finset.sum_congr rfl
            intro d hd
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro e he
            apply Finset.sum_congr rfl
            intro a ha
            ring
    · intro a b d e
      exact integrable_halfGaussian_inverseWishart_entry_four_h8h10
        (by omega) b b d e e a a d
  calc
    inverseWishartEntryGap k p *
        (∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace (realWishartGram R)⁻¹ ^ 2 *
            Matrix.trace ((realWishartGram R)⁻¹ ^ 2) ∂mu) =
      ∑ a : Fin p, ∑ b : Fin p, ∑ d : Fin p, ∑ e : Fin p,
        inverseWishartEntryGap k p * M4 b b d e e d a a := by
      rw [← hleft]
      simp_rw [Finset.mul_sum]
    _ = _ := by
      rw [hsum]
      simp_rw [Finset.sum_add_distrib]
      rw [hdelta, hy2, hxz1, hxz2]
      ring

/-- The fourth-entry recursion contracted against `Tr(A^2)^2`. -/
theorem halfGaussian_inverseWishart_traceTwoSq_steinRecursion_h8h10
    {k p : ℕ} (hgap : p + 10 ≤ k) :
    (inverseWishartEntryGap k p - 1) *
        (∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace ((realWishartGram R)⁻¹ ^ 2) ^ 2
          ∂halfGaussianMatrix k p) =
      2 * (∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace (realWishartGram R)⁻¹ *
          Matrix.trace ((realWishartGram R)⁻¹ ^ 2)
        ∂halfGaussianMatrix k p) +
      (∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace (realWishartGram R)⁻¹ ^ 2 *
          Matrix.trace ((realWishartGram R)⁻¹ ^ 2)
        ∂halfGaussianMatrix k p) +
      4 * (∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace ((realWishartGram R)⁻¹ ^ 4)
        ∂halfGaussianMatrix k p) := by
  let mu := halfGaussianMatrix k p
  let M3 := halfGaussianInverseWishartTripleEntryIntegral k p
  let M4 := halfGaussianInverseWishartFourthEntryIntegral k p
  have hsum :
      (∑ a : Fin p, ∑ b : Fin p, ∑ c : Fin p, ∑ d : Fin p,
        inverseWishartEntryGap k p * M4 a b b a c d d c) =
      ∑ a : Fin p, ∑ b : Fin p, ∑ c : Fin p, ∑ d : Fin p,
        (2 * realKroneckerDelta d c * M3 a b b a c d +
          M4 a c d b b a c d + M4 a d c b b a c d +
          M4 a b b c d a c d + M4 a b b d c a c d +
          M4 a b b a c c d d + M4 a b b a c d c d) := by
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro c hc
    apply Finset.sum_congr rfl
    intro d hd
    exact halfGaussian_inverseWishart_fourthEntry_steinRecursion
      hgap d c a b b a c d
  have hleft :
      (∑ a : Fin p, ∑ b : Fin p, ∑ c : Fin p, ∑ d : Fin p,
        M4 a b b a c d d c) =
      ∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace ((realWishartGram R)⁻¹ ^ 2) ^ 2 ∂mu := by
    dsimp only [M4, halfGaussianInverseWishartFourthEntryIntegral]
    rw [← integral_fintype_sum_four_h8h10 mu]
    · apply integral_congr_ae
      filter_upwards [] with R
      rw [trace_two_sq_entrySum_h8h10]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro c hc
      apply Finset.sum_congr rfl
      intro d hd
      ring
    · intro a b c d
      exact integrable_halfGaussian_inverseWishart_entry_four_h8h10
        (by omega) a b b a c d d c
  have hxy :
      (∑ a : Fin p, ∑ b : Fin p, ∑ c : Fin p, M3 a b b a c c) =
      ∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace (realWishartGram R)⁻¹ *
          Matrix.trace ((realWishartGram R)⁻¹ ^ 2) ∂mu := by
    dsimp only [M3, halfGaussianInverseWishartTripleEntryIntegral]
    rw [← integral_fintype_sum_three_h8h10 mu]
    · apply integral_congr_ae
      filter_upwards [] with R
      rw [trace_one_mul_trace_two_alt_entrySum_h8h10]
    · intro a b c
      exact integrable_halfGaussian_inverseWishart_entry_three_h8h10
        (by omega) a b b a c c
  have hdelta :
      (∑ a : Fin p, ∑ b : Fin p, ∑ c : Fin p, ∑ d : Fin p,
        2 * realKroneckerDelta d c * M3 a b b a c d) =
      2 * (∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace (realWishartGram R)⁻¹ *
          Matrix.trace ((realWishartGram R)⁻¹ ^ 2) ∂mu) := by
    rw [show (∑ a : Fin p, ∑ b : Fin p, ∑ c : Fin p, ∑ d : Fin p,
        2 * realKroneckerDelta d c * M3 a b b a c d) =
        2 * (∑ a : Fin p, ∑ b : Fin p, ∑ c : Fin p,
          M3 a b b a c c) by
      simp [realKroneckerDelta, Finset.mul_sum]]
    rw [hxy]
  have hq1 :
      (∑ a : Fin p, ∑ b : Fin p, ∑ c : Fin p, ∑ d : Fin p,
        M4 a c d b b a c d) =
      ∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace ((realWishartGram R)⁻¹ ^ 4) ∂mu := by
    dsimp only [M4, halfGaussianInverseWishartFourthEntryIntegral]
    rw [← integral_fintype_sum_four_h8h10 mu]
    · apply integral_congr_ae
      filter_upwards [] with R
      rw [trace_four_standard_entrySum_h8h10]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro c hc
      rw [(realWishartGram_inv_isSymm R).apply c a,
        (realWishartGram_inv_isSymm R).apply b d,
        (realWishartGram_inv_isSymm R).apply a b,
        (realWishartGram_inv_isSymm R).apply d c]
      ring
    · intro a b c d
      exact integrable_halfGaussian_inverseWishart_entry_four_h8h10
        (by omega) a c d b b a c d
  have hq2 :
      (∑ a : Fin p, ∑ b : Fin p, ∑ c : Fin p, ∑ d : Fin p,
        M4 a d c b b a c d) =
      ∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace ((realWishartGram R)⁻¹ ^ 4) ∂mu := by
    dsimp only [M4, halfGaussianInverseWishartFourthEntryIntegral]
    rw [← integral_fintype_sum_four_h8h10 mu]
    · apply integral_congr_ae
      filter_upwards [] with R
      rw [trace_four_standard_entrySum_h8h10]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro c hc
      apply Finset.sum_congr rfl
      intro d hd
      rw [(realWishartGram_inv_isSymm R).apply d a,
        (realWishartGram_inv_isSymm R).apply c b,
        (realWishartGram_inv_isSymm R).apply a b]
      ring
    · intro a b c d
      exact integrable_halfGaussian_inverseWishart_entry_four_h8h10
        (by omega) a d c b b a c d
  have hq3 :
      (∑ a : Fin p, ∑ b : Fin p, ∑ c : Fin p, ∑ d : Fin p,
        M4 a b b c d a c d) =
      ∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace ((realWishartGram R)⁻¹ ^ 4) ∂mu := by
    dsimp only [M4, halfGaussianInverseWishartFourthEntryIntegral]
    rw [← integral_fintype_sum_four_h8h10 mu]
    · apply integral_congr_ae
      filter_upwards [] with R
      rw [trace_four_standard_entrySum_h8h10]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro c hc
      apply Finset.sum_congr rfl
      intro d hd
      ring
    · intro a b c d
      exact integrable_halfGaussian_inverseWishart_entry_four_h8h10
        (by omega) a b b c d a c d
  have hq4 :
      (∑ a : Fin p, ∑ b : Fin p, ∑ c : Fin p, ∑ d : Fin p,
        M4 a b b d c a c d) =
      ∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace ((realWishartGram R)⁻¹ ^ 4) ∂mu := by
    dsimp only [M4, halfGaussianInverseWishartFourthEntryIntegral]
    rw [← integral_fintype_sum_four_h8h10 mu]
    · apply integral_congr_ae
      filter_upwards [] with R
      rw [trace_four_standard_entrySum_h8h10]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro c hc
      rw [(realWishartGram_inv_isSymm R).apply d c]
      ring
    · intro a b c d
      exact integrable_halfGaussian_inverseWishart_entry_four_h8h10
        (by omega) a b b d c a c d
  have hx2y :
      (∑ a : Fin p, ∑ b : Fin p, ∑ c : Fin p, ∑ d : Fin p,
        M4 a b b a c c d d) =
      ∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace (realWishartGram R)⁻¹ ^ 2 *
          Matrix.trace ((realWishartGram R)⁻¹ ^ 2) ∂mu := by
    dsimp only [M4, halfGaussianInverseWishartFourthEntryIntegral]
    rw [← integral_fintype_sum_four_h8h10 mu]
    · apply integral_congr_ae
      filter_upwards [] with R
      rw [trace_two_mul_trace_one_sq_alt_entrySum_h8h10]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro c hc
      apply Finset.sum_congr rfl
      intro d hd
      ring
    · intro a b c d
      exact integrable_halfGaussian_inverseWishart_entry_four_h8h10
        (by omega) a b b a c c d d
  have hy2 :
      (∑ a : Fin p, ∑ b : Fin p, ∑ c : Fin p, ∑ d : Fin p,
        M4 a b b a c d c d) =
      ∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace ((realWishartGram R)⁻¹ ^ 2) ^ 2 ∂mu := by
    dsimp only [M4, halfGaussianInverseWishartFourthEntryIntegral]
    rw [← integral_fintype_sum_four_h8h10 mu]
    · apply integral_congr_ae
      filter_upwards [] with R
      rw [trace_two_sq_entrySum_h8h10]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro c hc
      apply Finset.sum_congr rfl
      intro d hd
      rw [(realWishartGram_inv_isSymm R).apply d c]
      ring
    · intro a b c d
      exact integrable_halfGaussian_inverseWishart_entry_four_h8h10
        (by omega) a b b a c d c d
  have hrec :
      inverseWishartEntryGap k p *
          (∫ R : Matrix (Fin k) (Fin p) ℝ,
            Matrix.trace ((realWishartGram R)⁻¹ ^ 2) ^ 2 ∂mu) =
        2 * (∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace (realWishartGram R)⁻¹ *
            Matrix.trace ((realWishartGram R)⁻¹ ^ 2) ∂mu) +
        4 * (∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace ((realWishartGram R)⁻¹ ^ 4) ∂mu) +
        (∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace (realWishartGram R)⁻¹ ^ 2 *
            Matrix.trace ((realWishartGram R)⁻¹ ^ 2) ∂mu) +
        (∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace ((realWishartGram R)⁻¹ ^ 2) ^ 2 ∂mu) := by
    calc
      _ = ∑ a : Fin p, ∑ b : Fin p, ∑ c : Fin p, ∑ d : Fin p,
          inverseWishartEntryGap k p * M4 a b b a c d d c := by
        rw [← hleft]
        simp_rw [Finset.mul_sum]
      _ = _ := by
        rw [hsum]
        simp_rw [Finset.sum_add_distrib]
        rw [hdelta, hq1, hq2, hq3, hq4, hx2y, hy2]
        ring
  change (inverseWishartEntryGap k p - 1) * _ = _
  nlinarith [hrec]

/-- The fourth-entry recursion contracted against `Tr(A) Tr(A^3)`. -/
theorem halfGaussian_inverseWishart_traceOneTraceThree_steinRecursion_h8h10
    {k p : ℕ} (hgap : p + 10 ≤ k) :
    inverseWishartEntryGap k p *
        (∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace (realWishartGram R)⁻¹ *
            Matrix.trace ((realWishartGram R)⁻¹ ^ 3)
          ∂halfGaussianMatrix k p) =
      2 * (p : ℝ) *
        (∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace ((realWishartGram R)⁻¹ ^ 3)
          ∂halfGaussianMatrix k p) +
      6 * (∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace ((realWishartGram R)⁻¹ ^ 4)
        ∂halfGaussianMatrix k p) := by
  let mu := halfGaussianMatrix k p
  let M3 := halfGaussianInverseWishartTripleEntryIntegral k p
  let M4 := halfGaussianInverseWishartFourthEntryIntegral k p
  have hsum :
      (∑ a : Fin p, ∑ b : Fin p, ∑ c : Fin p, ∑ d : Fin p,
        inverseWishartEntryGap k p * M4 b c c d d b a a) =
      ∑ a : Fin p, ∑ b : Fin p, ∑ c : Fin p, ∑ d : Fin p,
        (2 * realKroneckerDelta a a * M3 b c c d d b +
          M4 b a a c c d d b + M4 b a a c c d d b +
          M4 b c c a a d d b + M4 b c c a a d d b +
          M4 b c c d d a a b + M4 b c c d d a a b) := by
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro c hc
    apply Finset.sum_congr rfl
    intro d hd
    exact halfGaussian_inverseWishart_fourthEntry_steinRecursion
      hgap a a b c c d d b
  have hleft :
      (∑ a : Fin p, ∑ b : Fin p, ∑ c : Fin p, ∑ d : Fin p,
        M4 b c c d d b a a) =
      ∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace (realWishartGram R)⁻¹ *
          Matrix.trace ((realWishartGram R)⁻¹ ^ 3) ∂mu := by
    dsimp only [M4, halfGaussianInverseWishartFourthEntryIntegral]
    rw [← integral_fintype_sum_four_h8h10 mu]
    · apply integral_congr_ae
      filter_upwards [] with R
      rw [trace_one_mul_trace_three_entrySum_h8h10]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro c hc
      apply Finset.sum_congr rfl
      intro d hd
      ring
    · intro a b c d
      exact integrable_halfGaussian_inverseWishart_entry_four_h8h10
        (by omega) b c c d d b a a
  have hz :
      (∑ b : Fin p, ∑ c : Fin p, ∑ d : Fin p, M3 b c c d d b) =
      ∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace ((realWishartGram R)⁻¹ ^ 3) ∂mu := by
    dsimp only [M3, halfGaussianInverseWishartTripleEntryIntegral]
    rw [← integral_fintype_sum_three_h8h10 mu]
    · apply integral_congr_ae
      filter_upwards [] with R
      rw [trace_three_entrySum_h8h10]
    · intro b c d
      exact integrable_halfGaussian_inverseWishart_entry_three_h8h10
        (by omega) b c c d d b
  have hdelta :
      (∑ a : Fin p, ∑ b : Fin p, ∑ c : Fin p, ∑ d : Fin p,
        2 * realKroneckerDelta a a * M3 b c c d d b) =
      2 * (p : ℝ) * (∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace ((realWishartGram R)⁻¹ ^ 3) ∂mu) := by
    rw [show (∑ a : Fin p, ∑ b : Fin p, ∑ c : Fin p, ∑ d : Fin p,
        2 * realKroneckerDelta a a * M3 b c c d d b) =
        2 * (p : ℝ) *
          (∑ b : Fin p, ∑ c : Fin p, ∑ d : Fin p, M3 b c c d d b) by
      simp [realKroneckerDelta, Finset.mul_sum]
      ring]
    rw [hz]
  have hq1 :
      (∑ a : Fin p, ∑ b : Fin p, ∑ c : Fin p, ∑ d : Fin p,
        M4 b a a c c d d b) =
      ∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace ((realWishartGram R)⁻¹ ^ 4) ∂mu := by
    dsimp only [M4, halfGaussianInverseWishartFourthEntryIntegral]
    rw [← integral_fintype_sum_four_h8h10 mu]
    · apply integral_congr_ae
      filter_upwards [] with R
      rw [trace_four_standard_entrySum_h8h10]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro c hc
      conv_lhs =>
        rw [((realWishartGram_inv_isSymm R).apply a c).symm,
          ((realWishartGram_inv_isSymm R).apply d b).symm]
      conv_rhs =>
        rw [(realWishartGram_inv_isSymm R).apply b a,
          (realWishartGram_inv_isSymm R).apply c d]
      ring
    · intro a b c d
      exact integrable_halfGaussian_inverseWishart_entry_four_h8h10
        (by omega) b a a c c d d b
  have hq2 :
      (∑ a : Fin p, ∑ b : Fin p, ∑ c : Fin p, ∑ d : Fin p,
        M4 b c c a a d d b) =
      ∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace ((realWishartGram R)⁻¹ ^ 4) ∂mu := by
    dsimp only [M4, halfGaussianInverseWishartFourthEntryIntegral]
    rw [← integral_fintype_sum_four_h8h10 mu]
    · apply integral_congr_ae
      filter_upwards [] with R
      rw [trace_four_standard_entrySum_h8h10, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.sum_comm]
    · intro a b c d
      exact integrable_halfGaussian_inverseWishart_entry_four_h8h10
        (by omega) b c c a a d d b
  have hq3 :
      (∑ a : Fin p, ∑ b : Fin p, ∑ c : Fin p, ∑ d : Fin p,
        M4 b c c d d a a b) =
      ∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace ((realWishartGram R)⁻¹ ^ 4) ∂mu := by
    dsimp only [M4, halfGaussianInverseWishartFourthEntryIntegral]
    rw [← integral_fintype_sum_four_h8h10 mu]
    · apply integral_congr_ae
      filter_upwards [] with R
      rw [trace_four_standard_entrySum_h8h10]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro c hc
      apply Finset.sum_congr rfl
      intro d hd
      ring
    · intro a b c d
      exact integrable_halfGaussian_inverseWishart_entry_four_h8h10
        (by omega) b c c d d a a b
  calc
    inverseWishartEntryGap k p *
        (∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace (realWishartGram R)⁻¹ *
            Matrix.trace ((realWishartGram R)⁻¹ ^ 3) ∂mu) =
      ∑ a : Fin p, ∑ b : Fin p, ∑ c : Fin p, ∑ d : Fin p,
        inverseWishartEntryGap k p * M4 b c c d d b a a := by
      rw [← hleft]
      simp_rw [Finset.mul_sum]
    _ = _ := by
      rw [hsum]
      simp_rw [Finset.sum_add_distrib]
      rw [hdelta, hq1, hq2, hq3]
      ring

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08
