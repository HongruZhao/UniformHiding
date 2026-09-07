import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.H14_DenominatorFourthTracePolynomialBounds
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.H14_MatsumotoTraceFourReductionConditional
import Mathlib.Tactic

/-!
# Direct trace contraction of the inverse-Wishart fourth-entry recursion

This module stays below every H3--H18 endpoint.  It contracts the audited
seven-term entry recursion into the scalar fourth-trace recurrence.  The four
remaining trace partitions are then controlled by the already checked PSD
trace contractions.  No literature atom, H6 contract, endpoint, or raw H14
trace-two majorant is used.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators MatrixOrder

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08

noncomputable section

open LogdetLean.GramHafnian
open LogdetLean.GramHafnian.Wishart
open LogdetLean.GramHafnian.UltimateHiding.DenseScore
open Matrix Unitary

set_option maxHeartbeats 3600000

/-! ## Finite trace contractions -/

private theorem trace_pow_three_eq_cycleSum
    {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) :
    Matrix.trace (A ^ 3) =
      ∑ a : Fin p, ∑ c : Fin p, ∑ b : Fin p,
        A a b * A b c * A c a := by
  simp [Matrix.trace, Matrix.mul_apply, pow_succ, Finset.sum_mul]

private theorem trace_pow_four_eq_cycleSum
    {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) :
    Matrix.trace (A ^ 4) =
      ∑ a : Fin p, ∑ d : Fin p, ∑ c : Fin p, ∑ b : Fin p,
        A a b * A b c * A c d * A d a := by
  simp [Matrix.trace, Matrix.mul_apply, pow_succ, Finset.sum_mul]

private theorem trace_mul_trace_three_eq_entrySum
    {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) :
    Matrix.trace A * Matrix.trace (A ^ 3) =
      ∑ d : Fin p, ∑ a : Fin p, ∑ c : Fin p, ∑ b : Fin p,
        A d d * (A a b * A b c * A c a) := by
  rw [trace_pow_three_eq_cycleSum]
  simp only [Matrix.trace, Matrix.diag_apply]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  rw [Finset.mul_sum]

private theorem trace_pow_two_eq_cycleSum
    {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) :
    Matrix.trace (A ^ 2) =
      ∑ a : Fin p, ∑ b : Fin p, A a b * A b a := by
  simp [Matrix.trace, Matrix.mul_apply, pow_two]

private theorem trace_two_sq_eq_entrySum
    {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) :
    Matrix.trace (A ^ 2) ^ 2 =
      ∑ a : Fin p, ∑ b : Fin p, ∑ c : Fin p, ∑ d : Fin p,
        (A a b * A b a) * (A c d * A d c) := by
  rw [trace_pow_two_eq_cycleSum, pow_two, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  rw [Finset.mul_sum]

private theorem traceFour_firstSplice_eq
    {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) (hA : A.IsSymm) :
    (∑ a : Fin p, ∑ d : Fin p, ∑ c : Fin p, ∑ b : Fin p,
        A a a * A d b * A b c * A c d) =
      Matrix.trace A * Matrix.trace (A ^ 3) := by
  calc
    (∑ a : Fin p, ∑ d : Fin p, ∑ c : Fin p, ∑ b : Fin p,
        A a a * A d b * A b c * A c d) =
        ∑ a : Fin p, A a a *
          (∑ d : Fin p, ∑ c : Fin p, ∑ b : Fin p,
            A d b * A b c * A c d) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c hc
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      ring
    _ = ∑ a : Fin p, A a a * Matrix.trace (A ^ 3) := by
      rw [trace_pow_three_eq_cycleSum]
    _ = Matrix.trace A * Matrix.trace (A ^ 3) := by
      simp [Matrix.trace, Finset.sum_mul]

private theorem traceFour_secondSplice_eq
    {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) (hA : A.IsSymm) :
    (∑ a : Fin p, ∑ d : Fin p, ∑ c : Fin p, ∑ b : Fin p,
        A a d * A a b * A b c * A c d) = Matrix.trace (A ^ 4) := by
  rw [trace_pow_four_eq_cycleSum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro b hb
  have hsymm : ∀ i j, A j i = A i j := Matrix.IsSymm.ext_iff.mp hA
  rw [hsymm d a]
  ring

private theorem traceFour_thirdSplice_eq
    {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) (hA : A.IsSymm) :
    (∑ a : Fin p, ∑ d : Fin p, ∑ c : Fin p, ∑ b : Fin p,
        A a b * A b a * A d c * A c d) =
      Matrix.trace (A ^ 2) ^ 2 := by
  rw [trace_two_sq_eq_entrySum]
  rw [show (∑ a : Fin p, ∑ d : Fin p, ∑ c : Fin p, ∑ b : Fin p,
      A a b * A b a * A d c * A c d) =
      ∑ a : Fin p, ∑ b : Fin p, ∑ c : Fin p, ∑ d : Fin p,
        A a b * A b a * A c d * A d c by
    apply Finset.sum_congr rfl
    intro a ha
    calc
      (∑ d : Fin p, ∑ c : Fin p, ∑ b : Fin p,
          A a b * A b a * A d c * A c d) =
          ∑ d : Fin p, ∑ b : Fin p, ∑ c : Fin p,
            A a b * A b a * A d c * A c d := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [Finset.sum_comm]
      _ = ∑ b : Fin p, ∑ d : Fin p, ∑ c : Fin p,
          A a b * A b a * A d c * A c d := by
        rw [Finset.sum_comm]
      _ = ∑ b : Fin p, ∑ c : Fin p, ∑ d : Fin p,
          A a b * A b a * A c d * A d c := by
        apply Finset.sum_congr rfl
        intro b hb
        rfl]
  simp only [mul_assoc]

private theorem traceFour_fourthSplice_eq
    {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) (hA : A.IsSymm) :
    (∑ a : Fin p, ∑ d : Fin p, ∑ c : Fin p, ∑ b : Fin p,
        A a b * A b d * A a c * A c d) = Matrix.trace (A ^ 4) := by
  rw [show (∑ a : Fin p, ∑ d : Fin p, ∑ c : Fin p, ∑ b : Fin p,
      A a b * A b d * A a c * A c d) =
      ∑ a : Fin p, ∑ c : Fin p, ∑ d : Fin p, ∑ b : Fin p,
        A a b * A b d * A a c * A c d by
    apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.sum_comm]]
  rw [trace_pow_four_eq_cycleSum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro b hb
  have hsymm : ∀ i j, A j i = A i j := Matrix.IsSymm.ext_iff.mp hA
  rw [hsymm c a, hsymm d c]
  ring

private theorem traceFour_fifthSplice_eq
    {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) (hA : A.IsSymm) :
    (∑ a : Fin p, ∑ d : Fin p, ∑ c : Fin p, ∑ b : Fin p,
        A a b * A b c * A c a * A d d) =
      Matrix.trace A * Matrix.trace (A ^ 3) := by
  rw [trace_mul_trace_three_eq_entrySum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro b hb
  ring

private theorem traceFour_sixthSplice_eq
    {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) (hA : A.IsSymm) :
    (∑ a : Fin p, ∑ d : Fin p, ∑ c : Fin p, ∑ b : Fin p,
        A a b * A b c * A c d * A a d) = Matrix.trace (A ^ 4) := by
  rw [trace_pow_four_eq_cycleSum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro b hb
  have hsymm : ∀ i j, A j i = A i j := Matrix.IsSymm.ext_iff.mp hA
  rw [hsymm d a]

private theorem traceFour_deltaSplice_eq
    {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) :
    (∑ a : Fin p, ∑ d : Fin p, ∑ c : Fin p, ∑ b : Fin p,
        2 * realKroneckerDelta d a * (A a b * A b c * A c d)) =
      2 * Matrix.trace (A ^ 3) := by
  rw [trace_pow_three_eq_cycleSum]
  simp [realKroneckerDelta, Finset.sum_mul, Finset.mul_sum]

/-! ## Integrable finite-sum contraction -/

private theorem integral_fintype_sum_four
    {X : Type*} [MeasurableSpace X] {p : ℕ} (μ : Measure X)
    (f : Fin p → Fin p → Fin p → Fin p → X → ℝ)
    (hf : ∀ a d c b, Integrable (f a d c b) μ) :
    (∫ x, ∑ a : Fin p, ∑ d : Fin p, ∑ c : Fin p, ∑ b : Fin p,
        f a d c b x ∂μ) =
      ∑ a : Fin p, ∑ d : Fin p, ∑ c : Fin p, ∑ b : Fin p,
        ∫ x, f a d c b x ∂μ := by
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro a ha
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro d hd
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro c hc
        rw [integral_finsetSum]
        intro b hb
        exact hf a d c b
      · intro c hc
        exact integrable_finsetSum Finset.univ fun b hb ↦ hf a d c b
    · intro d hd
      exact integrable_finsetSum Finset.univ fun c hc ↦
        integrable_finsetSum Finset.univ fun b hb ↦ hf a d c b
  · intro a ha
    exact integrable_finsetSum Finset.univ fun d hd ↦
      integrable_finsetSum Finset.univ fun c hc ↦
        integrable_finsetSum Finset.univ fun b hb ↦ hf a d c b

private theorem integrable_halfGaussian_inverseWishart_entryProduct_four_cycle
    {k p : ℕ} (hgap : p + 8 ≤ k) (a d c b : Fin p) :
    Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        (realWishartGram R)⁻¹ a b * (realWishartGram R)⁻¹ b c *
          (realWishartGram R)⁻¹ c d * (realWishartGram R)⁻¹ d a)
      (halfGaussianMatrix k p) := by
  let indices : Fin 4 → Fin p × Fin p :=
    ![(a, b), (b, c), (c, d), (d, a)]
  have hbase := integrable_inverseWishartEntryProduct_halfGaussianMatrix
    (k := k) (p := p) (q := 4) hgap indices
  apply hbase.congr
  filter_upwards [] with R
  simp [indices, inverseWishartEntryProduct, Fin.prod_univ_four]

/-- Fourth inverse-Gram trace integrability from the checked entry-product
engine. -/
theorem integrable_halfGaussian_inverseWishart_trace_four
    {k p : ℕ} (hgap : p + 8 ≤ k) :
    Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        Matrix.trace (((realWishartGram R)⁻¹) ^ 4))
      (halfGaussianMatrix k p) := by
  rw [show (fun R : Matrix (Fin k) (Fin p) ℝ ↦
      Matrix.trace (((realWishartGram R)⁻¹) ^ 4)) =
      fun R ↦ ∑ a : Fin p, ∑ d : Fin p, ∑ c : Fin p, ∑ b : Fin p,
        (realWishartGram R)⁻¹ a b * (realWishartGram R)⁻¹ b c *
          (realWishartGram R)⁻¹ c d * (realWishartGram R)⁻¹ d a by
    funext R
    exact trace_pow_four_eq_cycleSum (realWishartGram R)⁻¹]
  exact integrable_finsetSum Finset.univ fun a ha ↦
    integrable_finsetSum Finset.univ fun d hd ↦
      integrable_finsetSum Finset.univ fun c hc ↦
        integrable_finsetSum Finset.univ fun b hb ↦
          integrable_halfGaussian_inverseWishart_entryProduct_four_cycle
            hgap a d c b

private theorem integrable_halfGaussian_inverseWishart_entryProduct_three_cycle
    {k p : ℕ} (hgap : p + 6 ≤ k) (a c b : Fin p) :
    Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        (realWishartGram R)⁻¹ a b * (realWishartGram R)⁻¹ b c *
          (realWishartGram R)⁻¹ c a)
      (halfGaussianMatrix k p) := by
  let indices : Fin 3 → Fin p × Fin p := ![(a, b), (b, c), (c, a)]
  have hbase := integrable_inverseWishartEntryProduct_halfGaussianMatrix
    (k := k) (p := p) (q := 3) hgap indices
  apply hbase.congr
  filter_upwards [] with R
  simp [indices, inverseWishartEntryProduct, Fin.prod_univ_three]

/-- Exact trace-four contraction of the seven-term entry recursion. -/
theorem halfGaussian_inverseWishart_traceFour_steinRecursion
    {k p : ℕ} (hgap : p + 10 ≤ k) :
    inverseWishartEntryGap k p *
        (∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace (((realWishartGram R)⁻¹) ^ 4)
          ∂halfGaussianMatrix k p) =
      2 * (∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace (((realWishartGram R)⁻¹) ^ 3)
          ∂halfGaussianMatrix k p) +
      2 * (∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace ((realWishartGram R)⁻¹) *
            Matrix.trace (((realWishartGram R)⁻¹) ^ 3)
          ∂halfGaussianMatrix k p) +
      (∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace (((realWishartGram R)⁻¹) ^ 2) ^ 2
          ∂halfGaussianMatrix k p) +
      3 * (∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace (((realWishartGram R)⁻¹) ^ 4)
          ∂halfGaussianMatrix k p) := by
  let μ := halfGaussianMatrix k p
  let M3 := halfGaussianInverseWishartTripleEntryIntegral k p
  let M4 := halfGaussianInverseWishartFourthEntryIntegral k p
  have h3 (a d c b : Fin p) : Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        2 * realKroneckerDelta d a *
          ((realWishartGram R)⁻¹ a b * (realWishartGram R)⁻¹ b c *
            (realWishartGram R)⁻¹ c d)) μ := by
    have hbase := (integrable_inverseWishartEntryProduct_halfGaussianMatrix
      (k := k) (p := p) (q := 3) (by omega)
      (![(a, b), (b, c), (c, d)] : Fin 3 → Fin p × Fin p)).const_mul
        (2 * realKroneckerDelta d a)
    apply hbase.congr
    filter_upwards [] with R
    simp [inverseWishartEntryProduct, Fin.prod_univ_three]
  have h4 (u v x y z w i j : Fin p) : Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        (realWishartGram R)⁻¹ u v * (realWishartGram R)⁻¹ x y *
          (realWishartGram R)⁻¹ z w * (realWishartGram R)⁻¹ i j) μ := by
    let indices : Fin 4 → Fin p × Fin p :=
      ![(u, v), (x, y), (z, w), (i, j)]
    have hbase := integrable_inverseWishartEntryProduct_halfGaussianMatrix
      (k := k) (p := p) (q := 4) (by omega) indices
    apply hbase.congr
    filter_upwards [] with R
    simp [μ, indices, inverseWishartEntryProduct, Fin.prod_univ_four]
  have hsum :
      (∑ a : Fin p, ∑ d : Fin p, ∑ c : Fin p, ∑ b : Fin p,
        inverseWishartEntryGap k p * M4 a b b c c d d a) =
      ∑ a : Fin p, ∑ d : Fin p, ∑ c : Fin p, ∑ b : Fin p,
        (2 * realKroneckerDelta d a * M3 a b b c c d +
          M4 a a d b b c c d + M4 a d a b b c c d +
          M4 a b b a d c c d + M4 a b b d a c c d +
          M4 a b b c c a d d + M4 a b b c c d a d) := by
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro c hc
    apply Finset.sum_congr rfl
    intro b hb
    exact halfGaussian_inverseWishart_fourthEntry_steinRecursion
      hgap d a a b b c c d
  have hcycle :
      (∑ a : Fin p, ∑ d : Fin p, ∑ c : Fin p, ∑ b : Fin p,
        M4 a b b c c d d a) =
      ∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace (((realWishartGram R)⁻¹) ^ 4) ∂μ := by
    dsimp only [M4, halfGaussianInverseWishartFourthEntryIntegral]
    rw [← integral_fintype_sum_four μ]
    · apply integral_congr_ae
      filter_upwards [] with R
      exact (trace_pow_four_eq_cycleSum (realWishartGram R)⁻¹).symm
    · intro a d c b
      exact h4 a b b c c d d a
  have hdelta :
      (∑ a : Fin p, ∑ d : Fin p, ∑ c : Fin p, ∑ b : Fin p,
        2 * realKroneckerDelta d a * M3 a b b c c d) =
      2 * (∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace (((realWishartGram R)⁻¹) ^ 3) ∂μ) := by
    have hmove (a d c b : Fin p) :
        2 * realKroneckerDelta d a * M3 a b b c c d =
          ∫ R : Matrix (Fin k) (Fin p) ℝ,
            2 * realKroneckerDelta d a *
              ((realWishartGram R)⁻¹ a b * (realWishartGram R)⁻¹ b c *
                (realWishartGram R)⁻¹ c d) ∂μ := by
      dsimp only [M3, halfGaussianInverseWishartTripleEntryIntegral, μ]
      rw [integral_const_mul]
    simp_rw [hmove]
    rw [← integral_fintype_sum_four μ]
    · rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with R
      exact traceFour_deltaSplice_eq (realWishartGram R)⁻¹
    · intro a d c b
      exact h3 a d c b
  have hS1 :
      (∑ a : Fin p, ∑ d : Fin p, ∑ c : Fin p, ∑ b : Fin p,
        M4 a a d b b c c d) =
      ∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace ((realWishartGram R)⁻¹) *
          Matrix.trace (((realWishartGram R)⁻¹) ^ 3) ∂μ := by
    dsimp only [M4, halfGaussianInverseWishartFourthEntryIntegral]
    rw [← integral_fintype_sum_four μ]
    · apply integral_congr_ae
      filter_upwards [] with R
      exact traceFour_firstSplice_eq (realWishartGram R)⁻¹
        (realWishartGram_inv_isSymm R)
    · intro a d c b
      exact h4 a a d b b c c d
  have hS2 :
      (∑ a : Fin p, ∑ d : Fin p, ∑ c : Fin p, ∑ b : Fin p,
        M4 a d a b b c c d) =
      ∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace (((realWishartGram R)⁻¹) ^ 4) ∂μ := by
    dsimp only [M4, halfGaussianInverseWishartFourthEntryIntegral]
    rw [← integral_fintype_sum_four μ]
    · apply integral_congr_ae
      filter_upwards [] with R
      exact traceFour_secondSplice_eq (realWishartGram R)⁻¹
        (realWishartGram_inv_isSymm R)
    · intro a d c b
      exact h4 a d a b b c c d
  have hS3 :
      (∑ a : Fin p, ∑ d : Fin p, ∑ c : Fin p, ∑ b : Fin p,
        M4 a b b a d c c d) =
      ∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace (((realWishartGram R)⁻¹) ^ 2) ^ 2 ∂μ := by
    dsimp only [M4, halfGaussianInverseWishartFourthEntryIntegral]
    rw [← integral_fintype_sum_four μ]
    · apply integral_congr_ae
      filter_upwards [] with R
      exact traceFour_thirdSplice_eq (realWishartGram R)⁻¹
        (realWishartGram_inv_isSymm R)
    · intro a d c b
      exact h4 a b b a d c c d
  have hS4 :
      (∑ a : Fin p, ∑ d : Fin p, ∑ c : Fin p, ∑ b : Fin p,
        M4 a b b d a c c d) =
      ∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace (((realWishartGram R)⁻¹) ^ 4) ∂μ := by
    dsimp only [M4, halfGaussianInverseWishartFourthEntryIntegral]
    rw [← integral_fintype_sum_four μ]
    · apply integral_congr_ae
      filter_upwards [] with R
      exact traceFour_fourthSplice_eq (realWishartGram R)⁻¹
        (realWishartGram_inv_isSymm R)
    · intro a d c b
      exact h4 a b b d a c c d
  have hS5 :
      (∑ a : Fin p, ∑ d : Fin p, ∑ c : Fin p, ∑ b : Fin p,
        M4 a b b c c a d d) =
      ∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace ((realWishartGram R)⁻¹) *
          Matrix.trace (((realWishartGram R)⁻¹) ^ 3) ∂μ := by
    dsimp only [M4, halfGaussianInverseWishartFourthEntryIntegral]
    rw [← integral_fintype_sum_four μ]
    · apply integral_congr_ae
      filter_upwards [] with R
      exact traceFour_fifthSplice_eq (realWishartGram R)⁻¹
        (realWishartGram_inv_isSymm R)
    · intro a d c b
      exact h4 a b b c c a d d
  have hS6 :
      (∑ a : Fin p, ∑ d : Fin p, ∑ c : Fin p, ∑ b : Fin p,
        M4 a b b c c d a d) =
      ∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace (((realWishartGram R)⁻¹) ^ 4) ∂μ := by
    dsimp only [M4, halfGaussianInverseWishartFourthEntryIntegral]
    rw [← integral_fintype_sum_four μ]
    · apply integral_congr_ae
      filter_upwards [] with R
      exact traceFour_sixthSplice_eq (realWishartGram R)⁻¹
        (realWishartGram_inv_isSymm R)
    · intro a d c b
      exact h4 a b b c c d a d
  have hcoef :
      (∑ a : Fin p, ∑ d : Fin p, ∑ c : Fin p, ∑ b : Fin p,
        3 * M4 a b b c c d d a) =
      3 * (∑ a : Fin p, ∑ d : Fin p, ∑ c : Fin p, ∑ b : Fin p,
        M4 a b b c c d d a) := by
    simp only [Finset.mul_sum]
  change inverseWishartEntryGap k p *
      (∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace (((realWishartGram R)⁻¹) ^ 4) ∂μ) = _
  rw [← hcycle]
  simp only [Finset.mul_sum]
  rw [hsum]
  simp only [Finset.sum_add_distrib]
  rw [hdelta, hS1, hS2, hS3, hS4, hS5, hS6, hcoef, hcycle]
  dsimp only [μ]
  ring

/-! ## Spectral absorption of the lower trace partitions -/

private theorem trace_pow_eq_sum_eigenvalues_pow_u08
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A.PosSemidef) (r : ℕ) :
    Matrix.trace (A ^ r) =
      ∑ i, (hA.isHermitian.eigenvalues i) ^ r := by
  let hH : A.IsHermitian := hA.isHermitian
  conv_lhs => rw [hH.spectral_theorem]
  rw [← map_pow]
  rw [conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul]
  rw [Matrix.diagonal_pow, Matrix.trace_diagonal]
  rfl

/-- Scalar Young inequality used to absorb the cubic trace into the fourth
trace.  The slack `1` keeps all downstream arithmetic rational. -/
theorem nonneg_cube_le_half_fourth_add_one {x : ℝ} (hx : 0 ≤ x) :
    x ^ 3 ≤ (1 / 2 : ℝ) * x ^ 4 + 1 := by
  have hsquare : 0 ≤ (x - (3 / 2 : ℝ)) ^ 2 := sq_nonneg _
  have hfactor : 0 ≤ x ^ 2 + x + (3 / 4 : ℝ) := by
    nlinarith [sq_nonneg x]
  have hprod :
      0 ≤ (x - (3 / 2 : ℝ)) ^ 2 *
        (x ^ 2 + x + (3 / 4 : ℝ)) :=
    mul_nonneg hsquare hfactor
  nlinarith

/-- For a positive-semidefinite matrix, `tr(A^3)` is bounded by one half of
`tr(A^4)` plus the dimension. -/
theorem posSemidef_trace_three_le_half_trace_four_add_card
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A.PosSemidef) :
    Matrix.trace (A ^ 3) ≤
      (1 / 2 : ℝ) * Matrix.trace (A ^ 4) + (Fintype.card n : ℝ) := by
  rw [trace_pow_eq_sum_eigenvalues_pow_u08 A hA 3,
    trace_pow_eq_sum_eigenvalues_pow_u08 A hA 4]
  calc
    (∑ i, (hA.isHermitian.eigenvalues i) ^ 3) ≤
        ∑ i, ((1 / 2 : ℝ) * (hA.isHermitian.eigenvalues i) ^ 4 + 1) := by
      exact Finset.sum_le_sum fun i hi ↦
        nonneg_cube_le_half_fourth_add_one (hA.eigenvalues_nonneg i)
    _ = (1 / 2 : ℝ) *
          ∑ i, (hA.isHermitian.eigenvalues i) ^ 4 +
          (Fintype.card n : ℝ) := by
      simp [Finset.sum_add_distrib, Finset.mul_sum]

/-! ## Integrability of the contracted partitions -/

private theorem integrable_halfGaussian_inverseWishart_entryProduct_four
    {k p : ℕ} (hgap : p + 8 ≤ k)
    (u v x y z w i j : Fin p) :
    Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        (realWishartGram R)⁻¹ u v * (realWishartGram R)⁻¹ x y *
          (realWishartGram R)⁻¹ z w * (realWishartGram R)⁻¹ i j)
      (halfGaussianMatrix k p) := by
  let indices : Fin 4 → Fin p × Fin p :=
    ![(u, v), (x, y), (z, w), (i, j)]
  have hbase := integrable_inverseWishartEntryProduct_halfGaussianMatrix
    (k := k) (p := p) (q := 4) hgap indices
  apply hbase.congr
  filter_upwards [] with R
  simp [indices, inverseWishartEntryProduct, Fin.prod_univ_four]

/-- Raw inverse-Gram cubic trace integrability. -/
theorem integrable_halfGaussian_inverseWishart_trace_three
    {k p : ℕ} (hgap : p + 6 ≤ k) :
    Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        Matrix.trace (((realWishartGram R)⁻¹) ^ 3))
      (halfGaussianMatrix k p) := by
  rw [show (fun R : Matrix (Fin k) (Fin p) ℝ ↦
      Matrix.trace (((realWishartGram R)⁻¹) ^ 3)) =
      fun R ↦ ∑ a : Fin p, ∑ c : Fin p, ∑ b : Fin p,
        (realWishartGram R)⁻¹ a b * (realWishartGram R)⁻¹ b c *
          (realWishartGram R)⁻¹ c a by
    funext R
    exact trace_pow_three_eq_cycleSum (realWishartGram R)⁻¹]
  exact integrable_finsetSum Finset.univ fun a ha ↦
    integrable_finsetSum Finset.univ fun c hc ↦
      integrable_finsetSum Finset.univ fun b hb ↦
        integrable_halfGaussian_inverseWishart_entryProduct_three_cycle
          hgap a c b

/-- Raw `(1,3)` trace-partition integrability. -/
theorem integrable_halfGaussian_inverseWishart_trace_mul_trace_three
    {k p : ℕ} (hgap : p + 8 ≤ k) :
    Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        Matrix.trace (realWishartGram R)⁻¹ *
          Matrix.trace (((realWishartGram R)⁻¹) ^ 3))
      (halfGaussianMatrix k p) := by
  rw [show (fun R : Matrix (Fin k) (Fin p) ℝ ↦
      Matrix.trace (realWishartGram R)⁻¹ *
        Matrix.trace (((realWishartGram R)⁻¹) ^ 3)) =
      fun R ↦ ∑ d : Fin p, ∑ a : Fin p, ∑ c : Fin p, ∑ b : Fin p,
        (realWishartGram R)⁻¹ d d *
          ((realWishartGram R)⁻¹ a b * (realWishartGram R)⁻¹ b c *
            (realWishartGram R)⁻¹ c a) by
    funext R
    exact trace_mul_trace_three_eq_entrySum (realWishartGram R)⁻¹]
  exact integrable_finsetSum Finset.univ fun d hd ↦
    integrable_finsetSum Finset.univ fun a ha ↦
      integrable_finsetSum Finset.univ fun c hc ↦
        integrable_finsetSum Finset.univ fun b hb ↦ by
          have h := integrable_halfGaussian_inverseWishart_entryProduct_four
            hgap d d a b b c c a
          apply h.congr
          filter_upwards [] with R
          ring

/-- Raw `(2,2)` trace-partition integrability. -/
theorem integrable_halfGaussian_inverseWishart_trace_two_sq
    {k p : ℕ} (hgap : p + 8 ≤ k) :
    Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        Matrix.trace (((realWishartGram R)⁻¹) ^ 2) ^ 2)
      (halfGaussianMatrix k p) := by
  rw [show (fun R : Matrix (Fin k) (Fin p) ℝ ↦
      Matrix.trace (((realWishartGram R)⁻¹) ^ 2) ^ 2) =
      fun R ↦ ∑ a : Fin p, ∑ b : Fin p, ∑ c : Fin p, ∑ d : Fin p,
        ((realWishartGram R)⁻¹ a b * (realWishartGram R)⁻¹ b a) *
          ((realWishartGram R)⁻¹ c d * (realWishartGram R)⁻¹ d c) by
    funext R
    exact trace_two_sq_eq_entrySum (realWishartGram R)⁻¹]
  exact integrable_finsetSum Finset.univ fun a ha ↦
    integrable_finsetSum Finset.univ fun b hb ↦
      integrable_finsetSum Finset.univ fun c hc ↦
        integrable_finsetSum Finset.univ fun d hd ↦ by
          have h := integrable_halfGaussian_inverseWishart_entryProduct_four
            hgap a b b a c d d c
          apply h.congr
          filter_upwards [] with R
          ring

/-! ## Gap-normalized scalar recurrence -/

/-- The half-Gaussian inverse Gram normalized by half the degrees-of-freedom
gap.  Under the project substitution this is exactly Matsumoto's
identity-scale matrix `gamma W⁻¹`. -/
def steinNormalizedInverseWishartMatrix (k p : ℕ)
    (R : Matrix (Fin k) (Fin p) ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  (inverseWishartEntryGap k p / 2) • (realWishartGram R)⁻¹

private theorem trace_steinNormalized_pow
    (k p r : ℕ) (R : Matrix (Fin k) (Fin p) ℝ) :
    Matrix.trace ((steinNormalizedInverseWishartMatrix k p R) ^ r) =
      (inverseWishartEntryGap k p / 2) ^ r *
        Matrix.trace (((realWishartGram R)⁻¹) ^ r) := by
  simp [steinNormalizedInverseWishartMatrix, smul_pow,
    Matrix.trace_smul, smul_eq_mul]

/-- Exact scaled form of the contracted fourth-entry Stein recursion. -/
theorem halfGaussian_steinNormalized_traceFour_steinRecursion
    {k p : ℕ} (hgap : p + 10 ≤ k) :
    inverseWishartEntryGap k p *
        (∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace ((steinNormalizedInverseWishartMatrix k p R) ^ 4)
          ∂halfGaussianMatrix k p) =
      inverseWishartEntryGap k p *
        (∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace ((steinNormalizedInverseWishartMatrix k p R) ^ 3)
          ∂halfGaussianMatrix k p) +
      2 * (∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace (steinNormalizedInverseWishartMatrix k p R) *
            Matrix.trace ((steinNormalizedInverseWishartMatrix k p R) ^ 3)
          ∂halfGaussianMatrix k p) +
      (∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace ((steinNormalizedInverseWishartMatrix k p R) ^ 2) ^ 2
          ∂halfGaussianMatrix k p) +
      3 * (∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace ((steinNormalizedInverseWishartMatrix k p R) ^ 4)
          ∂halfGaussianMatrix k p) := by
  let c := inverseWishartEntryGap k p
  let g := c / 2
  have hraw := halfGaussian_inverseWishart_traceFour_steinRecursion hgap
  have h4 :
      (∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace ((steinNormalizedInverseWishartMatrix k p R) ^ 4)
          ∂halfGaussianMatrix k p) =
      g ^ 4 * (∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace (((realWishartGram R)⁻¹) ^ 4)
          ∂halfGaussianMatrix k p) := by
    simp_rw [trace_steinNormalized_pow]
    rw [integral_const_mul]
  have h3 :
      (∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace ((steinNormalizedInverseWishartMatrix k p R) ^ 3)
          ∂halfGaussianMatrix k p) =
      g ^ 3 * (∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace (((realWishartGram R)⁻¹) ^ 3)
          ∂halfGaussianMatrix k p) := by
    simp_rw [trace_steinNormalized_pow]
    rw [integral_const_mul]
  have h13 :
      (∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace (steinNormalizedInverseWishartMatrix k p R) *
          Matrix.trace ((steinNormalizedInverseWishartMatrix k p R) ^ 3)
          ∂halfGaussianMatrix k p) =
      g ^ 4 * (∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace (realWishartGram R)⁻¹ *
          Matrix.trace (((realWishartGram R)⁻¹) ^ 3)
          ∂halfGaussianMatrix k p) := by
    rw [show (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        Matrix.trace (steinNormalizedInverseWishartMatrix k p R) *
          Matrix.trace ((steinNormalizedInverseWishartMatrix k p R) ^ 3)) =
        fun R ↦ g ^ 4 *
          (Matrix.trace (realWishartGram R)⁻¹ *
            Matrix.trace (((realWishartGram R)⁻¹) ^ 3)) by
      funext R
      rw [trace_steinNormalized_pow]
      unfold steinNormalizedInverseWishartMatrix
      rw [Matrix.trace_smul]
      simp only [smul_eq_mul]
      dsimp only [g, c]
      ring]
    rw [integral_const_mul]
  have h22 :
      (∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace ((steinNormalizedInverseWishartMatrix k p R) ^ 2) ^ 2
          ∂halfGaussianMatrix k p) =
      g ^ 4 * (∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace (((realWishartGram R)⁻¹) ^ 2) ^ 2
          ∂halfGaussianMatrix k p) := by
    rw [show (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        Matrix.trace ((steinNormalizedInverseWishartMatrix k p R) ^ 2) ^ 2) =
        fun R ↦ g ^ 4 *
          Matrix.trace (((realWishartGram R)⁻¹) ^ 2) ^ 2 by
      funext R
      rw [trace_steinNormalized_pow]
      dsimp only [g, c]
      ring]
    rw [integral_const_mul]
  rw [h4, h3, h13, h22]
  dsimp only [g, c] at *
  linear_combination (inverseWishartEntryGap k p / 2) ^ 4 * hraw

/-- Integrability of the normalized fourth trace. -/
theorem integrable_halfGaussian_steinNormalized_trace_four
    {k p : ℕ} (hgap : p + 8 ≤ k) :
    Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        Matrix.trace ((steinNormalizedInverseWishartMatrix k p R) ^ 4))
      (halfGaussianMatrix k p) := by
  have hraw :=
    (integrable_halfGaussian_inverseWishart_trace_four hgap).const_mul
      ((inverseWishartEntryGap k p / 2) ^ 4)
  apply hraw.congr
  filter_upwards [] with R
  exact (trace_steinNormalized_pow k p 4 R).symm

/-- Integrability of the normalized cubic trace. -/
theorem integrable_halfGaussian_steinNormalized_trace_three
    {k p : ℕ} (hgap : p + 6 ≤ k) :
    Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        Matrix.trace ((steinNormalizedInverseWishartMatrix k p R) ^ 3))
      (halfGaussianMatrix k p) := by
  have hraw :=
    (integrable_halfGaussian_inverseWishart_trace_three hgap).const_mul
      ((inverseWishartEntryGap k p / 2) ^ 3)
  apply hraw.congr
  filter_upwards [] with R
  exact (trace_steinNormalized_pow k p 3 R).symm

/-- Integrability of the normalized `(1,3)` trace partition. -/
theorem integrable_halfGaussian_steinNormalized_trace_mul_trace_three
    {k p : ℕ} (hgap : p + 8 ≤ k) :
    Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        Matrix.trace (steinNormalizedInverseWishartMatrix k p R) *
          Matrix.trace ((steinNormalizedInverseWishartMatrix k p R) ^ 3))
      (halfGaussianMatrix k p) := by
  have hraw :=
    (integrable_halfGaussian_inverseWishart_trace_mul_trace_three hgap).const_mul
      ((inverseWishartEntryGap k p / 2) ^ 4)
  apply hraw.congr
  filter_upwards [] with R
  rw [trace_steinNormalized_pow]
  unfold steinNormalizedInverseWishartMatrix
  rw [Matrix.trace_smul]
  simp only [smul_eq_mul]
  ring

/-- Integrability of the normalized `(2,2)` trace partition. -/
theorem integrable_halfGaussian_steinNormalized_trace_two_sq
    {k p : ℕ} (hgap : p + 8 ≤ k) :
    Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        Matrix.trace ((steinNormalizedInverseWishartMatrix k p R) ^ 2) ^ 2)
      (halfGaussianMatrix k p) := by
  have hraw :=
    (integrable_halfGaussian_inverseWishart_trace_two_sq hgap).const_mul
      ((inverseWishartEntryGap k p / 2) ^ 4)
  apply hraw.congr
  filter_upwards [] with R
  rw [trace_steinNormalized_pow]
  ring

/-- Dimension-uniform fourth-trace bound for the gap-normalized inverse
Wishart matrix.  The hypothesis `15 p ≤ k` is precisely the denominator form
of the project's dense regime `16 N ≤ K`. -/
theorem halfGaussian_steinNormalized_trace_four_integral_le
    {k p : ℕ} (hp : 1 ≤ p) (hdense : 15 * p ≤ k) :
    (∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace ((steinNormalizedInverseWishartMatrix k p R) ^ 4)
          ∂halfGaussianMatrix k p) ≤
      128 * (p : ℝ) := by
  let μ := halfGaussianMatrix k p
  let c := inverseWishartEntryGap k p
  let B := steinNormalizedInverseWishartMatrix k p
  let X := ∫ R : Matrix (Fin k) (Fin p) ℝ, Matrix.trace ((B R) ^ 4) ∂μ
  let Y := ∫ R : Matrix (Fin k) (Fin p) ℝ, Matrix.trace ((B R) ^ 3) ∂μ
  let Z := ∫ R : Matrix (Fin k) (Fin p) ℝ,
    Matrix.trace (B R) * Matrix.trace ((B R) ^ 3) ∂μ
  let W := ∫ R : Matrix (Fin k) (Fin p) ℝ,
    Matrix.trace ((B R) ^ 2) ^ 2 ∂μ
  have hgap : p + 10 ≤ k := by omega
  have hpR : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hdenseR : (15 : ℝ) * (p : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast hdense
  have hcLower : 14 * (p : ℝ) - 1 ≤ c := by
    dsimp only [c, inverseWishartEntryGap]
    linarith
  have hc0 : 0 ≤ c := by linarith
  have hg0 : 0 ≤ c / 2 := by positivity
  have hB (R : Matrix (Fin k) (Fin p) ℝ) : (B R).PosSemidef := by
    dsimp only [B, steinNormalizedInverseWishartMatrix]
    exact (realWishartGram_inv_posSemidef R).smul hg0
  have hXint : Integrable (fun R : Matrix (Fin k) (Fin p) ℝ ↦
      Matrix.trace ((B R) ^ 4)) μ := by
    simpa only [B, μ] using
      (integrable_halfGaussian_steinNormalized_trace_four (by omega : p + 8 ≤ k))
  have hYint : Integrable (fun R : Matrix (Fin k) (Fin p) ℝ ↦
      Matrix.trace ((B R) ^ 3)) μ := by
    simpa only [B, μ] using
      (integrable_halfGaussian_steinNormalized_trace_three (by omega : p + 6 ≤ k))
  have hZint : Integrable (fun R : Matrix (Fin k) (Fin p) ℝ ↦
      Matrix.trace (B R) * Matrix.trace ((B R) ^ 3)) μ := by
    simpa only [B, μ] using
      (integrable_halfGaussian_steinNormalized_trace_mul_trace_three
        (by omega : p + 8 ≤ k))
  have hWint : Integrable (fun R : Matrix (Fin k) (Fin p) ℝ ↦
      Matrix.trace ((B R) ^ 2) ^ 2) μ := by
    simpa only [B, μ] using
      (integrable_halfGaussian_steinNormalized_trace_two_sq
        (by omega : p + 8 ≤ k))
  have hrec : c * X = c * Y + 2 * Z + W + 3 * X := by
    simpa only [c, X, Y, Z, W, B, μ] using
      halfGaussian_steinNormalized_traceFour_steinRecursion hgap
  have hX0 : 0 ≤ X := by
    dsimp only [X]
    exact integral_nonneg fun R ↦ posSemidef_trace_pow_nonneg (B R) (hB R) 4
  have hY : Y ≤ (1 / 2 : ℝ) * X + (p : ℝ) := by
    calc
      Y ≤ ∫ R : Matrix (Fin k) (Fin p) ℝ,
          ((1 / 2 : ℝ) * Matrix.trace ((B R) ^ 4) + (p : ℝ)) ∂μ := by
        apply integral_mono hYint
          ((hXint.const_mul (1 / 2 : ℝ)).add (integrable_const (p : ℝ)))
        intro R
        change Matrix.trace ((B R) ^ 3) ≤
          (1 / 2 : ℝ) * Matrix.trace ((B R) ^ 4) + (p : ℝ)
        simpa only [Fintype.card_fin] using
          posSemidef_trace_three_le_half_trace_four_add_card (B R) (hB R)
      _ = (1 / 2 : ℝ) * X + (p : ℝ) := by
        rw [integral_add (hXint.const_mul (1 / 2 : ℝ))
          (integrable_const (p : ℝ)), integral_const_mul, integral_const,
          probReal_univ]
        simp only [one_smul, X]
  have hZ : Z ≤ (p : ℝ) * X := by
    calc
      Z ≤ ∫ R : Matrix (Fin k) (Fin p) ℝ,
          (p : ℝ) * Matrix.trace ((B R) ^ 4) ∂μ := by
        apply integral_mono hZint (hXint.const_mul (p : ℝ))
        intro R
        simpa only [Fintype.card_fin] using
          posSemidef_trace_mul_trace_three_le_card_mul_trace_four (B R) (hB R)
      _ = (p : ℝ) * X := by
        rw [integral_const_mul]
  have hW : W ≤ (p : ℝ) * X := by
    calc
      W ≤ ∫ R : Matrix (Fin k) (Fin p) ℝ,
          (p : ℝ) * Matrix.trace ((B R) ^ 4) ∂μ := by
        apply integral_mono hWint (hXint.const_mul (p : ℝ))
        intro R
        simpa only [Fintype.card_fin] using
          posSemidef_trace_two_sq_le_card_mul_trace_four (B R) (hB R)
      _ = (p : ℝ) * X := by
        rw [integral_const_mul]
  have hCY : c * Y ≤ c * ((1 / 2 : ℝ) * X + (p : ℝ)) :=
    mul_le_mul_of_nonneg_left hY hc0
  have hAbsorb :
      (c / 2 - 3 * (p : ℝ) - 3) * X ≤ c * (p : ℝ) := by
    nlinarith [hrec, hCY, hZ, hW]
  have hcoefPos : 0 < c / 2 - 3 * (p : ℝ) - 3 := by
    nlinarith [hcLower, hpR]
  have hbracket : 0 ≤ 63 * c - 384 * (p : ℝ) - 384 := by
    nlinarith [hcLower, hpR]
  have hscale :
      c * (p : ℝ) ≤
        (c / 2 - 3 * (p : ℝ) - 3) * (128 * (p : ℝ)) := by
    have hp0 : 0 ≤ (p : ℝ) := by positivity
    nlinarith [mul_nonneg hp0 hbracket]
  have hmul :
      (c / 2 - 3 * (p : ℝ) - 3) * X ≤
        (c / 2 - 3 * (p : ℝ) - 3) * (128 * (p : ℝ)) :=
    hAbsorb.trans hscale
  have hfinal : X ≤ 128 * (p : ℝ) := by
    by_contra hnot
    have hdiff : 0 < X - 128 * (p : ℝ) := by linarith
    have hprod := mul_pos hcoefPos hdiff
    nlinarith [hmul, hprod]
  simpa only [X, B, μ] using hfinal

/-! ## Exact project substitution and denominator closure -/

/-- The project substitution identifies Matsumoto's identity-scale `gamma`
with half of the real inverse-Wishart entry gap.  This is an algebra theorem,
not a literature input. -/
theorem project_matsumotoGamma_eq_half_inverseWishartEntryGap
    {N K : ℕ} (hNK : N ≤ K) :
    matsumotoGamma N (matsumotoIntegerShapeBeta (K - N)) =
      inverseWishartEntryGap (K - N) N / 2 := by
  rw [projectDenominator_matsumotoGamma_eq hNK]
  unfold inverseWishartEntryGap
  rw [Nat.cast_sub hNK]
  ring

/-- The source-faithful identity-scale trace-four integrand is exactly the
gap-normalized Stein integrand after the separate project substitution. -/
theorem matsumotoIdentityScaledInverseTraceFour_eq_steinNormalized
    {N K : ℕ} (hNK : N ≤ K)
    (R : Matrix (Fin (K - N)) (Fin N) ℝ) :
    matsumotoIdentityScaledInverseTraceFour N K R =
      Matrix.trace
        ((steinNormalizedInverseWishartMatrix (K - N) N R) ^ 4) := by
  unfold matsumotoIdentityScaledInverseTraceFour
    steinNormalizedInverseWishartMatrix
  rw [project_matsumotoGamma_eq_half_inverseWishartEntryGap hNK]

/-- The previously conditional scalar trace-four producer is discharged
directly from the checked seven-term Stein recursion.  No literature axiom is
used. -/
theorem h14MatsumotoIdentityTraceFourBoundContract_internal (N K : ℕ) :
    H14MatsumotoIdentityTraceFourBoundContract N K := by
  constructor
  · intro hgap
    have hNK : N ≤ K := by omega
    have hraw := integrable_halfGaussian_steinNormalized_trace_four
      (k := K - N) (p := N) (by omega : N + 8 ≤ K - N)
    apply hraw.congr
    filter_upwards [] with R
    exact (matsumotoIdentityScaledInverseTraceFour_eq_steinNormalized hNK R).symm
  · intro hN hdense
    have hNK : N ≤ K := by omega
    have hdenseDen : 15 * N ≤ K - N := by omega
    have hbound := halfGaussian_steinNormalized_trace_four_integral_le
      (k := K - N) (p := N) hN hdenseDen
    have heq :
        (∫ R : Matrix (Fin (K - N)) (Fin N) ℝ,
          matsumotoIdentityScaledInverseTraceFour N K R
            ∂halfGaussianMatrix (K - N) N) =
        ∫ R : Matrix (Fin (K - N)) (Fin N) ℝ,
          Matrix.trace
            ((steinNormalizedInverseWishartMatrix (K - N) N R) ^ 4)
            ∂halfGaussianMatrix (K - N) N := by
      exact integral_congr_ae (Filter.Eventually.of_forall fun R ↦
        matsumotoIdentityScaledInverseTraceFour_eq_steinNormalized hNK R)
    rw [heq]
    exact hbound

/-- The exact denominator-only fourth-order Wick-polynomial contract.  This is
an unconditional non-endpoint producer for the radial H14 closure. -/
theorem h14DenominatorFourthTracePolynomialBounds_internal (N K : ℕ) :
    H14DenominatorFourthTracePolynomialBounds N K :=
  h14DenominatorFourthTracePolynomialBounds_of_matsumotoTraceFour_conditional
    (h14MatsumotoIdentityTraceFourBoundContract_internal N K)

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08
