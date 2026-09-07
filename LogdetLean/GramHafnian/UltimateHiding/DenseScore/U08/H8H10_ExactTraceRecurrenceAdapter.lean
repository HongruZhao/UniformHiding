import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.H8H10_MixedTraceSteinContractions
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.H8H10_ExactTraceRecurrenceAlgebra
import Mathlib.Tactic

/-!
# Exact H8/H10 inverse-Wishart trace-recurrence adapter

This file scales the raw half-Gaussian contractions to the project
normalization and transports them to the standard Gaussian denominator law.
It then instantiates the ten-equation scalar recurrence record used by the
foundations-only exact solver.
-/

open MeasureTheory ProbabilityTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08

noncomputable section

open LogdetLean.GramHafnian
open LogdetLean.GramHafnian.Wishart
open LogdetLean.GramHafnian.UltimateHiding.DenseScore

set_option maxHeartbeats 3600000
set_option maxRecDepth 100000

/-! ## Scaling identities -/

private theorem trace_steinNormalized_pow_h8h10
    (k p r : ℕ) (R : Matrix (Fin k) (Fin p) ℝ) :
    Matrix.trace ((steinNormalizedInverseWishartMatrix k p R) ^ r) =
      (inverseWishartEntryGap k p / 2) ^ r *
        Matrix.trace (((realWishartGram R)⁻¹) ^ r) := by
  simp [steinNormalizedInverseWishartMatrix, smul_pow,
    Matrix.trace_smul, smul_eq_mul]

private theorem trace_steinNormalized_h8h10
    (k p : ℕ) (R : Matrix (Fin k) (Fin p) ℝ) :
    Matrix.trace (steinNormalizedInverseWishartMatrix k p R) =
      (inverseWishartEntryGap k p / 2) *
        Matrix.trace (realWishartGram R)⁻¹ := by
  unfold steinNormalizedInverseWishartMatrix
  rw [Matrix.trace_smul]
  rfl

private theorem integral_steinNormalized_trace_pow_h8h10
    (k p r : ℕ) :
    (∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace ((steinNormalizedInverseWishartMatrix k p R) ^ r)
        ∂halfGaussianMatrix k p) =
      (inverseWishartEntryGap k p / 2) ^ r *
        (∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace (((realWishartGram R)⁻¹) ^ r)
          ∂halfGaussianMatrix k p) := by
  simp_rw [trace_steinNormalized_pow_h8h10]
  rw [integral_const_mul]

private theorem integral_steinNormalized_trace_one_pow_h8h10
    (k p r : ℕ) :
    (∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace (steinNormalizedInverseWishartMatrix k p R) ^ r
        ∂halfGaussianMatrix k p) =
      (inverseWishartEntryGap k p / 2) ^ r *
        (∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace (realWishartGram R)⁻¹ ^ r
          ∂halfGaussianMatrix k p) := by
  rw [show (fun R : Matrix (Fin k) (Fin p) ℝ ↦
      Matrix.trace (steinNormalizedInverseWishartMatrix k p R) ^ r) =
      fun R ↦ (inverseWishartEntryGap k p / 2) ^ r *
        Matrix.trace (realWishartGram R)⁻¹ ^ r by
    funext R
    rw [trace_steinNormalized_h8h10, mul_pow]]
  rw [integral_const_mul]

private theorem integral_steinNormalized_trace_h8h10
    (k p : ℕ) :
    (∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace (steinNormalizedInverseWishartMatrix k p R)
        ∂halfGaussianMatrix k p) =
      (inverseWishartEntryGap k p / 2) *
        (∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace (realWishartGram R)⁻¹
          ∂halfGaussianMatrix k p) := by
  simpa only [pow_one] using
    integral_steinNormalized_trace_one_pow_h8h10 k p 1

private theorem integral_steinNormalized_traceOnePow_mul_tracePow_h8h10
    (k p a r : ℕ) :
    (∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace (steinNormalizedInverseWishartMatrix k p R) ^ a *
          Matrix.trace ((steinNormalizedInverseWishartMatrix k p R) ^ r)
        ∂halfGaussianMatrix k p) =
      (inverseWishartEntryGap k p / 2) ^ (a + r) *
        (∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace (realWishartGram R)⁻¹ ^ a *
            Matrix.trace (((realWishartGram R)⁻¹) ^ r)
          ∂halfGaussianMatrix k p) := by
  rw [show (fun R : Matrix (Fin k) (Fin p) ℝ ↦
      Matrix.trace (steinNormalizedInverseWishartMatrix k p R) ^ a *
        Matrix.trace ((steinNormalizedInverseWishartMatrix k p R) ^ r)) =
      fun R ↦ (inverseWishartEntryGap k p / 2) ^ (a + r) *
        (Matrix.trace (realWishartGram R)⁻¹ ^ a *
          Matrix.trace (((realWishartGram R)⁻¹) ^ r)) by
    funext R
    rw [trace_steinNormalized_h8h10,
      trace_steinNormalized_pow_h8h10, mul_pow, pow_add]
    ring]
  rw [integral_const_mul]

private theorem integral_steinNormalized_trace_mul_tracePow_h8h10
    (k p r : ℕ) :
    (∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace (steinNormalizedInverseWishartMatrix k p R) *
          Matrix.trace ((steinNormalizedInverseWishartMatrix k p R) ^ r)
        ∂halfGaussianMatrix k p) =
      (inverseWishartEntryGap k p / 2) ^ (1 + r) *
        (∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace (realWishartGram R)⁻¹ *
            Matrix.trace (((realWishartGram R)⁻¹) ^ r)
          ∂halfGaussianMatrix k p) := by
  simpa only [pow_one] using
    integral_steinNormalized_traceOnePow_mul_tracePow_h8h10 k p 1 r

private theorem integral_steinNormalized_tracePow_sq_h8h10
    (k p r : ℕ) :
    (∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace ((steinNormalizedInverseWishartMatrix k p R) ^ r) ^ 2
        ∂halfGaussianMatrix k p) =
      (inverseWishartEntryGap k p / 2) ^ (2 * r) *
        (∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace (((realWishartGram R)⁻¹) ^ r) ^ 2
          ∂halfGaussianMatrix k p) := by
  rw [show (fun R : Matrix (Fin k) (Fin p) ℝ ↦
      Matrix.trace ((steinNormalizedInverseWishartMatrix k p R) ^ r) ^ 2) =
      fun R ↦ (inverseWishartEntryGap k p / 2) ^ (2 * r) *
        Matrix.trace (((realWishartGram R)⁻¹) ^ r) ^ 2 by
    funext R
    rw [trace_steinNormalized_pow_h8h10, mul_pow]
    ring_nf]
  rw [integral_const_mul]

/-! ## Normalized half-Gaussian recurrences -/

/-- Normalized version of the `Tr(A^2)` contraction. -/
theorem halfGaussian_steinNormalized_traceTwo_steinRecursion_h8h10
    {k p : ℕ} (hgap : p + 10 ≤ k) :
    (inverseWishartEntryGap k p - 1) *
        (∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace ((steinNormalizedInverseWishartMatrix k p R) ^ 2)
          ∂halfGaussianMatrix k p) =
      inverseWishartEntryGap k p *
        (∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace (steinNormalizedInverseWishartMatrix k p R)
          ∂halfGaussianMatrix k p) +
      (∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace (steinNormalizedInverseWishartMatrix k p R) ^ 2
        ∂halfGaussianMatrix k p) := by
  have hraw := halfGaussian_inverseWishart_traceTwo_steinRecursion_h8h10
    (k := k) (p := p) (by omega : p + 8 ≤ k)
  rw [integral_steinNormalized_trace_pow_h8h10,
    integral_steinNormalized_trace_h8h10,
    integral_steinNormalized_trace_one_pow_h8h10]
  linear_combination (inverseWishartEntryGap k p / 2) ^ 2 * hraw

/-- Normalized version of the `Tr(A) Tr(A^2)` contraction. -/
theorem halfGaussian_steinNormalized_traceOneTraceTwo_steinRecursion_h8h10
    {k p : ℕ} (hgap : p + 10 ≤ k) :
    inverseWishartEntryGap k p *
        (∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace (steinNormalizedInverseWishartMatrix k p R) *
            Matrix.trace ((steinNormalizedInverseWishartMatrix k p R) ^ 2)
          ∂halfGaussianMatrix k p) =
      (p : ℝ) * inverseWishartEntryGap k p *
        (∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace ((steinNormalizedInverseWishartMatrix k p R) ^ 2)
          ∂halfGaussianMatrix k p) +
      4 * (∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace ((steinNormalizedInverseWishartMatrix k p R) ^ 3)
        ∂halfGaussianMatrix k p) := by
  have hraw :=
    halfGaussian_inverseWishart_traceOneTraceTwo_steinRecursion_h8h10
      (k := k) (p := p) (by omega : p + 8 ≤ k)
  rw [integral_steinNormalized_trace_mul_tracePow_h8h10,
    integral_steinNormalized_trace_pow_h8h10,
    integral_steinNormalized_trace_pow_h8h10]
  linear_combination (inverseWishartEntryGap k p / 2) ^ 3 * hraw

/-- Normalized version of the `Tr(A^3)` contraction. -/
theorem halfGaussian_steinNormalized_traceThree_steinRecursion_h8h10
    {k p : ℕ} (hgap : p + 10 ≤ k) :
    (inverseWishartEntryGap k p - 2) *
        (∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace ((steinNormalizedInverseWishartMatrix k p R) ^ 3)
          ∂halfGaussianMatrix k p) =
      inverseWishartEntryGap k p *
        (∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace ((steinNormalizedInverseWishartMatrix k p R) ^ 2)
          ∂halfGaussianMatrix k p) +
      2 * (∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace (steinNormalizedInverseWishartMatrix k p R) *
          Matrix.trace ((steinNormalizedInverseWishartMatrix k p R) ^ 2)
        ∂halfGaussianMatrix k p) := by
  have hraw := halfGaussian_inverseWishart_traceThree_steinRecursion_h8h10
    (k := k) (p := p) (by omega : p + 8 ≤ k)
  rw [integral_steinNormalized_trace_pow_h8h10,
    integral_steinNormalized_trace_pow_h8h10,
    integral_steinNormalized_trace_mul_tracePow_h8h10]
  linear_combination (inverseWishartEntryGap k p / 2) ^ 3 * hraw

/-- Normalized version of the `Tr(A)^2 Tr(A^2)` contraction. -/
theorem halfGaussian_steinNormalized_traceOneSqTraceTwo_steinRecursion_h8h10
    {k p : ℕ} (hgap : p + 10 ≤ k) :
    inverseWishartEntryGap k p *
        (∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace (steinNormalizedInverseWishartMatrix k p R) ^ 2 *
            Matrix.trace ((steinNormalizedInverseWishartMatrix k p R) ^ 2)
          ∂halfGaussianMatrix k p) =
      (p : ℝ) * inverseWishartEntryGap k p *
        (∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace (steinNormalizedInverseWishartMatrix k p R) *
            Matrix.trace ((steinNormalizedInverseWishartMatrix k p R) ^ 2)
          ∂halfGaussianMatrix k p) +
      2 * (∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace ((steinNormalizedInverseWishartMatrix k p R) ^ 2) ^ 2
        ∂halfGaussianMatrix k p) +
      4 * (∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace (steinNormalizedInverseWishartMatrix k p R) *
          Matrix.trace ((steinNormalizedInverseWishartMatrix k p R) ^ 3)
        ∂halfGaussianMatrix k p) := by
  have hraw :=
    halfGaussian_inverseWishart_traceOneSqTraceTwo_steinRecursion_h8h10 hgap
  rw [integral_steinNormalized_traceOnePow_mul_tracePow_h8h10,
    integral_steinNormalized_trace_mul_tracePow_h8h10,
    integral_steinNormalized_tracePow_sq_h8h10,
    integral_steinNormalized_trace_mul_tracePow_h8h10]
  linear_combination (inverseWishartEntryGap k p / 2) ^ 4 * hraw

/-- Normalized version of the `Tr(A^2)^2` contraction. -/
theorem halfGaussian_steinNormalized_traceTwoSq_steinRecursion_h8h10
    {k p : ℕ} (hgap : p + 10 ≤ k) :
    (inverseWishartEntryGap k p - 1) *
        (∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace ((steinNormalizedInverseWishartMatrix k p R) ^ 2) ^ 2
          ∂halfGaussianMatrix k p) =
      inverseWishartEntryGap k p *
        (∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace (steinNormalizedInverseWishartMatrix k p R) *
            Matrix.trace ((steinNormalizedInverseWishartMatrix k p R) ^ 2)
          ∂halfGaussianMatrix k p) +
      (∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace (steinNormalizedInverseWishartMatrix k p R) ^ 2 *
          Matrix.trace ((steinNormalizedInverseWishartMatrix k p R) ^ 2)
        ∂halfGaussianMatrix k p) +
      4 * (∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace ((steinNormalizedInverseWishartMatrix k p R) ^ 4)
        ∂halfGaussianMatrix k p) := by
  have hraw := halfGaussian_inverseWishart_traceTwoSq_steinRecursion_h8h10 hgap
  rw [integral_steinNormalized_tracePow_sq_h8h10,
    integral_steinNormalized_trace_mul_tracePow_h8h10,
    integral_steinNormalized_traceOnePow_mul_tracePow_h8h10,
    integral_steinNormalized_trace_pow_h8h10]
  linear_combination (inverseWishartEntryGap k p / 2) ^ 4 * hraw

/-- Normalized version of the `Tr(A) Tr(A^3)` contraction. -/
theorem halfGaussian_steinNormalized_traceOneTraceThree_steinRecursion_h8h10
    {k p : ℕ} (hgap : p + 10 ≤ k) :
    inverseWishartEntryGap k p *
        (∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace (steinNormalizedInverseWishartMatrix k p R) *
            Matrix.trace ((steinNormalizedInverseWishartMatrix k p R) ^ 3)
          ∂halfGaussianMatrix k p) =
      (p : ℝ) * inverseWishartEntryGap k p *
        (∫ R : Matrix (Fin k) (Fin p) ℝ,
          Matrix.trace ((steinNormalizedInverseWishartMatrix k p R) ^ 3)
          ∂halfGaussianMatrix k p) +
      6 * (∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace ((steinNormalizedInverseWishartMatrix k p R) ^ 4)
        ∂halfGaussianMatrix k p) := by
  have hraw :=
    halfGaussian_inverseWishart_traceOneTraceThree_steinRecursion_h8h10 hgap
  rw [integral_steinNormalized_trace_mul_tracePow_h8h10,
    integral_steinNormalized_trace_pow_h8h10,
    integral_steinNormalized_trace_pow_h8h10]
  linear_combination (inverseWishartEntryGap k p / 2) ^ 4 * hraw

/-! ## Measurable project observables -/

private theorem measurable_realMatrix_mul_h8h10
    {X n : Type*} [MeasurableSpace X] [Fintype n]
    {A B : X → Matrix n n ℝ} (hA : Measurable A) (hB : Measurable B) :
    Measurable (fun x ↦ A x * B x) := by
  refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
  simp only [Matrix.mul_apply]
  exact Finset.measurable_sum _ fun k _ ↦
    ((measurable_pi_apply k).comp ((measurable_pi_apply i).comp hA)).mul
      ((measurable_pi_apply j).comp ((measurable_pi_apply k).comp hB))

private theorem measurable_realMatrix_pow_h8h10
    {X n : Type*} [MeasurableSpace X] [Fintype n] [DecidableEq n]
    {A : X → Matrix n n ℝ} (hA : Measurable A) :
    ∀ r : ℕ, Measurable (fun x ↦ (A x) ^ r)
  | 0 => by
      simpa using
        (measurable_const : Measurable (fun _ : X ↦ (1 : Matrix n n ℝ)))
  | r + 1 => by
      simpa only [pow_succ] using
        measurable_realMatrix_mul_h8h10 (measurable_realMatrix_pow_h8h10 hA r) hA

private theorem measurable_realMatrix_trace_h8h10
    {X n : Type*} [MeasurableSpace X] [Fintype n]
    {A : X → Matrix n n ℝ} (hA : Measurable A) :
    Measurable (fun x ↦ Matrix.trace (A x)) := by
  unfold Matrix.trace
  exact Finset.measurable_sum _ fun i _ ↦
    (measurable_pi_apply i).comp ((measurable_pi_apply i).comp hA)

private theorem measurable_matrix_trace_h8h10 (p : ℕ) :
    Measurable (fun D : Matrix (Fin p) (Fin p) ℝ ↦ Matrix.trace D) :=
  measurable_realMatrix_trace_h8h10 measurable_id

private theorem measurable_matrix_trace_pow_h8h10 (p r : ℕ) :
    Measurable
      (fun D : Matrix (Fin p) (Fin p) ℝ ↦ Matrix.trace (D ^ r)) :=
  measurable_realMatrix_trace_h8h10
    (measurable_realMatrix_pow_h8h10 measurable_id r)

/-! ## The ten concrete denominator moments -/

def h8H10TraceOneSqMoment (N K : ℕ) : ℝ :=
  ∫ B : H9InverseWishartSample N K,
    Matrix.trace (h9ScaledInverseWishart N K B) ^ 2
    ∂h9InverseWishartDenominatorLaw N K

def h8H10TraceTwoMoment (N K : ℕ) : ℝ :=
  ∫ B : H9InverseWishartSample N K,
    Matrix.trace ((h9ScaledInverseWishart N K B) ^ 2)
    ∂h9InverseWishartDenominatorLaw N K

def h8H10TraceOneCubeMoment (N K : ℕ) : ℝ :=
  ∫ B : H9InverseWishartSample N K,
    Matrix.trace (h9ScaledInverseWishart N K B) ^ 3
    ∂h9InverseWishartDenominatorLaw N K

def h8H10TraceOneTraceTwoMoment (N K : ℕ) : ℝ :=
  ∫ B : H9InverseWishartSample N K,
    Matrix.trace (h9ScaledInverseWishart N K B) *
      Matrix.trace ((h9ScaledInverseWishart N K B) ^ 2)
    ∂h9InverseWishartDenominatorLaw N K

def h8H10TraceThreeMoment (N K : ℕ) : ℝ :=
  ∫ B : H9InverseWishartSample N K,
    Matrix.trace ((h9ScaledInverseWishart N K B) ^ 3)
    ∂h9InverseWishartDenominatorLaw N K

def h8H10TraceOneFourthMoment (N K : ℕ) : ℝ :=
  ∫ B : H9InverseWishartSample N K,
    Matrix.trace (h9ScaledInverseWishart N K B) ^ 4
    ∂h9InverseWishartDenominatorLaw N K

def h8H10TraceOneSqTraceTwoMoment (N K : ℕ) : ℝ :=
  ∫ B : H9InverseWishartSample N K,
    Matrix.trace (h9ScaledInverseWishart N K B) ^ 2 *
      Matrix.trace ((h9ScaledInverseWishart N K B) ^ 2)
    ∂h9InverseWishartDenominatorLaw N K

def h8H10TraceTwoSqMoment (N K : ℕ) : ℝ :=
  ∫ B : H9InverseWishartSample N K,
    Matrix.trace ((h9ScaledInverseWishart N K B) ^ 2) ^ 2
    ∂h9InverseWishartDenominatorLaw N K

def h8H10TraceOneTraceThreeMoment (N K : ℕ) : ℝ :=
  ∫ B : H9InverseWishartSample N K,
    Matrix.trace (h9ScaledInverseWishart N K B) *
      Matrix.trace ((h9ScaledInverseWishart N K B) ^ 3)
    ∂h9InverseWishartDenominatorLaw N K

def h8H10TraceFourMoment (N K : ℕ) : ℝ :=
  ∫ B : H9InverseWishartSample N K,
    Matrix.trace ((h9ScaledInverseWishart N K B) ^ 4)
    ∂h9InverseWishartDenominatorLaw N K

/-! ## Standard-law recurrences -/

/-- Concrete project recurrence for the second matrix trace. -/
theorem h8H10ScaledInverse_traceTwo_steinRecursion_internal
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    (concreteCOEExponent N K - 1) * h8H10TraceTwoMoment N K =
      concreteCOEExponent N K * (N : ℝ) + h8H10TraceOneSqMoment N K := by
  have hNK : N ≤ K := by omega
  have hpk : N ≤ K - N := by omega
  have hc := inverseWishartEntryGap_project_eq_concreteCOEExponent_h9 hNK
  have hhalf := halfGaussian_steinNormalized_traceTwo_steinRecursion_h8h10
    (k := K - N) (p := N) (by omega : N + 10 ≤ K - N)
  have htrace := integral_steinNormalized_halfGaussian_eq_standardScaled_h9
    hpk (fun D : Matrix (Fin N) (Fin N) ℝ ↦ Matrix.trace D)
      (measurable_matrix_trace_h8h10 N)
  have htraceSq := integral_steinNormalized_halfGaussian_eq_standardScaled_h9
    hpk (fun D : Matrix (Fin N) (Fin N) ℝ ↦ Matrix.trace D ^ 2)
      ((measurable_matrix_trace_h8h10 N).pow_const 2)
  have hmatrixSq := integral_steinNormalized_halfGaussian_eq_standardScaled_h9
    hpk (fun D : Matrix (Fin N) (Fin N) ℝ ↦ Matrix.trace (D ^ 2))
      (measurable_matrix_trace_pow_h8h10 N 2)
  rw [hmatrixSq, htrace, htraceSq] at hhalf
  have hmean := integral_h9ScaledInverseTrace (by omega : 2 * N + 8 ≤ K)
  have hmean' :
      (∫ R : Matrix (Fin (K - N)) (Fin N) ℝ,
        Matrix.trace
          (concreteCOEExponent N K • (realWishartGram R)⁻¹)
        ∂standardRealGaussianMatrixMeasure (K - N) N) = (N : ℝ) := by
    simpa only [hc, h9InverseWishartDenominatorLaw,
      h9ScaledInverseWishart] using hmean
  rw [hc] at hhalf
  rw [hmean'] at hhalf
  simpa only [h9InverseWishartDenominatorLaw, h9ScaledInverseWishart,
    h8H10TraceTwoMoment, h8H10TraceOneSqMoment] using hhalf

/-- Concrete project recurrence for `Tr(D) Tr(D^2)`. -/
theorem h8H10ScaledInverse_traceOneTraceTwo_steinRecursion_internal
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    concreteCOEExponent N K * h8H10TraceOneTraceTwoMoment N K =
      concreteCOEExponent N K * (N : ℝ) * h8H10TraceTwoMoment N K +
        4 * h8H10TraceThreeMoment N K := by
  have hNK : N ≤ K := by omega
  have hpk : N ≤ K - N := by omega
  have hc := inverseWishartEntryGap_project_eq_concreteCOEExponent_h9 hNK
  have hhalf :=
    halfGaussian_steinNormalized_traceOneTraceTwo_steinRecursion_h8h10
      (k := K - N) (p := N) (by omega : N + 10 ≤ K - N)
  have hy := integral_steinNormalized_halfGaussian_eq_standardScaled_h9
    hpk (fun D : Matrix (Fin N) (Fin N) ℝ ↦ Matrix.trace (D ^ 2))
      (measurable_matrix_trace_pow_h8h10 N 2)
  have hxy := integral_steinNormalized_halfGaussian_eq_standardScaled_h9
    hpk (fun D : Matrix (Fin N) (Fin N) ℝ ↦
      Matrix.trace D * Matrix.trace (D ^ 2))
      ((measurable_matrix_trace_h8h10 N).mul
        (measurable_matrix_trace_pow_h8h10 N 2))
  have hz := integral_steinNormalized_halfGaussian_eq_standardScaled_h9
    hpk (fun D : Matrix (Fin N) (Fin N) ℝ ↦ Matrix.trace (D ^ 3))
      (measurable_matrix_trace_pow_h8h10 N 3)
  rw [hxy, hy, hz] at hhalf
  simp only [hc, h9InverseWishartDenominatorLaw, h9ScaledInverseWishart,
    h8H10TraceOneTraceTwoMoment, h8H10TraceTwoMoment,
    h8H10TraceThreeMoment] at hhalf ⊢
  ring_nf at hhalf ⊢
  exact hhalf

/-- Concrete project recurrence for the third matrix trace. -/
theorem h8H10ScaledInverse_traceThree_steinRecursion_internal
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    (concreteCOEExponent N K - 2) * h8H10TraceThreeMoment N K =
      concreteCOEExponent N K * h8H10TraceTwoMoment N K +
        2 * h8H10TraceOneTraceTwoMoment N K := by
  have hNK : N ≤ K := by omega
  have hpk : N ≤ K - N := by omega
  have hc := inverseWishartEntryGap_project_eq_concreteCOEExponent_h9 hNK
  have hhalf := halfGaussian_steinNormalized_traceThree_steinRecursion_h8h10
    (k := K - N) (p := N) (by omega : N + 10 ≤ K - N)
  have hy := integral_steinNormalized_halfGaussian_eq_standardScaled_h9
    hpk (fun D : Matrix (Fin N) (Fin N) ℝ ↦ Matrix.trace (D ^ 2))
      (measurable_matrix_trace_pow_h8h10 N 2)
  have hxy := integral_steinNormalized_halfGaussian_eq_standardScaled_h9
    hpk (fun D : Matrix (Fin N) (Fin N) ℝ ↦
      Matrix.trace D * Matrix.trace (D ^ 2))
      ((measurable_matrix_trace_h8h10 N).mul
        (measurable_matrix_trace_pow_h8h10 N 2))
  have hz := integral_steinNormalized_halfGaussian_eq_standardScaled_h9
    hpk (fun D : Matrix (Fin N) (Fin N) ℝ ↦ Matrix.trace (D ^ 3))
      (measurable_matrix_trace_pow_h8h10 N 3)
  rw [hz, hy, hxy] at hhalf
  simpa only [hc, h9InverseWishartDenominatorLaw, h9ScaledInverseWishart,
    h8H10TraceThreeMoment, h8H10TraceTwoMoment,
    h8H10TraceOneTraceTwoMoment] using hhalf

/-- Concrete project recurrence for `Tr(D)^2 Tr(D^2)`. -/
theorem h8H10ScaledInverse_traceOneSqTraceTwo_steinRecursion_internal
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    concreteCOEExponent N K * h8H10TraceOneSqTraceTwoMoment N K =
      concreteCOEExponent N K * (N : ℝ) *
          h8H10TraceOneTraceTwoMoment N K +
        2 * h8H10TraceTwoSqMoment N K +
        4 * h8H10TraceOneTraceThreeMoment N K := by
  have hNK : N ≤ K := by omega
  have hpk : N ≤ K - N := by omega
  have hc := inverseWishartEntryGap_project_eq_concreteCOEExponent_h9 hNK
  have hhalf :=
    halfGaussian_steinNormalized_traceOneSqTraceTwo_steinRecursion_h8h10
      (k := K - N) (p := N) (by omega : N + 10 ≤ K - N)
  have hxy := integral_steinNormalized_halfGaussian_eq_standardScaled_h9
    hpk (fun D : Matrix (Fin N) (Fin N) ℝ ↦
      Matrix.trace D * Matrix.trace (D ^ 2))
      ((measurable_matrix_trace_h8h10 N).mul
        (measurable_matrix_trace_pow_h8h10 N 2))
  have hx2y := integral_steinNormalized_halfGaussian_eq_standardScaled_h9
    hpk (fun D : Matrix (Fin N) (Fin N) ℝ ↦
      Matrix.trace D ^ 2 * Matrix.trace (D ^ 2))
      ((measurable_matrix_trace_h8h10 N).pow_const 2 |>.mul
        (measurable_matrix_trace_pow_h8h10 N 2))
  have hy2 := integral_steinNormalized_halfGaussian_eq_standardScaled_h9
    hpk (fun D : Matrix (Fin N) (Fin N) ℝ ↦ Matrix.trace (D ^ 2) ^ 2)
      ((measurable_matrix_trace_pow_h8h10 N 2).pow_const 2)
  have hxz := integral_steinNormalized_halfGaussian_eq_standardScaled_h9
    hpk (fun D : Matrix (Fin N) (Fin N) ℝ ↦
      Matrix.trace D * Matrix.trace (D ^ 3))
      ((measurable_matrix_trace_h8h10 N).mul
        (measurable_matrix_trace_pow_h8h10 N 3))
  rw [hx2y, hxy, hy2, hxz] at hhalf
  simp only [hc, h9InverseWishartDenominatorLaw, h9ScaledInverseWishart,
    h8H10TraceOneSqTraceTwoMoment, h8H10TraceOneTraceTwoMoment,
    h8H10TraceTwoSqMoment, h8H10TraceOneTraceThreeMoment] at hhalf ⊢
  ring_nf at hhalf ⊢
  exact hhalf

/-- Concrete project recurrence for `Tr(D^2)^2`. -/
theorem h8H10ScaledInverse_traceTwoSq_steinRecursion_internal
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    (concreteCOEExponent N K - 1) * h8H10TraceTwoSqMoment N K =
      concreteCOEExponent N K * h8H10TraceOneTraceTwoMoment N K +
        h8H10TraceOneSqTraceTwoMoment N K + 4 * h8H10TraceFourMoment N K := by
  have hNK : N ≤ K := by omega
  have hpk : N ≤ K - N := by omega
  have hc := inverseWishartEntryGap_project_eq_concreteCOEExponent_h9 hNK
  have hhalf := halfGaussian_steinNormalized_traceTwoSq_steinRecursion_h8h10
    (k := K - N) (p := N) (by omega : N + 10 ≤ K - N)
  have hxy := integral_steinNormalized_halfGaussian_eq_standardScaled_h9
    hpk (fun D : Matrix (Fin N) (Fin N) ℝ ↦
      Matrix.trace D * Matrix.trace (D ^ 2))
      ((measurable_matrix_trace_h8h10 N).mul
        (measurable_matrix_trace_pow_h8h10 N 2))
  have hx2y := integral_steinNormalized_halfGaussian_eq_standardScaled_h9
    hpk (fun D : Matrix (Fin N) (Fin N) ℝ ↦
      Matrix.trace D ^ 2 * Matrix.trace (D ^ 2))
      ((measurable_matrix_trace_h8h10 N).pow_const 2 |>.mul
        (measurable_matrix_trace_pow_h8h10 N 2))
  have hy2 := integral_steinNormalized_halfGaussian_eq_standardScaled_h9
    hpk (fun D : Matrix (Fin N) (Fin N) ℝ ↦ Matrix.trace (D ^ 2) ^ 2)
      ((measurable_matrix_trace_pow_h8h10 N 2).pow_const 2)
  have hq := integral_steinNormalized_halfGaussian_eq_standardScaled_h9
    hpk (fun D : Matrix (Fin N) (Fin N) ℝ ↦ Matrix.trace (D ^ 4))
      (measurable_matrix_trace_pow_h8h10 N 4)
  rw [hy2, hxy, hx2y, hq] at hhalf
  simpa only [hc, h9InverseWishartDenominatorLaw, h9ScaledInverseWishart,
    h8H10TraceTwoSqMoment, h8H10TraceOneTraceTwoMoment,
    h8H10TraceOneSqTraceTwoMoment, h8H10TraceFourMoment] using hhalf

/-- Concrete project recurrence for `Tr(D) Tr(D^3)`. -/
theorem h8H10ScaledInverse_traceOneTraceThree_steinRecursion_internal
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    concreteCOEExponent N K * h8H10TraceOneTraceThreeMoment N K =
      concreteCOEExponent N K * (N : ℝ) * h8H10TraceThreeMoment N K +
        6 * h8H10TraceFourMoment N K := by
  have hNK : N ≤ K := by omega
  have hpk : N ≤ K - N := by omega
  have hc := inverseWishartEntryGap_project_eq_concreteCOEExponent_h9 hNK
  have hhalf :=
    halfGaussian_steinNormalized_traceOneTraceThree_steinRecursion_h8h10
      (k := K - N) (p := N) (by omega : N + 10 ≤ K - N)
  have hz := integral_steinNormalized_halfGaussian_eq_standardScaled_h9
    hpk (fun D : Matrix (Fin N) (Fin N) ℝ ↦ Matrix.trace (D ^ 3))
      (measurable_matrix_trace_pow_h8h10 N 3)
  have hxz := integral_steinNormalized_halfGaussian_eq_standardScaled_h9
    hpk (fun D : Matrix (Fin N) (Fin N) ℝ ↦
      Matrix.trace D * Matrix.trace (D ^ 3))
      ((measurable_matrix_trace_h8h10 N).mul
        (measurable_matrix_trace_pow_h8h10 N 3))
  have hq := integral_steinNormalized_halfGaussian_eq_standardScaled_h9
    hpk (fun D : Matrix (Fin N) (Fin N) ℝ ↦ Matrix.trace (D ^ 4))
      (measurable_matrix_trace_pow_h8h10 N 4)
  rw [hxz, hz, hq] at hhalf
  simp only [hc, h9InverseWishartDenominatorLaw, h9ScaledInverseWishart,
    h8H10TraceOneTraceThreeMoment, h8H10TraceThreeMoment,
    h8H10TraceFourMoment] at hhalf ⊢
  ring_nf at hhalf ⊢
  exact hhalf

/-- Concrete project recurrence for the fourth matrix trace. -/
theorem h8H10ScaledInverse_traceFour_steinRecursion_internal
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    (concreteCOEExponent N K - 3) * h8H10TraceFourMoment N K =
      concreteCOEExponent N K * h8H10TraceThreeMoment N K +
        2 * h8H10TraceOneTraceThreeMoment N K + h8H10TraceTwoSqMoment N K := by
  have hNK : N ≤ K := by omega
  have hpk : N ≤ K - N := by omega
  have hc := inverseWishartEntryGap_project_eq_concreteCOEExponent_h9 hNK
  have hhalf := halfGaussian_steinNormalized_traceFour_steinRecursion
    (k := K - N) (p := N) (by omega : N + 10 ≤ K - N)
  have hz := integral_steinNormalized_halfGaussian_eq_standardScaled_h9
    hpk (fun D : Matrix (Fin N) (Fin N) ℝ ↦ Matrix.trace (D ^ 3))
      (measurable_matrix_trace_pow_h8h10 N 3)
  have hxz := integral_steinNormalized_halfGaussian_eq_standardScaled_h9
    hpk (fun D : Matrix (Fin N) (Fin N) ℝ ↦
      Matrix.trace D * Matrix.trace (D ^ 3))
      ((measurable_matrix_trace_h8h10 N).mul
        (measurable_matrix_trace_pow_h8h10 N 3))
  have hy2 := integral_steinNormalized_halfGaussian_eq_standardScaled_h9
    hpk (fun D : Matrix (Fin N) (Fin N) ℝ ↦ Matrix.trace (D ^ 2) ^ 2)
      ((measurable_matrix_trace_pow_h8h10 N 2).pow_const 2)
  have hq := integral_steinNormalized_halfGaussian_eq_standardScaled_h9
    hpk (fun D : Matrix (Fin N) (Fin N) ℝ ↦ Matrix.trace (D ^ 4))
      (measurable_matrix_trace_pow_h8h10 N 4)
  rw [hq, hz, hxz, hy2] at hhalf
  have hrec :
      concreteCOEExponent N K * h8H10TraceFourMoment N K =
        concreteCOEExponent N K * h8H10TraceThreeMoment N K +
          2 * h8H10TraceOneTraceThreeMoment N K +
          h8H10TraceTwoSqMoment N K + 3 * h8H10TraceFourMoment N K := by
    simpa only [hc, h9InverseWishartDenominatorLaw, h9ScaledInverseWishart,
      h8H10TraceFourMoment, h8H10TraceThreeMoment,
      h8H10TraceOneTraceThreeMoment, h8H10TraceTwoSqMoment] using hhalf
  nlinarith [hrec]

/-! ## Instantiation of the exact scalar solver interface -/

/-- All ten exact trace recurrences for the concrete project denominator
law.  This is the probability-to-algebra adapter required by the H8/H10
exact rational solver. -/
theorem h8H10ExactTraceRecurrenceSystem_internal
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    H8H10ExactTraceRecurrenceSystem
      (N : ℝ) (concreteCOEExponent N K)
      (h8H10TraceOneSqMoment N K)
      (h8H10TraceTwoMoment N K)
      (h8H10TraceOneCubeMoment N K)
      (h8H10TraceOneTraceTwoMoment N K)
      (h8H10TraceThreeMoment N K)
      (h8H10TraceOneFourthMoment N K)
      (h8H10TraceOneSqTraceTwoMoment N K)
      (h8H10TraceTwoSqMoment N K)
      (h8H10TraceOneTraceThreeMoment N K)
      (h8H10TraceFourMoment N K) := by
  have hgap : 2 * N + 8 ≤ K := by omega
  have hmean := integral_h9ScaledInverseTrace hgap
  have hrec1raw := h9ScaledInverseWishart_traceSq_steinRecursion_internal hN hdense
  have hrec3raw := h9ScaledInverseWishart_traceCube_steinRecursion_internal hN hdense
  have hrec6raw :=
    h9ScaledInverseWishart_traceFourthPower_steinRecursion_internal hN hdense
  have hrec1 :
      concreteCOEExponent N K * h8H10TraceOneSqMoment N K =
        concreteCOEExponent N K * (N : ℝ) * (N : ℝ) +
          2 * h8H10TraceTwoMoment N K := by
    simp only [h8H10TraceOneSqMoment, h8H10TraceTwoMoment] at ⊢
    rw [hmean] at hrec1raw
    ring_nf at hrec1raw ⊢
    exact hrec1raw
  have hrec3 :
      concreteCOEExponent N K * h8H10TraceOneCubeMoment N K =
        concreteCOEExponent N K * (N : ℝ) * h8H10TraceOneSqMoment N K +
          4 * h8H10TraceOneTraceTwoMoment N K := by
    simp only [h8H10TraceOneCubeMoment, h8H10TraceOneSqMoment,
      h8H10TraceOneTraceTwoMoment] at ⊢
    ring_nf at hrec3raw ⊢
    exact hrec3raw
  have hrec6 :
      concreteCOEExponent N K * h8H10TraceOneFourthMoment N K =
        concreteCOEExponent N K * (N : ℝ) * h8H10TraceOneCubeMoment N K +
          6 * h8H10TraceOneSqTraceTwoMoment N K := by
    simp only [h8H10TraceOneFourthMoment, h8H10TraceOneCubeMoment,
      h8H10TraceOneSqTraceTwoMoment] at ⊢
    ring_nf at hrec6raw ⊢
    exact hrec6raw
  exact
    { traceOne_sq := hrec1
      traceTwo := h8H10ScaledInverse_traceTwo_steinRecursion_internal hN hdense
      traceOne_cube := hrec3
      traceOne_traceTwo :=
        h8H10ScaledInverse_traceOneTraceTwo_steinRecursion_internal hN hdense
      traceThree := h8H10ScaledInverse_traceThree_steinRecursion_internal hN hdense
      traceOne_fourth := hrec6
      traceOne_sq_traceTwo :=
        h8H10ScaledInverse_traceOneSqTraceTwo_steinRecursion_internal hN hdense
      traceTwo_sq := h8H10ScaledInverse_traceTwoSq_steinRecursion_internal hN hdense
      traceOne_traceThree :=
        h8H10ScaledInverse_traceOneTraceThree_steinRecursion_internal hN hdense
      traceFour := h8H10ScaledInverse_traceFour_steinRecursion_internal hN hdense }

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08
