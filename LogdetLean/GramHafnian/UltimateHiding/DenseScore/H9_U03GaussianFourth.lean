import LogdetLean.GramHafnian.GaussianEvenMoments
import LogdetLean.GramHafnian.UltimateHiding.RealWishartGram
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ClassicalCOEExternal
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.Normed
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# H9 U03 Gaussian fourth-moment reduction

This file mirrors exactly the four fields of `H9U03GaussianFourthContract`.  It
proves every deterministic and functional-analytic consequence needed by that
contract and isolates the remaining probabilistic input as one standard
Gaussian Wick identity, `H9StandardGaussianQuadraticFourthWick`.

The remaining identity asks simultaneously for integrability and the exact
fourth moment of a centered real Gaussian quadratic form.  Its scalar inputs
through degree eight are already proved in `GaussianEvenMoments`; no new axiom
is introduced here.
-/

open scoped BigOperators Matrix.Norms.Frobenius

open MeasureTheory
open ProbabilityTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

open LogdetLean.GramHafnian.Wishart

/-- Centered Gaussian quadratic form, copied definitionally from the U03
contract source so this reduction can be checked without importing the broken
H9 source chain. -/
def h9U03FixedDenominatorGaussianFluctuation {m n : ℕ}
    (D : Matrix (Fin n) (Fin n) ℝ)
    (G : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  Matrix.trace (D * realWishartGram G) -
    (m : ℝ) * Matrix.trace D

private theorem h9U03FixedDenominatorGaussianFluctuation_measurable
    {m n : ℕ} (D : Matrix (Fin n) (Fin n) ℝ) :
    Measurable (h9U03FixedDenominatorGaussianFluctuation (m := m) D) := by
  classical
  unfold h9U03FixedDenominatorGaussianFluctuation realWishartGram
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  fun_prop

/-- Squared Frobenius norm, copied definitionally from the H9 regularization
source. -/
def h9U03MatrixFrobeniusSq {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  ∑ i, ∑ j, (A i j) ^ 2

/-- Centered numerator Gram matrix `G.transpose * G - (N+1) I`. -/
def h9U03CenteredNumeratorGram (N : ℕ)
    (G : Matrix (Fin (N + 1)) (Fin N) ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  realWishartGram G - (((N + 1 : ℕ) : ℝ)) •
    (1 : Matrix (Fin N) (Fin N) ℝ)

/-- Field-for-field exact mirror of `H9U03GaussianFourthContract`.  The suffix
records that the original source declaration could not be imported under the
pinned toolchain because an earlier H9 module does not elaborate. -/
structure H9U03GaussianFourthContractExactReduction (N : ℕ) : Prop where
  fixedDenominator_memLp_four :
    ∀ (D : Matrix (Fin N) (Fin N) ℝ), D.transpose = D →
      MemLp
        (h9U03FixedDenominatorGaussianFluctuation (m := N + 1) D)
        4 (standardRealGaussianMatrixMeasure (N + 1) N)
  fixedDenominator_fourth_integral :
    ∀ (D : Matrix (Fin N) (Fin N) ℝ), D.transpose = D →
      (∫ G : Matrix (Fin (N + 1)) (Fin N) ℝ,
          (h9U03FixedDenominatorGaussianFluctuation D G) ^ 4
          ∂standardRealGaussianMatrixMeasure (N + 1) N) =
        48 * ((N + 1 : ℕ) : ℝ) * Matrix.trace (D ^ 4) +
          12 * ((N + 1 : ℕ) : ℝ) ^ 2 *
            (Matrix.trace (D ^ 2)) ^ 2
  symmetric_trace_four_le_trace_two_sq :
    ∀ (D : Matrix (Fin N) (Fin N) ℝ), D.transpose = D →
      Matrix.trace (D ^ 4) ≤ (Matrix.trace (D ^ 2)) ^ 2
  centeredGram_frobeniusFourth_integrable :
    Integrable
      (fun G : Matrix (Fin (N + 1)) (Fin N) ℝ ↦
        (h9U03MatrixFrobeniusSq (h9U03CenteredNumeratorGram N G)) ^ 2)
      (standardRealGaussianMatrixMeasure (N + 1) N)

/-- The single remaining standard-Gaussian Wick bridge.  This is deliberately
not an axiom: it is a proposition accepted as a hypothesis by the audited
reduction below. -/
def H9StandardGaussianQuadraticFourthWick (N : ℕ) : Prop :=
  ∀ (D : Matrix (Fin N) (Fin N) ℝ), D.transpose = D →
    Integrable
        (fun G : Matrix (Fin (N + 1)) (Fin N) ℝ ↦
          (h9U03FixedDenominatorGaussianFluctuation D G) ^ 4)
        (standardRealGaussianMatrixMeasure (N + 1) N) ∧
      (∫ G : Matrix (Fin (N + 1)) (Fin N) ℝ,
          (h9U03FixedDenominatorGaussianFluctuation D G) ^ 4
          ∂standardRealGaussianMatrixMeasure (N + 1) N) =
        48 * ((N + 1 : ℕ) : ℝ) * Matrix.trace (D ^ 4) +
          12 * ((N + 1 : ℕ) : ℝ) ^ 2 *
            (Matrix.trace (D ^ 2)) ^ 2

private theorem h9_trace_sq_eq_frobenius_norm_sq
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.transpose = A) :
    Matrix.trace (A ^ 2) = ‖A‖ ^ 2 := by
  classical
  have hsymm (i j : Fin n) : A j i = A i j := by
    simpa [Matrix.transpose_apply] using congrArg (fun M ↦ M i j) hA
  have hsum_nonneg :
      0 ≤ ∑ i : Fin n, ∑ j : Fin n, ‖A i j‖ ^ (2 : ℝ) := by
    positivity
  have hnorm :
      ‖A‖ ^ 2 = ∑ i : Fin n, ∑ j : Fin n, (A i j) ^ 2 := by
    calc
      ‖A‖ ^ 2 =
          ((∑ i : Fin n, ∑ j : Fin n, ‖A i j‖ ^ (2 : ℝ)) ^
            (1 / 2 : ℝ)) ^ 2 := by
              rw [Matrix.frobenius_norm_def]
      _ = (Real.sqrt (∑ i : Fin n, ∑ j : Fin n,
            ‖A i j‖ ^ (2 : ℝ))) ^ 2 := by
              rw [Real.sqrt_eq_rpow]
      _ = ∑ i : Fin n, ∑ j : Fin n, ‖A i j‖ ^ (2 : ℝ) :=
            Real.sq_sqrt hsum_nonneg
      _ = ∑ i : Fin n, ∑ j : Fin n, (A i j) ^ 2 := by
            simp [Real.rpow_two, Real.norm_eq_abs, sq_abs]
  calc
    Matrix.trace (A ^ 2) =
        ∑ i : Fin n, ∑ j : Fin n, A i j * A j i := by
          simp [Matrix.trace, pow_two, Matrix.mul_apply]
    _ = ∑ i : Fin n, ∑ j : Fin n, (A i j) ^ 2 := by
          simp_rw [hsymm]
          simp [pow_two]
    _ = ‖A‖ ^ 2 := hnorm.symm

theorem h9_symmetric_trace_four_le_trace_two_sq_foundational
    {N : ℕ} (D : Matrix (Fin N) (Fin N) ℝ) (hD : D.transpose = D) :
    Matrix.trace (D ^ 4) ≤ (Matrix.trace (D ^ 2)) ^ 2 := by
  have hD2 : (D ^ 2).transpose = D ^ 2 := by
    rw [Matrix.transpose_pow, hD]
  have hmul : ‖D ^ 2‖ ≤ ‖D‖ * ‖D‖ := by
    simpa [pow_two] using Matrix.frobenius_norm_mul D D
  have hmul_sq : ‖D ^ 2‖ ^ 2 ≤ (‖D‖ * ‖D‖) ^ 2 := by
    nlinarith [norm_nonneg (D ^ 2), norm_nonneg D,
      mul_nonneg (norm_nonneg D) (norm_nonneg D)]
  calc
    Matrix.trace (D ^ 4) = Matrix.trace ((D ^ 2) ^ 2) := by
      congr 1
      simp [pow_succ, mul_assoc]
    _ = ‖D ^ 2‖ ^ 2 := h9_trace_sq_eq_frobenius_norm_sq (D ^ 2) hD2
    _ ≤ (‖D‖ * ‖D‖) ^ 2 := hmul_sq
    _ = (‖D‖ ^ 2) ^ 2 := by ring
    _ = (Matrix.trace (D ^ 2)) ^ 2 := by
      rw [h9_trace_sq_eq_frobenius_norm_sq D hD]

private theorem h9_memLp_four_of_integrable_four
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : AEStronglyMeasurable f μ)
    (hint : Integrable (fun x ↦ (f x) ^ 4) μ) :
    MemLp f 4 μ := by
  apply (integrable_norm_rpow_iff hf (by norm_num) (by norm_num)).mp
  simpa [Real.rpow_natCast, norm_pow] using hint.norm

private noncomputable def h9SymmetricEntryProbe
    {N : ℕ} (i j : Fin N) : Matrix (Fin N) (Fin N) ℝ :=
  (1 / 2 : ℝ) •
    (Matrix.single j i 1 + Matrix.single i j 1)

private theorem h9SymmetricEntryProbe_transpose
    {N : ℕ} (i j : Fin N) :
    (h9SymmetricEntryProbe i j).transpose = h9SymmetricEntryProbe i j := by
  classical
  simp [h9SymmetricEntryProbe, add_comm]

private theorem h9U03CenteredNumeratorGram_transpose
    (N : ℕ) (G : Matrix (Fin (N + 1)) (Fin N) ℝ) :
    (h9U03CenteredNumeratorGram N G).transpose = h9U03CenteredNumeratorGram N G := by
  simp [h9U03CenteredNumeratorGram, realWishartGram, Matrix.transpose_mul]

private theorem h9_fluctuation_eq_trace_mul_centered
    (N : ℕ) (D : Matrix (Fin N) (Fin N) ℝ)
    (G : Matrix (Fin (N + 1)) (Fin N) ℝ) :
    h9U03FixedDenominatorGaussianFluctuation D G =
      Matrix.trace (D * h9U03CenteredNumeratorGram N G) := by
  simp [h9U03FixedDenominatorGaussianFluctuation, h9U03CenteredNumeratorGram,
    Matrix.mul_sub, Matrix.mul_smul]

private theorem h9_entry_probe_fluctuation
    (N : ℕ) (i j : Fin N)
    (G : Matrix (Fin (N + 1)) (Fin N) ℝ) :
    h9U03FixedDenominatorGaussianFluctuation (h9SymmetricEntryProbe i j) G =
      h9U03CenteredNumeratorGram N G i j := by
  rw [h9_fluctuation_eq_trace_mul_centered]
  let A := h9U03CenteredNumeratorGram N G
  have hA : A.transpose = A := h9U03CenteredNumeratorGram_transpose N G
  have hsymm : A j i = A i j := by
    simpa [Matrix.transpose_apply] using congrArg (fun M ↦ M i j) hA
  simp only [h9SymmetricEntryProbe, smul_add, Matrix.smul_mul,
    Matrix.add_mul, Matrix.trace_smul, Matrix.trace_add]
  rw [Matrix.trace_single_mul, Matrix.trace_single_mul]
  simp only [smul_eq_mul, one_mul]
  dsimp [A] at hsymm ⊢
  rw [hsymm]
  ring

private theorem h9_centeredGram_frobeniusFourth_integrable_of_wick
    {N : ℕ} (hwick : H9StandardGaussianQuadraticFourthWick N) :
    Integrable
      (fun G : Matrix (Fin (N + 1)) (Fin N) ℝ ↦
        (h9U03MatrixFrobeniusSq (h9U03CenteredNumeratorGram N G)) ^ 2)
      (standardRealGaussianMatrixMeasure (N + 1) N) := by
  classical
  let μ := standardRealGaussianMatrixMeasure (N + 1) N
  let A := fun G : Matrix (Fin (N + 1)) (Fin N) ℝ ↦
    h9U03CenteredNumeratorGram N G
  have hentry (i j : Fin N) :
      Integrable (fun G ↦ (A G i j) ^ 4) μ := by
    have h := (hwick (h9SymmetricEntryProbe i j)
      (h9SymmetricEntryProbe_transpose i j)).1
    apply h.congr
    filter_upwards [] with G
    rw [h9_entry_probe_fluctuation]
  have hsq (i j : Fin N) :
      MemLp (fun G ↦ (A G i j) ^ 2) 2 μ := by
    apply (memLp_two_iff_integrable_sq (by
      dsimp [A, h9U03CenteredNumeratorGram, realWishartGram]
      simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply,
        Matrix.transpose_apply]
      fun_prop)).2
    convert hentry i j using 1
    ring
  have hprod (i j k l : Fin N) :
      Integrable (fun G ↦ (A G i j) ^ 2 * (A G k l) ^ 2) μ := by
    change Integrable
      ((fun G ↦ (A G i j) ^ 2) * (fun G ↦ (A G k l) ^ 2)) μ
    exact MemLp.integrable_mul (hsq i j) (hsq k l)
  have hsum :
      Integrable
        (fun G ↦ ∑ i : Fin N, ∑ k : Fin N,
          ∑ l : Fin N, ∑ j : Fin N,
            (A G i j) ^ 2 * (A G k l) ^ 2) μ := by
    exact integrable_finset_sum _ fun i _ ↦
      integrable_finset_sum _ fun k _ ↦
        integrable_finset_sum _ fun l _ ↦
          integrable_finset_sum _ fun j _ ↦ hprod i j k l
  apply hsum.congr
  filter_upwards [] with G
  dsimp [A]
  simp only [h9U03MatrixFrobeniusSq, pow_two]
  rw [Finset.sum_mul_sum]
  simp only [Finset.mul_sum, Finset.sum_mul]

/-- Strong audited field-exact reduction of `H9U03GaussianFourthContract` to
one standard Gaussian Wick proposition. -/
theorem h9U03GaussianFourthContractExactReduction_of_standardGaussianQuadraticFourthWick
    (N : ℕ) (hwick : H9StandardGaussianQuadraticFourthWick N) :
    H9U03GaussianFourthContractExactReduction N where
  fixedDenominator_memLp_four D hD := by
    apply h9_memLp_four_of_integrable_four
      (h9U03FixedDenominatorGaussianFluctuation_measurable D).aestronglyMeasurable
    exact (hwick D hD).1
  fixedDenominator_fourth_integral D hD := (hwick D hD).2
  symmetric_trace_four_le_trace_two_sq D hD :=
    h9_symmetric_trace_four_le_trace_two_sq_foundational D hD
  centeredGram_frobeniusFourth_integrable :=
    h9_centeredGram_frobeniusFourth_integrable_of_wick hwick

/-! ### Standard-Gaussian fourth Wick contraction -/

private structure H9U03CenteredFourthData {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (X : α → ℝ) (v k : ℝ) : Prop where
  integrable_one : Integrable X μ
  integrable_two : Integrable (fun x => X x ^ 2) μ
  integrable_three : Integrable (fun x => X x ^ 3) μ
  integrable_four : Integrable (fun x => X x ^ 4) μ
  mean : ∫ x, X x ∂μ = 0
  second : ∫ x, X x ^ 2 ∂μ = v
  fourth : ∫ x, X x ^ 4 ∂μ = k

private theorem h9U03IntegralAddFun {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f g : α → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) :
    ∫ x, f x + g x ∂μ = (∫ x, f x ∂μ) + ∫ x, g x ∂μ := by
  simpa only [Pi.add_apply] using integral_add hf hg

private theorem h9U03IntegralSubFun {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f g : α → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) :
    ∫ x, f x - g x ∂μ = (∫ x, f x ∂μ) - ∫ x, g x ∂μ := by
  simpa only [Pi.sub_apply] using integral_sub hf hg

private theorem H9U03CenteredFourthData.const_mul {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {X : α → ℝ} {v k : ℝ}
    (h : H9U03CenteredFourthData μ X v k) (a : ℝ) :
    H9U03CenteredFourthData μ (fun x => a * X x) (a ^ 2 * v) (a ^ 4 * k) := by
  have h1 := h.integrable_one.const_mul a
  have h2 := h.integrable_two.const_mul (a ^ 2)
  have h3 := h.integrable_three.const_mul (a ^ 3)
  have h4 := h.integrable_four.const_mul (a ^ 4)
  refine ⟨h1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h2.congr (Filter.Eventually.of_forall fun x => by ring)
  · exact h3.congr (Filter.Eventually.of_forall fun x => by ring)
  · exact h4.congr (Filter.Eventually.of_forall fun x => by ring)
  · rw [integral_const_mul, h.mean, mul_zero]
  · calc
      ∫ x, (a * X x) ^ 2 ∂μ = ∫ x, a ^ 2 * X x ^ 2 ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
      _ = a ^ 2 * ∫ x, X x ^ 2 ∂μ := integral_const_mul _ _
      _ = a ^ 2 * v := by rw [h.second]
  · calc
      ∫ x, (a * X x) ^ 4 ∂μ = ∫ x, a ^ 4 * X x ^ 4 ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
      _ = a ^ 4 * ∫ x, X x ^ 4 ∂μ := integral_const_mul _ _
      _ = a ^ 4 * k := by rw [h.fourth]

private theorem H9U03CenteredFourthData.add_prod {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : α → ℝ} {Y : β → ℝ} {vx kx vy ky : ℝ}
    (hX : H9U03CenteredFourthData μ X vx kx)
    (hY : H9U03CenteredFourthData ν Y vy ky) :
    H9U03CenteredFourthData (μ.prod ν) (fun z => X z.1 + Y z.2)
      (vx + vy) (kx + ky + 6 * vx * vy) := by
  have hX1 : Integrable (fun z : α × β => X z.1) (μ.prod ν) := by
    simpa [Function.comp_def] using
      (measurePreserving_fst (μ := μ) (ν := ν)).integrable_comp_of_integrable hX.integrable_one
  have hX2 : Integrable (fun z : α × β => X z.1 ^ 2) (μ.prod ν) := by
    simpa [Function.comp_def] using
      (measurePreserving_fst (μ := μ) (ν := ν)).integrable_comp_of_integrable hX.integrable_two
  have hX3 : Integrable (fun z : α × β => X z.1 ^ 3) (μ.prod ν) := by
    simpa [Function.comp_def] using
      (measurePreserving_fst (μ := μ) (ν := ν)).integrable_comp_of_integrable hX.integrable_three
  have hX4 : Integrable (fun z : α × β => X z.1 ^ 4) (μ.prod ν) := by
    simpa [Function.comp_def] using
      (measurePreserving_fst (μ := μ) (ν := ν)).integrable_comp_of_integrable hX.integrable_four
  have hY1 : Integrable (fun z : α × β => Y z.2) (μ.prod ν) := by
    simpa [Function.comp_def] using
      (measurePreserving_snd (μ := μ) (ν := ν)).integrable_comp_of_integrable hY.integrable_one
  have hY2 : Integrable (fun z : α × β => Y z.2 ^ 2) (μ.prod ν) := by
    simpa [Function.comp_def] using
      (measurePreserving_snd (μ := μ) (ν := ν)).integrable_comp_of_integrable hY.integrable_two
  have hY3 : Integrable (fun z : α × β => Y z.2 ^ 3) (μ.prod ν) := by
    simpa [Function.comp_def] using
      (measurePreserving_snd (μ := μ) (ν := ν)).integrable_comp_of_integrable hY.integrable_three
  have hY4 : Integrable (fun z : α × β => Y z.2 ^ 4) (μ.prod ν) := by
    simpa [Function.comp_def] using
      (measurePreserving_snd (μ := μ) (ν := ν)).integrable_comp_of_integrable hY.integrable_four
  have h11 : Integrable (fun z : α × β => X z.1 * Y z.2) (μ.prod ν) :=
    hX.integrable_one.mul_prod hY.integrable_one
  have h21 : Integrable (fun z : α × β => X z.1 ^ 2 * Y z.2) (μ.prod ν) :=
    hX.integrable_two.mul_prod hY.integrable_one
  have h12 : Integrable (fun z : α × β => X z.1 * Y z.2 ^ 2) (μ.prod ν) :=
    hX.integrable_one.mul_prod hY.integrable_two
  have h31 : Integrable (fun z : α × β => X z.1 ^ 3 * Y z.2) (μ.prod ν) :=
    hX.integrable_three.mul_prod hY.integrable_one
  have h22 : Integrable (fun z : α × β => X z.1 ^ 2 * Y z.2 ^ 2) (μ.prod ν) :=
    hX.integrable_two.mul_prod hY.integrable_two
  have h13 : Integrable (fun z : α × β => X z.1 * Y z.2 ^ 3) (μ.prod ν) :=
    hX.integrable_one.mul_prod hY.integrable_three
  have hi2poly : Integrable (fun z : α × β =>
      X z.1 ^ 2 + (2 * (X z.1 * Y z.2) + Y z.2 ^ 2)) (μ.prod ν) :=
    hX2.add ((h11.const_mul 2).add hY2)
  have hrest2 : Integrable (fun z : α × β =>
      2 * (X z.1 * Y z.2) + Y z.2 ^ 2) (μ.prod ν) :=
    (h11.const_mul 2).add hY2
  have hi3poly : Integrable (fun z : α × β =>
      X z.1 ^ 3 + (3 * (X z.1 ^ 2 * Y z.2) +
        (3 * (X z.1 * Y z.2 ^ 2) + Y z.2 ^ 3))) (μ.prod ν) :=
    hX3.add ((h21.const_mul 3).add ((h12.const_mul 3).add hY3))
  have hi4poly : Integrable (fun z : α × β =>
      X z.1 ^ 4 + (4 * (X z.1 ^ 3 * Y z.2) +
        (6 * (X z.1 ^ 2 * Y z.2 ^ 2) +
          (4 * (X z.1 * Y z.2 ^ 3) + Y z.2 ^ 4)))) (μ.prod ν) :=
    hX4.add ((h31.const_mul 4).add
      ((h22.const_mul 6).add ((h13.const_mul 4).add hY4)))
  have hrest43 : Integrable (fun z : α × β =>
      4 * (X z.1 * Y z.2 ^ 3) + Y z.2 ^ 4) (μ.prod ν) :=
    (h13.const_mul 4).add hY4
  have hrest42 : Integrable (fun z : α × β =>
      6 * (X z.1 ^ 2 * Y z.2 ^ 2) +
        (4 * (X z.1 * Y z.2 ^ 3) + Y z.2 ^ 4)) (μ.prod ν) :=
    (h22.const_mul 6).add hrest43
  have hrest41 : Integrable (fun z : α × β =>
      4 * (X z.1 ^ 3 * Y z.2) +
        (6 * (X z.1 ^ 2 * Y z.2 ^ 2) +
          (4 * (X z.1 * Y z.2 ^ 3) + Y z.2 ^ 4))) (μ.prod ν) :=
    (h31.const_mul 4).add hrest42
  have hi2 : Integrable (fun z : α × β => (X z.1 + Y z.2) ^ 2) (μ.prod ν) :=
    hi2poly.congr (Filter.Eventually.of_forall fun z => by ring)
  have hi3 : Integrable (fun z : α × β => (X z.1 + Y z.2) ^ 3) (μ.prod ν) :=
    hi3poly.congr (Filter.Eventually.of_forall fun z => by ring)
  have hi4 : Integrable (fun z : α × β => (X z.1 + Y z.2) ^ 4) (μ.prod ν) :=
    hi4poly.congr (Filter.Eventually.of_forall fun z => by ring)
  have intX1 : ∫ z : α × β, X z.1 ∂(μ.prod ν) = 0 := by
    calc
      _ = (∫ x, X x ∂μ) * ∫ _y : β, (1 : ℝ) ∂ν := by
        simpa using (integral_prod_mul (μ := μ) (ν := ν) X (fun _ : β => (1 : ℝ)))
      _ = 0 := by rw [hX.mean, zero_mul]
  have intY1 : ∫ z : α × β, Y z.2 ∂(μ.prod ν) = 0 := by
    calc
      _ = (∫ _x : α, (1 : ℝ) ∂μ) * ∫ y, Y y ∂ν := by
        simpa using (integral_prod_mul (μ := μ) (ν := ν) (fun _ : α => (1 : ℝ)) Y)
      _ = 0 := by rw [hY.mean, mul_zero]
  have intX2 : ∫ z : α × β, X z.1 ^ 2 ∂(μ.prod ν) = vx := by
    calc
      _ = (∫ x, X x ^ 2 ∂μ) * ∫ _y : β, (1 : ℝ) ∂ν := by
        simpa using (integral_prod_mul (μ := μ) (ν := ν) (fun x => X x ^ 2)
          (fun _ : β => (1 : ℝ)))
      _ = vx := by rw [hX.second]; simp
  have intY2 : ∫ z : α × β, Y z.2 ^ 2 ∂(μ.prod ν) = vy := by
    calc
      _ = (∫ _x : α, (1 : ℝ) ∂μ) * ∫ y, Y y ^ 2 ∂ν := by
        simpa using (integral_prod_mul (μ := μ) (ν := ν) (fun _ : α => (1 : ℝ))
          (fun y => Y y ^ 2))
      _ = vy := by rw [hY.second]; simp
  have intX4 : ∫ z : α × β, X z.1 ^ 4 ∂(μ.prod ν) = kx := by
    calc
      _ = (∫ x, X x ^ 4 ∂μ) * ∫ _y : β, (1 : ℝ) ∂ν := by
        simpa using (integral_prod_mul (μ := μ) (ν := ν) (fun x => X x ^ 4)
          (fun _ : β => (1 : ℝ)))
      _ = kx := by rw [hX.fourth]; simp
  have intY4 : ∫ z : α × β, Y z.2 ^ 4 ∂(μ.prod ν) = ky := by
    calc
      _ = (∫ _x : α, (1 : ℝ) ∂μ) * ∫ y, Y y ^ 4 ∂ν := by
        simpa using (integral_prod_mul (μ := μ) (ν := ν) (fun _ : α => (1 : ℝ))
          (fun y => Y y ^ 4))
      _ = ky := by rw [hY.fourth]; simp
  have int11 : ∫ z : α × β, X z.1 * Y z.2 ∂(μ.prod ν) = 0 := by
    rw [integral_prod_mul, hX.mean, hY.mean, zero_mul]
  have int31 : ∫ z : α × β, X z.1 ^ 3 * Y z.2 ∂(μ.prod ν) = 0 := by
    calc
      _ = (∫ x, X x ^ 3 ∂μ) * ∫ y, Y y ∂ν :=
        integral_prod_mul (fun x => X x ^ 3) Y
      _ = 0 := by rw [hY.mean, mul_zero]
  have int22 : ∫ z : α × β, X z.1 ^ 2 * Y z.2 ^ 2 ∂(μ.prod ν) = vx * vy := by
    calc
      _ = (∫ x, X x ^ 2 ∂μ) * ∫ y, Y y ^ 2 ∂ν :=
        integral_prod_mul (fun x => X x ^ 2) (fun y => Y y ^ 2)
      _ = vx * vy := by rw [hX.second, hY.second]
  have int13 : ∫ z : α × β, X z.1 * Y z.2 ^ 3 ∂(μ.prod ν) = 0 := by
    calc
      _ = (∫ x, X x ∂μ) * ∫ y, Y y ^ 3 ∂ν :=
        integral_prod_mul X (fun y => Y y ^ 3)
      _ = 0 := by rw [hX.mean, zero_mul]
  refine ⟨hX1.add hY1, hi2, hi3, hi4, ?_, ?_, ?_⟩
  · rw [integral_add hX1 hY1, intX1, intY1, add_zero]
  · calc
      ∫ z : α × β, (X z.1 + Y z.2) ^ 2 ∂(μ.prod ν) =
          ∫ z : α × β, X z.1 ^ 2 +
            (2 * (X z.1 * Y z.2) + Y z.2 ^ 2) ∂(μ.prod ν) :=
        integral_congr_ae (Filter.Eventually.of_forall fun z => by ring)
      _ = (∫ z : α × β, X z.1 ^ 2 ∂(μ.prod ν)) +
          ((∫ z : α × β, 2 * (X z.1 * Y z.2) ∂(μ.prod ν)) +
            ∫ z : α × β, Y z.2 ^ 2 ∂(μ.prod ν)) := by
        rw [h9U03IntegralAddFun hX2 hrest2,
          h9U03IntegralAddFun (h11.const_mul 2) hY2]
      _ = vx + vy := by rw [integral_const_mul, intX2, int11, intY2]; ring
  · calc
      ∫ z : α × β, (X z.1 + Y z.2) ^ 4 ∂(μ.prod ν) =
          ∫ z : α × β, X z.1 ^ 4 +
            (4 * (X z.1 ^ 3 * Y z.2) +
              (6 * (X z.1 ^ 2 * Y z.2 ^ 2) +
                (4 * (X z.1 * Y z.2 ^ 3) + Y z.2 ^ 4))) ∂(μ.prod ν) :=
        integral_congr_ae (Filter.Eventually.of_forall fun z => by ring)
      _ = (∫ z : α × β, X z.1 ^ 4 ∂(μ.prod ν)) +
          ((∫ z : α × β, 4 * (X z.1 ^ 3 * Y z.2) ∂(μ.prod ν)) +
            ((∫ z : α × β, 6 * (X z.1 ^ 2 * Y z.2 ^ 2) ∂(μ.prod ν)) +
              ((∫ z : α × β, 4 * (X z.1 * Y z.2 ^ 3) ∂(μ.prod ν)) +
                ∫ z : α × β, Y z.2 ^ 4 ∂(μ.prod ν)))) := by
        rw [h9U03IntegralAddFun hX4 hrest41,
          h9U03IntegralAddFun (h31.const_mul 4) hrest42,
          h9U03IntegralAddFun (h22.const_mul 6) hrest43,
          h9U03IntegralAddFun (h13.const_mul 4) hY4]
      _ = kx + ky + 6 * vx * vy := by
        rw [integral_const_mul, integral_const_mul, integral_const_mul,
          intX4, int31, int22, int13, intY4]
        ring

private theorem H9U03CenteredFourthData.comp_measurableEquiv {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {Y : β → ℝ} {v k : ℝ}
    (e : α ≃ᵐ β) (he : MeasurePreserving e μ ν)
    (h : H9U03CenteredFourthData ν Y v k) :
    H9U03CenteredFourthData μ (fun x => Y (e x)) v k := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Function.comp_def] using he.integrable_comp_of_integrable h.integrable_one
  · simpa [Function.comp_def] using he.integrable_comp_of_integrable h.integrable_two
  · simpa [Function.comp_def] using he.integrable_comp_of_integrable h.integrable_three
  · simpa [Function.comp_def] using he.integrable_comp_of_integrable h.integrable_four
  · simpa using (he.integral_comp' Y).trans h.mean
  · simpa using (he.integral_comp' (fun y => Y y ^ 2)).trans h.second
  · simpa using (he.integral_comp' (fun y => Y y ^ 4)).trans h.fourth

private def h9U03WeightedSum {n : ℕ} {α : Type*} (f : α → ℝ)
    (a : Fin n → ℝ) (x : Fin n → α) : ℝ :=
  ∑ i, a i * f (x i)

private theorem h9U03H9U03CenteredFourthDataWeightedSum {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ]
    {f : α → ℝ} {v k : ℝ} (h : H9U03CenteredFourthData μ f v k) :
    ∀ (n : ℕ) (a : Fin n → ℝ),
      H9U03CenteredFourthData (Measure.pi fun _ : Fin n => μ) (h9U03WeightedSum f a)
        (v * ∑ i, a i ^ 2)
        (3 * v ^ 2 * (∑ i, a i ^ 2) ^ 2 + (k - 3 * v ^ 2) * ∑ i, a i ^ 4) := by
  intro n
  induction n with
  | zero =>
      intro a
      refine ⟨by simp [h9U03WeightedSum], by simp [h9U03WeightedSum], by simp [h9U03WeightedSum],
        by simp [h9U03WeightedSum], by simp [h9U03WeightedSum], by simp [h9U03WeightedSum], by simp [h9U03WeightedSum]⟩
  | succ n ih =>
      intro a
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) 0
      have he : MeasurePreserving e (Measure.pi fun _ : Fin (n + 1) => μ)
          (μ.prod (Measure.pi fun _ : Fin n => μ)) := by
        simpa [e] using
          (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0)
      have hHead := h.const_mul (a 0)
      have hTail := ih (fun i : Fin n => a i.succ)
      have hProd := hHead.add_prod hTail
      have hPull := hProd.comp_measurableEquiv e he
      have hfun :
          (fun x => a 0 * f (e x).1 + h9U03WeightedSum f (fun i : Fin n => a i.succ) (e x).2) =
            h9U03WeightedSum f a := by
        funext x
        simp [h9U03WeightedSum, e, Fin.sum_univ_succ, Fin.tail_def]
      rw [hfun] at hPull
      convert hPull using 1 <;> simp [Fin.sum_univ_succ] <;> ring

private theorem h9U03CenteredSquareGaussianData :
    H9U03CenteredFourthData (gaussianReal 0 1) (fun x : ℝ => x ^ 2 - 1) 2 60 := by
  have hp (r : ℕ) : Integrable (fun x : ℝ => x ^ r) (gaussianReal 0 1) :=
    LogdetLean.GramHafnian.integrable_pow_gaussianReal r
  have hone : Integrable (fun _x : ℝ => (1 : ℝ)) (gaussianReal 0 1) := integrable_const 1
  have hpoly1 : Integrable (fun x : ℝ => x ^ 2 - 1) (gaussianReal 0 1) :=
    (hp 2).sub hone
  have hpoly2base : Integrable (fun x : ℝ => x ^ 4 - 2 * x ^ 2)
      (gaussianReal 0 1) :=
    (hp 4).sub ((hp 2).const_mul 2)
  have hpoly2 : Integrable (fun x : ℝ => x ^ 4 - 2 * x ^ 2 + 1)
      (gaussianReal 0 1) :=
    hpoly2base.add hone
  have hpoly3 : Integrable (fun x : ℝ => x ^ 6 - 3 * x ^ 4 + 3 * x ^ 2 - 1)
      (gaussianReal 0 1) :=
    (((hp 6).sub ((hp 4).const_mul 3)).add ((hp 2).const_mul 3)).sub hone
  have hpoly4 : Integrable (fun x : ℝ =>
      x ^ 8 - 4 * x ^ 6 + 6 * x ^ 4 - 4 * x ^ 2 + 1) (gaussianReal 0 1) :=
    ((((hp 8).sub ((hp 6).const_mul 4)).add ((hp 4).const_mul 6)).sub
      ((hp 2).const_mul 4)).add hone
  have hpoly4base1 : Integrable (fun x : ℝ => x ^ 8 - 4 * x ^ 6)
      (gaussianReal 0 1) :=
    (hp 8).sub ((hp 6).const_mul 4)
  have hpoly4base2 : Integrable (fun x : ℝ =>
      x ^ 8 - 4 * x ^ 6 + 6 * x ^ 4) (gaussianReal 0 1) :=
    hpoly4base1.add ((hp 4).const_mul 6)
  have hpoly4base3 : Integrable (fun x : ℝ =>
      x ^ 8 - 4 * x ^ 6 + 6 * x ^ 4 - 4 * x ^ 2) (gaussianReal 0 1) :=
    hpoly4base2.sub ((hp 2).const_mul 4)
  have honeInt : ∫ _x : ℝ, (1 : ℝ) ∂(gaussianReal 0 1) = 1 := by simp
  have hm2 : ∫ x : ℝ, x ^ 2 ∂(gaussianReal 0 1) = 1 := by
    simpa [Nat.doubleFactorial] using
      (LogdetLean.GramHafnian.integral_pow_two_gaussianReal 1)
  have hm4 : ∫ x : ℝ, x ^ 4 ∂(gaussianReal 0 1) = 3 := by
    simpa [Nat.doubleFactorial] using
      (LogdetLean.GramHafnian.integral_pow_two_gaussianReal 2)
  have hm6 : ∫ x : ℝ, x ^ 6 ∂(gaussianReal 0 1) = 15 := by
    simpa [Nat.doubleFactorial] using
      (LogdetLean.GramHafnian.integral_pow_two_gaussianReal 3)
  have hm8 : ∫ x : ℝ, x ^ 8 ∂(gaussianReal 0 1) = 105 := by
    simpa [Nat.doubleFactorial] using
      (LogdetLean.GramHafnian.integral_pow_two_gaussianReal 4)
  have honePow : Integrable (fun x : ℝ => (x ^ 2 - 1) ^ 1) (gaussianReal 0 1) := by
    simpa using hpoly1
  have htwo : Integrable (fun x : ℝ => (x ^ 2 - 1) ^ 2) (gaussianReal 0 1) :=
    hpoly2.congr (Filter.Eventually.of_forall fun x => by ring)
  have hthree : Integrable (fun x : ℝ => (x ^ 2 - 1) ^ 3) (gaussianReal 0 1) :=
    hpoly3.congr (Filter.Eventually.of_forall fun x => by ring)
  have hfour : Integrable (fun x : ℝ => (x ^ 2 - 1) ^ 4) (gaussianReal 0 1) :=
    hpoly4.congr (Filter.Eventually.of_forall fun x => by ring)
  refine ⟨hpoly1, htwo, hthree, hfour, ?_, ?_, ?_⟩
  · calc
      ∫ x : ℝ, x ^ 2 - 1 ∂(gaussianReal 0 1) =
          (∫ x : ℝ, x ^ 2 ∂(gaussianReal 0 1)) - ∫ _x : ℝ, 1 ∂(gaussianReal 0 1) := by
        exact h9U03IntegralSubFun (hp 2) hone
      _ = 0 := by rw [hm2, honeInt]; norm_num
  · calc
      ∫ x : ℝ, (x ^ 2 - 1) ^ 2 ∂(gaussianReal 0 1) =
          ∫ x : ℝ, x ^ 4 - 2 * x ^ 2 + 1 ∂(gaussianReal 0 1) :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
      _ = (∫ x : ℝ, x ^ 4 ∂(gaussianReal 0 1)) -
          2 * (∫ x : ℝ, x ^ 2 ∂(gaussianReal 0 1)) +
          ∫ _x : ℝ, 1 ∂(gaussianReal 0 1) := by
        rw [h9U03IntegralAddFun hpoly2base hone,
          h9U03IntegralSubFun (hp 4) ((hp 2).const_mul 2), integral_const_mul]
      _ = 2 := by rw [hm4, hm2, honeInt]; norm_num
  · calc
      ∫ x : ℝ, (x ^ 2 - 1) ^ 4 ∂(gaussianReal 0 1) =
          ∫ x : ℝ, x ^ 8 - 4 * x ^ 6 + 6 * x ^ 4 - 4 * x ^ 2 + 1
            ∂(gaussianReal 0 1) :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
      _ = ((((∫ x : ℝ, x ^ 8 ∂(gaussianReal 0 1)) -
          4 * (∫ x : ℝ, x ^ 6 ∂(gaussianReal 0 1))) +
          6 * (∫ x : ℝ, x ^ 4 ∂(gaussianReal 0 1))) -
          4 * (∫ x : ℝ, x ^ 2 ∂(gaussianReal 0 1))) +
          (∫ _x : ℝ, 1 ∂(gaussianReal 0 1)) := by
        rw [h9U03IntegralAddFun hpoly4base3 hone,
          h9U03IntegralSubFun hpoly4base2 ((hp 2).const_mul 4),
          h9U03IntegralAddFun hpoly4base1 ((hp 4).const_mul 6),
          h9U03IntegralSubFun (hp 8) ((hp 6).const_mul 4),
          integral_const_mul, integral_const_mul, integral_const_mul]
      _ = 60 := by rw [hm8, hm6, hm4, hm2, honeInt]; norm_num

private def h9U03DiagonalRowFluctuation {N : ℕ} (l : Fin N → ℝ) (x : Fin N → ℝ) : ℝ :=
  h9U03WeightedSum (fun t : ℝ => t ^ 2 - 1) l x

private def h9U03DiagonalMatrixFluctuation {m N : ℕ} (l : Fin N → ℝ)
    (G : Matrix (Fin m) (Fin N) ℝ) : ℝ :=
  ∑ r, h9U03DiagonalRowFluctuation l (G r)

private theorem h9U03DiagonalRowData {N : ℕ} (l : Fin N → ℝ) :
    H9U03CenteredFourthData (LogdetLean.GramHafnian.standardRealGaussianVectorMeasure N)
      (h9U03DiagonalRowFluctuation l)
      (2 * ∑ i, l i ^ 2)
      (48 * ∑ i, l i ^ 4 + 12 * (∑ i, l i ^ 2) ^ 2) := by
  have h := h9U03H9U03CenteredFourthDataWeightedSum h9U03CenteredSquareGaussianData N l
  change H9U03CenteredFourthData (Measure.pi fun _ : Fin N => gaussianReal 0 1)
    (h9U03WeightedSum (fun t : ℝ => t ^ 2 - 1) l)
    (2 * ∑ i, l i ^ 2)
    (48 * ∑ i, l i ^ 4 + 12 * (∑ i, l i ^ 2) ^ 2)
  convert h using 1 <;> ring

private theorem h9U03DiagonalMatrixData {m N : ℕ} (l : Fin N → ℝ) :
    H9U03CenteredFourthData (standardRealGaussianMatrixMeasure m N)
      (h9U03DiagonalMatrixFluctuation l)
      ((m : ℝ) * (2 * ∑ i, l i ^ 2))
      (48 * (m : ℝ) * ∑ i, l i ^ 4 +
        12 * (m : ℝ) ^ 2 * (∑ i, l i ^ 2) ^ 2) := by
  have hrow := h9U03DiagonalRowData l
  have h := h9U03H9U03CenteredFourthDataWeightedSum hrow m (fun _ : Fin m => (1 : ℝ))
  have hfun : h9U03WeightedSum (h9U03DiagonalRowFluctuation l) (fun _ : Fin m => (1 : ℝ)) =
      fun G => ∑ r, h9U03DiagonalRowFluctuation l (G r) := by
    funext G
    simp [h9U03WeightedSum]
  rw [hfun] at h
  unfold standardRealGaussianMatrixMeasure h9U03DiagonalMatrixFluctuation
  convert h using 1 <;> simp <;> ring_nf
  rfl

private noncomputable def h9U03RowRotation {N : ℕ} {D : Matrix (Fin N) (Fin N) ℝ}
    (hD : D.IsHermitian) : (Fin N → ℝ) ≃ᵐ (Fin N → ℝ) :=
  (MeasurableEquiv.toLp 2 (Fin N → ℝ)).trans
    (hD.eigenvectorBasis.repr.toMeasurableEquiv.trans
      (MeasurableEquiv.toLp 2 (Fin N → ℝ)).symm)

private noncomputable def h9U03MatrixRotation {m N : ℕ} {D : Matrix (Fin N) (Fin N) ℝ}
    (hD : D.IsHermitian) :
    Matrix (Fin m) (Fin N) ℝ ≃ᵐ Matrix (Fin m) (Fin N) ℝ :=
  MeasurableEquiv.piCongrRight (fun _ => h9U03RowRotation hD)

private theorem h9U03RowRotationMeasurePreserving {N : ℕ}
    {D : Matrix (Fin N) (Fin N) ℝ} (hD : D.IsHermitian) :
    MeasurePreserving (h9U03RowRotation hD)
      (LogdetLean.GramHafnian.standardRealGaussianVectorMeasure N)
      (LogdetLean.GramHafnian.standardRealGaussianVectorMeasure N) := by
  let eLp := MeasurableEquiv.toLp 2 (Fin N → ℝ)
  let eRep := hD.eigenvectorBasis.repr.toMeasurableEquiv
  have hLp : MeasurePreserving eLp
      (LogdetLean.GramHafnian.standardRealGaussianVectorMeasure N)
      (stdGaussian (EuclideanSpace ℝ (Fin N))) := by
    refine ⟨eLp.measurable, ?_⟩
    change Measure.map (WithLp.toLp 2)
      (Measure.pi fun _ : Fin N => gaussianReal 0 1) =
        stdGaussian (EuclideanSpace ℝ (Fin N))
    exact map_pi_eq_stdGaussian
  have hRep : MeasurePreserving eRep
      (stdGaussian (EuclideanSpace ℝ (Fin N)))
      (stdGaussian (EuclideanSpace ℝ (Fin N))) := by
    refine ⟨eRep.measurable, ?_⟩
    simpa [eRep] using stdGaussian_map hD.eigenvectorBasis.repr
  have hLpInv := MeasurePreserving.symm eLp hLp
  change MeasurePreserving
    (fun x => (hD.eigenvectorBasis.repr (WithLp.toLp 2 x)).ofLp)
    (LogdetLean.GramHafnian.standardRealGaussianVectorMeasure N)
    (LogdetLean.GramHafnian.standardRealGaussianVectorMeasure N)
  exact hLpInv.comp (hRep.comp hLp)

private theorem h9U03MatrixRotationMeasurePreserving {m N : ℕ}
    {D : Matrix (Fin N) (Fin N) ℝ} (hD : D.IsHermitian) :
    MeasurePreserving (h9U03MatrixRotation (m := m) hD)
      (standardRealGaussianMatrixMeasure m N)
      (standardRealGaussianMatrixMeasure m N) := by
  have h := measurePreserving_pi
    (fun _ : Fin m => LogdetLean.GramHafnian.standardRealGaussianVectorMeasure N)
    (fun _ : Fin m => LogdetLean.GramHafnian.standardRealGaussianVectorMeasure N)
    (f := fun _ : Fin m => h9U03RowRotation hD)
    (fun _ => h9U03RowRotationMeasurePreserving hD)
  change MeasurePreserving (fun G i => h9U03RowRotation hD (G i))
    (Measure.pi fun _ : Fin m => LogdetLean.GramHafnian.standardRealGaussianVectorMeasure N)
    (Measure.pi fun _ : Fin m => LogdetLean.GramHafnian.standardRealGaussianVectorMeasure N)
  exact h

private theorem h9U03MatrixRotationEqMul {m N : ℕ}
    {D : Matrix (Fin N) (Fin N) ℝ} (hD : D.IsHermitian)
    (G : Matrix (Fin m) (Fin N) ℝ) :
    h9U03MatrixRotation (m := m) hD G =
      G * (hD.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℝ) := by
  ext i j
  change (hD.eigenvectorBasis.repr (WithLp.toLp 2 (G i))).ofLp j = _
  rw [OrthonormalBasis.repr_apply_apply]
  change inner ℝ (hD.eigenvectorBasis j) (WithLp.toLp 2 (G i)) =
    ∑ k, G i k * Matrix.transpose
      (↑hD.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℝ) j k
  rw [hD.eigenvectorUnitary_transpose_apply]
  simp [PiLp.inner_apply]

private theorem h9U03GramMatrixRotation {m N : ℕ}
    {D : Matrix (Fin N) (Fin N) ℝ} (hD : D.IsHermitian)
    (G : Matrix (Fin m) (Fin N) ℝ) :
    realWishartGram (h9U03MatrixRotation (m := m) hD G) =
      star (hD.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℝ) *
        realWishartGram G *
          (hD.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℝ) := by
  have hstar : Matrix.transpose
      (↑hD.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℝ) =
      star (↑hD.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℝ) := by
    ext i j
    simp
  rw [h9U03MatrixRotationEqMul hD G]
  simp only [realWishartGram, Matrix.transpose_mul, Matrix.mul_assoc]
  rw [hstar]

private theorem h9U03TraceMulEqDiagonalRotated {N : ℕ}
    {D W : Matrix (Fin N) (Fin N) ℝ} (hD : D.IsHermitian) :
    Matrix.trace (D * W) =
      Matrix.trace (Matrix.diagonal hD.eigenvalues *
        (star (hD.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℝ) * W *
          (hD.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℝ))) := by
  conv_lhs => rw [hD.spectral_theorem]
  simp only [Unitary.conjStarAlgAut_apply]
  change
    ((hD.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℝ) *
      Matrix.diagonal hD.eigenvalues *
      star (hD.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℝ) * W).trace = _
  calc
    _ = ((hD.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℝ) *
          (Matrix.diagonal hD.eigenvalues *
            star (hD.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℝ) * W)).trace := by
          simp only [Matrix.mul_assoc]
    _ = ((Matrix.diagonal hD.eigenvalues *
            star (hD.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℝ) * W) *
          (hD.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℝ)).trace :=
          Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]

private theorem h9U03TracePowEqSumEigenvalues {N r : ℕ}
    {D : Matrix (Fin N) (Fin N) ℝ} (hD : D.IsHermitian) :
    Matrix.trace (D ^ r) = ∑ i, hD.eigenvalues i ^ r := by
  have hdiagpow : Matrix.diagonal hD.eigenvalues ^ r =
      Matrix.diagonal (fun i => hD.eigenvalues i ^ r) := by
    induction r with
    | zero => simpa using (Matrix.diagonal_one (n := Fin N) (α := ℝ)).symm
    | succ r ih =>
        rw [pow_succ, ih, Matrix.diagonal_mul_diagonal]
        ext i j
        simp [pow_succ]
  conv_lhs => rw [hD.spectral_theorem]
  rw [← map_pow]
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul]
  change (Matrix.diagonal hD.eigenvalues ^ r).trace = _
  rw [hdiagpow]
  simp [Matrix.trace]

private theorem h9U03DiagonalFixedDenominatorFluctuation {m N : ℕ} (l : Fin N → ℝ)
    (G : Matrix (Fin m) (Fin N) ℝ) :
    h9U03FixedDenominatorGaussianFluctuation (Matrix.diagonal l) G = h9U03DiagonalMatrixFluctuation l G := by
  simp only [h9U03FixedDenominatorGaussianFluctuation, h9U03DiagonalMatrixFluctuation, h9U03DiagonalRowFluctuation, h9U03WeightedSum,
    realWishartGram, Matrix.trace, Matrix.diag_apply]
  simp_rw [Matrix.diagonal_mul]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.diagonal_apply_eq]
  rw [Finset.sum_comm]
  simp_rw [Finset.mul_sum, mul_sub, mul_one, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  ring

private theorem h9U03FixedDenominatorFluctuationEqDiagonalRotated {m N : ℕ}
    {D : Matrix (Fin N) (Fin N) ℝ} (hD : D.IsHermitian)
    (G : Matrix (Fin m) (Fin N) ℝ) :
    h9U03FixedDenominatorGaussianFluctuation D G =
      h9U03DiagonalMatrixFluctuation hD.eigenvalues (h9U03MatrixRotation (m := m) hD G) := by
  rw [← h9U03DiagonalFixedDenominatorFluctuation]
  unfold h9U03FixedDenominatorGaussianFluctuation
  rw [h9U03TraceMulEqDiagonalRotated hD]
  rw [← h9U03GramMatrixRotation hD G]
  have htrD := h9U03TracePowEqSumEigenvalues (r := 1) hD
  simp only [pow_one] at htrD
  have htrDiag : Matrix.trace (Matrix.diagonal hD.eigenvalues) =
      ∑ i, hD.eigenvalues i := by simp [Matrix.trace]
  rw [htrD, htrDiag]

private theorem h9U03StandardGaussianQuadraticFourthWickGeneral {m N : ℕ} (D : Matrix (Fin N) (Fin N) ℝ)
    (hD : D.transpose = D) :
    Integrable (fun G => h9U03FixedDenominatorGaussianFluctuation (m := m) D G ^ 4)
      (standardRealGaussianMatrixMeasure m N) ∧
    (∫ G, h9U03FixedDenominatorGaussianFluctuation (m := m) D G ^ 4
        ∂(standardRealGaussianMatrixMeasure m N)) =
      48 * (m : ℝ) * Matrix.trace (D ^ 4) +
        12 * (m : ℝ) ^ 2 * (Matrix.trace (D ^ 2)) ^ 2 := by
  have hH : D.IsHermitian := by simpa [Matrix.IsHermitian] using hD
  have hDiag := h9U03DiagonalMatrixData (m := m) hH.eigenvalues
  have hMP := h9U03MatrixRotationMeasurePreserving (m := m) hH
  constructor
  · have hcomp := hMP.integrable_comp_of_integrable hDiag.integrable_four
    apply hcomp.congr
    filter_upwards with G
    rw [h9U03FixedDenominatorFluctuationEqDiagonalRotated hH G]
    rfl
  · calc
      ∫ G, h9U03FixedDenominatorGaussianFluctuation D G ^ 4 ∂(standardRealGaussianMatrixMeasure m N) =
          ∫ G, h9U03DiagonalMatrixFluctuation hH.eigenvalues
            (h9U03MatrixRotation (m := m) hH G) ^ 4
            ∂(standardRealGaussianMatrixMeasure m N) :=
        integral_congr_ae (Filter.Eventually.of_forall fun G =>
          congrArg (fun x : ℝ => x ^ 4) (h9U03FixedDenominatorFluctuationEqDiagonalRotated hH G))
      _ = ∫ G, h9U03DiagonalMatrixFluctuation hH.eigenvalues G ^ 4
            ∂(standardRealGaussianMatrixMeasure m N) :=
        hMP.integral_comp' (fun G => h9U03DiagonalMatrixFluctuation hH.eigenvalues G ^ 4)
      _ = 48 * (m : ℝ) * ∑ i, hH.eigenvalues i ^ 4 +
          12 * (m : ℝ) ^ 2 * (∑ i, hH.eigenvalues i ^ 2) ^ 2 := hDiag.fourth
      _ = 48 * (m : ℝ) * Matrix.trace (D ^ 4) +
          12 * (m : ℝ) ^ 2 * (Matrix.trace (D ^ 2)) ^ 2 := by
        rw [h9U03TracePowEqSumEigenvalues (r := 4) hH,
          h9U03TracePowEqSumEigenvalues (r := 2) hH]

/-- The deterministic standard-Gaussian fourth Wick lemma required by the exact U03 reduction. -/
theorem h9StandardGaussianQuadraticFourthWick (N : ℕ) :
    H9StandardGaussianQuadraticFourthWick N := by
  intro D hD
  simpa using
    h9U03StandardGaussianQuadraticFourthWickGeneral (m := N + 1) D hD

/-- Audited U03 contract mirror instantiated from the proved standard-Gaussian Wick lemma. -/
theorem h9U03GaussianFourthContractExactReduction_standardGaussianWick (N : ℕ) :
    H9U03GaussianFourthContractExactReduction N :=
  h9U03GaussianFourthContractExactReduction_of_standardGaussianQuadraticFourthWick
    N (h9StandardGaussianQuadraticFourthWick N)

#print axioms h9_symmetric_trace_four_le_trace_two_sq_foundational
#print axioms h9U03GaussianFourthContractExactReduction_of_standardGaussianQuadraticFourthWick
#print axioms h9StandardGaussianQuadraticFourthWick
#print axioms h9U03GaussianFourthContractExactReduction_standardGaussianWick

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
