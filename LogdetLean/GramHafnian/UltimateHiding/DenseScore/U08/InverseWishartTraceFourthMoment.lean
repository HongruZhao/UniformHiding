import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.BetaPrimeMomentInputsConditional
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod

/-!
# Axiom-free fourth-moment closure for denominator inverse-Wishart traces

The entry-product theorem is converted here into the exact qualitative trace
facts needed by H8 and H10.  At `K >= 2*N+8`, the scaled denominator trace is
in `L^4` and its squared trace is in `L^2`; the trace of the matrix square is
also in `L^2`.  No Poincare estimate and no H6 input is used.

The final two arithmetic lemmas record the important threshold split for the
regularized Poincare route: fourth inverse-entry products are available at the
global qualitative threshold, whereas a direct gradient estimate for
`tr(C_epsilon^2)` needs order five.  Order five follows in the dense branch
`16*N <= K`, for every `N >= 1`.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.DenseScore
open LogdetLean.GramHafnian.Wishart

/-- A single entry of an inverse real-Wishart matrix belongs to `L^4` once
there are eight spare Gaussian degrees of freedom. -/
theorem inverseWishartEntry_memLp_four_standardGaussian
    {k p : ℕ} (hgap : p + 8 ≤ k) (i j : Fin p) :
    MemLp (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        (realWishartGram R)⁻¹ i j) 4
      (standardRealGaussianMatrixMeasure k p) := by
  let indices : Fin 4 → Fin p × Fin p := fun _ ↦ (i, j)
  have hprod : Integrable
      (inverseWishartEntryProduct (k := k) indices)
      (standardRealGaussianMatrixMeasure k p) :=
    integrable_inverseWishartEntryProduct_standardGaussian
      (by omega) indices
  have hmeas : AEStronglyMeasurable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        (realWishartGram R)⁻¹ i j)
      (standardRealGaussianMatrixMeasure k p) := by
    have hGram : Measurable
        (fun R : Matrix (Fin k) (Fin p) ℝ ↦ realWishartGram R) := by
      unfold realWishartGram
      refine measurable_pi_lambda _ fun a ↦ measurable_pi_lambda _ fun b ↦ ?_
      simp only [Matrix.mul_apply, Matrix.transpose_apply]
      fun_prop
    have hinv : Measurable
        (fun R : Matrix (Fin k) (Fin p) ℝ ↦ (realWishartGram R)⁻¹) :=
      (measurable_realMatrix_inv p).comp hGram
    exact ((measurable_pi_apply j).comp
      ((measurable_pi_apply i).comp hinv)).aestronglyMeasurable
  apply (integrable_norm_rpow_iff hmeas (by norm_num) (by norm_num)).mp
  simpa [indices, inverseWishartEntryProduct, Real.rpow_natCast, norm_pow]
    using hprod.norm

/-- The inverse-Wishart trace belongs to `L^4` under the same sharp integer
margin. -/
theorem inverseWishartTrace_memLp_four_standardGaussian
    {k p : ℕ} (hgap : p + 8 ≤ k) :
    MemLp (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        Matrix.trace (realWishartGram R)⁻¹) 4
      (standardRealGaussianMatrixMeasure k p) := by
  have hsum : MemLp
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        ∑ i : Fin p, (realWishartGram R)⁻¹ i i) 4
      (standardRealGaussianMatrixMeasure k p) :=
    memLp_finsetSum Finset.univ fun i _ ↦
      inverseWishartEntry_memLp_four_standardGaussian hgap i i
  simpa [Matrix.trace] using hsum

/-- The trace of the squared inverse-Wishart matrix belongs to `L^2`.
This is exactly the finite fourth-order entry contraction. -/
theorem inverseWishartTraceSquare_memLp_two_standardGaussian
    {k p : ℕ} (hgap : p + 8 ≤ k) :
    MemLp (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        Matrix.trace ((realWishartGram R)⁻¹ ^ 2)) 2
      (standardRealGaussianMatrixMeasure k p) := by
  have htriple : ENNReal.HolderTriple 4 4 2 :=
    ENNReal.HolderTriple.of_toReal (by constructor <;> norm_num)
  let _ := htriple
  have hsum : MemLp
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        ∑ i : Fin p, ∑ j : Fin p,
          (realWishartGram R)⁻¹ i j * (realWishartGram R)⁻¹ j i) 2
      (standardRealGaussianMatrixMeasure k p) :=
    memLp_finsetSum Finset.univ fun i _ ↦
      memLp_finsetSum Finset.univ fun j _ ↦
        (inverseWishartEntry_memLp_four_standardGaussian hgap j i).mul'
          (inverseWishartEntry_memLp_four_standardGaussian hgap i j)
  simpa [Matrix.trace, pow_two, Matrix.mul_apply] using hsum

/-- `L^4` for the literal scaled denominator trace at the exact H8/H10
qualitative threshold. -/
theorem denominatorTraceOneSource_memLp_four
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K) :
    MemLp (denominatorTraceOneSource N K) 4
      (realBetaPrimeGaussianSourceLaw N K) := by
  let muA := standardRealGaussianMatrixMeasure (N + 1) N
  let muB := standardRealGaussianMatrixMeasure (K - N) N
  letI : IsProbabilityMeasure muA :=
    standardRealGaussianMatrixMeasure_isProbability_internal _ _
  letI : IsProbabilityMeasure muB :=
    standardRealGaussianMatrixMeasure_isProbability_internal _ _
  have hB : MemLp (fun R : Matrix (Fin (K - N)) (Fin N) ℝ ↦
      concreteCOEExponent N K * Matrix.trace (realWishartGram R)⁻¹) 4 muB := by
    exact (inverseWishartTrace_memLp_four_standardGaussian
      (k := K - N) (p := N) (by omega)).const_smul
        (concreteCOEExponent N K)
  have hlift := hB.comp_snd muA
  apply hlift.ae_eq
  filter_upwards [] with source
  simp [muA, muB, denominatorTraceOneSource,
    scaledInverseWishartDenominator, Matrix.trace_smul, smul_eq_mul]

/-- `L^2` for the trace of the squared literal scaled denominator at the
exact H8/H10 qualitative threshold. -/
theorem denominatorTraceTwoSource_memLp_two
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K) :
    MemLp (denominatorTraceTwoSource N K) 2
      (realBetaPrimeGaussianSourceLaw N K) := by
  let muA := standardRealGaussianMatrixMeasure (N + 1) N
  let muB := standardRealGaussianMatrixMeasure (K - N) N
  letI : IsProbabilityMeasure muA :=
    standardRealGaussianMatrixMeasure_isProbability_internal _ _
  letI : IsProbabilityMeasure muB :=
    standardRealGaussianMatrixMeasure_isProbability_internal _ _
  have hB : MemLp (fun R : Matrix (Fin (K - N)) (Fin N) ℝ ↦
      concreteCOEExponent N K ^ 2 *
        Matrix.trace ((realWishartGram R)⁻¹ ^ 2)) 2 muB := by
    exact (inverseWishartTraceSquare_memLp_two_standardGaussian
      (k := K - N) (p := N) (by omega)).const_smul
        (concreteCOEExponent N K ^ 2)
  have hlift := hB.comp_snd muA
  apply hlift.ae_eq
  filter_upwards [] with source
  simp [muA, muB, denominatorTraceTwoSource,
    scaledInverseWishartDenominator, pow_two, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, mul_assoc]

/-- Exact first moment of the scaled inverse-Wishart denominator.  The scale
`c = K - 2*N - 1` cancels the inverse-Wishart trace denominator. -/
theorem denominatorTraceOneSource_integral_eq
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K) :
    (∫ source, denominatorTraceOneSource N K source
      ∂(realBetaPrimeGaussianSourceLaw N K)) = (N : ℝ) := by
  let muA := standardRealGaussianMatrixMeasure (N + 1) N
  let muB := standardRealGaussianMatrixMeasure (K - N) N
  letI : IsProbabilityMeasure muA :=
    standardRealGaussianMatrixMeasure_isProbability_internal _ _
  letI : IsProbabilityMeasure muB :=
    standardRealGaussianMatrixMeasure_isProbability_internal _ _
  have hmean := standardGaussian_inverseWishart_trace_mean
    (k := K - N) (p := N) (by omega)
  have hNK : N ≤ K := by omega
  have hden :
      (((K - N : ℕ) : ℝ) - (N : ℝ) - 1) =
        concreteCOEExponent N K := by
    rw [Nat.cast_sub hNK]
    unfold concreteCOEExponent
    ring
  have hcpos : 0 < concreteCOEExponent N K := by
    have hgapR : ((2 * N + 8 : ℕ) : ℝ) ≤ (K : ℝ) := by
      exact_mod_cast hgap
    push_cast at hgapR
    unfold concreteCOEExponent
    linarith
  unfold realBetaPrimeGaussianSourceLaw denominatorTraceOneSource
    scaledInverseWishartDenominator
  simp_rw [Matrix.trace_smul, smul_eq_mul]
  change (∫ source,
      (fun R : Matrix (Fin (K - N)) (Fin N) ℝ ↦
        concreteCOEExponent N K * Matrix.trace (realWishartGram R)⁻¹)
        source.2 ∂muA.prod muB) = (N : ℝ)
  rw [integral_fun_snd (μ := muA) (ν := muB)
    (fun R : Matrix (Fin (K - N)) (Fin N) ℝ ↦
      concreteCOEExponent N K * Matrix.trace (realWishartGram R)⁻¹),
    integral_const_mul]
  rw [probReal_univ, one_smul, hmean, hden]
  field_simp [hcpos.ne']

/-- Centered first denominator trace in `L^4`, with no quantitative bound. -/
theorem denominatorTraceOneSource_centered_memLp_four
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K) :
    MemLp (fun source ↦ denominatorTraceOneSource N K source - (N : ℝ)) 4
      (realBetaPrimeGaussianSourceLaw N K) := by
  letI : IsProbabilityMeasure (realBetaPrimeGaussianSourceLaw N K) :=
    realBetaPrimeGaussianSourceLaw_isProbability N K
  exact (denominatorTraceOneSource_memLp_four hgap).sub (memLp_const (N : ℝ))

/-- The first denominator trace has an integrable pointwise square. -/
theorem denominatorTraceOneSource_square_integrable
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K) :
    Integrable (fun source ↦ denominatorTraceOneSource N K source ^ 2)
      (realBetaPrimeGaussianSourceLaw N K) := by
  letI : IsProbabilityMeasure (realBetaPrimeGaussianSourceLaw N K) :=
    realBetaPrimeGaussianSourceLaw_isProbability N K
  exact ((denominatorTraceOneSource_memLp_four hgap).mono_exponent
    (by norm_num)).integrable_sq

/-- The second denominator trace is integrable. -/
theorem denominatorTraceTwoSource_integrable
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K) :
    Integrable (denominatorTraceTwoSource N K)
      (realBetaPrimeGaussianSourceLaw N K) := by
  letI : IsProbabilityMeasure (realBetaPrimeGaussianSourceLaw N K) :=
    realBetaPrimeGaussianSourceLaw_isProbability N K
  exact memLp_one_iff_integrable.mp
    ((denominatorTraceTwoSource_memLp_two hgap).mono_exponent (by norm_num))

/-- Centered second denominator trace in `L^2`, with no quantitative bound. -/
theorem denominatorTraceTwoSource_centered_memLp_two
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K) :
    MemLp (fun source ↦ denominatorTraceTwoSource N K source -
      ∫ z, denominatorTraceTwoSource N K z
        ∂(realBetaPrimeGaussianSourceLaw N K)) 2
      (realBetaPrimeGaussianSourceLaw N K) := by
  letI : IsProbabilityMeasure (realBetaPrimeGaussianSourceLaw N K) :=
    realBetaPrimeGaussianSourceLaw_isProbability N K
  exact (denominatorTraceTwoSource_memLp_two hgap).sub (memLp_const _)

/-- The exact global threshold provides every denominator product through
degree four. -/
theorem betaPrime_order_four_threshold
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K) :
    N + 2 * 4 ≤ K - N := by
  omega

/-- In the dense regime, the fifth inverse-entry moment needed by the direct
Poincare gradient of `tr(C_epsilon^2)` is also available. -/
theorem dense_implies_betaPrime_order_five_threshold
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    N + 2 * 5 ≤ K - N := by
  omega

/-- Order-five denominator entry products, used only in the dense Poincare
branch. -/
theorem integrable_betaPrimeDenominator_inverseEntryProduct_order_five_dense
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K)
    (indices : Fin 5 → Fin N × Fin N) :
    Integrable
      (inverseWishartEntryProduct (k := K - N) indices)
      (standardRealGaussianMatrixMeasure (K - N) N) := by
  exact integrable_inverseWishartEntryProduct_standardGaussian
    (dense_implies_betaPrime_order_five_threshold hN hdense) indices

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08
