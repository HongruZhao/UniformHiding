import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.InverseWishartTraceFourthMoment
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.InverseWishartSecondMomentLedger
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.H8_Proof
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.GaussianPoincareRegularizationConditional
import Mathlib.Analysis.Matrix.Order
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic

/-!
# The raw beta-prime second trace is genuinely cubic

This file isolates a structural obstruction to the proposed U10 raw
second-trace `O(N^2)` formal-mean contract.  It uses no inverse-Wishart
second-entry formula: positivity, the exact first-trace mean, and Jensen
already force a cubic lower bound.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators MatrixOrder

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08

noncomputable section

open LogdetLean.GramHafnian.Wishart
open Matrix Unitary

/-- For a positive-semidefinite matrix, the square of the trace is at most
the dimension times the trace of the square. -/
theorem sq_trace_le_card_mul_trace_sq
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A.PosSemidef) :
    Matrix.trace A ^ 2 ≤ (Fintype.card n : ℝ) * Matrix.trace (A ^ 2) := by
  let hH : A.IsHermitian := hA.isHermitian
  have htrace : Matrix.trace A = ∑ i, hH.eigenvalues i :=
    hH.trace_eq_sum_eigenvalues
  have htrace2 : Matrix.trace (A ^ 2) =
      ∑ i, (hH.eigenvalues i) ^ 2 := by
    conv_lhs => rw [hH.spectral_theorem]
    rw [← map_pow]
    rw [conjStarAlgAut_apply, Matrix.trace_mul_cycle,
      Unitary.coe_star_mul_self, one_mul]
    rw [Matrix.diagonal_pow, Matrix.trace_diagonal]
    rfl
  rw [htrace, htrace2]
  simpa using
    (sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset n))
      (f := fun i ↦ hH.eigenvalues i))

/-- The same inequality for a product of two positive-semidefinite matrices.
Although `C * A` need not be symmetric, it is trace-similar to the
positive-semidefinite sandwich `sqrt(C) * A * sqrt(C)`. -/
theorem sq_trace_mul_le_card_mul_trace_mul_sq
    {n : Type*} [Fintype n] [DecidableEq n]
    (C A : Matrix n n ℝ) (hC : C.PosSemidef) (hA : A.PosSemidef) :
    Matrix.trace (C * A) ^ 2 ≤
      (Fintype.card n : ℝ) * Matrix.trace ((C * A) ^ 2) := by
  let S : Matrix n n ℝ := CFC.sqrt C
  let P : Matrix n n ℝ := S * A * S
  have hS : S.PosSemidef := by
    exact (CFC.sqrt_nonneg C).posSemidef
  have hSstar : Sᴴ = S := hS.isHermitian.eq
  have hP : P.PosSemidef := by
    have h := hA.mul_mul_conjTranspose_same S
    rw [hSstar] at h
    exact h
  have hSS : S * S = C := by
    simpa only [S, pow_two] using CFC.sq_sqrt C
  have htrace : Matrix.trace P = Matrix.trace (C * A) := by
    calc
      Matrix.trace P = Matrix.trace ((S * A) * S) := by rfl
      _ = Matrix.trace (S * S * A) := Matrix.trace_mul_cycle S A S
      _ = Matrix.trace (C * A) := by rw [hSS]
  have htrace2 : Matrix.trace (P ^ 2) = Matrix.trace ((C * A) ^ 2) := by
    calc
      Matrix.trace (P ^ 2) =
          Matrix.trace ((S * A * S * S * A) * S) := by
            simp only [P, pow_two, mul_assoc]
      _ = Matrix.trace (S * (A * S * S * A) * S) := by
        simp only [mul_assoc]
      _ = Matrix.trace (S * S * (A * S * S * A)) :=
        Matrix.trace_mul_cycle S (A * S * S * A) S
      _ = Matrix.trace ((S * S) * A * (S * S) * A) := by
        simp only [mul_assoc]
      _ = Matrix.trace (C * A * C * A) := by rw [hSS]
      _ = Matrix.trace ((C * A) ^ 2) := by simp only [pow_two, mul_assoc]
  rw [← htrace, ← htrace2]
  exact sq_trace_le_card_mul_trace_sq P hP

/-- Pointwise source-level trace inequality for the scaled beta-prime
matrix.  The only parameter hypothesis is nonnegativity of the scale `c`. -/
theorem betaPrimeTraceOneSource_sq_le_dimension_mul_traceTwoSource
    {N K : ℕ} (hc : 0 ≤ concreteCOEExponent N K)
    (source : BetaPrimeGaussianSource N K) :
    betaPrimeTraceOneSource N K source ^ 2 ≤
      (N : ℝ) * betaPrimeTraceTwoSource N K source := by
  let C := scaledInverseWishartDenominator N K source
  let A := realWishartGram source.1
  have hC : C.PosSemidef := by
    dsimp only [C, scaledInverseWishartDenominator]
    exact (realWishartGram_inv_posSemidef source.2).smul hc
  have hA : A.PosSemidef := by
    exact realWishartGram_posSemidef source.1
  have h := sq_trace_mul_le_card_mul_trace_mul_sq C A hC hA
  simpa only [C, A, Fintype.card_fin,
    betaPrimeTraceOneSource_eq_scaledInverseWishart_trace,
    betaPrimeTraceTwoSource_eq_scaledInverseWishart_trace,
    pow_two, mul_assoc] using h

/-! ## Axiom-free integrability of the two source traces -/

/-- Every scalar coordinate of a finite standard-Gaussian matrix belongs to
`L^4`. -/
theorem standardRealGaussianMatrix_coordinate_memLp_four
    {rows p : ℕ} (a : Fin rows) (i : Fin p) :
    MemLp (fun R : Matrix (Fin rows) (Fin p) ℝ ↦ R a i) 4
      (standardRealGaussianMatrixMeasure rows p) := by
  have hscalar : MemLp (id : ℝ → ℝ) 4 (gaussianReal 0 1) :=
    memLp_id_gaussianReal' 4 (by norm_num)
  have hvector : MemLp (fun x : Fin p → ℝ ↦ x i) 4
      (standardRealGaussianVectorMeasure p) := by
    unfold standardRealGaussianVectorMeasure
    have h := hscalar.comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin p ↦ gaussianReal 0 1) i)
    change MemLp (fun x : Fin p → ℝ ↦ x i) 4
      (Measure.pi fun _ : Fin p ↦ gaussianReal 0 1) at h
    exact h
  have hcurried : MemLp (fun R : Fin rows → Fin p → ℝ ↦ R a i) 4
      (Measure.pi fun _ : Fin rows ↦ standardRealGaussianVectorMeasure p) := by
    have h := hvector.comp_measurePreserving
      (measurePreserving_eval
        (fun _ : Fin rows ↦ standardRealGaussianVectorMeasure p) a)
    change MemLp (fun R : Fin rows → Fin p → ℝ ↦ R a i) 4
      (Measure.pi fun _ : Fin rows ↦ standardRealGaussianVectorMeasure p) at h
    exact h
  rw [← show Measure.map (curriedMatrixMeasurableEquiv rows p)
      (Measure.pi fun _ : Fin rows ↦ standardRealGaussianVectorMeasure p) =
      standardRealGaussianMatrixMeasure rows p by
    unfold standardRealGaussianMatrixMeasure
    change Measure.map (id : (Fin rows → Fin p → ℝ) →
        (Fin rows → Fin p → ℝ))
      (Measure.pi fun _ : Fin rows ↦ standardRealGaussianVectorMeasure p) =
      Measure.pi fun _ : Fin rows ↦ standardRealGaussianVectorMeasure p
    exact Measure.map_id]
  have hcoordMeas : Measurable
      (fun R : Matrix (Fin rows) (Fin p) ℝ ↦ R a i) := by
    fun_prop
  apply (memLp_map_measure_iff hcoordMeas.aestronglyMeasurable
    (curriedMatrixMeasurableEquiv rows p).measurable.aemeasurable).2
  change MemLp (fun R : Fin rows → Fin p → ℝ ↦ R a i) 4
    (Measure.pi fun _ : Fin rows ↦ standardRealGaussianVectorMeasure p)
  exact hcurried

/-- A product of two real-Wishart entries is integrable.  This is the only
finite Gaussian fourth-moment fact needed for the raw trace-two
integrability proof below. -/
theorem integrable_realWishartGram_entry_mul_entry_standardGaussian
    {rows p : ℕ} (i j k l : Fin p) :
    Integrable
      (fun R : Matrix (Fin rows) (Fin p) ℝ ↦
        realWishartGram R i j * realWishartGram R k l)
      (standardRealGaussianMatrixMeasure rows p) := by
  have h442 : ENNReal.HolderTriple 4 4 2 :=
    ENNReal.HolderTriple.of_toReal (by constructor <;> norm_num)
  let _ := h442
  have hij : MemLp
      (fun R : Matrix (Fin rows) (Fin p) ℝ ↦ realWishartGram R i j) 2
      (standardRealGaussianMatrixMeasure rows p) := by
    simp only [realWishartGram, Matrix.mul_apply, Matrix.transpose_apply]
    apply memLp_finsetSum Finset.univ
    intro a ha
    exact (standardRealGaussianMatrix_coordinate_memLp_four a j).mul'
      (standardRealGaussianMatrix_coordinate_memLp_four a i)
  have hkl : MemLp
      (fun R : Matrix (Fin rows) (Fin p) ℝ ↦ realWishartGram R k l) 2
      (standardRealGaussianMatrixMeasure rows p) := by
    simp only [realWishartGram, Matrix.mul_apply, Matrix.transpose_apply]
    apply memLp_finsetSum Finset.univ
    intro a ha
    exact (standardRealGaussianMatrix_coordinate_memLp_four a l).mul'
      (standardRealGaussianMatrix_coordinate_memLp_four a k)
  have h221 : ENNReal.HolderTriple 2 2 1 :=
    ENNReal.HolderTriple.of_toReal (by constructor <;> norm_num)
  let _ := h221
  exact memLp_one_iff_integrable.mp (hkl.mul' hij)

/-- One fully expanded summand of `tr(C A C A)` is integrable under the
independent numerator/denominator Gaussian source law. -/
theorem integrable_betaPrimeTraceTwoSource_summand
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K) (i j k l : Fin N) :
    Integrable
      (fun source : BetaPrimeGaussianSource N K ↦
        scaledInverseWishartDenominator N K source i j *
          realWishartGram source.1 j k *
          scaledInverseWishartDenominator N K source k l *
          realWishartGram source.1 l i)
      (realBetaPrimeGaussianSourceLaw N K) := by
  let indices : Fin 2 → Fin N × Fin N := ![(i, j), (k, l)]
  have hA := integrable_realWishartGram_entry_mul_entry_standardGaussian
    (rows := N + 1) j k l i
  have hB :=
    integrable_betaPrimeDenominator_inverseEntryProduct_order_le_four
      hgap (by norm_num) indices
  have hprod := hA.mul_prod hB
  have hscaled := hprod.const_mul (concreteCOEExponent N K ^ 2)
  unfold realBetaPrimeGaussianSourceLaw
  simpa [Function.uncurry, scaledInverseWishartDenominator, indices,
    inverseWishartEntryProduct, pow_two, smul_eq_mul, mul_assoc, mul_comm,
    mul_left_comm] using hscaled

/-- The raw second beta-prime trace is integrable at the qualitative
fourth inverse-entry threshold. -/
theorem integrable_betaPrimeTraceTwoSource_internal
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K) :
    Integrable (betaPrimeTraceTwoSource N K)
      (realBetaPrimeGaussianSourceLaw N K) := by
  rw [show betaPrimeTraceTwoSource N K = fun source ↦
      Matrix.trace (scaledInverseWishartDenominator N K source *
        realWishartGram source.1 *
        scaledInverseWishartDenominator N K source *
        realWishartGram source.1) by
    funext source
    exact betaPrimeTraceTwoSource_eq_scaledInverseWishart_trace N K source]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Finset.sum_mul]
  apply integrable_finsetSum Finset.univ
  intro i hi
  apply integrable_finsetSum Finset.univ
  intro j hj
  apply integrable_finsetSum Finset.univ
  intro k hk
  apply integrable_finsetSum Finset.univ
  intro l hl
  exact integrable_betaPrimeTraceTwoSource_summand hgap i l k j

/-- The square of the raw first beta-prime trace is integrable.  The proof
uses the PSD trace inequality to dominate it by `N * tr(Y^2)`. -/
theorem integrable_betaPrimeTraceOneSource_sq_internal
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K) :
    Integrable (fun source ↦ betaPrimeTraceOneSource N K source ^ 2)
      (realBetaPrimeGaussianSourceLaw N K) := by
  have hc : 0 ≤ concreteCOEExponent N K := by
    have hgapR : ((2 * N + 8 : ℕ) : ℝ) ≤ (K : ℝ) := by
      exact_mod_cast hgap
    push_cast at hgapR
    unfold concreteCOEExponent
    linarith
  have htwo := integrable_betaPrimeTraceTwoSource_internal hgap
  have hmajor := htwo.const_mul (N : ℝ)
  have honeMeas : Measurable (betaPrimeTraceOneSource N K) := by
    unfold betaPrimeTraceOneSource betaPrimeYTraceOne
    exact measurable_const.mul ((measurable_pi_apply _).comp
      (measurable_realBetaPrimeTracePowerVector_internal 4 N K))
  apply Integrable.mono' hmajor (honeMeas.pow_const 2).aestronglyMeasurable
  filter_upwards [] with source
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact betaPrimeTraceOneSource_sq_le_dimension_mul_traceTwoSource hc source

/-- Equivalently, the raw first beta-prime trace belongs to `L^2`. -/
theorem betaPrimeTraceOneSource_memLp_two_internal
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K) :
    MemLp (betaPrimeTraceOneSource N K) 2
      (realBetaPrimeGaussianSourceLaw N K) := by
  have honeMeas : Measurable (betaPrimeTraceOneSource N K) := by
    unfold betaPrimeTraceOneSource betaPrimeYTraceOne
    exact measurable_const.mul ((measurable_pi_apply _).comp
      (measurable_realBetaPrimeTracePowerVector_internal 4 N K))
  exact (memLp_two_iff_integrable_sq honeMeas.aestronglyMeasurable).2
    (integrable_betaPrimeTraceOneSource_sq_internal hgap)

/-- Jensen's square inequality in the exact `MemLp` form used below. -/
theorem sq_integral_le_integral_sq_probability
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (f : Omega → ℝ) (hf : MemLp f 2 mu) :
    (∫ omega, f omega ∂mu) ^ 2 ≤ ∫ omega, f omega ^ 2 ∂mu := by
  have hvar := variance_nonneg f mu
  rw [variance_eq_sub hf] at hvar
  simpa only [Pi.pow_apply, sub_nonneg] using hvar

/-- The internally proved first beta-prime mean, pulled back to the literal
Gaussian source measure. -/
theorem betaPrimeTraceOneSource_integral_eq_internal
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 2 ≤ K) :
    (∫ source, betaPrimeTraceOneSource N K source
      ∂(realBetaPrimeGaussianSourceLaw N K)) =
      (N : ℝ) * ((N : ℝ) + 1) := by
  have hmean := betaPrimeYTraceOne_integral_external hN hgap
  have hbeta : Measurable (betaPrimeYTraceOne N K) := by
    unfold betaPrimeYTraceOne
    exact measurable_const.mul (measurable_pi_apply _)
  unfold betaPrimeTraceFourLaw at hmean
  rw [integral_map
    (measurable_realBetaPrimeTracePowerVector_internal 4 N K).aemeasurable
    hbeta.aestronglyMeasurable] at hmean
  simpa only [Function.comp_apply, betaPrimeTraceOneSource] using hmean

/-- Positivity and Jensen force the raw source-level second-trace mean to be
at least `N * (N+1)^2`; no inverse-Wishart second-moment identity is used. -/
theorem betaPrimeTraceTwoSource_integral_ge_cube_internal
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    (N : ℝ) * ((N : ℝ) + 1) ^ 2 ≤
      ∫ source, betaPrimeTraceTwoSource N K source
        ∂(realBetaPrimeGaussianSourceLaw N K) := by
  letI : IsProbabilityMeasure (realBetaPrimeGaussianSourceLaw N K) :=
    realBetaPrimeGaussianSourceLaw_isProbability N K
  have hc : 0 ≤ concreteCOEExponent N K := by
    have hgapR : ((2 * N + 8 : ℕ) : ℝ) ≤ (K : ℝ) := by
      exact_mod_cast hgap
    push_cast at hgapR
    unfold concreteCOEExponent
    linarith
  have honeSq := integrable_betaPrimeTraceOneSource_sq_internal hgap
  have htwo := integrable_betaPrimeTraceTwoSource_internal hgap
  have hmajor := htwo.const_mul (N : ℝ)
  have hdom :
      (∫ source, betaPrimeTraceOneSource N K source ^ 2
        ∂(realBetaPrimeGaussianSourceLaw N K)) ≤
      ∫ source, (N : ℝ) * betaPrimeTraceTwoSource N K source
        ∂(realBetaPrimeGaussianSourceLaw N K) := by
    exact integral_mono honeSq hmajor fun source ↦
      betaPrimeTraceOneSource_sq_le_dimension_mul_traceTwoSource hc source
  rw [integral_const_mul] at hdom
  have hjensen := sq_integral_le_integral_sq_probability
    (realBetaPrimeGaussianSourceLaw N K)
    (betaPrimeTraceOneSource N K)
    (betaPrimeTraceOneSource_memLp_two_internal hgap)
  have hmean := betaPrimeTraceOneSource_integral_eq_internal
    (N := N) (K := K) hN (by omega)
  rw [hmean] at hjensen
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  nlinarith [sq_nonneg ((N : ℝ) + 1)]

/-- The exposed beta-prime second-trace integral is definitionally the
source integral after the proved measurable pushforward. -/
theorem betaPrimeYTraceTwo_integral_eq_source_internal (N K : ℕ) :
    (∫ u, betaPrimeYTraceTwo N K u ∂(betaPrimeTraceFourLaw N K)) =
      ∫ source, betaPrimeTraceTwoSource N K source
        ∂(realBetaPrimeGaussianSourceLaw N K) := by
  have hbeta : Measurable (betaPrimeYTraceTwo N K) := by
    unfold betaPrimeYTraceTwo
    exact measurable_const.mul (measurable_pi_apply _)
  unfold betaPrimeTraceFourLaw
  rw [integral_map
    (measurable_realBetaPrimeTracePowerVector_internal 4 N K).aemeasurable
    hbeta.aestronglyMeasurable]
  rfl

/-- Cubic lower bound for the actual exposed raw second-trace formal mean. -/
theorem betaPrimeYTraceTwo_integral_ge_cube_internal
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    (N : ℝ) * ((N : ℝ) + 1) ^ 2 ≤
      ∫ u, betaPrimeYTraceTwo N K u ∂(betaPrimeTraceFourLaw N K) := by
  rw [betaPrimeYTraceTwo_integral_eq_source_internal]
  exact betaPrimeTraceTwoSource_integral_ge_cube_internal hN hgap

/-- Concrete counterexample to the raw `O(N^2)` H14 probability contract.
The chosen dimension is `2^40`, exactly the numerical value of the proposed
universal constant. -/
theorem u08H14TraceTwoMeanBoundFormula_counterexample_internal :
    16 * u10TraceTwoCounterexampleDimension ≤ u10TraceTwoCounterexampleK ∧
    denseClassicalMomentConstant *
        (u10TraceTwoCounterexampleDimension : ℝ) ^ 2 <
      |∫ u, betaPrimeYTraceTwo u10TraceTwoCounterexampleDimension
          u10TraceTwoCounterexampleK u
        ∂(betaPrimeTraceFourLaw u10TraceTwoCounterexampleDimension
          u10TraceTwoCounterexampleK)| := by
  have hN : 1 ≤ u10TraceTwoCounterexampleDimension := by
    norm_num [u10TraceTwoCounterexampleDimension]
  have hgap :
      2 * u10TraceTwoCounterexampleDimension + 8 ≤
        u10TraceTwoCounterexampleK := by
    norm_num [u10TraceTwoCounterexampleK,
      u10TraceTwoCounterexampleDimension]
  have hlower := betaPrimeYTraceTwo_integral_ge_cube_internal
    (N := u10TraceTwoCounterexampleDimension)
    (K := u10TraceTwoCounterexampleK) hN hgap
  have hconstant :
      denseClassicalMomentConstant *
          (u10TraceTwoCounterexampleDimension : ℝ) ^ 2 <
        (u10TraceTwoCounterexampleDimension : ℝ) *
          ((u10TraceTwoCounterexampleDimension : ℝ) + 1) ^ 2 := by
    norm_num [denseClassicalMomentConstant,
      u10TraceTwoCounterexampleDimension]
  have hnonneg : 0 ≤
      ∫ u, betaPrimeYTraceTwo u10TraceTwoCounterexampleDimension
          u10TraceTwoCounterexampleK u
        ∂(betaPrimeTraceFourLaw u10TraceTwoCounterexampleDimension
          u10TraceTwoCounterexampleK) := by
    have hcube : 0 ≤
        (u10TraceTwoCounterexampleDimension : ℝ) *
          ((u10TraceTwoCounterexampleDimension : ℝ) + 1) ^ 2 := by
      positivity
    exact hcube.trans hlower
  refine ⟨u10TraceTwoCounterexample_dense, ?_⟩
  rw [abs_of_nonneg hnonneg]
  exact hconstant.trans_le hlower

/-- The exact underlying formula of U10's `u08H14TraceTwoMeanBoundContract`
is false at the concrete dense pair above. -/
theorem u08H14TraceTwoMeanBoundFormula_false_at_counterexample_internal :
    ¬ (16 * u10TraceTwoCounterexampleDimension ≤
          u10TraceTwoCounterexampleK →
        |∫ u, betaPrimeYTraceTwo u10TraceTwoCounterexampleDimension
            u10TraceTwoCounterexampleK u
          ∂(betaPrimeTraceFourLaw u10TraceTwoCounterexampleDimension
            u10TraceTwoCounterexampleK)| ≤
          denseClassicalMomentConstant *
            (u10TraceTwoCounterexampleDimension : ℝ) ^ 2) := by
  intro hcontract
  have hupper := hcontract
    u08H14TraceTwoMeanBoundFormula_counterexample_internal.1
  exact (not_lt_of_ge hupper)
    u08H14TraceTwoMeanBoundFormula_counterexample_internal.2

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08
