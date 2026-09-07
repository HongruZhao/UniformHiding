import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.H14FourthRadialContracts
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.MatsumotoWishartSigmaScaleConversion
import Mathlib.Analysis.Matrix.Order
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic

/-!
# A4 trace-four reduction for the H14 denominator

This module is below every H3--H18 endpoint.  It first uses the already
audited `sigma = I` to `sigma = 2 I` conversion, and only then exposes the
smallest project-side consequence still required from the approved Matsumoto
atom A4: one identity-scale bound for `tr((gamma W⁻¹)^4)`.

All remaining work in this file is axiom-free.  Positive-semidefinite spectral
inequalities reduce the five order-four trace partitions, and hence both H14
Wick polynomials, to that single scalar trace-four producer.  In particular no
raw `O(N^2)` trace-two majorant, H6 contract, or endpoint is imported.
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

private theorem measurable_realMatrix_mul
    {X n : Type*} [MeasurableSpace X] [Fintype n]
    {A B : X → Matrix n n ℝ} (hA : Measurable A) (hB : Measurable B) :
    Measurable (fun x ↦ A x * B x) := by
  refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
  simp only [Matrix.mul_apply]
  exact Finset.measurable_sum _ fun k _ ↦
    ((measurable_pi_apply k).comp ((measurable_pi_apply i).comp hA)).mul
      ((measurable_pi_apply j).comp ((measurable_pi_apply k).comp hB))

private theorem measurable_realMatrix_pow
    {X n : Type*} [MeasurableSpace X] [Fintype n] [DecidableEq n]
    {A : X → Matrix n n ℝ} (hA : Measurable A) :
    ∀ r : ℕ, Measurable (fun x ↦ (A x) ^ r)
  | 0 => by simpa using (measurable_const : Measurable (fun _ : X ↦ (1 : Matrix n n ℝ)))
  | r + 1 => by
      simpa only [pow_succ] using
        measurable_realMatrix_mul (measurable_realMatrix_pow hA r) hA

private theorem measurable_realMatrix_trace
    {X n : Type*} [MeasurableSpace X] [Fintype n]
    {A : X → Matrix n n ℝ} (hA : Measurable A) :
    Measurable (fun x ↦ Matrix.trace (A x)) := by
  unfold Matrix.trace
  exact Finset.measurable_sum _ fun i _ ↦
    (measurable_pi_apply i).comp ((measurable_pi_apply i).comp hA)

/-- Measurability of every scaled inverse-Gram trace power. -/
theorem measurable_scaledInverseGram_trace_pow
    (k p : ℕ) (a : ℝ) (r : ℕ) :
    Measurable (fun R : Matrix (Fin k) (Fin p) ℝ ↦
      Matrix.trace ((a • (realWishartGram R)⁻¹) ^ r)) := by
  have hinv : Measurable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦ (realWishartGram R)⁻¹) :=
    measurable_nonsingInv_realWishartGram_matrix
  have hscaled : Measurable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦ a • (realWishartGram R)⁻¹) := by
    refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
    simp only [Matrix.smul_apply, smul_eq_mul]
    exact measurable_const.mul
      ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hinv))
  exact measurable_realMatrix_trace (measurable_realMatrix_pow hscaled r)

/-- Paper-side identity-scale integrand after the separate project-variable
substitution `d=N`, `beta=(K-N)/2`, and `gamma=beta-(d+1)/2` has been made. -/
def matsumotoIdentityScaledInverseTraceFour (N K : ℕ)
    (R : Matrix (Fin (K - N)) (Fin N) ℝ) : ℝ :=
  Matrix.trace
    ((matsumotoGamma N (matsumotoIntegerShapeBeta (K - N)) •
      (realWishartGram R)⁻¹) ^ 4)

/-- The literal project denominator trace-four integrand. -/
def projectScaledInverseTraceFour (N K : ℕ)
    (R : Matrix (Fin (K - N)) (Fin N) ℝ) : ℝ :=
  Matrix.trace ((scaledInverseWishartMatrix N K R) ^ 4)

/-- Exact pointwise sigma-scale conversion on the full-rank locus. -/
theorem matsumotoIdentityScaledInverseTraceFour_invSqrtTwoScaleMatrix
    {N K : ℕ} (hNK : N ≤ K)
    (R : Matrix (Fin (K - N)) (Fin N) ℝ)
    (hunit : IsUnit (realWishartGram R).det) :
    matsumotoIdentityScaledInverseTraceFour N K
        (invSqrtTwoScaleMatrix (K - N) N R) =
      projectScaledInverseTraceFour N K R := by
  have hinv :
      (realWishartGram (invSqrtTwoScaleMatrix (K - N) N R))⁻¹ =
        (2 : ℝ) • (realWishartGram R)⁻¹ := by
    rw [realWishartGram_invSqrtTwoScaleMatrix]
    letI : Invertible (1 / 2 : ℝ) :=
      invertibleOfNonzero (by norm_num)
    rw [Matrix.inv_smul (A := realWishartGram R) (1 / 2 : ℝ) hunit]
    change (⅟ (1 / 2 : ℝ)) • (realWishartGram R)⁻¹ =
      (2 : ℝ) • (realWishartGram R)⁻¹
    norm_num
  have hgamma :
      matsumotoGamma N (matsumotoIntegerShapeBeta (K - N)) * 2 =
        concreteCOEExponent N K := by
    rw [projectDenominator_matsumotoGamma_eq hNK]
    unfold concreteCOEExponent
    ring
  unfold matsumotoIdentityScaledInverseTraceFour
    projectScaledInverseTraceFour scaledInverseWishartMatrix
  rw [hinv, smul_smul, hgamma]

/-- Exact equality of the identity-scale A4 integral and the project's
variance-one denominator integral.  This theorem is proved before any A4
input is consumed. -/
theorem matsumotoIdentityScaledInverseTraceFour_integral_eq_project
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K) :
    (∫ R : Matrix (Fin (K - N)) (Fin N) ℝ,
        matsumotoIdentityScaledInverseTraceFour N K R
          ∂halfGaussianMatrix (K - N) N) =
      ∫ R : Matrix (Fin (K - N)) (Fin N) ℝ,
        projectScaledInverseTraceFour N K R
          ∂standardRealGaussianMatrixMeasure (K - N) N := by
  let f := matsumotoIdentityScaledInverseTraceFour N K
  have hf : Measurable f := by
    change Measurable (fun R : Matrix (Fin (K - N)) (Fin N) ℝ ↦
      Matrix.trace
        ((matsumotoGamma N (matsumotoIntegerShapeBeta (K - N)) •
          (realWishartGram R)⁻¹) ^ 4))
    exact measurable_scaledInverseGram_trace_pow (K - N) N
      (matsumotoGamma N (matsumotoIntegerShapeBeta (K - N))) 4
  have hunit :=
    ae_isUnit_det_realWishartGram_standardRealGaussianMatrixMeasure
      (k := K - N) (p := N) (by omega)
  calc
    (∫ R : Matrix (Fin (K - N)) (Fin N) ℝ, f R
        ∂halfGaussianMatrix (K - N) N) =
      ∫ R, f R
        ∂Measure.map (invSqrtTwoScaleMatrix (K - N) N)
          (standardRealGaussianMatrixMeasure (K - N) N) := by
        rw [map_invSqrtTwoScaleMatrix_standardRealGaussianMatrixMeasure]
    _ = ∫ R, f (invSqrtTwoScaleMatrix (K - N) N R)
        ∂standardRealGaussianMatrixMeasure (K - N) N := by
      rw [integral_map (measurable_invSqrtTwoScaleMatrix (K - N) N).aemeasurable
        hf.aestronglyMeasurable]
    _ = ∫ R, projectScaledInverseTraceFour N K R
        ∂standardRealGaussianMatrixMeasure (K - N) N := by
      apply integral_congr_ae
      filter_upwards [hunit] with R hR
      exact matsumotoIdentityScaledInverseTraceFour_invSqrtTwoScaleMatrix
        (by omega) R hR

/-- Integrability crosses the exact sigma-scale conversion in the same
direction as the moment identity. -/
theorem integrable_projectScaledInverseTraceFour_of_matsumotoIdentity
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K)
    (hA4 : Integrable (matsumotoIdentityScaledInverseTraceFour N K)
      (halfGaussianMatrix (K - N) N)) :
    Integrable (projectScaledInverseTraceFour N K)
      (standardRealGaussianMatrixMeasure (K - N) N) := by
  let e := invSqrtTwoScaleMatrix (K - N) N
  have hmp : MeasurePreserving e
      (standardRealGaussianMatrixMeasure (K - N) N)
      (halfGaussianMatrix (K - N) N) :=
    ⟨measurable_invSqrtTwoScaleMatrix (K - N) N,
      map_invSqrtTwoScaleMatrix_standardRealGaussianMatrixMeasure (K - N) N⟩
  have hcomp := hmp.integrable_comp_of_integrable hA4
  apply hcomp.congr
  filter_upwards [
    ae_isUnit_det_realWishartGram_standardRealGaussianMatrixMeasure
      (k := K - N) (p := N) (by omega)] with R hR
  exact matsumotoIdentityScaledInverseTraceFour_invSqrtTwoScaleMatrix
    (by omega) R hR

/-! ## Axiom-free positive-semidefinite trace reduction -/

private theorem trace_pow_eq_sum_eigenvalues_pow
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

/-- Every positive-semidefinite trace power is nonnegative. -/
theorem posSemidef_trace_pow_nonneg
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A.PosSemidef) (r : ℕ) :
    0 ≤ Matrix.trace (A ^ r) := by
  rw [trace_pow_eq_sum_eigenvalues_pow A hA r]
  exact Finset.sum_nonneg fun i _ ↦ pow_nonneg (hA.eigenvalues_nonneg i) r

/-- `tr(A)^4` is controlled by the single scalar `tr(A^4)`. -/
theorem posSemidef_trace_fourth_le_card_cube_mul_trace_four
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A.PosSemidef) :
    Matrix.trace A ^ 4 ≤
      (Fintype.card n : ℝ) ^ 3 * Matrix.trace (A ^ 4) := by
  let hH : A.IsHermitian := hA.isHermitian
  have htrace : Matrix.trace A = ∑ i, hH.eigenvalues i :=
    hH.trace_eq_sum_eigenvalues
  have htrace4 := trace_pow_eq_sum_eigenvalues_pow A hA 4
  rw [htrace, htrace4]
  simpa using
    (pow_sum_le_card_mul_sum_pow
      (s := (Finset.univ : Finset n))
      (f := fun i ↦ hH.eigenvalues i)
      (fun i _ ↦ hA.eigenvalues_nonneg i) 3)

/-- `tr(A^2)^2` is controlled by `tr(A^4)`. -/
theorem posSemidef_trace_two_sq_le_card_mul_trace_four
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A.PosSemidef) :
    Matrix.trace (A ^ 2) ^ 2 ≤
      (Fintype.card n : ℝ) * Matrix.trace (A ^ 4) := by
  let hH : A.IsHermitian := hA.isHermitian
  have htrace2 := trace_pow_eq_sum_eigenvalues_pow A hA 2
  have htrace4 := trace_pow_eq_sum_eigenvalues_pow A hA 4
  rw [htrace2, htrace4]
  have h := sq_sum_le_card_mul_sum_sq
    (s := (Finset.univ : Finset n))
    (f := fun i ↦ (hH.eigenvalues i) ^ 2)
  simpa only [Finset.sum_filter, Finset.mem_univ, ↓reduceIte,
    Finset.card_univ, ← pow_mul, Nat.reduceMul] using h

/-- The `(2,1,1)` trace partition is controlled by `tr(A^4)`. -/
theorem posSemidef_trace_sq_mul_trace_two_le_card_sq_mul_trace_four
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A.PosSemidef) :
    Matrix.trace A ^ 2 * Matrix.trace (A ^ 2) ≤
      (Fintype.card n : ℝ) ^ 2 * Matrix.trace (A ^ 4) := by
  have h12 := posSemidef_trace_fourth_le_card_cube_mul_trace_four A hA
  have h22 := posSemidef_trace_two_sq_le_card_mul_trace_four A hA
  have ht1 := hA.trace_nonneg
  have ht2 := posSemidef_trace_pow_nonneg A hA 2
  have ht4 := posSemidef_trace_pow_nonneg A hA 4
  have hc : 0 ≤ (Fintype.card n : ℝ) := by positivity
  have hsquare : Matrix.trace A ^ 2 ≤
      (Fintype.card n : ℝ) * Matrix.trace (A ^ 2) := by
    let hH : A.IsHermitian := hA.isHermitian
    have htrace : Matrix.trace A = ∑ i, hH.eigenvalues i :=
      hH.trace_eq_sum_eigenvalues
    have htrace2 := trace_pow_eq_sum_eigenvalues_pow A hA 2
    rw [htrace, htrace2]
    simpa using (sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset n))
      (f := fun i ↦ hH.eigenvalues i))
  calc
    Matrix.trace A ^ 2 * Matrix.trace (A ^ 2) ≤
        ((Fintype.card n : ℝ) * Matrix.trace (A ^ 2)) *
          Matrix.trace (A ^ 2) :=
      mul_le_mul_of_nonneg_right hsquare ht2
    _ = (Fintype.card n : ℝ) * Matrix.trace (A ^ 2) ^ 2 := by ring
    _ ≤ (Fintype.card n : ℝ) *
        ((Fintype.card n : ℝ) * Matrix.trace (A ^ 4)) :=
      mul_le_mul_of_nonneg_left h22 hc
    _ = (Fintype.card n : ℝ) ^ 2 * Matrix.trace (A ^ 4) := by ring

/-- The `(3,1)` trace partition is controlled by `tr(A^4)`. -/
theorem posSemidef_trace_mul_trace_three_le_card_mul_trace_four
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A.PosSemidef) :
    Matrix.trace A * Matrix.trace (A ^ 3) ≤
      (Fintype.card n : ℝ) * Matrix.trace (A ^ 4) := by
  let hH : A.IsHermitian := hA.isHermitian
  have htrace : Matrix.trace A = ∑ i, hH.eigenvalues i :=
    hH.trace_eq_sum_eigenvalues
  have htrace3 := trace_pow_eq_sum_eigenvalues_pow A hA 3
  have htrace4 := trace_pow_eq_sum_eigenvalues_pow A hA 4
  rw [htrace, htrace3, htrace4]
  have hmono : MonovaryOn
      (fun i : n ↦ hH.eigenvalues i)
      (fun i : n ↦ (hH.eigenvalues i) ^ 3)
      (Finset.univ : Finset n) :=
    (monovaryOn_self (fun i : n ↦ hH.eigenvalues i) _).pow_right₀
      (fun i _ ↦ hA.eigenvalues_nonneg i) 3
  simpa [pow_succ, mul_comm] using hmono.sum_mul_sum_le_card_mul_sum

/-! ## The single post-A4 producer and its five-moment closure -/

/-- Measurability of the project-scaled inverse-Wishart trace powers. -/
theorem measurable_projectScaledInverse_trace_pow
    (N K r : ℕ) :
    Measurable (fun R : Matrix (Fin (K - N)) (Fin N) ℝ ↦
      Matrix.trace ((scaledInverseWishartMatrix N K R) ^ r)) := by
  simpa only [scaledInverseWishartMatrix] using
    measurable_scaledInverseGram_trace_pow (K - N) N
      (concreteCOEExponent N K) r

/-- In the dense positive-dimensional regime the literal scaled inverse
denominator is positive semidefinite, including on the singular set. -/
theorem projectScaledInverse_posSemidef_of_dense
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K)
    (R : Matrix (Fin (K - N)) (Fin N) ℝ) :
    (scaledInverseWishartMatrix N K R).PosSemidef := by
  have hdenseR : (16 : ℝ) * (N : ℝ) ≤ (K : ℝ) := by
    exact_mod_cast hdense
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hc : 0 ≤ concreteCOEExponent N K := by
    unfold concreteCOEExponent
    linarith
  unfold scaledInverseWishartMatrix
  exact (realWishartGram_inv_posSemidef R).smul hc

/-- **CONDITIONAL, post-substitution A4 producer.**  This is not a new
scientific axiom.  A source-faithful literal-paper-variable formalization of
Matsumoto Theorem 3 must prove these two fields after the separate substitution
`d=N`, `beta=(K-N)/2`, `gamma=beta-(d+1)/2`.  It is strictly smaller than any
H3--H18 conclusion: only the identity-scale scalar `tr((gamma W⁻¹)^4)` is
present. -/
structure H14MatsumotoIdentityTraceFourBoundContract (N K : ℕ) : Prop where
  traceFour_integrable : 2 * N + 8 ≤ K →
    Integrable (matsumotoIdentityScaledInverseTraceFour N K)
      (halfGaussianMatrix (K - N) N)
  traceFour_integral_le : 1 ≤ N → 16 * N ≤ K →
    (∫ R : Matrix (Fin (K - N)) (Fin N) ℝ,
        matsumotoIdentityScaledInverseTraceFour N K R
          ∂halfGaussianMatrix (K - N) N) ≤
      128 * (N : ℝ)

/-- The five order-four trace partitions needed by the H12/H14 Wick
polynomials, after exact sigma-scale transport. -/
structure H14ScaledInverseFourthTraceMomentLedger (N K : ℕ) : Prop where
  traceOneFourth_integrable :
    Integrable
      (fun R : Matrix (Fin (K - N)) (Fin N) ℝ ↦
        Matrix.trace (scaledInverseWishartMatrix N K R) ^ 4)
      (standardRealGaussianMatrixMeasure (K - N) N)
  traceOneFourth_integral_le :
    (∫ R : Matrix (Fin (K - N)) (Fin N) ℝ,
        Matrix.trace (scaledInverseWishartMatrix N K R) ^ 4
          ∂standardRealGaussianMatrixMeasure (K - N) N) ≤
      128 * (N : ℝ) ^ 4
  traceOneSqTraceTwo_integrable :
    Integrable
      (fun R : Matrix (Fin (K - N)) (Fin N) ℝ ↦
        Matrix.trace (scaledInverseWishartMatrix N K R) ^ 2 *
          Matrix.trace ((scaledInverseWishartMatrix N K R) ^ 2))
      (standardRealGaussianMatrixMeasure (K - N) N)
  traceOneSqTraceTwo_integral_le :
    (∫ R : Matrix (Fin (K - N)) (Fin N) ℝ,
        Matrix.trace (scaledInverseWishartMatrix N K R) ^ 2 *
          Matrix.trace ((scaledInverseWishartMatrix N K R) ^ 2)
          ∂standardRealGaussianMatrixMeasure (K - N) N) ≤
      128 * (N : ℝ) ^ 3
  traceTwoSquare_integrable :
    Integrable
      (fun R : Matrix (Fin (K - N)) (Fin N) ℝ ↦
        Matrix.trace ((scaledInverseWishartMatrix N K R) ^ 2) ^ 2)
      (standardRealGaussianMatrixMeasure (K - N) N)
  traceTwoSquare_integral_le :
    (∫ R : Matrix (Fin (K - N)) (Fin N) ℝ,
        Matrix.trace ((scaledInverseWishartMatrix N K R) ^ 2) ^ 2
          ∂standardRealGaussianMatrixMeasure (K - N) N) ≤
      128 * (N : ℝ) ^ 2
  traceOneTraceThree_integrable :
    Integrable
      (fun R : Matrix (Fin (K - N)) (Fin N) ℝ ↦
        Matrix.trace (scaledInverseWishartMatrix N K R) *
          Matrix.trace ((scaledInverseWishartMatrix N K R) ^ 3))
      (standardRealGaussianMatrixMeasure (K - N) N)
  traceOneTraceThree_integral_le :
    (∫ R : Matrix (Fin (K - N)) (Fin N) ℝ,
        Matrix.trace (scaledInverseWishartMatrix N K R) *
          Matrix.trace ((scaledInverseWishartMatrix N K R) ^ 3)
          ∂standardRealGaussianMatrixMeasure (K - N) N) ≤
      128 * (N : ℝ) ^ 2
  traceFour_integrable :
    Integrable
      (fun R : Matrix (Fin (K - N)) (Fin N) ℝ ↦
        Matrix.trace ((scaledInverseWishartMatrix N K R) ^ 4))
      (standardRealGaussianMatrixMeasure (K - N) N)
  traceFour_integral_le :
    (∫ R : Matrix (Fin (K - N)) (Fin N) ℝ,
        Matrix.trace ((scaledInverseWishartMatrix N K R) ^ 4)
          ∂standardRealGaussianMatrixMeasure (K - N) N) ≤
      128 * (N : ℝ)

/-- **CONDITIONAL, non-endpoint.**  The one scalar post-A4 producer yields all
five dimension-sharp trace-partition envelopes.  Every implication after the
producer parameter is axiom-free. -/
theorem h14_scaledInverseFourthTraceMomentLedger_of_matsumotoTraceFour_conditional
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K)
    (HA4 : H14MatsumotoIdentityTraceFourBoundContract N K) :
    H14ScaledInverseFourthTraceMomentLedger N K := by
  let μ := standardRealGaussianMatrixMeasure (K - N) N
  let C : Matrix (Fin (K - N)) (Fin N) ℝ → Matrix (Fin N) (Fin N) ℝ :=
    scaledInverseWishartMatrix N K
  have hgap : 2 * N + 8 ≤ K := by omega
  have hC (R : Matrix (Fin (K - N)) (Fin N) ℝ) : (C R).PosSemidef := by
    exact projectScaledInverse_posSemidef_of_dense hN hdense R
  have hm1 : Measurable (fun R : Matrix (Fin (K - N)) (Fin N) ℝ ↦
      Matrix.trace (C R)) := by
    simpa only [C, pow_one] using measurable_projectScaledInverse_trace_pow N K 1
  have hm2 : Measurable (fun R : Matrix (Fin (K - N)) (Fin N) ℝ ↦
      Matrix.trace ((C R) ^ 2)) := by
    simpa only [C] using measurable_projectScaledInverse_trace_pow N K 2
  have hm3 : Measurable (fun R : Matrix (Fin (K - N)) (Fin N) ℝ ↦
      Matrix.trace ((C R) ^ 3)) := by
    simpa only [C] using measurable_projectScaledInverse_trace_pow N K 3
  have hm4 : Measurable (fun R : Matrix (Fin (K - N)) (Fin N) ℝ ↦
      Matrix.trace ((C R) ^ 4)) := by
    simpa only [C] using measurable_projectScaledInverse_trace_pow N K 4
  have h4int : Integrable
      (fun R : Matrix (Fin (K - N)) (Fin N) ℝ ↦ Matrix.trace ((C R) ^ 4)) μ := by
    change Integrable (projectScaledInverseTraceFour N K)
      (standardRealGaussianMatrixMeasure (K - N) N)
    exact integrable_projectScaledInverseTraceFour_of_matsumotoIdentity hgap
      (HA4.traceFour_integrable hgap)
  have h4bound :
      (∫ R : Matrix (Fin (K - N)) (Fin N) ℝ,
          Matrix.trace ((C R) ^ 4) ∂μ) ≤ 128 * (N : ℝ) := by
    change (∫ R : Matrix (Fin (K - N)) (Fin N) ℝ,
        projectScaledInverseTraceFour N K R
          ∂standardRealGaussianMatrixMeasure (K - N) N) ≤ 128 * (N : ℝ)
    rw [← matsumotoIdentityScaledInverseTraceFour_integral_eq_project hgap]
    exact HA4.traceFour_integral_le hN hdense
  have h1111int : Integrable
      (fun R : Matrix (Fin (K - N)) (Fin N) ℝ ↦ Matrix.trace (C R) ^ 4) μ := by
    apply Integrable.mono' (h4int.const_mul ((N : ℝ) ^ 3))
      (hm1.pow_const 4).aestronglyMeasurable
    filter_upwards [] with R
    have ht1 : 0 ≤ Matrix.trace (C R) := (hC R).trace_nonneg
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ht1 4)]
    simpa only [Fintype.card_fin] using
      posSemidef_trace_fourth_le_card_cube_mul_trace_four (C R) (hC R)
  have h211int : Integrable
      (fun R : Matrix (Fin (K - N)) (Fin N) ℝ ↦
        Matrix.trace (C R) ^ 2 * Matrix.trace ((C R) ^ 2)) μ := by
    apply Integrable.mono' (h4int.const_mul ((N : ℝ) ^ 2))
      ((hm1.pow_const 2).mul hm2).aestronglyMeasurable
    filter_upwards [] with R
    have ht2 : 0 ≤ Matrix.trace ((C R) ^ 2) :=
      posSemidef_trace_pow_nonneg (C R) (hC R) 2
    simp only [Pi.mul_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) ht2)]
    simpa only [Fintype.card_fin] using
      posSemidef_trace_sq_mul_trace_two_le_card_sq_mul_trace_four (C R) (hC R)
  have h22int : Integrable
      (fun R : Matrix (Fin (K - N)) (Fin N) ℝ ↦
        Matrix.trace ((C R) ^ 2) ^ 2) μ := by
    apply Integrable.mono' (h4int.const_mul (N : ℝ))
      (hm2.pow_const 2).aestronglyMeasurable
    filter_upwards [] with R
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simpa only [Fintype.card_fin] using
      posSemidef_trace_two_sq_le_card_mul_trace_four (C R) (hC R)
  have h31int : Integrable
      (fun R : Matrix (Fin (K - N)) (Fin N) ℝ ↦
        Matrix.trace (C R) * Matrix.trace ((C R) ^ 3)) μ := by
    apply Integrable.mono' (h4int.const_mul (N : ℝ))
      (hm1.mul hm3).aestronglyMeasurable
    filter_upwards [] with R
    have ht1 : 0 ≤ Matrix.trace (C R) := (hC R).trace_nonneg
    have ht3 : 0 ≤ Matrix.trace ((C R) ^ 3) :=
      posSemidef_trace_pow_nonneg (C R) (hC R) 3
    simp only [Pi.mul_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ht1 ht3)]
    simpa only [Fintype.card_fin] using
      posSemidef_trace_mul_trace_three_le_card_mul_trace_four (C R) (hC R)
  have h1111bound :
      (∫ R : Matrix (Fin (K - N)) (Fin N) ℝ,
          Matrix.trace (C R) ^ 4 ∂μ) ≤ 128 * (N : ℝ) ^ 4 := by
    calc
      _ ≤ ∫ R, (N : ℝ) ^ 3 * Matrix.trace ((C R) ^ 4) ∂μ := by
        apply integral_mono h1111int (h4int.const_mul ((N : ℝ) ^ 3))
        intro R
        simpa only [Fintype.card_fin] using
          posSemidef_trace_fourth_le_card_cube_mul_trace_four (C R) (hC R)
      _ = (N : ℝ) ^ 3 * ∫ R, Matrix.trace ((C R) ^ 4) ∂μ :=
        by rw [integral_const_mul]
      _ ≤ (N : ℝ) ^ 3 * (128 * (N : ℝ)) := by
        exact mul_le_mul_of_nonneg_left h4bound (by positivity)
      _ = 128 * (N : ℝ) ^ 4 := by ring
  have h211bound :
      (∫ R : Matrix (Fin (K - N)) (Fin N) ℝ,
          Matrix.trace (C R) ^ 2 * Matrix.trace ((C R) ^ 2) ∂μ) ≤
        128 * (N : ℝ) ^ 3 := by
    calc
      _ ≤ ∫ R, (N : ℝ) ^ 2 * Matrix.trace ((C R) ^ 4) ∂μ := by
        apply integral_mono h211int (h4int.const_mul ((N : ℝ) ^ 2))
        intro R
        simpa only [Fintype.card_fin] using
          posSemidef_trace_sq_mul_trace_two_le_card_sq_mul_trace_four (C R) (hC R)
      _ = (N : ℝ) ^ 2 * ∫ R, Matrix.trace ((C R) ^ 4) ∂μ :=
        by rw [integral_const_mul]
      _ ≤ (N : ℝ) ^ 2 * (128 * (N : ℝ)) := by
        exact mul_le_mul_of_nonneg_left h4bound (by positivity)
      _ = 128 * (N : ℝ) ^ 3 := by ring
  have h22bound :
      (∫ R : Matrix (Fin (K - N)) (Fin N) ℝ,
          Matrix.trace ((C R) ^ 2) ^ 2 ∂μ) ≤ 128 * (N : ℝ) ^ 2 := by
    calc
      _ ≤ ∫ R, (N : ℝ) * Matrix.trace ((C R) ^ 4) ∂μ := by
        apply integral_mono h22int (h4int.const_mul (N : ℝ))
        intro R
        simpa only [Fintype.card_fin] using
          posSemidef_trace_two_sq_le_card_mul_trace_four (C R) (hC R)
      _ = (N : ℝ) * ∫ R, Matrix.trace ((C R) ^ 4) ∂μ :=
        by rw [integral_const_mul]
      _ ≤ (N : ℝ) * (128 * (N : ℝ)) := by
        exact mul_le_mul_of_nonneg_left h4bound (by positivity)
      _ = 128 * (N : ℝ) ^ 2 := by ring
  have h31bound :
      (∫ R : Matrix (Fin (K - N)) (Fin N) ℝ,
          Matrix.trace (C R) * Matrix.trace ((C R) ^ 3) ∂μ) ≤
        128 * (N : ℝ) ^ 2 := by
    calc
      _ ≤ ∫ R, (N : ℝ) * Matrix.trace ((C R) ^ 4) ∂μ := by
        apply integral_mono h31int (h4int.const_mul (N : ℝ))
        intro R
        simpa only [Fintype.card_fin] using
          posSemidef_trace_mul_trace_three_le_card_mul_trace_four (C R) (hC R)
      _ = (N : ℝ) * ∫ R, Matrix.trace ((C R) ^ 4) ∂μ :=
        by rw [integral_const_mul]
      _ ≤ (N : ℝ) * (128 * (N : ℝ)) := by
        exact mul_le_mul_of_nonneg_left h4bound (by positivity)
      _ = 128 * (N : ℝ) ^ 2 := by ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [C, μ] using h1111int
  · simpa only [C, μ] using h1111bound
  · simpa only [C, μ] using h211int
  · simpa only [C, μ] using h211bound
  · simpa only [C, μ] using h22int
  · simpa only [C, μ] using h22bound
  · simpa only [C, μ] using h31int
  · simpa only [C, μ] using h31bound
  · simpa only [C, μ] using h4int
  · simpa only [C, μ] using h4bound

/-! ## Wick-polynomial closure from the five-moment ledger -/

private theorem h14_traceOneFourthWick_scalar_le
    {n a x1111 x211 x22 x31 x4 : ℝ}
    (hn : 1 ≤ n) (ha0 : 0 ≤ a) (ha : a ≤ 2 * n) (hx4 : 0 ≤ x4)
    (h1111 : x1111 ≤ n ^ 3 * x4)
    (h211 : x211 ≤ n ^ 2 * x4)
    (h22 : x22 ≤ n * x4) (h31 : x31 ≤ n * x4) :
    a ^ 4 * x1111 + 12 * a ^ 3 * x211 + 12 * a ^ 2 * x22 +
        32 * a ^ 2 * x31 + 48 * a * x4 ≤
      384 * n ^ 7 * x4 := by
  have hn0 : 0 ≤ n := le_trans (by norm_num) hn
  have ha2 : a ^ 2 ≤ (2 * n) ^ 2 := pow_le_pow_left₀ ha0 ha 2
  have ha3 : a ^ 3 ≤ (2 * n) ^ 3 := pow_le_pow_left₀ ha0 ha 3
  have ha4 : a ^ 4 ≤ (2 * n) ^ 4 := pow_le_pow_left₀ ha0 ha 4
  have hn17 : n ^ 1 ≤ n ^ 7 := pow_le_pow_right₀ hn (by omega)
  have hn37 : n ^ 3 ≤ n ^ 7 := pow_le_pow_right₀ hn (by omega)
  have hn57 : n ^ 5 ≤ n ^ 7 := pow_le_pow_right₀ hn (by omega)
  have hM1 : a ^ 4 * x1111 ≤ 16 * n ^ 7 * x4 := by
    calc
      a ^ 4 * x1111 ≤ a ^ 4 * (n ^ 3 * x4) := by
        exact mul_le_mul_of_nonneg_left h1111 (pow_nonneg ha0 4)
      _ ≤ (2 * n) ^ 4 * (n ^ 3 * x4) := by
        exact mul_le_mul_of_nonneg_right ha4
          (mul_nonneg (pow_nonneg hn0 3) hx4)
      _ = 16 * n ^ 7 * x4 := by ring
  have hM2 : 12 * a ^ 3 * x211 ≤ 96 * n ^ 7 * x4 := by
    calc
      12 * a ^ 3 * x211 ≤ 12 * a ^ 3 * (n ^ 2 * x4) := by
        exact mul_le_mul_of_nonneg_left h211 (by positivity)
      _ ≤ 12 * (2 * n) ^ 3 * (n ^ 2 * x4) := by
        gcongr
      _ = 96 * n ^ 5 * x4 := by ring
      _ ≤ 96 * n ^ 7 * x4 := by
        gcongr
  have hM3 : 12 * a ^ 2 * x22 ≤ 48 * n ^ 7 * x4 := by
    calc
      12 * a ^ 2 * x22 ≤ 12 * a ^ 2 * (n * x4) := by
        exact mul_le_mul_of_nonneg_left h22 (by positivity)
      _ ≤ 12 * (2 * n) ^ 2 * (n * x4) := by
        gcongr
      _ = 48 * n ^ 3 * x4 := by ring
      _ ≤ 48 * n ^ 7 * x4 := by
        gcongr
  have hM4 : 32 * a ^ 2 * x31 ≤ 128 * n ^ 7 * x4 := by
    calc
      32 * a ^ 2 * x31 ≤ 32 * a ^ 2 * (n * x4) := by
        exact mul_le_mul_of_nonneg_left h31 (by positivity)
      _ ≤ 32 * (2 * n) ^ 2 * (n * x4) := by
        gcongr
      _ = 128 * n ^ 3 * x4 := by ring
      _ ≤ 128 * n ^ 7 * x4 := by
        gcongr
  have hM5 : 48 * a * x4 ≤ 96 * n ^ 7 * x4 := by
    calc
      48 * a * x4 ≤ 48 * (2 * n) * x4 := by gcongr
      _ = 96 * n ^ 1 * x4 := by ring
      _ ≤ 96 * n ^ 7 * x4 := by gcongr
  nlinarith

private theorem h14_traceTwoSquareWick_scalar_le
    {n a x1111 x211 x22 x31 x4 : ℝ}
    (hn : 1 ≤ n) (ha0 : 0 ≤ a) (ha : a ≤ 2 * n) (hx4 : 0 ≤ x4)
    (h1111 : x1111 ≤ n ^ 3 * x4)
    (h211 : x211 ≤ n ^ 2 * x4)
    (h22 : x22 ≤ n * x4) (h31 : x31 ≤ n * x4) :
    a ^ 2 * x1111 + (2 * a ^ 3 + 2 * a ^ 2 + 8 * a) * x211 +
        (a ^ 4 + 2 * a ^ 3 + 5 * a ^ 2 + 4 * a) * x22 +
        16 * a * (a + 1) * x31 +
        (8 * a ^ 3 + 20 * a ^ 2 + 20 * a) * x4 ≤
      384 * n ^ 5 * x4 := by
  have hn0 : 0 ≤ n := le_trans (by norm_num) hn
  have ha1 : a + 1 ≤ 3 * n := by linarith
  have ha2 : a ^ 2 ≤ (2 * n) ^ 2 := pow_le_pow_left₀ ha0 ha 2
  have ha3 : a ^ 3 ≤ (2 * n) ^ 3 := pow_le_pow_left₀ ha0 ha 3
  have ha4 : a ^ 4 ≤ (2 * n) ^ 4 := pow_le_pow_left₀ ha0 ha 4
  have hn12 : n ^ 1 ≤ n ^ 2 := pow_le_pow_right₀ hn (by omega)
  have hn13 : n ^ 1 ≤ n ^ 3 := pow_le_pow_right₀ hn (by omega)
  have hn14 : n ^ 1 ≤ n ^ 4 := pow_le_pow_right₀ hn (by omega)
  have hn23 : n ^ 2 ≤ n ^ 3 := pow_le_pow_right₀ hn (by omega)
  have hn24 : n ^ 2 ≤ n ^ 4 := pow_le_pow_right₀ hn (by omega)
  have hn34 : n ^ 3 ≤ n ^ 4 := pow_le_pow_right₀ hn (by omega)
  have hn35 : n ^ 3 ≤ n ^ 5 := pow_le_pow_right₀ hn (by omega)
  have hcoef211 : 2 * a ^ 3 + 2 * a ^ 2 + 8 * a ≤ 40 * n ^ 3 := by
    nlinarith
  have hcoef22 : a ^ 4 + 2 * a ^ 3 + 5 * a ^ 2 + 4 * a ≤
      60 * n ^ 4 := by
    nlinarith
  have haa : a * (a + 1) ≤ (2 * n) * (3 * n) := by
    exact mul_le_mul ha ha1 (by positivity) (by positivity)
  have hcoef31 : 16 * a * (a + 1) ≤ 96 * n ^ 2 := by
    nlinarith
  have hcoef4 : 8 * a ^ 3 + 20 * a ^ 2 + 20 * a ≤ 184 * n ^ 3 := by
    nlinarith
  have hM1 : a ^ 2 * x1111 ≤ 4 * n ^ 5 * x4 := by
    calc
      a ^ 2 * x1111 ≤ a ^ 2 * (n ^ 3 * x4) := by
        exact mul_le_mul_of_nonneg_left h1111 (pow_nonneg ha0 2)
      _ ≤ (2 * n) ^ 2 * (n ^ 3 * x4) := by
        exact mul_le_mul_of_nonneg_right ha2
          (mul_nonneg (pow_nonneg hn0 3) hx4)
      _ = 4 * n ^ 5 * x4 := by ring
  have hM2 : (2 * a ^ 3 + 2 * a ^ 2 + 8 * a) * x211 ≤
      40 * n ^ 5 * x4 := by
    calc
      _ ≤ (2 * a ^ 3 + 2 * a ^ 2 + 8 * a) * (n ^ 2 * x4) := by
        exact mul_le_mul_of_nonneg_left h211 (by positivity)
      _ ≤ (40 * n ^ 3) * (n ^ 2 * x4) := by
        exact mul_le_mul_of_nonneg_right hcoef211
          (mul_nonneg (pow_nonneg hn0 2) hx4)
      _ = 40 * n ^ 5 * x4 := by ring
  have hM3 : (a ^ 4 + 2 * a ^ 3 + 5 * a ^ 2 + 4 * a) * x22 ≤
      60 * n ^ 5 * x4 := by
    calc
      _ ≤ (a ^ 4 + 2 * a ^ 3 + 5 * a ^ 2 + 4 * a) * (n * x4) := by
        exact mul_le_mul_of_nonneg_left h22 (by positivity)
      _ ≤ (60 * n ^ 4) * (n * x4) := by
        exact mul_le_mul_of_nonneg_right hcoef22 (mul_nonneg hn0 hx4)
      _ = 60 * n ^ 5 * x4 := by ring
  have hM4 : 16 * a * (a + 1) * x31 ≤ 96 * n ^ 5 * x4 := by
    calc
      _ ≤ (16 * a * (a + 1)) * (n * x4) := by
        exact mul_le_mul_of_nonneg_left h31 (by positivity)
      _ ≤ (96 * n ^ 2) * (n * x4) := by
        exact mul_le_mul_of_nonneg_right hcoef31 (mul_nonneg hn0 hx4)
      _ = 96 * n ^ 3 * x4 := by ring
      _ ≤ 96 * n ^ 5 * x4 := by gcongr
  have hM5 : (8 * a ^ 3 + 20 * a ^ 2 + 20 * a) * x4 ≤
      184 * n ^ 5 * x4 := by
    calc
      _ ≤ (184 * n ^ 3) * x4 :=
        mul_le_mul_of_nonneg_right hcoef4 hx4
      _ ≤ 184 * n ^ 5 * x4 := by gcongr
  nlinarith

/-- Pointwise H12-side denominator Wick polynomial reduction to `tr(C^4)`. -/
theorem h14TraceOneFourthWickPolynomial_le_traceFour
    {N : ℕ} (hN : 1 ≤ N) (A : Matrix (Fin N) (Fin N) ℝ)
    (hA : A.PosSemidef) :
    h14TraceOneFourthWickPolynomial (N + 1) A ≤
      384 * (N : ℝ) ^ 7 * Matrix.trace (A ^ 4) := by
  have hn : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have ha : ((N + 1 : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by
    push_cast
    linarith
  unfold h14TraceOneFourthWickPolynomial
  simpa only [mul_assoc] using h14_traceOneFourthWick_scalar_le hn (by positivity) ha
    (posSemidef_trace_pow_nonneg A hA 4)
    (by simpa only [Fintype.card_fin] using
      posSemidef_trace_fourth_le_card_cube_mul_trace_four A hA)
    (by simpa only [Fintype.card_fin] using
      posSemidef_trace_sq_mul_trace_two_le_card_sq_mul_trace_four A hA)
    (by simpa only [Fintype.card_fin] using
      posSemidef_trace_two_sq_le_card_mul_trace_four A hA)
    (by simpa only [Fintype.card_fin] using
      posSemidef_trace_mul_trace_three_le_card_mul_trace_four A hA)

/-- Pointwise H14-side denominator Wick polynomial reduction to `tr(C^4)`. -/
theorem h14TraceTwoSquareWickPolynomial_le_traceFour
    {N : ℕ} (hN : 1 ≤ N) (A : Matrix (Fin N) (Fin N) ℝ)
    (hA : A.PosSemidef) :
    h14TraceTwoSquareWickPolynomial (N + 1) A ≤
      384 * (N : ℝ) ^ 5 * Matrix.trace (A ^ 4) := by
  have hn : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have ha : ((N + 1 : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by
    push_cast
    linarith
  unfold h14TraceTwoSquareWickPolynomial
  simpa only [mul_assoc] using h14_traceTwoSquareWick_scalar_le hn (by positivity) ha
    (posSemidef_trace_pow_nonneg A hA 4)
    (by simpa only [Fintype.card_fin] using
      posSemidef_trace_fourth_le_card_cube_mul_trace_four A hA)
    (by simpa only [Fintype.card_fin] using
      posSemidef_trace_sq_mul_trace_two_le_card_sq_mul_trace_four A hA)
    (by simpa only [Fintype.card_fin] using
      posSemidef_trace_two_sq_le_card_mul_trace_four A hA)
    (by simpa only [Fintype.card_fin] using
      posSemidef_trace_mul_trace_three_le_card_mul_trace_four A hA)

/-- **CONDITIONAL, non-endpoint.**  The single post-A4 trace-four producer
closes both dense denominator Wick-polynomial bounds. -/
theorem h14_denominatorFourthTracePolynomialBounds_dense_of_matsumotoTraceFour_conditional
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K)
    (HA4 : H14MatsumotoIdentityTraceFourBoundContract N K) :
    ((∫ H : Matrix (Fin (K - N)) (Fin N) ℝ,
        h14TraceOneFourthWickPolynomial (N + 1)
          (scaledInverseWishartMatrix N K H)
        ∂standardRealGaussianMatrixMeasure (K - N) N) ≤
      (2 : ℝ) ^ 16 * (N : ℝ) ^ 8) ∧
    ((∫ H : Matrix (Fin (K - N)) (Fin N) ℝ,
        h14TraceTwoSquareWickPolynomial (N + 1)
          (scaledInverseWishartMatrix N K H)
        ∂standardRealGaussianMatrixMeasure (K - N) N) ≤
      (2 : ℝ) ^ 16 * (N : ℝ) ^ 6) := by
  let μ := standardRealGaussianMatrixMeasure (K - N) N
  let C : Matrix (Fin (K - N)) (Fin N) ℝ → Matrix (Fin N) (Fin N) ℝ :=
    scaledInverseWishartMatrix N K
  let L := h14_scaledInverseFourthTraceMomentLedger_of_matsumotoTraceFour_conditional
    hN hdense HA4
  have hC (H : Matrix (Fin (K - N)) (Fin N) ℝ) : (C H).PosSemidef :=
    projectScaledInverse_posSemidef_of_dense hN hdense H
  have hP1int : Integrable
      (fun H : Matrix (Fin (K - N)) (Fin N) ℝ ↦
        h14TraceOneFourthWickPolynomial (N + 1) (C H)) μ := by
    have hsum := ((((L.traceOneFourth_integrable.const_mul
        (((N + 1 : ℕ) : ℝ) ^ 4)).add
      (L.traceOneSqTraceTwo_integrable.const_mul
        (12 * ((N + 1 : ℕ) : ℝ) ^ 3))).add
      (L.traceTwoSquare_integrable.const_mul
        (12 * ((N + 1 : ℕ) : ℝ) ^ 2))).add
      (L.traceOneTraceThree_integrable.const_mul
        (32 * ((N + 1 : ℕ) : ℝ) ^ 2))).add
      (L.traceFour_integrable.const_mul (48 * ((N + 1 : ℕ) : ℝ)))
    apply hsum.congr
    filter_upwards [] with H
    unfold h14TraceOneFourthWickPolynomial
    simp only [Pi.add_apply, Pi.mul_apply, C]
    push_cast
    ring
  have hP2int : Integrable
      (fun H : Matrix (Fin (K - N)) (Fin N) ℝ ↦
        h14TraceTwoSquareWickPolynomial (N + 1) (C H)) μ := by
    have hsum := ((((L.traceOneFourth_integrable.const_mul
        (((N + 1 : ℕ) : ℝ) ^ 2)).add
      (L.traceOneSqTraceTwo_integrable.const_mul
        (2 * ((N + 1 : ℕ) : ℝ) ^ 3 +
          2 * ((N + 1 : ℕ) : ℝ) ^ 2 +
          8 * ((N + 1 : ℕ) : ℝ)))).add
      (L.traceTwoSquare_integrable.const_mul
        (((N + 1 : ℕ) : ℝ) ^ 4 +
          2 * ((N + 1 : ℕ) : ℝ) ^ 3 +
          5 * ((N + 1 : ℕ) : ℝ) ^ 2 +
          4 * ((N + 1 : ℕ) : ℝ)))).add
      (L.traceOneTraceThree_integrable.const_mul
        (16 * ((N + 1 : ℕ) : ℝ) * (((N + 1 : ℕ) : ℝ) + 1)))).add
      (L.traceFour_integrable.const_mul
        (8 * ((N + 1 : ℕ) : ℝ) ^ 3 +
          20 * ((N + 1 : ℕ) : ℝ) ^ 2 +
          20 * ((N + 1 : ℕ) : ℝ)))
    apply hsum.congr
    filter_upwards [] with H
    unfold h14TraceTwoSquareWickPolynomial
    simp only [Pi.add_apply, Pi.mul_apply, C]
    push_cast
    ring
  have h4int : Integrable
      (fun H : Matrix (Fin (K - N)) (Fin N) ℝ ↦ Matrix.trace ((C H) ^ 4)) μ := by
    simpa only [C, μ] using L.traceFour_integrable
  have h4bound :
      (∫ H : Matrix (Fin (K - N)) (Fin N) ℝ,
          Matrix.trace ((C H) ^ 4) ∂μ) ≤ 128 * (N : ℝ) := by
    simpa only [C, μ] using L.traceFour_integral_le
  constructor
  · calc
      (∫ H, h14TraceOneFourthWickPolynomial (N + 1) (C H) ∂μ) ≤
          ∫ H, 384 * (N : ℝ) ^ 7 * Matrix.trace ((C H) ^ 4) ∂μ := by
        apply integral_mono hP1int (h4int.const_mul (384 * (N : ℝ) ^ 7))
        intro H
        exact h14TraceOneFourthWickPolynomial_le_traceFour hN (C H) (hC H)
      _ = 384 * (N : ℝ) ^ 7 *
          ∫ H, Matrix.trace ((C H) ^ 4) ∂μ := by
        rw [integral_const_mul]
      _ ≤ 384 * (N : ℝ) ^ 7 * (128 * (N : ℝ)) := by
        exact mul_le_mul_of_nonneg_left h4bound (by positivity)
      _ = 49152 * (N : ℝ) ^ 8 := by ring
      _ ≤ (2 : ℝ) ^ 16 * (N : ℝ) ^ 8 := by
        have hpow : 0 ≤ (N : ℝ) ^ 8 := by positivity
        norm_num
        nlinarith
  · calc
      (∫ H, h14TraceTwoSquareWickPolynomial (N + 1) (C H) ∂μ) ≤
          ∫ H, 384 * (N : ℝ) ^ 5 * Matrix.trace ((C H) ^ 4) ∂μ := by
        apply integral_mono hP2int (h4int.const_mul (384 * (N : ℝ) ^ 5))
        intro H
        exact h14TraceTwoSquareWickPolynomial_le_traceFour hN (C H) (hC H)
      _ = 384 * (N : ℝ) ^ 5 *
          ∫ H, Matrix.trace ((C H) ^ 4) ∂μ := by
        rw [integral_const_mul]
      _ ≤ 384 * (N : ℝ) ^ 5 * (128 * (N : ℝ)) := by
        exact mul_le_mul_of_nonneg_left h4bound (by positivity)
      _ = 49152 * (N : ℝ) ^ 6 := by ring
      _ ≤ (2 : ℝ) ^ 16 * (N : ℝ) ^ 6 := by
        have hpow : 0 ≤ (N : ℝ) ^ 6 := by positivity
        norm_num
        nlinarith

/-- **CONDITIONAL, exact existing denominator interface.**  The zero-dimensional
case is algebraic; every positive-dimensional dense case is supplied by the
single identity-scale trace-four producer. -/
theorem h14DenominatorFourthTracePolynomialBounds_of_matsumotoTraceFour_conditional
    {N K : ℕ} (HA4 : H14MatsumotoIdentityTraceFourBoundContract N K) :
    H14DenominatorFourthTracePolynomialBounds N K := by
  constructor
  · intro hdense
    by_cases hzero : N = 0
    · subst N
      simp [h14TraceOneFourthWickPolynomial, Matrix.trace]
    · exact
        (h14_denominatorFourthTracePolynomialBounds_dense_of_matsumotoTraceFour_conditional
          (Nat.one_le_iff_ne_zero.mpr hzero) hdense HA4).1
  · intro hdense
    by_cases hzero : N = 0
    · subst N
      simp [h14TraceTwoSquareWickPolynomial, Matrix.trace]
    · exact
        (h14_denominatorFourthTracePolynomialBounds_dense_of_matsumotoTraceFour_conditional
          (Nat.one_le_iff_ne_zero.mpr hzero) hdense HA4).2

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08
