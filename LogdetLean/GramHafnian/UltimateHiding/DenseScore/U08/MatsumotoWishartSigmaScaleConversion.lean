import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.InverseWishartEntryProductIntegrability
import Mathlib.Tactic

/-!
# Matsumoto Wishart sigma-scale conversion

Matsumoto's real-Wishart convention realizes `W_d(k/2, sigma; R)` as the
Gram matrix of `k` independent rows with covariance `sigma / 2`.  Thus the
literal half-Gaussian source already present in the project is the
`sigma = I` realization, whereas the project's variance-one denominator is
the `sigma = 2 I` realization.

This module proves that conversion before any use of the approved literature
atom A4.  It also proves the exact order-four parameter arithmetic
`gamma > 3` from `2 * N + 8 <= K` and transports arbitrary finite products of
inverse entries between the two Gaussian normalizations.  No endpoint or
scientific axiom is imported.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08

noncomputable section

open LogdetLean.GramHafnian
open LogdetLean.GramHafnian.Wishart
open LogdetLean.GramHafnian.UltimateHiding.DenseScore

/-- Scalar multiplication on a real square-matrix space. -/
def realWishartSigmaScaleMatrix (p : ℕ) (a : ℝ) :
    Matrix (Fin p) (Fin p) ℝ → Matrix (Fin p) (Fin p) ℝ :=
  fun W ↦ a • W

theorem measurable_realWishartSigmaScaleMatrix (p : ℕ) (a : ℝ) :
    Measurable (realWishartSigmaScaleMatrix p a) := by
  refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
  simp only [realWishartSigmaScaleMatrix, Matrix.smul_apply, smul_eq_mul]
  exact measurable_const.mul
    ((measurable_pi_apply j).comp (measurable_pi_apply i))

/-- Matsumoto's integer-shape Gaussian realization at paper scale
`sigma = I`: every source entry is `N(0, 1/2)`. -/
def matsumotoIdentityWishartGramLaw (k p : ℕ) :
    Measure (Matrix (Fin p) (Fin p) ℝ) :=
  Measure.map
    (realWishartGram : Matrix (Fin k) (Fin p) ℝ → Matrix (Fin p) (Fin p) ℝ)
    (halfGaussianMatrix k p)

/-- The project's literal variance-one real-Wishart Gram law. -/
def projectStandardWishartGramLaw (k p : ℕ) :
    Measure (Matrix (Fin p) (Fin p) ℝ) :=
  Measure.map
    (realWishartGram : Matrix (Fin k) (Fin p) ℝ → Matrix (Fin p) (Fin p) ℝ)
    (standardRealGaussianMatrixMeasure k p)

/-- The `sigma = I` Matsumoto realization is exactly the half-scale image of
the project's variance-one (`sigma = 2 I`) Wishart law. -/
theorem matsumotoIdentityWishartGramLaw_eq_halfScale_projectStandard
    (k p : ℕ) :
    matsumotoIdentityWishartGramLaw k p =
      Measure.map (realWishartSigmaScaleMatrix p (1 / 2 : ℝ))
        (projectStandardWishartGramLaw k p) := by
  unfold matsumotoIdentityWishartGramLaw projectStandardWishartGramLaw
  rw [← map_invSqrtTwoScaleMatrix_standardRealGaussianMatrixMeasure k p]
  rw [Measure.map_map
    (measurable_realWishartGram_genericSteinHaff
      (k := Fin k) (p := Fin p))
    (measurable_invSqrtTwoScaleMatrix k p)]
  rw [Measure.map_map
    (measurable_realWishartSigmaScaleMatrix p (1 / 2 : ℝ))
    (measurable_realWishartGram_genericSteinHaff
      (k := Fin k) (p := Fin p))]
  apply Measure.map_congr
  filter_upwards [] with R
  simpa only [Function.comp_apply, realWishartSigmaScaleMatrix] using
    realWishartGram_invSqrtTwoScaleMatrix k p R

/-- Equivalently, the project's variance-one law is Matsumoto's identity-scale
law pushed forward by `W ↦ 2 W`, i.e. the exact `sigma = I` to
`sigma = 2 I` conversion. -/
theorem projectStandardWishartGramLaw_eq_sigmaTwo_pushforward
    (k p : ℕ) :
    projectStandardWishartGramLaw k p =
      Measure.map (realWishartSigmaScaleMatrix p 2)
        (matsumotoIdentityWishartGramLaw k p) := by
  rw [matsumotoIdentityWishartGramLaw_eq_halfScale_projectStandard]
  unfold projectStandardWishartGramLaw
  rw [Measure.map_map
    (measurable_realWishartSigmaScaleMatrix p 2)
    (measurable_realWishartSigmaScaleMatrix p (1 / 2 : ℝ))]
  have hfun :
      realWishartSigmaScaleMatrix p 2 ∘
          realWishartSigmaScaleMatrix p (1 / 2 : ℝ) = id := by
    funext W
    ext i j
    simp [realWishartSigmaScaleMatrix, Function.comp_apply]
  rw [hfun, Measure.map_id]

/-- Matsumoto's integer-shape parameter `beta = k/2`, kept separate from all
project substitutions. -/
def matsumotoIntegerShapeBeta (k : ℕ) : ℝ :=
  (k : ℝ) / 2

/-- Matsumoto's paper variable `gamma = beta - (d+1)/2`. -/
def matsumotoGamma (d : ℕ) (beta : ℝ) : ℝ :=
  beta - ((d : ℝ) + 1) / 2

/-- Project-variable substitution for the denominator Wishart shape. -/
theorem projectDenominator_matsumotoGamma_eq
    {N K : ℕ} (hNK : N ≤ K) :
    matsumotoGamma N (matsumotoIntegerShapeBeta (K - N)) =
      ((K : ℝ) - 2 * (N : ℝ) - 1) / 2 := by
  unfold matsumotoGamma matsumotoIntegerShapeBeta
  rw [Nat.cast_sub hNK]
  ring

/-- The exact A4 order-four existence condition follows from the endpoint
threshold without any rounding loss. -/
theorem projectDenominator_matsumotoGamma_gt_three
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K) :
    3 < matsumotoGamma N (matsumotoIntegerShapeBeta (K - N)) := by
  rw [projectDenominator_matsumotoGamma_eq (by omega : N ≤ K)]
  have hgapR : (2 : ℝ) * (N : ℝ) + 8 ≤ (K : ℝ) := by
    exact_mod_cast hgap
  linarith

/-- Literal Theorem-3 side condition `gamma > n-1` for every contraction
order at most four. -/
theorem projectDenominator_matsumotoGamma_gt_order_sub_one
    {N K n : ℕ} (hgap : 2 * N + 8 ≤ K) (hn : n ≤ 4) :
    (n : ℝ) - 1 <
      matsumotoGamma N (matsumotoIntegerShapeBeta (K - N)) := by
  have hgamma := projectDenominator_matsumotoGamma_gt_three hgap
  have hnR : (n : ℝ) ≤ 4 := by exact_mod_cast hn
  linarith

/-- Exact inverse-entry moment scaling.  Under the paper's `sigma = I`
source, an order-`q` inverse product is `2^q` times its value under the
project's variance-one (`sigma = 2 I`) source. -/
theorem halfGaussian_inverseWishartEntryProduct_integral_sigmaScale
    {k p q : ℕ} (hpk : p ≤ k)
    (indices : Fin q → Fin p × Fin p) :
    (∫ R : Matrix (Fin k) (Fin p) ℝ,
        inverseWishartEntryProduct indices R ∂halfGaussianMatrix k p) =
      (2 : ℝ) ^ q *
        ∫ R : Matrix (Fin k) (Fin p) ℝ,
          inverseWishartEntryProduct indices R
            ∂standardRealGaussianMatrixMeasure k p := by
  let f : Matrix (Fin k) (Fin p) ℝ → ℝ :=
    inverseWishartEntryProduct indices
  have hf : Measurable f :=
    measurable_inverseWishartEntryProduct k p q indices
  have hunit :=
    ae_isUnit_det_realWishartGram_standardRealGaussianMatrixMeasure
      (k := k) (p := p) hpk
  have hscale :
      f ∘ invSqrtTwoScaleMatrix k p =ᵐ[
        standardRealGaussianMatrixMeasure k p]
        fun R ↦ (2 : ℝ) ^ q * f R := by
    filter_upwards [hunit] with R hR
    exact inverseWishartEntryProduct_invSqrtTwoScaleMatrix indices R hR
  calc
    (∫ R : Matrix (Fin k) (Fin p) ℝ, f R ∂halfGaussianMatrix k p) =
        ∫ R, f R
          ∂Measure.map (invSqrtTwoScaleMatrix k p)
            (standardRealGaussianMatrixMeasure k p) := by
      rw [map_invSqrtTwoScaleMatrix_standardRealGaussianMatrixMeasure]
    _ = ∫ R, f (invSqrtTwoScaleMatrix k p R)
        ∂standardRealGaussianMatrixMeasure k p := by
      rw [integral_map (measurable_invSqrtTwoScaleMatrix k p).aemeasurable
        hf.aestronglyMeasurable]
    _ = ∫ R, (2 : ℝ) ^ q * f R
        ∂standardRealGaussianMatrixMeasure k p := by
      apply integral_congr_ae
      filter_upwards [hscale] with R hR
      simpa only [Function.comp_apply] using hR
    _ = (2 : ℝ) ^ q * ∫ R, f R
        ∂standardRealGaussianMatrixMeasure k p := by
      rw [integral_const_mul]

/-- The same scale identity solved in the direction needed to substitute the
approved A4 identity-scale formula into the project's denominator law. -/
theorem projectStandard_inverseWishartEntryProduct_integral_sigmaScale
    {k p q : ℕ} (hpk : p ≤ k)
    (indices : Fin q → Fin p × Fin p) :
    (∫ R : Matrix (Fin k) (Fin p) ℝ,
        inverseWishartEntryProduct indices R
          ∂standardRealGaussianMatrixMeasure k p) =
      ((2 : ℝ) ^ q)⁻¹ *
        ∫ R : Matrix (Fin k) (Fin p) ℝ,
          inverseWishartEntryProduct indices R ∂halfGaussianMatrix k p := by
  rw [halfGaussian_inverseWishartEntryProduct_integral_sigmaScale hpk indices]
  simp

/-- Exact fourth-order specialization for the beta-prime denominator. -/
theorem betaPrimeDenominator_inverseWishartEntryProduct_four_sigmaScale
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K)
    (indices : Fin 4 → Fin N × Fin N) :
    (∫ R : Matrix (Fin (K - N)) (Fin N) ℝ,
        inverseWishartEntryProduct indices R
          ∂standardRealGaussianMatrixMeasure (K - N) N) =
      (16 : ℝ)⁻¹ *
        ∫ R : Matrix (Fin (K - N)) (Fin N) ℝ,
          inverseWishartEntryProduct indices R
            ∂halfGaussianMatrix (K - N) N := by
  have h :=
    projectStandard_inverseWishartEntryProduct_integral_sigmaScale
      (k := K - N) (p := N) (q := 4) (by omega) indices
  convert h using 1 <;> norm_num

/-- CONDITIONAL adapter: once A4 supplies an identity-scale fourth-entry
moment in literal paper variables, this separately proved project substitution
converts it to the variance-one beta-prime denominator. -/
theorem betaPrimeDenominator_fourthEntryMoment_of_matsumotoIdentity_conditional
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K)
    (indices : Fin 4 → Fin N × Fin N) (value : ℝ)
    (hA4Identity :
      (∫ R : Matrix (Fin (K - N)) (Fin N) ℝ,
          inverseWishartEntryProduct indices R
            ∂halfGaussianMatrix (K - N) N) = value) :
    (∫ R : Matrix (Fin (K - N)) (Fin N) ℝ,
        inverseWishartEntryProduct indices R
          ∂standardRealGaussianMatrixMeasure (K - N) N) =
      (16 : ℝ)⁻¹ * value := by
  rw [betaPrimeDenominator_inverseWishartEntryProduct_four_sigmaScale
    hgap indices, hA4Identity]

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08
