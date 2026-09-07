import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H6_RadialContractsConditional
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H6_RadialMeasureAdapters
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic

/-!
# Raw Muirhead beta-II contract and proved H6 adapters

This file exposes the beta-II input below the existing normalized radial
contract.  The primitive premise is a raw spectral-density theorem for the
literal independent Gaussian/Wishart ratio, up to one positive finite
normalizer.  The general real beta-II density retains both its origin and tail
exponents.  The specialization

`m = N+1`, `n = K-N`

is proved internally: the origin exponent is exactly zero and the tail
parameter is exactly `(K+1)/2`.  Thus no `x_i` power remains.  Support and
canonical normalization are also derived rather than assumed.
-/

open scoped BigOperators ENNReal
open Set MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.Wishart
open H6CoordinateAlgebra H6DensityTransform H6VectorChangeOfVariables
open H6RadialMeasureAdapters

/-! ## General real beta-II radial density -/

/-- Origin exponent in the real symmetric beta-II eigenvalue density with
numerator degrees of freedom `m`. -/
def realBetaIIOriginExponent (N m : ℕ) : ℝ :=
  ((m : ℝ) - (N : ℝ) - 1) / 2

/-- Positive tail parameter `(m+n)/2`; the density uses its negative. -/
def realBetaIITailParameter (m n : ℕ) : ℝ :=
  ((m : ℝ) + (n : ℝ)) / 2

/-- Product of origin powers in the general beta-II radial density. -/
def positiveOriginRpowProduct (N : ℕ) (a : ℝ)
    (x : Fin N → ℝ) : ℝ :=
  ∏ i : Fin N, Real.rpow (x i) a

/-- General unnormalized real symmetric beta-II eigenvalue weight. -/
def realBetaIIEigenvalueWeight (N m n : ℕ)
    (x : Fin N → ℝ) : ℝ :=
  vandermondeAbs N x *
    positiveOriginRpowProduct N (realBetaIIOriginExponent N m) x *
    positiveCoordinateRpowProduct N
      (-(realBetaIITailParameter m n)) x

def realBetaIIEigenvalueDensity (N m n : ℕ)
    (x : Fin N → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (realBetaIIEigenvalueWeight N m n x)

/-- Raw general real beta-II radial measure. -/
def realBetaIIEigenvalueRadialMeasure (N m n : ℕ) :
    Measure (Fin N → ℝ) :=
  (volume.restrict (openPositiveOrthant N)).withDensity
    (realBetaIIEigenvalueDensity N m n)

theorem realBetaIIOriginExponent_N_add_one (N : ℕ) :
    realBetaIIOriginExponent N (N + 1) = 0 := by
  unfold realBetaIIOriginExponent
  push_cast
  ring

theorem realBetaIITailParameter_N_add_one_K_sub_N
    {N K : ℕ} (hNK : N ≤ K) :
    realBetaIITailParameter (N + 1) (K - N) =
      ((K : ℝ) + 1) / 2 := by
  unfold realBetaIITailParameter
  rw [Nat.cast_sub hNK]
  push_cast
  ring

@[simp]
theorem positiveOriginRpowProduct_zero
    (N : ℕ) (x : Fin N → ℝ) :
    positiveOriginRpowProduct N 0 x = 1 := by
  classical
  unfold positiveOriginRpowProduct
  simp

/-- Exact parameter specialization: the `x_i` origin factor disappears and
the tail exponent becomes `-(K+1)/2`. -/
theorem realBetaIIEigenvalueWeight_specializes
    {N K : ℕ} (hNK : N ≤ K) (x : Fin N → ℝ) :
    realBetaIIEigenvalueWeight N (N + 1) (K - N) x =
      betaPrimeEigenvalueWeight N (((K : ℝ) + 1) / 2) x := by
  unfold realBetaIIEigenvalueWeight betaPrimeEigenvalueWeight
  rw [realBetaIIOriginExponent_N_add_one,
    realBetaIITailParameter_N_add_one_K_sub_N hNK,
    positiveOriginRpowProduct_zero, mul_one]

theorem realBetaIIEigenvalueDensity_specializes
    {N K : ℕ} (hNK : N ≤ K) :
    realBetaIIEigenvalueDensity N (N + 1) (K - N) =
      betaPrimeEigenvalueDensity N K := by
  funext x
  unfold realBetaIIEigenvalueDensity betaPrimeEigenvalueDensity
  rw [realBetaIIEigenvalueWeight_specializes hNK]

theorem realBetaIIEigenvalueRadialMeasure_specializes
    {N K : ℕ} (hNK : N ≤ K) :
    realBetaIIEigenvalueRadialMeasure N (N + 1) (K - N) =
      betaPrimeEigenvalueRadialMeasure N K := by
  unfold realBetaIIEigenvalueRadialMeasure betaPrimeEigenvalueRadialMeasure
  rw [realBetaIIEigenvalueDensity_specializes hNK]

theorem h6_range_implies_N_le_K
    {N K : ℕ} (h2NK : 2 * N ≤ K) : N ≤ K := by omega

theorem h6_range_implies_denominator_df
    {N K : ℕ} (h2NK : 2 * N ≤ K) : N ≤ K - N := by omega

/-- Numerator beta-II shape is above the real multivariate-gamma threshold. -/
theorem realBetaII_numerator_shape_gt_threshold (N : ℕ) :
    ((N + 1 : ℕ) : ℝ) / 2 > ((N : ℝ) - 1) / 2 := by
  push_cast
  linarith

/-- The exact H6 range puts the denominator shape above the same threshold. -/
theorem realBetaII_denominator_shape_gt_threshold
    {N K : ℕ} (h2NK : 2 * N ≤ K) :
    (((K - N : ℕ) : ℝ) / 2) > ((N : ℝ) - 1) / 2 := by
  have hNK : N ≤ K := h6_range_implies_N_le_K h2NK
  have hdf : N ≤ K - N := h6_range_implies_denominator_df h2NK
  have hdfR : (N : ℝ) ≤ ((K - N : ℕ) : ℝ) := by
    exact_mod_cast hdf
  rw [Nat.cast_sub hNK] at hdfR
  rw [Nat.cast_sub hNK]
  linarith [hdfR]

/-! ## Primitive raw Gaussian--Wishart/Muirhead contract -/

/-- **CONDITIONAL primitive Muirhead contract.**  The literal Gaussian
Wishart ratio admits measurable spectral coordinates whose raw law is the
general real beta-II radial density for degrees of freedom `N+1` and `K-N`,
up to one positive finite scalar.

This statement contains no COE matrix, H5 premise, trace-vector equality, or
H6 endpoint.  It is strictly below the normalized contract used previously. -/
structure GaussianWishartMuirheadRawSpectralContract
    (N K : ℕ) where
  spectrum : RealBetaPrimeGaussianSource N K → (Fin N → ℝ)
  measurable_spectrum : Measurable spectrum
  conjugator : RealBetaPrimeGaussianSource N K → Matrix (Fin N) (Fin N) ℝ
  conjugator_unit : ∀ᵐ p ∂realBetaPrimeGaussianSourceLaw N K,
    IsUnit (conjugator p).det
  diagonalization : ∀ᵐ p ∂realBetaPrimeGaussianSourceLaw N K,
    realMatrixBetaPrimeOfGaussianSource p =
      (conjugator p)⁻¹ * Matrix.diagonal (spectrum p) * conjugator p
  radialNormalizer : NNReal
  radialNormalizer_ne_zero : radialNormalizer ≠ 0
  raw_radial_law :
    Measure.map spectrum (realBetaPrimeGaussianSourceLaw N K) =
      (radialNormalizer : ℝ≥0∞) •
        realBetaIIEigenvalueRadialMeasure N (N + 1) (K - N)

theorem realBetaPrimeGaussianSourceLaw_apply_univ (N K : ℕ) :
    realBetaPrimeGaussianSourceLaw N K Set.univ = 1 := by
  letI : IsProbabilityMeasure
      (standardRealGaussianMatrixMeasure (N + 1) N) := by
    unfold standardRealGaussianMatrixMeasure
    apply Measure.pi.instIsProbabilityMeasure
  letI : IsProbabilityMeasure
      (standardRealGaussianMatrixMeasure (K - N) N) := by
    unfold standardRealGaussianMatrixMeasure
    apply Measure.pi.instIsProbabilityMeasure
  letI : IsProbabilityMeasure (realBetaPrimeGaussianSourceLaw N K) := by
    unfold realBetaPrimeGaussianSourceLaw
    infer_instance
  exact measure_univ

theorem GaussianWishartMuirheadRawSpectralContract.raw_betaPrime_radial_law
    {N K : ℕ} (h : GaussianWishartMuirheadRawSpectralContract N K)
    (h2NK : 2 * N ≤ K) :
    Measure.map h.spectrum (realBetaPrimeGaussianSourceLaw N K) =
      (h.radialNormalizer : ℝ≥0∞) •
        betaPrimeEigenvalueRadialMeasure N K := by
  calc
    Measure.map h.spectrum (realBetaPrimeGaussianSourceLaw N K) =
        (h.radialNormalizer : ℝ≥0∞) •
          realBetaIIEigenvalueRadialMeasure N (N + 1) (K - N) :=
      h.raw_radial_law
    _ = (h.radialNormalizer : ℝ≥0∞) •
        betaPrimeEigenvalueRadialMeasure N K := by
      rw [realBetaIIEigenvalueRadialMeasure_specializes
        (h6_range_implies_N_le_K h2NK)]

/-- Probability normalization determines and cancels the unknown Muirhead
normalizer; no multivariate-beta gamma product is evaluated. -/
theorem GaussianWishartMuirheadRawSpectralContract.normalized_radial_law
    {N K : ℕ} (h : GaussianWishartMuirheadRawSpectralContract N K)
    (h2NK : 2 * N ≤ K) :
    Measure.map h.spectrum (realBetaPrimeGaussianSourceLaw N K) =
      normalizedBetaPrimeEigenvalueRadialMeasure N K := by
  have hnorm := map_normalizeMeasure_of_map_eq_nnreal_smul
    (realBetaPrimeGaussianSourceLaw N K)
    (betaPrimeEigenvalueRadialMeasure N K)
    h.spectrum h.radialNormalizer h.measurable_spectrum
    h.radialNormalizer_ne_zero (h.raw_betaPrime_radial_law h2NK)
  have hsourceNormalize :
      normalizeMeasure (realBetaPrimeGaussianSourceLaw N K) =
        realBetaPrimeGaussianSourceLaw N K := by
    unfold normalizeMeasure
    rw [realBetaPrimeGaussianSourceLaw_apply_univ]
    simp
  rw [hsourceNormalize] at hnorm
  simpa [normalizeMeasure, normalizedBetaPrimeEigenvalueRadialMeasure] using hnorm

theorem normalizedBetaPrimeEigenvalueRadialMeasure_ae_positive
    (N K : ℕ) :
    ∀ᵐ x ∂normalizedBetaPrimeEigenvalueRadialMeasure N K,
      x ∈ openPositiveOrthant N := by
  have hraw : ∀ᵐ x ∂betaPrimeEigenvalueRadialMeasure N K,
      x ∈ openPositiveOrthant N := by
    unfold betaPrimeEigenvalueRadialMeasure
    exact withDensity_restrict_ae_mem volume (openPositiveOrthant N)
      (betaPrimeEigenvalueDensity N K) (by
        simpa [← betaPrimeCoordVector_target] using
          (betaPrimeCoordVector N).open_target.measurableSet)
  simpa [normalizeMeasure, normalizedBetaPrimeEigenvalueRadialMeasure] using
    (normalizeMeasure_ae_of_ae hraw)

theorem GaussianWishartMuirheadRawSpectralContract.spectrum_ae_positive
    {N K : ℕ} (h : GaussianWishartMuirheadRawSpectralContract N K)
    (h2NK : 2 * N ≤ K) :
    ∀ᵐ p ∂realBetaPrimeGaussianSourceLaw N K,
      h.spectrum p ∈ openPositiveOrthant N := by
  have htarget :
      ∀ᵐ x ∂Measure.map h.spectrum
          (realBetaPrimeGaussianSourceLaw N K),
        x ∈ openPositiveOrthant N :=
    (h.normalized_radial_law h2NK).symm ▸
      normalizedBetaPrimeEigenvalueRadialMeasure_ae_positive N K
  have hset : MeasurableSet (openPositiveOrthant N) := by
    simpa [← betaPrimeCoordVector_target] using
      (betaPrimeCoordVector N).open_target.measurableSet
  exact (ae_map_iff h.measurable_spectrum.aemeasurable hset).mp htarget

/-- Fully proved adapter to the normalized Muirhead radial contract consumed
by the saved H6 reduction. -/
def GaussianWishartMuirheadRawSpectralContract.toWishartMuirheadBetaIIRadialContract
    {N K : ℕ} (h : GaussianWishartMuirheadRawSpectralContract N K)
    (h2NK : 2 * N ≤ K) :
    WishartMuirheadBetaIIRadialContract N K where
  spectrum := h.spectrum
  measurable_spectrum := h.measurable_spectrum
  conjugator := h.conjugator
  conjugator_unit := h.conjugator_unit
  diagonalization := h.diagonalization
  radial_law := h.normalized_radial_law h2NK

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
