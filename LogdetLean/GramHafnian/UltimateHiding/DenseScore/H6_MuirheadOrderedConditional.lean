import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H6_OrderedRadialAdapters
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# Selector-free ordered Muirhead reduction for H6 (CONDITIONAL)

The generalized eigenvalue problem is replaced by the canonical symmetric
quotient

`B^(-1/2) A B^(-1/2)`.

The denominator square root, almost-sure invertibility, similarity to
`B⁻¹ A`, and trace-power transfer are proved.  Mathlib's spectral theorem
then gives the power sums without a measurable eigenbasis.  The remaining
conditional inputs are only measurability of the canonical ordered
eigenvalues and their ordered raw beta-II density.
-/

open scoped BigOperators ENNReal MatrixOrder
open Set MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.Wishart
open H6CoordinateAlgebra H6VectorChangeOfVariables
open H6RadialMeasureAdapters

/-- Canonical positive square root of the denominator Wishart Gram matrix. -/
def wishartDenominatorSqrt {N K : ℕ}
    (p : RealBetaPrimeGaussianSource N K) : Matrix (Fin N) (Fin N) ℝ :=
  CFC.sqrt (realWishartGram p.2)

/-- Canonical symmetric representative of the beta-II matrix ratio. -/
def realBetaPrimeSymmetricQuotient {N K : ℕ}
    (p : RealBetaPrimeGaussianSource N K) : Matrix (Fin N) (Fin N) ℝ :=
  wishartSymmetricConjugate (wishartDenominatorSqrt p)
    (realWishartGram p.1)

theorem wishartDenominatorSqrt_isSymm
    {N K : ℕ} (p : RealBetaPrimeGaussianSource N K) :
    (wishartDenominatorSqrt p).IsSymm := by
  rw [← Matrix.isHermitian_iff_isSymm]
  exact (CFC.sqrt_nonneg (realWishartGram p.2)).isSelfAdjoint

theorem wishartDenominatorSqrt_square
    {N K : ℕ} (p : RealBetaPrimeGaussianSource N K) :
    realWishartGram p.2 =
      wishartDenominatorSqrt p * wishartDenominatorSqrt p := by
  symm
  exact CFC.sqrt_mul_sqrt_self (realWishartGram p.2)
    (realWishartGram_posSemidef_internal p.2).nonneg

theorem realBetaPrimeSymmetricQuotient_isSymm
    {N K : ℕ} (p : RealBetaPrimeGaussianSource N K) :
    (realBetaPrimeSymmetricQuotient p).IsSymm := by
  exact wishartSymmetricConjugate_isSymm
    (wishartDenominatorSqrt_isSymm p)
    (realWishartGram_isSymm_internal p.1)

theorem realBetaPrimeSymmetricQuotient_isHermitian
    {N K : ℕ} (p : RealBetaPrimeGaussianSource N K) :
    (realBetaPrimeSymmetricQuotient p).IsHermitian := by
  simpa only [Matrix.isHermitian_iff_isSymm] using
    (realBetaPrimeSymmetricQuotient_isSymm p)

/-- Canonical decreasing eigenvalues of the symmetric quotient. -/
def orderedWishartSymmetricSpectrum (N K : ℕ)
    (p : RealBetaPrimeGaussianSource N K) : Fin N → ℝ :=
  (realBetaPrimeSymmetricQuotient_isHermitian p).eigenvalues

/-- Trace powers of a real Hermitian matrix are the power sums of Mathlib's
canonical ordered eigenvalues. -/
theorem trace_pow_eq_sum_eigenvalues_real
    {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.IsHermitian) (m : ℕ) :
    Matrix.trace (A ^ m) = ∑ i : Fin N, (hA.eigenvalues i) ^ m := by
  classical
  let U := hA.eigenvectorUnitary
  let D : Matrix (Fin N) (Fin N) ℝ :=
    Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues)
  calc
    Matrix.trace (A ^ m) =
        Matrix.trace ((Unitary.conjStarAlgAut ℝ _ U D) ^ m) := by
      rw [hA.spectral_theorem]
    _ = Matrix.trace (Unitary.conjStarAlgAut ℝ _ U (D ^ m)) := by
      rw [map_pow]
    _ = Matrix.trace (D ^ m) := by
      rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
        Unitary.coe_star_mul_self, one_mul]
    _ = ∑ i : Fin N, (hA.eigenvalues i) ^ m := by
      simp [D, Matrix.diagonal_pow]

theorem trace_realBetaPrimeSymmetricQuotient_pow
    {N K : ℕ} (p : RealBetaPrimeGaussianSource N K) (m : ℕ) :
    Matrix.trace ((realBetaPrimeSymmetricQuotient p) ^ m) =
      ∑ i : Fin N, (orderedWishartSymmetricSpectrum N K p i) ^ m := by
  simpa [orderedWishartSymmetricSpectrum] using
    trace_pow_eq_sum_eigenvalues_real
      (realBetaPrimeSymmetricQuotient_isHermitian p) m

theorem wishartDenominatorSqrt_det_isUnit
    {N K : ℕ} (p : RealBetaPrimeGaussianSource N K)
    (hdet : IsUnit (realWishartGram p.2).det) :
    IsUnit (wishartDenominatorSqrt p).det := by
  have hB : IsUnit (realWishartGram p.2) :=
    (Matrix.isUnit_iff_isUnit_det (realWishartGram p.2)).mpr hdet
  have hS : IsUnit (wishartDenominatorSqrt p) := by
    apply (CFC.isUnit_sqrt_iff (realWishartGram p.2)
      (realWishartGram_posSemidef_internal p.2).nonneg).mpr
    exact hB
  exact (Matrix.isUnit_iff_isUnit_det (wishartDenominatorSqrt p)).mp hS

/-- The nonsymmetric ratio is almost surely similar to the canonical
symmetric quotient.  This discharges denominator invertibility and the
similarity algebra independently of any density theorem. -/
theorem ae_realBetaPrime_ratio_similar_to_symmetricQuotient
    {N K : ℕ} (h2NK : 2 * N ≤ K) :
    ∀ᵐ p ∂realBetaPrimeGaussianSourceLaw N K,
      IsUnit (wishartDenominatorSqrt p).det ∧
        realMatrixBetaPrimeOfGaussianSource p =
          (wishartDenominatorSqrt p)⁻¹ *
            realBetaPrimeSymmetricQuotient p *
              wishartDenominatorSqrt p := by
  filter_upwards [ae_betaPrimeSource_wishart_det_units_internal h2NK]
    with p hp
  have hS := wishartDenominatorSqrt_det_isUnit p hp.2
  exact ⟨hS,
    inverse_mul_eq_inverse_conjugate_of_square hS
      (wishartDenominatorSqrt_square p)⟩

/-- Pointwise spectral diagonalization of the symmetric representative.
No measurable eigenbasis is asserted or needed. -/
theorem realBetaPrimeSymmetricQuotient_spectral_theorem
    {N K : ℕ} (p : RealBetaPrimeGaussianSource N K) :
    realBetaPrimeSymmetricQuotient p =
      Unitary.conjStarAlgAut ℝ _
        (realBetaPrimeSymmetricQuotient_isHermitian p).eigenvectorUnitary
        (Matrix.diagonal (RCLike.ofReal ∘
          orderedWishartSymmetricSpectrum N K p)) := by
  simpa [orderedWishartSymmetricSpectrum] using
    (realBetaPrimeSymmetricQuotient_isHermitian p).spectral_theorem

/-- Almost-sure trace-power transfer from the literal Gaussian ratio to the
canonical ordered symmetric spectrum. -/
theorem ae_realBetaPrime_trace_pow_eq_orderedSpectrum
    {N K : ℕ} (h2NK : 2 * N ≤ K) :
    ∀ᵐ p ∂realBetaPrimeGaussianSourceLaw N K,
      ∀ m : ℕ,
        Matrix.trace ((realMatrixBetaPrimeOfGaussianSource p) ^ m) =
          ∑ i : Fin N,
            (orderedWishartSymmetricSpectrum N K p i) ^ m := by
  filter_upwards [ae_realBetaPrime_ratio_similar_to_symmetricQuotient h2NK]
    with p hp
  intro m
  calc
    Matrix.trace ((realMatrixBetaPrimeOfGaussianSource p) ^ m) =
        Matrix.trace ((realBetaPrimeSymmetricQuotient p) ^ m) := by
      rw [hp.2]
      exact trace_inverse_conjugate_pow (wishartDenominatorSqrt p)
        (realBetaPrimeSymmetricQuotient p) m hp.1
    _ = ∑ i : Fin N,
          (orderedWishartSymmetricSpectrum N K p i) ^ m :=
      trace_realBetaPrimeSymmetricQuotient_pow p m

/-- **CONDITIONAL measurable ordered-eigenvalue API.**  This is the exact
topological gap left by the pinned library: Borel measurability of the fixed
canonical eigenvalue map.  It contains no density or probability law. -/
structure WishartSymmetricOrderedSpectrumAPI (N K : ℕ) where
  measurable_spectrum : Measurable (orderedWishartSymmetricSpectrum N K)

/-- **CONDITIONAL ordered Muirhead/Weyl contract.**  This is the remaining
raw beta-II spectral-density theorem for the fixed symmetric quotient.  It
does not contain a conjugator, an eigenbasis, a COE matrix, H5, trace powers,
or H6. -/
structure GaussianWishartMuirheadOrderedRadialContract (N K : ℕ) where
  radialNormalizer : NNReal
  radialNormalizer_ne_zero : radialNormalizer ≠ 0
  raw_ordered_radial_law :
    Measure.map (orderedWishartSymmetricSpectrum N K)
        (realBetaPrimeGaussianSourceLaw N K) =
      (radialNormalizer : ℝ≥0∞) •
        orderedRealBetaIIEigenvalueRadialMeasure N (N + 1) (K - N)

theorem GaussianWishartMuirheadOrderedRadialContract.raw_ordered_betaPrime_law
    {N K : ℕ} (h : GaussianWishartMuirheadOrderedRadialContract N K)
    (h2NK : 2 * N ≤ K) :
    Measure.map (orderedWishartSymmetricSpectrum N K)
        (realBetaPrimeGaussianSourceLaw N K) =
      (h.radialNormalizer : ℝ≥0∞) •
        orderedBetaPrimeEigenvalueRadialMeasure N K := by
  calc
    Measure.map (orderedWishartSymmetricSpectrum N K)
        (realBetaPrimeGaussianSourceLaw N K) =
        (h.radialNormalizer : ℝ≥0∞) •
          orderedRealBetaIIEigenvalueRadialMeasure N (N + 1) (K - N) :=
      h.raw_ordered_radial_law
    _ = (h.radialNormalizer : ℝ≥0∞) •
        orderedBetaPrimeEigenvalueRadialMeasure N K := by
      rw [orderedRealBetaIIEigenvalueRadialMeasure_specializes
        (h6_range_implies_N_le_K h2NK)]

/-- Probability normalization cancels the unknown Muirhead/Weyl constant. -/
theorem GaussianWishartMuirheadOrderedRadialContract.normalized_ordered_law
    {N K : ℕ} (hSpec : WishartSymmetricOrderedSpectrumAPI N K)
    (h : GaussianWishartMuirheadOrderedRadialContract N K)
    (h2NK : 2 * N ≤ K) :
    Measure.map (orderedWishartSymmetricSpectrum N K)
        (realBetaPrimeGaussianSourceLaw N K) =
      normalizedOrderedBetaPrimeEigenvalueRadialMeasure N K := by
  have hnorm := map_normalizeMeasure_of_map_eq_nnreal_smul
    (realBetaPrimeGaussianSourceLaw N K)
    (orderedBetaPrimeEigenvalueRadialMeasure N K)
    (orderedWishartSymmetricSpectrum N K) h.radialNormalizer
    hSpec.measurable_spectrum h.radialNormalizer_ne_zero
    (h.raw_ordered_betaPrime_law h2NK)
  have hsourceNormalize :
      normalizeMeasure (realBetaPrimeGaussianSourceLaw N K) =
        realBetaPrimeGaussianSourceLaw N K := by
    unfold normalizeMeasure
    rw [realBetaPrimeGaussianSourceLaw_apply_univ]
    simp
  rw [hsourceNormalize] at hnorm
  simpa [normalizeMeasure,
    normalizedOrderedBetaPrimeEigenvalueRadialMeasure] using hnorm

theorem normalizedOrderedBetaPrimeEigenvalueRadialMeasure_ae_positive_ordered
    (N K : ℕ) :
    ∀ᵐ x ∂normalizedOrderedBetaPrimeEigenvalueRadialMeasure N K,
      x ∈ openPositiveOrthant N ∧ x ∈ strictSpectralChamber N := by
  simpa [normalizeMeasure,
    normalizedOrderedBetaPrimeEigenvalueRadialMeasure] using
    (normalizeMeasure_ae_of_ae
      (orderedBetaPrimeEigenvalueRadialMeasure_ae_positive_ordered N K))

theorem GaussianWishartMuirheadOrderedRadialContract.spectrum_ae_positive_ordered
    {N K : ℕ} (hSpec : WishartSymmetricOrderedSpectrumAPI N K)
    (h : GaussianWishartMuirheadOrderedRadialContract N K)
    (h2NK : 2 * N ≤ K) :
    ∀ᵐ p ∂realBetaPrimeGaussianSourceLaw N K,
      orderedWishartSymmetricSpectrum N K p ∈ openPositiveOrthant N ∧
        orderedWishartSymmetricSpectrum N K p ∈ strictSpectralChamber N := by
  have htarget :
      ∀ᵐ x ∂Measure.map (orderedWishartSymmetricSpectrum N K)
          (realBetaPrimeGaussianSourceLaw N K),
        x ∈ openPositiveOrthant N ∧ x ∈ strictSpectralChamber N :=
    (h.normalized_ordered_law hSpec h2NK).symm ▸
      normalizedOrderedBetaPrimeEigenvalueRadialMeasure_ae_positive_ordered N K
  exact (ae_map_iff hSpec.measurable_spectrum.aemeasurable
    ((measurableSet_openPositiveOrthant_h6 N).inter
      (measurableSet_strictSpectralChamber N))).mp htarget

/-- Complete trace-vector factorization, derived from the canonical square
root, similarity, and spectral theorem rather than assumed by the radial
density contract. -/
theorem GaussianWishartMuirheadOrderedRadialContract.trace_factorization
    {N K : ℕ} (_hSpec : WishartSymmetricOrderedSpectrumAPI N K)
    (_h : GaussianWishartMuirheadOrderedRadialContract N K)
    (h2NK : 2 * N ≤ K) (r : ℕ) :
    realBetaPrimeTracePowerVector r N K =ᵐ[
      realBetaPrimeGaussianSourceLaw N K]
      spectralPowerSumVector r N ∘ orderedWishartSymmetricSpectrum N K := by
  filter_upwards [ae_realBetaPrime_trace_pow_eq_orderedSpectrum h2NK]
    with p hp
  funext j
  unfold realBetaPrimeTracePowerVector spectralPowerSumVector
  exact hp (j.1 + 1)

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
