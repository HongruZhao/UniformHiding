import LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep.ConcreteCanonicalMatrixEndpoints
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H11H13_CanonicalMomentPackageA1A4
import LogdetLean.GramHafnian.UltimateHiding.SquaredNormalized
import LogdetLean.GramHafnian.UltimateHiding.SquaredRateAlgebra
import LogdetLean.GramHafnian.UltimateHiding.InverseGradientEndpoint

/-!
# Paper-facing endpoints for the successor matrix-law article

This module publishes literal wrappers for displays whose mathematical content
was already checked by the hiding development but which previously had no
one-declaration paper-facing surface.  It introduces no new scientific input.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.MatrixLawEndpoints

noncomputable section

open LocalAnticoncentration
open UltimateHiding
open UltimateHiding.DenseScore
open UltimateHiding.DenseLocalStep

/-- The article's normalized transpose-Gram map
`Upsilon_K(Y) = K^(-1/2) Y Y^T`. -/
def normalizedTransposeGramMatrix {N K : ℕ}
    (Y : Matrix (Fin N) (Fin K) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  normalizeTransposeGram N K (rectangularTransposeGram Y)

/-- Literal endpoint for `eq:hide-covariance` (and hence the commutative
diagram `eq:hide-commutative-diagram`). -/
theorem eq_hide_covariance {N K : ℕ}
    (g : Matrix (Fin N) (Fin N) ℂ)
    (Y : Matrix (Fin N) (Fin K) ℂ) :
    normalizedTransposeGramMatrix (g * Y) =
      g * normalizedTransposeGramMatrix Y * g.transpose := by
  simp only [normalizedTransposeGramMatrix, normalizeTransposeGram,
    rectangularTransposeGram, Matrix.transpose_mul]
  rw [Matrix.mul_assoc g Y (Y.transpose * g.transpose)]
  rw [← Matrix.mul_assoc Y Y.transpose g.transpose]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]

/-- Literal normalized form of `eq:uniform-product-hiding`. -/
theorem eq_uniform_product_hiding_normalized
    (H : UnitaryHaarProbabilityFamily) {M N K : ℕ}
    (hN : 1 ≤ N) (hNK : N ≤ K) (hKM : K ≤ M) :
    probabilityTotalVariationLE
      (normalizedHaarTransposeGramLaw H M N K)
      (normalizedGaussianTransposeGramLaw N K)
      (min 1
        (concreteCanonicalHidingSquaredConstant *
          ultimateSquaredHidingRate M N)) :=
  normalizedProductMatrixHidingSquared_of_unnormalized
    uniformProductMatrixHidingSquaredAt_concreteCanonical
    H hN hNK hKM

/-- Literal unnormalized form `eq:uniform-product-hiding-unscaled`. -/
theorem eq_uniform_product_hiding_unscaled
    (H : UnitaryHaarProbabilityFamily) {M N K : ℕ}
    (hN : 1 ≤ N) (hNK : N ≤ K) (hKM : K ≤ M) :
    probabilityTotalVariationLE
      (scaledHaarTransposeGramLaw H M N K)
      (gaussianTransposeGramLaw N K)
      (min 1
        (concreteCanonicalHidingSquaredConstant *
          ultimateSquaredHidingRate M N)) :=
  uniformProductMatrixHidingSquaredAt_concreteCanonical.apply
    H hN hNK hKM

/-- The direct dense-branch coefficient before the finite sparse stitch. -/
def concreteCanonicalDenseHidingSquaredConstant : ℝ :=
  4 * exactVarianceCentralScoreOneConstant +
    5 * exactVarianceCentralScoreTwoConstant +
    2 * exactVarianceOrbitalScoreTwoConstant +
    2 * combinedSharperCanonicalOrbitalThirdConstant + 72

/-- Literal direct dense branch `eq:dense-product-hiding`, with the concrete
thresholds used by the checked proof (`16*N ≤ K`, `24*N² ≤ M`). -/
theorem eq_dense_product_hiding
    (H : UnitaryHaarProbabilityFamily) {M N K : ℕ}
    (hN : 1 ≤ N) (hNK : N ≤ K) (hKM : K ≤ M)
    (hlarge : 24 * N ^ 2 ≤ M) (hdense : 16 * N ≤ K) :
    probabilityTotalVariationLE
      (scaledHaarTransposeGramLaw H M N K)
      (gaussianTransposeGramLaw N K)
      (concreteCanonicalDenseHidingSquaredConstant *
        ultimateSquaredHidingRate M N) := by
  have hlocal : UltimateHiding.Dense.ConcreteDenseSquaredLocalStepAt
      concreteCanonicalDenseHidingSquaredConstant 24 16 := by
    simpa only [concreteCanonicalDenseHidingSquaredConstant] using
      concreteDenseSquaredLocalStepAt_of_canonicalCOEBaseScoreCertificate
        uniformCanonicalScaledCOESharedBetaScoreCertificate_combinedSharper
  have hdirect :=
    UltimateHiding.Dense.veryLargeDenseSquaredBranchAt_of_localStep hlocal
      H M N K hN hNK hKM hlarge hdense
  exact hdirect.mono (min_le_right _ _)

/-- Literal normalized matrix law displayed in `eq:dense-product-hiding`.
The unnormalized theorem above is pushed through the common `K^{-1/2}`
normalization, so the error is unchanged. -/
theorem eq_dense_product_hiding_normalized
    (H : UnitaryHaarProbabilityFamily) {M N K : ℕ}
    (hN : 1 ≤ N) (hNK : N ≤ K) (hKM : K ≤ M)
    (hlarge : 24 * N ^ 2 ≤ M) (hdense : 16 * N ≤ K) :
    probabilityTotalVariationLE
      (normalizedHaarTransposeGramLaw H M N K)
      (normalizedGaussianTransposeGramLaw N K)
      (concreteCanonicalDenseHidingSquaredConstant *
        ultimateSquaredHidingRate M N) := by
  unfold normalizedHaarTransposeGramLaw normalizedGaussianTransposeGramLaw
  exact (eq_dense_product_hiding H hN hNK hKM hlarge hdense).map
    (measurable_normalizeTransposeGram N K)

/-- Literal constant-free rate comparison in `eq:hide-rate-comparison`.
The first comparison uses the probability cap in the small-ambient range. -/
theorem eq_hide_rate_comparison {M N K : ℕ}
    (hM : 1 ≤ M) (hNK : N ≤ K) :
    min 1 (ultimateSquaredHidingRate M N) ≤
        min 1 (ultimateHidingRate M N) ∧
      min 1 (ultimateHidingRate M N) ≤
        min 1 (rectangularHidingRate M N K) := by
  constructor
  · by_cases hlarge : N ^ 2 ≤ M
    · simpa using
        (min_squaredHidingRate_le_min_hidingRate
          (C := (1 : ℝ)) (by norm_num) hM hlarge)
    · have hsmall : M ≤ N ^ 2 := by omega
      have hsquared : min 1 (ultimateSquaredHidingRate M N) = 1 := by
        simpa using
          (min_one_mul_ultimateSquaredHidingRate_eq_one_of_le_sq
            (C := (1 : ℝ)) (by norm_num) hM hsmall)
      have hsqrt : min 1 (ultimateHidingRate M N) = 1 := by
        simpa using
          (min_one_mul_ultimateHidingRate_eq_one_of_le_sq
            (C := (1 : ℝ)) (by norm_num) hM hsmall)
      rw [hsquared, hsqrt]
  · exact min_le_min_left 1
      (ultimateHidingRate_le_rectangularHidingRate hM hNK)

end

end LogdetLean.GramHafnian.MatrixLawEndpoints
