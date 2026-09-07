import LogdetLean.GramHafnian.UltimateHiding.DenseScore.BetaPrimeMeanInternal

/-!
# Deterministic Wishart similarity algebra for H6

This module isolates the algebraic part of the Muirhead side of H6.  It proves
that real Wishart Gram matrices are symmetric and positive semidefinite, records
their exact full-column-rank invertibility criterion, and factors every positive
trace power of `B⁻¹ A` through a symmetric congruence whenever a symmetric
invertible square root of `B` is supplied.

No density or spectral-disintegration claim is made here.
-/

open MeasureTheory
open scoped BigOperators

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.Wishart

/-- A real Wishart Gram matrix is symmetric. -/
theorem realWishartGram_isSymm_internal
    {k n : Type*} [Fintype k] [Fintype n]
    (R : Matrix k n ℝ) : (realWishartGram R).IsSymm := by
  unfold realWishartGram Matrix.IsSymm
  rw [Matrix.transpose_mul, Matrix.transpose_transpose]

/-- A real Wishart Gram matrix is positive semidefinite. -/
theorem realWishartGram_posSemidef_internal
    {k n : Type*} [Fintype k] [Fintype n]
    (R : Matrix k n ℝ) : (realWishartGram R).PosSemidef :=
  LogdetLean.GramHafnian.Wishart.realWishartGram_posSemidef R

/-- The exact deterministic full-column-rank criterion for invertibility of a
literal real Wishart Gram matrix. -/
theorem isUnit_det_realWishartGram_iff_linearIndependent_columns
    {k n : ℕ} (R : Matrix (Fin k) (Fin n) ℝ) :
    IsUnit (realWishartGram R).det ↔
      LinearIndependent ℝ
        (fun j ↦ WithLp.toLp 2 (fun i ↦ R i j) :
          Fin n → EuclideanSpace ℝ (Fin k)) := by
  rw [LogdetLean.GramHafnian.Wishart.realWishartGram_eq_gram_toLp_columns]
  simpa [isUnit_iff_ne_zero] using
    (Matrix.det_gram_ne_zero_iff_linearIndependent (𝕜 := ℝ)
      (v := fun j : Fin n ↦
        (WithLp.toLp 2 (fun i ↦ R i j) : EuclideanSpace ℝ (Fin k))))

/-- Under the literal beta-prime Gaussian source law, both real Wishart Gram
determinants are units almost surely in the H6 dimension range. -/
theorem ae_betaPrimeSource_wishart_det_units_internal
    {N K : ℕ} (h2NK : 2 * N ≤ K) :
    ∀ᵐ p ∂realBetaPrimeGaussianSourceLaw N K,
      IsUnit (realWishartGram p.1).det ∧
        IsUnit (realWishartGram p.2).det := by
  have hA :
      ∀ᵐ A ∂standardRealGaussianMatrixMeasure (N + 1) N,
        IsUnit (realWishartGram A).det :=
    ae_isUnit_det_realWishartGram_standardRealGaussianMatrixMeasure
      (k := N + 1) (p := N) (by omega)
  have hB :
      ∀ᵐ B ∂standardRealGaussianMatrixMeasure (K - N) N,
        IsUnit (realWishartGram B).det :=
    ae_isUnit_det_realWishartGram_standardRealGaussianMatrixMeasure
      (k := K - N) (p := N) (by omega)
  have hAprod := (Measure.quasiMeasurePreserving_fst
    (μ := standardRealGaussianMatrixMeasure (N + 1) N)
    (ν := standardRealGaussianMatrixMeasure (K - N) N)).ae hA
  have hBprod := (Measure.quasiMeasurePreserving_snd
    (μ := standardRealGaussianMatrixMeasure (N + 1) N)
    (ν := standardRealGaussianMatrixMeasure (K - N) N)).ae hB
  simpa [realBetaPrimeGaussianSourceLaw] using hAprod.and hBprod

/-- The symmetric-congruence representative attached to a proposed symmetric
square root `S` of a positive definite denominator and a numerator `A`. -/
def wishartSymmetricConjugate
    {n : Type*} [Fintype n] [DecidableEq n]
    (S A : Matrix n n ℝ) : Matrix n n ℝ :=
  S⁻¹ * A * S⁻¹

/-- A symmetric numerator and symmetric square-root factor give a symmetric
congruence representative. -/
theorem wishartSymmetricConjugate_isSymm
    {n : Type*} [Fintype n] [DecidableEq n]
    {S A : Matrix n n ℝ} (hS : S.IsSymm) (hA : A.IsSymm) :
    (wishartSymmetricConjugate S A).IsSymm := by
  unfold wishartSymmetricConjugate Matrix.IsSymm
  rw [Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_nonsing_inv, hS.eq, hA.eq]
  simp only [Matrix.mul_assoc]

/-- Positive semidefiniteness is preserved by the inverse congruence. -/
theorem wishartSymmetricConjugate_posSemidef
    {n : Type*} [Fintype n] [DecidableEq n]
    {S A : Matrix n n ℝ} (hS : S.IsSymm) (hA : A.PosSemidef) :
    (wishartSymmetricConjugate S A).PosSemidef := by
  simpa [wishartSymmetricConjugate,
    Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.transpose_nonsing_inv, hS.eq] using
    hA.mul_mul_conjTranspose_same S⁻¹

/-- Conjugation by a nonsingular matrix commutes with every natural power. -/
theorem inverse_conjugate_pow
    {n : Type*} [Fintype n] [DecidableEq n]
    (S X : Matrix n n ℝ) (m : ℕ) (hS : IsUnit S.det) :
    (S⁻¹ * X * S) ^ m = S⁻¹ * X ^ m * S := by
  have hconj : SemiconjBy S (S⁻¹ * X * S) X := by
    unfold SemiconjBy
    calc
      S * (S⁻¹ * X * S) = (S * S⁻¹) * X * S := by
        simp only [Matrix.mul_assoc]
      _ = X * S := by rw [Matrix.mul_nonsing_inv S hS, one_mul]
  have hpow := hconj.pow_right m
  calc
    (S⁻¹ * X * S) ^ m =
        S⁻¹ * (S * (S⁻¹ * X * S) ^ m) := by
          rw [Matrix.nonsing_inv_mul_cancel_left S _ hS]
    _ = S⁻¹ * (X ^ m * S) := by rw [hpow.eq]
    _ = S⁻¹ * X ^ m * S := by rw [Matrix.mul_assoc]

/-- Trace is invariant under an arbitrary nonsingular similarity, uniformly
over every natural power. -/
theorem trace_inverse_conjugate_pow
    {n : Type*} [Fintype n] [DecidableEq n]
    (S X : Matrix n n ℝ) (m : ℕ) (hS : IsUnit S.det) :
    Matrix.trace ((S⁻¹ * X * S) ^ m) = Matrix.trace (X ^ m) := by
  rw [inverse_conjugate_pow S X m hS]
  calc
    Matrix.trace (S⁻¹ * X ^ m * S) =
        Matrix.trace (S * (S⁻¹ * X ^ m)) := by
      rw [Matrix.trace_mul_cycle]
      congr 1
      noncomm_ring
    _ = Matrix.trace ((S * S⁻¹) * X ^ m) := by
      congr 1
      noncomm_ring
    _ = Matrix.trace (X ^ m) := by
      rw [Matrix.mul_nonsing_inv S hS, one_mul]

/-- If `B = S*S`, then `B⁻¹ A` is similar to the inverse congruence
`S⁻¹ A S⁻¹`. -/
theorem inverse_mul_eq_inverse_conjugate_of_square
    {n : Type*} [Fintype n] [DecidableEq n]
    {S A B : Matrix n n ℝ} (hS : IsUnit S.det) (hB : B = S * S) :
    B⁻¹ * A = S⁻¹ * wishartSymmetricConjugate S A * S := by
  subst B
  rw [Matrix.mul_inv_rev]
  unfold wishartSymmetricConjugate
  simp only [Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul S hS]
  simp

/-- Pointwise factorization of every trace power through the symmetric
congruence representative. -/
theorem inverse_mul_pow_factorization_of_square
    {n : Type*} [Fintype n] [DecidableEq n]
    {S A B : Matrix n n ℝ} (hS : IsUnit S.det) (hB : B = S * S)
    (m : ℕ) :
    (B⁻¹ * A) ^ m =
      S⁻¹ * (wishartSymmetricConjugate S A) ^ m * S := by
  rw [inverse_mul_eq_inverse_conjugate_of_square hS hB]
  exact inverse_conjugate_pow S (wishartSymmetricConjugate S A) m hS

/-- Cyclicity of trace removes the similarity factors from every power. -/
theorem trace_inverse_mul_pow_eq_trace_symmetricConjugate_pow_of_square
    {n : Type*} [Fintype n] [DecidableEq n]
    {S A B : Matrix n n ℝ} (hS : IsUnit S.det) (hB : B = S * S)
    (m : ℕ) :
    Matrix.trace ((B⁻¹ * A) ^ m) =
      Matrix.trace ((wishartSymmetricConjugate S A) ^ m) := by
  rw [inverse_mul_pow_factorization_of_square hS hB]
  rw [Matrix.trace_mul_cycle]
  rw [Matrix.mul_nonsing_inv S hS, one_mul]

/-- Exact source-level power factorization for the literal matrix beta-prime
random variable, conditional only on a supplied nonsingular square-root
factor of its denominator. -/
theorem realMatrixBetaPrimeOfGaussianSource_pow_factorization
    {N K : ℕ}
    (p : Matrix (Fin (N + 1)) (Fin N) ℝ ×
      Matrix (Fin (K - N)) (Fin N) ℝ)
    (S : Matrix (Fin N) (Fin N) ℝ)
    (hS : IsUnit S.det) (hroot : realWishartGram p.2 = S * S)
    (m : ℕ) :
    (realMatrixBetaPrimeOfGaussianSource p) ^ m =
      S⁻¹ *
        (wishartSymmetricConjugate S (realWishartGram p.1)) ^ m * S := by
  exact inverse_mul_pow_factorization_of_square hS hroot m

/-- The complete finite trace-power vector equals that of the symmetric
congruence representative, under the same square-root contract. -/
theorem realBetaPrimeTracePowerVector_eq_symmetricConjugate
    {r N K : ℕ}
    (p : Matrix (Fin (N + 1)) (Fin N) ℝ ×
      Matrix (Fin (K - N)) (Fin N) ℝ)
    (S : Matrix (Fin N) (Fin N) ℝ)
    (hS : IsUnit S.det) (hroot : realWishartGram p.2 = S * S) :
    realBetaPrimeTracePowerVector r N K p =
      fun j ↦ Matrix.trace
        ((wishartSymmetricConjugate S (realWishartGram p.1)) ^
          (j.1 + 1)) := by
  funext j
  unfold realBetaPrimeTracePowerVector
  exact trace_inverse_mul_pow_eq_trace_symmetricConjugate_pow_of_square
    hS hroot (j.1 + 1)

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
