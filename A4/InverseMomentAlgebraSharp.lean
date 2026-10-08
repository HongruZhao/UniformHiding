import A4.InverseMomentAlgebra
import A4.MatchingGramExpansion

/-!
# Exact inverse coefficients throughout the sharp real parameter range

The determinant conditions in the elementary inverse identities are now
discharged by the unconditional signed feature expansion.  No moment or
Stein identity is assumed in these finite Gram inverse identities.
-/

open scoped BigOperators Matrix

noncomputable section

namespace MatsumotoPaper

private abbrev PM (n : ℕ) := A4Standalone.GramHafnian.PerfectMatching n

theorem orthogonalGram_det_ne_zero_negative {n : ℕ} (gamma : ℝ)
    (hgamma : (n : ℝ) - 1 < gamma) :
    (orthogonalGram n (-2 * (gamma : ℂ))).det ≠ 0 :=
  isUnit_iff_ne_zero.mp (orthogonalGram_isUnit_det_negative gamma hgamma)

theorem normalizedOrthogonalGram_mul_modified_of_gamma_gt {n : ℕ} (gamma : ℝ)
    (hgamma : (n : ℝ) - 1 < gamma) :
    normalizedOrthogonalGram n gamma * modifiedGramInverse n gamma = 1 :=
  normalizedOrthogonalGram_mul_modified gamma (orthogonalGram_isUnit_det_negative gamma hgamma)

theorem modified_mul_normalizedOrthogonalGram_of_gamma_gt {n : ℕ} (gamma : ℝ)
    (hgamma : (n : ℝ) - 1 < gamma) :
    modifiedGramInverse n gamma * normalizedOrthogonalGram n gamma = 1 :=
  modified_mul_normalizedOrthogonalGram gamma (orthogonalGram_isUnit_det_negative gamma hgamma)

theorem normalizedOrthogonalGram_isUnit_det {n : ℕ} (gamma : ℝ)
    (hgamma : (n : ℝ) - 1 < gamma) : IsUnit (normalizedOrthogonalGram n gamma).det :=
  Matrix.isUnit_det_of_right_inverse (normalizedOrthogonalGram_mul_modified_of_gamma_gt gamma hgamma)

theorem normalizedOrthogonalGram_det_ne_zero {n : ℕ} (gamma : ℝ)
    (hgamma : (n : ℝ) - 1 < gamma) : (normalizedOrthogonalGram n gamma).det ≠ 0 :=
  isUnit_iff_ne_zero.mp (normalizedOrthogonalGram_isUnit_det gamma hgamma)

theorem wgTilde_matching_convolution_of_gamma_gt {n : ℕ} (gamma : ℝ)
    (hgamma : (n : ℝ) - 1 < gamma) (g h : Equiv.Perm (Fin (2 * n))) :
    ∑ M : PerfectMatching n,
      (((-2 : ℂ) ^ n)⁻¹ * (-2 * (gamma : ℂ)) ^ kappa (g⁻¹ * M.toPerm)) *
        wgTilde (M.toPerm⁻¹ * h) gamma =
      if transportedPairPartition g = transportedPairPartition h then 1 else 0 :=
  wgTilde_matching_convolution gamma (orthogonalGram_isUnit_det_negative gamma hgamma) g h

theorem normalizedMatchingSystem_solution {n : ℕ} (gamma : ℝ)
    (hgamma : (n : ℝ) - 1 < gamma) (x rhs : PM n → ℂ)
    (hrec : ∀ P : PM n,
      (∑ Q : PM n, normalizedOrthogonalGram n gamma P Q * x Q) = rhs P) :
    x = modifiedGramInverse n gamma *ᵥ rhs := by
  classical
  have hvec : normalizedOrthogonalGram n gamma *ᵥ x = rhs := funext hrec
  calc
    x = (1 : Matrix (PM n) (PM n) ℂ) *ᵥ x := (Matrix.one_mulVec x).symm
    _ = (modifiedGramInverse n gamma * normalizedOrthogonalGram n gamma) *ᵥ x := by
      rw [modified_mul_normalizedOrthogonalGram_of_gamma_gt gamma hgamma]
    _ = _ := by rw [← Matrix.mulVec_mulVec, hvec]

theorem normalizedMatchingSystem_unique {n : ℕ} (gamma : ℝ)
    (hgamma : (n : ℝ) - 1 < gamma) (x y rhs : PM n → ℂ)
    (hx : ∀ P : PM n,
      (∑ Q : PM n, normalizedOrthogonalGram n gamma P Q * x Q) = rhs P)
    (hy : ∀ P : PM n,
      (∑ Q : PM n, normalizedOrthogonalGram n gamma P Q * y Q) = rhs P) : x = y := by
  rw [normalizedMatchingSystem_solution gamma hgamma x rhs hx,
    normalizedMatchingSystem_solution gamma hgamma y rhs hy]

end MatsumotoPaper
