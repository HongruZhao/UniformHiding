import A3.HermitianCoordinates
import A3.Shared.SpectrumMeasurable
import A3.Shared.SpectrumPermutation

open scoped BigOperators
open Matrix MeasureTheory

noncomputable section
namespace A3Research

set_option maxHeartbeats 1000000

variable {n : ℕ} {K : Type*} [RCLike K]

theorem hermitian_eigenvalues_congr {A B : Matrix (Fin n) (Fin n) K}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (h : A = B) :
    hA.eigenvalues = hB.eigenvalues := by
  subst B
  rfl

/-- The actual Mathlib Hermitian spectrum of the literal independent coordinates. -/
def canonicalHermitianSpectrum (x : HermitianCoordinates n K) : Fin n → ℝ :=
  (hermitianMatrixOfCoordinates_isHermitian x).eigenvalues

theorem measurable_canonicalHermitianSpectrum
    [MeasurableSpace K] [BorelSpace K] [PolishSpace K] :
    Measurable (canonicalHermitianSpectrum : HermitianCoordinates n K → Fin n → ℝ) :=
  measurable_hermitian_eigenvalues hermitianMatrixOfCoordinates
    hermitianMatrixOfCoordinates_isHermitian continuous_hermitianMatrixOfCoordinates.measurable

/-- Every supplied unitary diagonalization gives the same finite spectrum up to permutation. -/
theorem canonicalHermitianSpectrum_permutation_of_diagonalization
    (x : HermitianCoordinates n K) (U : Matrix.unitaryGroup (Fin n) K)
    (lambda : Fin n → ℝ)
    (hx : hermitianMatrixOfCoordinates x = (U : Matrix (Fin n) (Fin n) K) *
      Matrix.diagonal (RCLike.ofReal ∘ lambda) * star (U : Matrix (Fin n) (Fin n) K)) :
    ∃ sigma : Equiv.Perm (Fin n), canonicalHermitianSpectrum x = lambda ∘ sigma :=
  eigenvalues_permutation_of_unitary_diagonalization
    (hermitianMatrixOfCoordinates_isHermitian x) U lambda hx

theorem canonicalHermitianSpectrum_projection
    (H : Matrix (Fin n) (Fin n) K) (hH : H.IsHermitian) :
    canonicalHermitianSpectrum (hermitianCoordinateProjection H) = hH.eigenvalues := by
  exact hermitian_eigenvalues_congr
    (hermitianMatrixOfCoordinates_isHermitian (hermitianCoordinateProjection H)) hH
    (hermitianMatrixOfCoordinates_projection H hH)

end A3Research
