import AllFourIntegration.ProviderBase

open scoped BigOperators ENNReal ComplexConjugate ComplexOrder MatrixOrder
open Set MeasureTheory
noncomputable section
namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore
open LogdetLean.GramHafnian.UltimateHiding.Dense
open H6CoordinateAlgebra H6DensityTransform

/-- Flat measure on the embedded space of complex symmetric matrices, using
exactly the independent upper-triangular coordinate convention of H5. -/
def complexSymmetricMatrixVolume (N : ℕ) : Measure (ConcreteMatrixState N) :=
  Measure.map (complexSymmetricMatrixOfCoordinates (N := N))
    (complexSymmetricCoordinateVolume N)

/-- Flat squared-Takagi density.  Its only coordinate factor is the absolute
Vandermonde of power one; there is no `lambda_i` power. -/
def takagiFlatEigenvalueDensity (N : ℕ) (lambda : Fin N → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (vandermondeAbs N lambda)

/-- Unnormalized flat squared-Takagi radial measure on the full unordered
positive orthant. -/
def takagiFlatEigenvalueRadialMeasure (N : ℕ) : Measure (Fin N → ℝ) :=
  (volume.restrict (openPositiveOrthant N)).withDensity
    (takagiFlatEigenvalueDensity N)

/-- The Hermitian right gap attached to an arbitrary complex matrix. -/
def coeHermitianGap {N : ℕ} (C : ConcreteMatrixState N) :
    ConcreteMatrixState N :=
  1 - C.conjTranspose * C

theorem coeHermitianGap_isHermitian {N : ℕ}
    (C : ConcreteMatrixState N) : (coeHermitianGap C).IsHermitian := by
  exact Matrix.isHermitian_one.sub
    (Matrix.isHermitian_conjTranspose_mul_self C)

/-- Canonical squared-singular-value statistic, without any Takagi vectors:
`lambda_i = 1 - eigenvalue_i(I - Cᴴ C)`. -/
def canonicalGapSquaredSpectrum (N : ℕ)
    (C : ConcreteMatrixState N) : Fin N → ℝ :=
  fun i ↦ 1 - (coeHermitianGap_isHermitian C).eigenvalues i


end LogdetLean.GramHafnian.UltimateHiding.DenseScore
