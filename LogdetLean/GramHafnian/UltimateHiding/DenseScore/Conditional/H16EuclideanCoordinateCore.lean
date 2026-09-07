import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16DeterminantJetAlgebra
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Euclidean coordinates for the active H16 boundary argument

This module contains only the finite-dimensional coordinate identification,
determinant gap, and positive-definite support used by the internally proved
A1 route.  It is separated from the alternative A5/A6 coarea and
Gauss--Green interfaces, so those literature atoms are not physical
dependencies of the uniformly-hiding endpoint.
-/

open MeasureTheory Set

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- Real dimension of the independent complex-symmetric coordinate space. -/
abbrev H16CoordinateRealDimension (N : ℕ) : ℕ :=
  Module.finrank ℝ (ComplexSymmetricCoordinates N)

/-- Literal Euclidean carrier used for the finite-dimensional boundary
argument. -/
abbrev H16EuclideanCoordinateSpace (N : ℕ) :=
  EuclideanSpace ℝ (Fin (H16CoordinateRealDimension N))

/-- Continuous real-linear coordinates on the independent symmetric matrix
entries. -/
noncomputable def h16CoordinateEuclideanEquiv (N : ℕ) :
    ComplexSymmetricCoordinates N ≃L[ℝ] H16EuclideanCoordinateSpace N :=
  (Module.finBasis ℝ (ComplexSymmetricCoordinates N)).equivFun.toContinuousLinearEquiv |>.trans
    (PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : Fin (H16CoordinateRealDimension N) ↦ ℝ)).symm

/-- Determinant gap in Euclidean coordinates. -/
def h16EucGap (N : ℕ) (y : H16EuclideanCoordinateSpace N) : ℝ :=
  h16COECoordinateGapDeterminant N
    ((h16CoordinateEuclideanEquiv N).symm y)

theorem continuous_h16EucGap (N : ℕ) :
    Continuous (h16EucGap N) := by
  unfold h16EucGap h16COECoordinateGapDeterminant
  fun_prop

/-- Positive-definite COE support in Euclidean coordinates. -/
def h16EucSupport (N : ℕ) : Set (H16EuclideanCoordinateSpace N) :=
  {y | coeCornerSupport <|
    complexSymmetricMatrixOfCoordinates
      ((h16CoordinateEuclideanEquiv N).symm y)}

theorem measurableSet_h16EucSupport (N : ℕ) :
    MeasurableSet (h16EucSupport N) := by
  exact (measurableSet_coeCornerSupport N).preimage
    ((measurable_complexSymmetricMatrixOfCoordinates N).comp
      (h16CoordinateEuclideanEquiv N).symm.continuous.measurable)

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
