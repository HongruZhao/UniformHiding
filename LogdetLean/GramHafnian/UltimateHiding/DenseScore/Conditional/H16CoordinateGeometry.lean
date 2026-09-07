import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ClassicalCOEExternal
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Congruence
import LogdetLean.GramHafnian.UltimateHiding.Dense.RadialConcrete
import Mathlib.LinearAlgebra.Determinant
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-!
# Upper-triangular coordinates for the H16 centered flow

This file isolates the finite-dimensional coordinate geometry needed by the
event-free H16 transport route.  It does not import the conditional H16
endpoint and does not use any density, moment, score, event-derivative, or
hiding axiom.

The full symmetric matrix reconstructed by
`complexSymmetricMatrixOfCoordinates` is identified exactly with its
independent upper-triangular coordinates.  Transpose-congruence is then
transported to a complex-linear coordinate equivalence.  Its inverse is the
same exponential flow at time `-t`.
-/

open MeasureTheory NormedSpace

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-! ## Exact extraction/reconstruction -/

/-- Extract the independent upper-triangular entries of a square matrix. -/
def complexSymmetricCoordinatesOfMatrix {N : ℕ}
    (C : ConcreteMatrixState N) : ComplexSymmetricCoordinates N :=
  fun ij ↦ C ij.1.1 ij.1.2

@[simp]
theorem complexSymmetricCoordinatesOfMatrix_apply {N : ℕ}
    (C : ConcreteMatrixState N) (ij : ComplexSymmetricCoordinateIndex N) :
    complexSymmetricCoordinatesOfMatrix C ij = C ij.1.1 ij.1.2 :=
  rfl

/-- Extracting after symmetric reconstruction is exactly the identity. -/
@[simp]
theorem complexSymmetricCoordinatesOfMatrix_matrixOfCoordinates
    {N : ℕ} (x : ComplexSymmetricCoordinates N) :
    complexSymmetricCoordinatesOfMatrix
        (complexSymmetricMatrixOfCoordinates x) = x := by
  funext ij
  simp [complexSymmetricCoordinatesOfMatrix,
    complexSymmetricMatrixOfCoordinates, ij.2]

/-- Reconstructing after extraction recovers every complex-symmetric matrix. -/
theorem complexSymmetricMatrixOfCoordinates_coordinatesOfMatrix
    {N : ℕ} (C : ConcreteMatrixState N) (hC : C.IsSymm) :
    complexSymmetricMatrixOfCoordinates
        (complexSymmetricCoordinatesOfMatrix C) = C := by
  ext i j
  simp only [complexSymmetricMatrixOfCoordinates,
    complexSymmetricCoordinatesOfMatrix]
  by_cases hij : i ≤ j
  · simp [hij]
  · simp [hij, hC.apply i j]

theorem complexSymmetricCoordinatesOfMatrix_add
    {N : ℕ} (C D : ConcreteMatrixState N) :
    complexSymmetricCoordinatesOfMatrix (C + D) =
      complexSymmetricCoordinatesOfMatrix C +
        complexSymmetricCoordinatesOfMatrix D := by
  rfl

theorem complexSymmetricCoordinatesOfMatrix_smul
    {N : ℕ} (z : ℂ) (C : ConcreteMatrixState N) :
    complexSymmetricCoordinatesOfMatrix (z • C) =
      z • complexSymmetricCoordinatesOfMatrix C := by
  rfl

theorem measurable_complexSymmetricCoordinatesOfMatrix (N : ℕ) :
    Measurable (complexSymmetricCoordinatesOfMatrix (N := N)) := by
  refine measurable_pi_lambda _ fun ij ↦ ?_
  exact (measurable_pi_apply ij.1.2).comp (measurable_pi_apply ij.1.1)

theorem complexSymmetricMatrixOfCoordinates_add
    {N : ℕ} (x y : ComplexSymmetricCoordinates N) :
    complexSymmetricMatrixOfCoordinates (x + y) =
      complexSymmetricMatrixOfCoordinates x +
        complexSymmetricMatrixOfCoordinates y := by
  ext i j
  simp only [complexSymmetricMatrixOfCoordinates, Pi.add_apply, Matrix.add_apply]
  split_ifs <;> rfl

theorem complexSymmetricMatrixOfCoordinates_smul
    {N : ℕ} (z : ℂ) (x : ComplexSymmetricCoordinates N) :
    complexSymmetricMatrixOfCoordinates (z • x) =
      z • complexSymmetricMatrixOfCoordinates x := by
  ext i j
  simp only [complexSymmetricMatrixOfCoordinates, Pi.smul_apply, Matrix.smul_apply]
  split_ifs <;> rfl

/-! ## The induced complex-linear flow on independent coordinates -/

/-- Transpose-congruence transported to the independent symmetric
coordinates.  The surrounding reconstruction makes the definition meaningful
on the full coordinate space, while symmetry preservation makes it closed. -/
def transposeCongruenceFlowCoordinates {N : ℕ}
    (A : ConcreteMatrixState N) (t : ℝ)
    (x : ComplexSymmetricCoordinates N) : ComplexSymmetricCoordinates N :=
  complexSymmetricCoordinatesOfMatrix <|
    transposeCongruenceFlow A t (complexSymmetricMatrixOfCoordinates x)

theorem transposeCongruenceFlowCoordinates_matrix
    {N : ℕ} (A : ConcreteMatrixState N) (t : ℝ)
    (x : ComplexSymmetricCoordinates N) :
    complexSymmetricMatrixOfCoordinates
        (transposeCongruenceFlowCoordinates A t x) =
      transposeCongruenceFlow A t
        (complexSymmetricMatrixOfCoordinates x) := by
  apply complexSymmetricMatrixOfCoordinates_coordinatesOfMatrix
  exact transposeCongruence_isSymm _
    (complexSymmetricMatrixOfCoordinates_isSymm x)

@[simp]
theorem transposeCongruenceFlowCoordinates_zero
    {N : ℕ} (A : ConcreteMatrixState N)
    (x : ComplexSymmetricCoordinates N) :
    transposeCongruenceFlowCoordinates A 0 x = x := by
  simp [transposeCongruenceFlowCoordinates]

theorem transposeCongruenceFlowCoordinates_add_time
    {N : ℕ} (A : ConcreteMatrixState N) (s t : ℝ)
    (x : ComplexSymmetricCoordinates N) :
    transposeCongruenceFlowCoordinates A (s + t) x =
      transposeCongruenceFlowCoordinates A s
        (transposeCongruenceFlowCoordinates A t x) := by
  apply congrArg complexSymmetricCoordinatesOfMatrix
  rw [transposeCongruenceFlowCoordinates_matrix]
  simp only [transposeCongruenceFlowCoordinates,
    transposeCongruenceFlow_add]

@[simp]
theorem transposeCongruenceFlowCoordinates_neg_left
    {N : ℕ} (A : ConcreteMatrixState N) (t : ℝ)
    (x : ComplexSymmetricCoordinates N) :
    transposeCongruenceFlowCoordinates A (-t)
        (transposeCongruenceFlowCoordinates A t x) = x := by
  rw [← transposeCongruenceFlowCoordinates_add_time]
  simp

@[simp]
theorem transposeCongruenceFlowCoordinates_neg_right
    {N : ℕ} (A : ConcreteMatrixState N) (t : ℝ)
    (x : ComplexSymmetricCoordinates N) :
    transposeCongruenceFlowCoordinates A t
        (transposeCongruenceFlowCoordinates A (-t) x) = x := by
  rw [← transposeCongruenceFlowCoordinates_add_time]
  simp

theorem transposeCongruenceFlowCoordinates_add
    {N : ℕ} (A : ConcreteMatrixState N) (t : ℝ)
    (x y : ComplexSymmetricCoordinates N) :
    transposeCongruenceFlowCoordinates A t (x + y) =
      transposeCongruenceFlowCoordinates A t x +
        transposeCongruenceFlowCoordinates A t y := by
  unfold transposeCongruenceFlowCoordinates transposeCongruenceFlow
  rw [show complexSymmetricMatrixOfCoordinates (x + y) =
      complexSymmetricMatrixOfCoordinates x +
        complexSymmetricMatrixOfCoordinates y by
      exact complexSymmetricMatrixOfCoordinates_add x y]
  rw [transposeCongruence_add]
  exact complexSymmetricCoordinatesOfMatrix_add _ _

theorem transposeCongruenceFlowCoordinates_smul
    {N : ℕ} (A : ConcreteMatrixState N) (t : ℝ) (z : ℂ)
    (x : ComplexSymmetricCoordinates N) :
    transposeCongruenceFlowCoordinates A t (z • x) =
      z • transposeCongruenceFlowCoordinates A t x := by
  unfold transposeCongruenceFlowCoordinates transposeCongruenceFlow
  rw [show complexSymmetricMatrixOfCoordinates (z • x) =
      z • complexSymmetricMatrixOfCoordinates x by
      exact complexSymmetricMatrixOfCoordinates_smul z x]
  rw [transposeCongruence_smul]
  exact complexSymmetricCoordinatesOfMatrix_smul _ _

/-- The induced coordinate flow as a complex-linear equivalence. -/
def transposeCongruenceFlowCoordinateLinearEquiv {N : ℕ}
    (A : ConcreteMatrixState N) (t : ℝ) :
    ComplexSymmetricCoordinates N ≃ₗ[ℂ] ComplexSymmetricCoordinates N where
  toFun := transposeCongruenceFlowCoordinates A t
  invFun := transposeCongruenceFlowCoordinates A (-t)
  left_inv := transposeCongruenceFlowCoordinates_neg_left A t
  right_inv := transposeCongruenceFlowCoordinates_neg_right A t
  map_add' := transposeCongruenceFlowCoordinates_add A t
  map_smul' := transposeCongruenceFlowCoordinates_smul A t

@[simp]
theorem transposeCongruenceFlowCoordinateLinearEquiv_apply
    {N : ℕ} (A : ConcreteMatrixState N) (t : ℝ)
    (x : ComplexSymmetricCoordinates N) :
    transposeCongruenceFlowCoordinateLinearEquiv A t x =
      transposeCongruenceFlowCoordinates A t x :=
  rfl

@[simp]
theorem transposeCongruenceFlowCoordinateLinearEquiv_symm_apply
    {N : ℕ} (A : ConcreteMatrixState N) (t : ℝ)
    (x : ComplexSymmetricCoordinates N) :
    (transposeCongruenceFlowCoordinateLinearEquiv A t).symm x =
      transposeCongruenceFlowCoordinates A (-t) x :=
  rfl

/-- The inverse coordinate linear equivalence is literally time `-t`. -/
theorem transposeCongruenceFlowCoordinateLinearEquiv_symm
    {N : ℕ} (A : ConcreteMatrixState N) (t : ℝ) :
    (transposeCongruenceFlowCoordinateLinearEquiv A t).symm =
      transposeCongruenceFlowCoordinateLinearEquiv A (-t) := by
  ext x
  rfl

/-- The centered orbital flow is the same exact coordinate equivalence,
specialized to the traceless rank-one direction. -/
abbrev centeredTransposeCongruenceFlowCoordinateLinearEquiv {N : ℕ}
    (v : ComplexUnitSphere N) (t : ℝ) :
    ComplexSymmetricCoordinates N ≃ₗ[ℂ] ComplexSymmetricCoordinates N :=
  transposeCongruenceFlowCoordinateLinearEquiv
    (concreteCenteredOrbitalDirection N v) t

@[simp]
theorem centeredTransposeCongruenceFlowCoordinateLinearEquiv_symm
    {N : ℕ} (v : ComplexUnitSphere N) (t : ℝ) :
    (centeredTransposeCongruenceFlowCoordinateLinearEquiv v t).symm =
      centeredTransposeCongruenceFlowCoordinateLinearEquiv v (-t) := by
  exact transposeCongruenceFlowCoordinateLinearEquiv_symm _ _

/-! ## Determinant identities forced by the inverse flow -/

/-- The coordinate determinant is nonzero because the induced flow is a
linear equivalence. -/
theorem transposeCongruenceFlowCoordinate_det_ne_zero
    {N : ℕ} (A : ConcreteMatrixState N) (t : ℝ) :
    LinearMap.det
        (transposeCongruenceFlowCoordinateLinearEquiv A t).toLinearMap ≠ 0 := by
  exact (LinearEquiv.isUnit_det'
    (transposeCongruenceFlowCoordinateLinearEquiv A t)).ne_zero

/-- Forward and backward complex Jacobians are exact reciprocals. -/
theorem transposeCongruenceFlowCoordinate_det_mul_neg
    {N : ℕ} (A : ConcreteMatrixState N) (t : ℝ) :
    LinearMap.det
          (transposeCongruenceFlowCoordinateLinearEquiv A t).toLinearMap *
        LinearMap.det
          (transposeCongruenceFlowCoordinateLinearEquiv A (-t)).toLinearMap = 1 := by
  rw [← LinearMap.det_comp]
  have hcomp :
      (transposeCongruenceFlowCoordinateLinearEquiv A t).toLinearMap.comp
          (transposeCongruenceFlowCoordinateLinearEquiv A (-t)).toLinearMap =
        LinearMap.id := by
    ext x
    simp
  rw [hcomp, LinearMap.det_id]

/-- Hence the backward complex Jacobian is the inverse of the forward one. -/
theorem transposeCongruenceFlowCoordinate_det_neg
    {N : ℕ} (A : ConcreteMatrixState N) (t : ℝ) :
    LinearMap.det
        (transposeCongruenceFlowCoordinateLinearEquiv A (-t)).toLinearMap =
      (LinearMap.det
        (transposeCongruenceFlowCoordinateLinearEquiv A t).toLinearMap)⁻¹ := by
  exact ((mul_eq_one_iff_inv_eq₀
    (transposeCongruenceFlowCoordinate_det_ne_zero A t)).mp
      (transposeCongruenceFlowCoordinate_det_mul_neg A t)).symm

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
