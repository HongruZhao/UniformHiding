import A2.Definitions
import A2.PolynomialNullity

open MeasureTheory Matrix
open LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

namespace A2Research

/-- The literal independent symmetric coordinates, regarded as indeterminates. -/
def symmetricCoordinatePolynomialMatrix (N : ℕ) :
    Matrix (Fin N) (Fin N) (MvPolynomial (ComplexSymmetricCoordinateIndex N) ℂ) :=
  fun i j ↦ if h : i ≤ j then MvPolynomial.X ⟨(i, j), h⟩
    else MvPolynomial.X ⟨(j, i), le_of_lt (lt_of_not_ge h)⟩

theorem eval_symmetricCoordinatePolynomialMatrix (N : ℕ)
    (x : ComplexSymmetricCoordinates N) :
    (MvPolynomial.eval x).mapMatrix (symmetricCoordinatePolynomialMatrix N) =
      complexSymmetricMatrixOfCoordinates x := by
  ext i j
  by_cases hij : i ≤ j <;>
    simp [symmetricCoordinatePolynomialMatrix, complexSymmetricMatrixOfCoordinates, hij]

theorem eval_det_symmetricCoordinatePolynomialMatrix (N : ℕ)
    (x : ComplexSymmetricCoordinates N) :
    MvPolynomial.eval x (symmetricCoordinatePolynomialMatrix N).det =
      (complexSymmetricMatrixOfCoordinates x).det := by
  rw [RingHom.map_det, eval_symmetricCoordinatePolynomialMatrix]

theorem det_symmetricCoordinatePolynomialMatrix_ne_zero (N : ℕ) :
    (symmetricCoordinatePolynomialMatrix N).det ≠ 0 := by
  let x : ComplexSymmetricCoordinates N := fun ij ↦ if ij.1.1 = ij.1.2 then 1 else 0
  have hx : complexSymmetricMatrixOfCoordinates x = 1 := by
    ext i j
    by_cases hij : i ≤ j <;> by_cases heq : i = j <;>
      simp [x, complexSymmetricMatrixOfCoordinates, hij, heq, eq_comm, Matrix.one_apply]
  intro h
  have heval := congrArg (MvPolynomial.eval x) h
  rw [eval_det_symmetricCoordinatePolynomialMatrix, hx, Matrix.det_one, map_zero] at heval
  exact one_ne_zero heval

/-- A symmetric complex matrix is nonsingular almost everywhere for the exact
coordinate volume used in A2. -/
theorem ae_det_ne_zero_complexSymmetricCoordinateVolume (N : ℕ) :
    ∀ᵐ x ∂(complexSymmetricCoordinateVolume N),
      (complexSymmetricMatrixOfCoordinates x).det ≠ 0 := by
  have h := ae_mvPolynomial_eval_ne_zero (volume : Measure ℂ)
    (symmetricCoordinatePolynomialMatrix N).det
    (det_symmetricCoordinatePolynomialMatrix_ne_zero N)
  simpa only [complexSymmetricCoordinateVolume,
    eval_det_symmetricCoordinatePolynomialMatrix] using h

/-- The singular part of the actual flat complex-symmetric matrix measure is null. -/
theorem ae_det_ne_zero_complexSymmetricMatrixVolume (N : ℕ) :
    ∀ᵐ C ∂(complexSymmetricMatrixVolume N), C.det ≠ 0 := by
  rw [complexSymmetricMatrixVolume]
  have hdet : Measurable (fun C : Matrix (Fin N) (Fin N) ℂ ↦ C.det) :=
    (show Continuous (fun C : Matrix (Fin N) (Fin N) ℂ ↦ C.det) from
      continuous_id.matrix_det).measurable
  have hset : MeasurableSet {C : Matrix (Fin N) (Fin N) ℂ | C.det ≠ 0} := by
    simpa only [Set.compl_setOf] using
      (hdet.eq_const (0 : ℂ)).setOf.compl
  exact (ae_map_iff (measurable_complexSymmetricMatrixOfCoordinates N).aemeasurable hset).mpr
    (ae_det_ne_zero_complexSymmetricCoordinateVolume N)

end A2Research
