import A2.CompactDeterminant

open scoped ComplexConjugate
open Matrix
open LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

namespace A2Research

def symmetricCoordinateEmbedding (N : ℕ) :
    ComplexSymmetricCoordinates N →ₗ[ℂ] Matrix (Fin N) (Fin N) ℂ where
  toFun := complexSymmetricMatrixOfCoordinates
  map_add' x y := by
    ext i j
    by_cases hij : i ≤ j <;> simp [complexSymmetricMatrixOfCoordinates, hij]
  map_smul' a x := by
    ext i j
    by_cases hij : i ≤ j <;> simp [complexSymmetricMatrixOfCoordinates, hij]

def symmetricCoordinateProjection (N : ℕ) :
    Matrix (Fin N) (Fin N) ℂ →ₗ[ℂ] ComplexSymmetricCoordinates N where
  toFun C ij := C ij.1.1 ij.1.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem symmetricCoordinateProjection_embedding (N : ℕ)
    (x : ComplexSymmetricCoordinates N) :
    symmetricCoordinateProjection N (symmetricCoordinateEmbedding N x) = x := by
  funext ij
  change complexSymmetricMatrixOfCoordinates x ij.1.1 ij.1.2 = x ij
  simp only [complexSymmetricMatrixOfCoordinates, dif_pos ij.property]

theorem symmetricCoordinateEmbedding_projection {N : ℕ}
    (C : Matrix (Fin N) (Fin N) ℂ) (hC : C.IsSymm) :
    symmetricCoordinateEmbedding N (symmetricCoordinateProjection N C) = C := by
  ext i j
  change complexSymmetricMatrixOfCoordinates (fun ij ↦ C ij.1.1 ij.1.2) i j = C i j
  by_cases hij : i ≤ j
  · simp [symmetricCoordinateEmbedding, symmetricCoordinateProjection,
      complexSymmetricMatrixOfCoordinates, hij]
  · simpa [symmetricCoordinateEmbedding, symmetricCoordinateProjection,
      complexSymmetricMatrixOfCoordinates, hij] using hC.apply i j

def matrixCongruenceLinearMap {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin N) (Fin N) ℂ →ₗ[ℂ] Matrix (Fin N) (Fin N) ℂ where
  toFun C := U * C * U.transpose
  map_add' x y := by simp only [mul_add, add_mul]
  map_smul' a x := by simp [Matrix.mul_smul, Matrix.smul_mul]

theorem isSymm_matrixCongruence {N : ℕ} (U C : Matrix (Fin N) (Fin N) ℂ)
    (hC : C.IsSymm) : (U * C * U.transpose).IsSymm := by
  unfold Matrix.IsSymm at hC ⊢
  rw [transpose_mul, transpose_mul, transpose_transpose, hC, mul_assoc]

def symmetricCongruenceLinearMap {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ) :
    ComplexSymmetricCoordinates N →ₗ[ℂ] ComplexSymmetricCoordinates N :=
  (symmetricCoordinateProjection N).comp
    ((matrixCongruenceLinearMap U).comp (symmetricCoordinateEmbedding N))

theorem symmetricCoordinateEmbedding_congruence {N : ℕ}
    (U : Matrix (Fin N) (Fin N) ℂ) (x : ComplexSymmetricCoordinates N) :
    symmetricCoordinateEmbedding N (symmetricCongruenceLinearMap U x) =
      U * symmetricCoordinateEmbedding N x * U.transpose :=
  symmetricCoordinateEmbedding_projection _
    (isSymm_matrixCongruence U _ (complexSymmetricMatrixOfCoordinates_isSymm x))

theorem symmetricCongruenceLinearMap_one (N : ℕ) :
    symmetricCongruenceLinearMap (1 : Matrix (Fin N) (Fin N) ℂ) = 1 := by
  apply LinearMap.ext
  intro x
  change symmetricCoordinateProjection N (1 * symmetricCoordinateEmbedding N x *
    (1 : Matrix (Fin N) (Fin N) ℂ).transpose) = x
  simpa only [transpose_one, one_mul, mul_one] using
    symmetricCoordinateProjection_embedding N x

theorem symmetricCongruenceLinearMap_mul {N : ℕ}
    (U V : Matrix (Fin N) (Fin N) ℂ) :
    symmetricCongruenceLinearMap (U * V) =
      symmetricCongruenceLinearMap U * symmetricCongruenceLinearMap V := by
  apply LinearMap.ext
  intro x
  change symmetricCoordinateProjection N ((U * V) * symmetricCoordinateEmbedding N x * (U * V).transpose) =
    symmetricCoordinateProjection N (U * symmetricCoordinateEmbedding N
      (symmetricCongruenceLinearMap V x) * U.transpose)
  rw [symmetricCoordinateEmbedding_congruence, transpose_mul]
  simp only [mul_assoc]

/-- The actual congruence action on the independent symmetric coordinates. -/
def unitaryCongruenceRepresentation (N : ℕ) :
    Matrix.unitaryGroup (Fin N) ℂ →*
      (ComplexSymmetricCoordinates N →ₗ[ℝ] ComplexSymmetricCoordinates N) where
  toFun U := (symmetricCongruenceLinearMap (U : Matrix (Fin N) (Fin N) ℂ)).restrictScalars ℝ
  map_one' := by
    apply LinearMap.ext
    intro x
    change symmetricCongruenceLinearMap (1 : Matrix (Fin N) (Fin N) ℂ) x = x
    rw [symmetricCongruenceLinearMap_one]
    rfl
  map_mul' U V := by
    apply LinearMap.ext
    intro x
    change symmetricCongruenceLinearMap
      ((U : Matrix (Fin N) (Fin N) ℂ) * (V : Matrix (Fin N) (Fin N) ℂ)) x =
      symmetricCongruenceLinearMap (U : Matrix (Fin N) (Fin N) ℂ)
        (symmetricCongruenceLinearMap (V : Matrix (Fin N) (Fin N) ℂ) x)
    rw [symmetricCongruenceLinearMap_mul]
    rfl

theorem unitaryCongruenceRepresentation_apply (N : ℕ)
    (U : Matrix.unitaryGroup (Fin N) ℂ) (x : ComplexSymmetricCoordinates N)
    (ij : ComplexSymmetricCoordinateIndex N) :
    unitaryCongruenceRepresentation N U x ij =
      ((U : Matrix (Fin N) (Fin N) ℂ) * complexSymmetricMatrixOfCoordinates x *
        (U : Matrix (Fin N) (Fin N) ℂ).transpose) ij.1.1 ij.1.2 := rfl

theorem continuous_unitaryCongruenceRepresentation_apply (N : ℕ)
    (x : ComplexSymmetricCoordinates N) :
    Continuous (fun U : Matrix.unitaryGroup (Fin N) ℂ ↦
      unitaryCongruenceRepresentation N U x) := by
  refine continuous_pi fun ij ↦ ?_
  simp only [unitaryCongruenceRepresentation_apply]
  fun_prop

end A2Research
