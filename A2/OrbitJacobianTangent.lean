import A2.OrbitJacobianDiagonal

/-! The diagonal operator is the actual differential of unitary congruence. -/

open scoped BigOperators Matrix ComplexOrder MatrixOrder

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

def takagiSkewMatrix {N : ℕ} (x : TakagiRealCoordinates N) :
    Matrix (Fin N) (Fin N) ℂ := fun i j =>
  if h : i = j then Complex.mk 0 (x (⟨(i, i), le_refl i⟩, 1))
  else if h : i ≤ j then
    Complex.mk (x (⟨(i, j), h⟩, 0)) (x (⟨(i, j), h⟩, 1))
  else -star (Complex.mk (x (⟨(j, i), le_of_not_ge h⟩, 0))
    (x (⟨(j, i), le_of_not_ge h⟩, 1)))

theorem takagiSkewMatrix_skewHermitian {N : ℕ} (x : TakagiRealCoordinates N) :
    (takagiSkewMatrix x).conjTranspose = -takagiSkewMatrix x := by
  ext i j
  by_cases he : i = j
  · subst j
    apply Complex.ext <;> simp [takagiSkewMatrix, Matrix.conjTranspose_apply]
  · by_cases hij : i ≤ j
    · have hji : ¬ j ≤ i := not_le.mpr (lt_of_le_of_ne hij he)
      simp [takagiSkewMatrix, Matrix.conjTranspose_apply, he, Ne.symm he, hij, hji]
    · have hji : j ≤ i := le_of_not_ge hij
      simp [takagiSkewMatrix, Matrix.conjTranspose_apply, he, Ne.symm he, hij, hji]

def takagiSkewLinearMap (N : ℕ) :
    TakagiRealCoordinates N →ₗ[ℝ] Matrix (Fin N) (Fin N) ℂ where
  toFun := takagiSkewMatrix
  map_add' x y := by
    ext i j
    by_cases he : i = j <;> by_cases hij : i ≤ j <;>
      simp [takagiSkewMatrix, he, hij, Complex.ext_iff] <;> ring
  map_smul' a x := by
    ext i j
    by_cases he : i = j <;> by_cases hij : i ≤ j <;>
      simp [takagiSkewMatrix, he, hij, Complex.ext_iff, Complex.real_smul]

def takagiRadialMatrix {N : ℕ} (lambda : Fin N → ℝ) (x : TakagiRealCoordinates N) :
    Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal fun i => ((2 * Real.sqrt (lambda i))⁻¹ *
    x (⟨(i, i), le_refl i⟩, 0) : ℝ)

def takagiDiagonalOrbitTangent {N : ℕ} (lambda : Fin N → ℝ)
    (x : TakagiRealCoordinates N) : Matrix (Fin N) (Fin N) ℂ :=
  takagiSkewMatrix x * Matrix.diagonal (fun i => (Real.sqrt (lambda i) : ℂ)) +
    Matrix.diagonal (fun i => (Real.sqrt (lambda i) : ℂ)) * (takagiSkewMatrix x).transpose +
    takagiRadialMatrix lambda x

theorem takagiDiagonalOrbitTangent_upper_coordinates {N : ℕ} (lambda : Fin N → ℝ)
    (x : TakagiRealCoordinates N) (ij : ComplexSymmetricCoordinateIndex N) :
    takagiDiagonalOrbitTangent lambda x ij.val.1 ij.val.2 =
      takagiRealComplexCoordinatesEquiv N (takagiDiagonalDifferential lambda x) ij := by
  classical
  have happ (p : TakagiRealCoordinateIndex N) :
      takagiDiagonalDifferential lambda x p = takagiDiagonalDifferentialWeight lambda p * x p := by
    simp [takagiDiagonalDifferential, takagiDiagonalDifferentialMatrix,
      Matrix.toLin'_apply, Matrix.mulVec_diagonal]
  rcases ij with ⟨⟨i, j⟩, hij⟩
  change takagiDiagonalOrbitTangent lambda x i j = _
  by_cases he : i = j
  · subst j
    apply Complex.ext <;>
      simp [takagiDiagonalOrbitTangent, Matrix.mul_diagonal, Matrix.diagonal_mul,
        Matrix.transpose_apply, takagiSkewMatrix, takagiRadialMatrix,
        takagiRealComplexCoordinatesEquiv, happ, takagiDiagonalDifferentialWeight,
        Complex.mul_re, Complex.mul_im]
    ring
  · have hji : ¬ j ≤ i := not_le.mpr (lt_of_le_of_ne hij he)
    apply Complex.ext <;>
      simp [takagiDiagonalOrbitTangent, Matrix.mul_diagonal, Matrix.diagonal_mul,
        Matrix.transpose_apply, takagiSkewMatrix, he, Ne.symm he, hij, hji,
        takagiRadialMatrix, Matrix.diagonal_apply, takagiRealComplexCoordinatesEquiv,
        happ, takagiDiagonalDifferentialWeight, Complex.mul_re, Complex.mul_im]
      <;> ring

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
