import Mathlib

/-!
# A neutral inverse-Gram gradient endpoint for the hiding Article

This file proves the finite-dimensional identity

`‖∇ tr(c (RᵀR)⁻¹)‖_F² = 4 c² tr((RᵀR)⁻³)`

on the full-column-rank locus.  It deliberately depends only on Mathlib:
the identity belongs to elementary rectangular-matrix calculus and does not
need any module from the anticoncentration development.
-/

open scoped BigOperators

namespace LogdetLean.GramHafnian.MatrixLawEndpoints

noncomputable section

variable {k m : Type*} [Fintype k] [Fintype m]
  [DecidableEq k] [DecidableEq m]

/-- The real transpose-Gram matrix used by the hiding Article. -/
def hidingRealGram (R : Matrix k m ℝ) : Matrix m m ℝ :=
  R.transpose * R

/-- Frobenius pairing in the ambient rectangular coordinates. -/
def hidingRealFrobeniusInner (R V : Matrix k m ℝ) : ℝ :=
  ∑ i, ∑ j, R i j * V i j

/-- The rectangular Frobenius pairing is the trace pairing `tr(RᵀV)`. -/
theorem hidingRealFrobeniusInner_eq_trace_transpose_mul
    (R V : Matrix k m ℝ) :
    hidingRealFrobeniusInner R V = Matrix.trace (R.transpose * V) := by
  simp only [hidingRealFrobeniusInner, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]

/-- The inverse of a real transpose-Gram matrix is symmetric, including under
Mathlib's totalized nonsingular inverse at singular inputs. -/
theorem hidingRealGram_inv_isSymm (R : Matrix k m ℝ) :
    ((hidingRealGram R)⁻¹).IsSymm := by
  unfold Matrix.IsSymm
  rw [Matrix.transpose_nonsing_inv]
  congr 1
  unfold hidingRealGram
  rw [Matrix.transpose_mul, Matrix.transpose_transpose]

/-- The inverse lift `R (RᵀR)⁻¹` has Gram matrix `(RᵀR)⁻¹` on the
full-column-rank locus. -/
theorem hidingTransposeInverseLift_mul_inverseLift
    (R : Matrix k m ℝ) (hM : IsUnit (hidingRealGram R).det) :
    (R * (hidingRealGram R)⁻¹).transpose *
        (R * (hidingRealGram R)⁻¹) =
      (hidingRealGram R)⁻¹ := by
  rw [Matrix.transpose_mul, (hidingRealGram_inv_isSymm R).eq]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc R.transpose R (hidingRealGram R)⁻¹]
  change (hidingRealGram R)⁻¹ *
      (hidingRealGram R * (hidingRealGram R)⁻¹) = _
  rw [← Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul _ hM, Matrix.one_mul]

/-- The ambient rectangular gradient of `R ↦ tr(c (RᵀR)⁻¹)`. -/
def inverseWishartTraceGradient (c : ℝ) (R : Matrix k m ℝ) :
    Matrix k m ℝ :=
  (-2 * c) •
    ((R * (hidingRealGram R)⁻¹) * (hidingRealGram R)⁻¹)

/-- The paper's `tr(B⁻³)` notation, with `B = RᵀR`. -/
def inverseWishartTraceCube (R : Matrix k m ℝ) : ℝ :=
  Matrix.trace
    ((hidingRealGram R)⁻¹ *
      (hidingRealGram R)⁻¹ *
      (hidingRealGram R)⁻¹)

/-- The scalar functional whose ambient gradient is displayed in the paper. -/
def inverseWishartTraceFunctional (c : ℝ) (R : Matrix k m ℝ) : ℝ :=
  c * Matrix.trace (hidingRealGram R)⁻¹

/-- Matrix identity underlying the squared Frobenius norm calculation. -/
theorem transpose_inverseWishartTraceGradient_mul_self
    (c : ℝ) (R : Matrix k m ℝ)
    (hM : IsUnit (hidingRealGram R).det) :
    (inverseWishartTraceGradient c R).transpose *
        inverseWishartTraceGradient c R =
      (4 * c ^ 2) •
        ((hidingRealGram R)⁻¹ *
          (hidingRealGram R)⁻¹ *
          (hidingRealGram R)⁻¹) := by
  rw [inverseWishartTraceGradient, Matrix.transpose_smul,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [Matrix.transpose_mul, (hidingRealGram_inv_isSymm R).eq]
  have hcore :
      ((hidingRealGram R)⁻¹ *
          (R * (hidingRealGram R)⁻¹).transpose) *
          ((R * (hidingRealGram R)⁻¹) *
            (hidingRealGram R)⁻¹) =
        (hidingRealGram R)⁻¹ *
          (hidingRealGram R)⁻¹ *
          (hidingRealGram R)⁻¹ := by
    rw [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc
      (R * (hidingRealGram R)⁻¹).transpose
      (R * (hidingRealGram R)⁻¹)
      (hidingRealGram R)⁻¹]
    rw [hidingTransposeInverseLift_mul_inverseLift R hM]
    rw [Matrix.mul_assoc]
  rw [hcore]
  congr 1
  ring

/-- Literal endpoint for `eq:hide-inverse-gradient`: the squared Frobenius
norm of the inverse-Gram trace gradient is `4 c² tr(B⁻³)`. -/
theorem eq_hide_inverse_gradient
    (c : ℝ) (R : Matrix k m ℝ)
    (hM : IsUnit (hidingRealGram R).det) :
    hidingRealFrobeniusInner
        (inverseWishartTraceGradient c R)
        (inverseWishartTraceGradient c R) =
      4 * c ^ 2 * inverseWishartTraceCube R := by
  rw [hidingRealFrobeniusInner_eq_trace_transpose_mul,
    transpose_inverseWishartTraceGradient_mul_self c R hM,
    Matrix.trace_smul]
  rfl

end

end LogdetLean.GramHafnian.MatrixLawEndpoints
