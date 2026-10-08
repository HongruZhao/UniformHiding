import A4.Target
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Tactic

open scoped BigOperators
namespace A4Research
noncomputable section
namespace InverseStein
variable {k m : Type*}

section SteinLift

variable [Fintype k] [Fintype m] [DecidableEq m]

/-- The real Gram matrix of a rectangular matrix. -/
def realWishartGram (R : Matrix k m ℝ) : Matrix m m ℝ :=
  R.transpose * R

/-- Value of the Gaussian-Stein vector field which lifts the Gram direction
`D` to the rectangular matrix `R`. -/
def steinVectorFieldValue (R : Matrix k m ℝ) (D : Matrix m m ℝ) :
    Matrix k m ℝ :=
  (1 / 2 : ℝ) • (R * (realWishartGram R)⁻¹ * D)

/-- The right-hand contribution to the first variation of `RᵀR` is `D/2`. -/
theorem transpose_mul_steinVectorFieldValue
    (R : Matrix k m ℝ) (D : Matrix m m ℝ)
    (hM : IsUnit (realWishartGram R).det) :
    R.transpose * steinVectorFieldValue R D = (1 / 2 : ℝ) • D := by
  calc
    R.transpose * steinVectorFieldValue R D =
        (1 / 2 : ℝ) •
          (realWishartGram R * (realWishartGram R)⁻¹ * D) := by
      simp [steinVectorFieldValue, realWishartGram, Matrix.mul_assoc]
    _ = (1 / 2 : ℝ) • D := by
      rw [Matrix.mul_nonsing_inv _ hM]
      simp

/-- For symmetric `D`, the left-hand contribution to the first Gram
variation is also `D/2`. -/
theorem steinVectorFieldValue_transpose_mul
    (R : Matrix k m ℝ) {D : Matrix m m ℝ} (hD : D.IsSymm)
    (hM : IsUnit (realWishartGram R).det) :
    (steinVectorFieldValue R D).transpose * R = (1 / 2 : ℝ) • D := by
  have h := congrArg Matrix.transpose
    (transpose_mul_steinVectorFieldValue R D hM)
  simpa [Matrix.transpose_mul, hD.eq] using h

/-- The Stein vector field has exactly the prescribed first variation of
the real Gram map `R ↦ RᵀR`. -/
theorem gram_firstVariation_steinVectorFieldValue
    (R : Matrix k m ℝ) {D : Matrix m m ℝ} (hD : D.IsSymm)
    (hM : IsUnit (realWishartGram R).det) :
    (steinVectorFieldValue R D).transpose * R +
        R.transpose * steinVectorFieldValue R D = D := by
  rw [steinVectorFieldValue_transpose_mul R hD hM,
    transpose_mul_steinVectorFieldValue R D hM]
  ext i j
  simp
  ring

/-- Frobenius inner product of two real rectangular matrices. -/
def realFrobeniusInner (R V : Matrix k m ℝ) : ℝ :=
  ∑ i, ∑ j, R i j * V i j

/-- The Frobenius inner product is the trace pairing `tr(RᵀV)`. -/
theorem realFrobeniusInner_eq_trace_transpose_mul
    (R V : Matrix k m ℝ) :
    realFrobeniusInner R V = Matrix.trace (R.transpose * V) := by
  simp only [realFrobeniusInner, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.transpose_apply]
  rw [Finset.sum_comm]

/-- The Gaussian radial term of the Stein vector field is exactly
`tr(D)/2`; equivalently, twice the Frobenius pairing is `tr(D)`. -/
theorem two_mul_frobenius_steinVectorFieldValue
    (R : Matrix k m ℝ) (D : Matrix m m ℝ)
    (hM : IsUnit (realWishartGram R).det) :
    2 * realFrobeniusInner R (steinVectorFieldValue R D) = Matrix.trace D := by
  rw [realFrobeniusInner_eq_trace_transpose_mul,
    transpose_mul_steinVectorFieldValue R D hM, Matrix.trace_smul]
  simp

end SteinLift

end InverseStein
end
end A4Research
