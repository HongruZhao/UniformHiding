import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic

/-!
# A two-column matrix determinant lemma

This is the purely algebraic rank-two update used by the H7 rank-one line.
It is independent of the COE likelihood and introduces no assumptions beyond
invertibility of the base determinant.
-/

open scoped Matrix

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

/-- The two-column determinant lemma expressed by the two diagonal entries
and the product of the off-diagonal entries of the small matrix. -/
theorem det_add_mul_fin_two_entries
    {m α : Type*} [Fintype m] [DecidableEq m] [Field α]
    (A : Matrix m m α)
    (U : Matrix m (Fin 2) α)
    (V : Matrix (Fin 2) m α)
    (hA : IsUnit A.det)
    (a d b : α)
    (h00 : (V * A⁻¹ * U) 0 0 = a)
    (h11 : (V * A⁻¹ * U) 1 1 = d)
    (hoff : (V * A⁻¹ * U) 0 1 * (V * A⁻¹ * U) 1 0 = b) :
    (A + U * V).det = A.det * ((1 + a) * (1 + d) - b) := by
  rw [Matrix.det_add_mul U V hA, Matrix.det_fin_two]
  have hI00 :
      ((1 : Matrix (Fin 2) (Fin 2) α) + V * A⁻¹ * U) 0 0 =
        1 + (V * A⁻¹ * U) 0 0 := by simp
  have hI11 :
      ((1 : Matrix (Fin 2) (Fin 2) α) + V * A⁻¹ * U) 1 1 =
        1 + (V * A⁻¹ * U) 1 1 := by simp
  have hI01 :
      ((1 : Matrix (Fin 2) (Fin 2) α) + V * A⁻¹ * U) 0 1 =
        (V * A⁻¹ * U) 0 1 := by simp
  have hI10 :
      ((1 : Matrix (Fin 2) (Fin 2) α) + V * A⁻¹ * U) 1 0 =
        (V * A⁻¹ * U) 1 0 := by simp
  rw [hI00, hI11, hI01, hI10, h00, h11, hoff]

/-- The determinant lemma after the small update matrix has equal diagonal
entries and a known product of off-diagonal entries.  This form avoids any
division by the (complex-valued) base determinant. -/
theorem det_add_mul_fin_two_square
    {m α : Type*} [Fintype m] [DecidableEq m] [Field α]
    (A : Matrix m m α)
    (U : Matrix m (Fin 2) α)
    (V : Matrix (Fin 2) m α)
    (hA : IsUnit A.det)
    (a b : α)
    (h00 : (V * A⁻¹ * U) 0 0 = a)
    (h11 : (V * A⁻¹ * U) 1 1 = a)
    (hoff : (V * A⁻¹ * U) 0 1 * (V * A⁻¹ * U) 1 0 = b) :
    (A + U * V).det = A.det * ((1 + a) ^ 2 - b) := by
  rw [Matrix.det_add_mul U V hA, Matrix.det_fin_two]
  have hI00 :
      ((1 : Matrix (Fin 2) (Fin 2) α) + V * A⁻¹ * U) 0 0 =
        1 + (V * A⁻¹ * U) 0 0 := by simp
  have hI11 :
      ((1 : Matrix (Fin 2) (Fin 2) α) + V * A⁻¹ * U) 1 1 =
        1 + (V * A⁻¹ * U) 1 1 := by simp
  have hI01 :
      ((1 : Matrix (Fin 2) (Fin 2) α) + V * A⁻¹ * U) 0 1 =
        (V * A⁻¹ * U) 0 1 := by simp
  have hI10 :
      ((1 : Matrix (Fin 2) (Fin 2) α) + V * A⁻¹ * U) 1 0 =
        (V * A⁻¹ * U) 1 0 := by simp
  rw [hI00, hI11, hI01, hI10, h00, h11, hoff]
  ring

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
