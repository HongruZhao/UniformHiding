import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H11_InvolutionFourthTraceInequality
import Mathlib.Tactic

/-!
# Square-root congruence bridge for the H11 Cayley trace inequality

This file performs the finite noncommutative substitution linking the
involution sum-of-squares theorem to the three traces in the Cayley reduction.
It deliberately accepts the square root `R` and its grading relation
`R J R = J` as explicit hypotheses; constructing those facts from the
positive COE block matrix is the separate spectral-calculus splice.
-/

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

set_option maxHeartbeats 1200000

private theorem trace_RER_four_eq_trace_ERsq_four
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E R : Matrix ι ι ℂ) :
    Matrix.trace ((R * E * R) ^ 4) =
      Matrix.trace ((E * R ^ 2) ^ 4) := by
  have hword : (R * E * R) ^ 4 =
      R * (E * R ^ 2 * E * R ^ 2 * E * R ^ 2 * E * R) := by
    noncomm_ring
  rw [hword]
  calc
    Matrix.trace
        (R * (E * R ^ 2 * E * R ^ 2 * E * R ^ 2 * E * R)) =
        Matrix.trace
          ((E * R ^ 2 * E * R ^ 2 * E * R ^ 2 * E * R) * R) :=
      Matrix.trace_mul_comm _ _
    _ = Matrix.trace ((E * R ^ 2) ^ 4) := by
      congr 1 <;> noncomm_ring

private theorem trace_RER_cube_J_RER_J_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E R J : Matrix ι ι ℂ)
    (hJ2 : J * J = 1) (hRJR : R * J * R = J)
    (hEJ : E * J = J * E) :
    Matrix.trace ((R * E * R) ^ 3 * J * (R * E * R) * J) =
      Matrix.trace (E ^ 3 * R ^ 2 * E * R ^ 2) := by
  have hEJEJ : E * J * E * J = E ^ 2 := by
    calc
      E * J * E * J = E * (J * E) * J := by noncomm_ring
      _ = (E * E) * (J * J) := by rw [← hEJ]; noncomm_ring
      _ = E ^ 2 := by rw [hJ2, Matrix.mul_one, pow_two]
  let W : Matrix ι ι ℂ :=
    E * R ^ 2 * E * R ^ 2 * E * R * J * R * E * R * J
  have hword : (R * E * R) ^ 3 * J * (R * E * R) * J = R * W := by
    dsimp only [W]
    noncomm_ring
  have hcollapse : W * R = E * R ^ 2 * E * R ^ 2 * E ^ 2 := by
    dsimp only [W]
    calc
      (E * R ^ 2 * E * R ^ 2 * E * R * J * R * E * R * J) * R =
          E * R ^ 2 * E * R ^ 2 * E * (R * J * R) * E *
            (R * J * R) := by noncomm_ring
      _ = E * R ^ 2 * E * R ^ 2 * E * J * E * J := by rw [hRJR]
      _ = E * R ^ 2 * E * R ^ 2 * E ^ 2 := by
        rw [show E * R ^ 2 * E * R ^ 2 * E * J * E * J =
          E * R ^ 2 * E * R ^ 2 * (E * J * E * J) by
            noncomm_ring, hEJEJ]
  rw [hword]
  calc
    Matrix.trace (R * W) = Matrix.trace (W * R) :=
      Matrix.trace_mul_comm _ _
    _ = Matrix.trace (E * R ^ 2 * E * R ^ 2 * E ^ 2) := by rw [hcollapse]
    _ = Matrix.trace (E ^ 3 * R ^ 2 * E * R ^ 2) := by
      calc
        Matrix.trace (E * R ^ 2 * E * R ^ 2 * E ^ 2) =
            Matrix.trace (E ^ 2 * (E * R ^ 2 * E * R ^ 2)) :=
          Matrix.trace_mul_comm _ _
        _ = Matrix.trace (E ^ 3 * R ^ 2 * E * R ^ 2) := by
          congr 1 <;> noncomm_ring

private theorem trace_RER_J_four_eq_trace_E_four
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E R J : Matrix ι ι ℂ)
    (hJ2 : J * J = 1) (hRJR : R * J * R = J)
    (hEJ : E * J = J * E) :
    Matrix.trace (((R * E * R) * J) ^ 4) = Matrix.trace (E ^ 4) := by
  have hEJEJ : E * J * E * J = E ^ 2 := by
    calc
      E * J * E * J = E * (J * E) * J := by noncomm_ring
      _ = (E * E) * (J * J) := by rw [← hEJ]; noncomm_ring
      _ = E ^ 2 := by rw [hJ2, Matrix.mul_one, pow_two]
  let W : Matrix ι ι ℂ :=
    E * R * J * R * E * R * J * R * E * R * J * R * E * R * J
  have hword : ((R * E * R) * J) ^ 4 = R * W := by
    dsimp only [W]
    noncomm_ring
  have hcollapse : W * R = E ^ 4 := by
    dsimp only [W]
    calc
      (E * R * J * R * E * R * J * R * E * R * J * R * E * R * J) * R =
          E * (R * J * R) * E * (R * J * R) * E *
            (R * J * R) * E * (R * J * R) := by noncomm_ring
      _ = E * J * E * J * E * J * E * J := by rw [hRJR]
      _ = (E * J * E * J) * (E * J * E * J) := by noncomm_ring
      _ = E ^ 4 := by rw [hEJEJ]; noncomm_ring
  rw [hword]
  calc
    Matrix.trace (R * W) = Matrix.trace (W * R) :=
      Matrix.trace_mul_comm _ _
    _ = Matrix.trace (E ^ 4) := by rw [hcollapse]

/-- If `S=R²`, `RJR=J`, and `E` commutes with the grading involution, the
involution fourth-trace inequality is exactly the Cayley inequality. -/
theorem four_trace_E_cube_Rsq_E_Rsq_le_of_grading_square_root
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E R J : Matrix ι ι ℂ)
    (hE : E.IsHermitian) (hR : R.IsHermitian) (hJ : J.IsHermitian)
    (hJ2 : J * J = 1) (hRJR : R * J * R = J)
    (hEJ : E * J = J * E) :
    4 * (Matrix.trace (E ^ 3 * R ^ 2 * E * R ^ 2)).re ≤
      (Matrix.trace (E ^ 4)).re +
        3 * (Matrix.trace ((E * R ^ 2) ^ 4)).re := by
  let X : Matrix ι ι ℂ := R * E * R
  have hX : X.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_mul, hR.eq, hE.eq]
    simp only [X, Matrix.mul_assoc]
  have hbase :=
    four_trace_X_cube_JXJ_le_trace_XJ_four_add_three_trace_X_four
      X J hX hJ hJ2
  have hXfour : Matrix.trace (X ^ 4) =
      Matrix.trace ((E * R ^ 2) ^ 4) := by
    exact trace_RER_four_eq_trace_ERsq_four E R
  have hcross : Matrix.trace (X ^ 3 * J * X * J) =
      Matrix.trace (E ^ 3 * R ^ 2 * E * R ^ 2) := by
    exact trace_RER_cube_J_RER_J_eq E R J hJ2 hRJR hEJ
  have hleft : Matrix.trace ((X * J) ^ 4) = Matrix.trace (E ^ 4) := by
    exact trace_RER_J_four_eq_trace_E_four E R J hJ2 hRJR hEJ
  rw [hcross, hleft, hXfour] at hbase
  exact hbase

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
