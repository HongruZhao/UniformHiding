import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H11_BlockFourthTraceReduction
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic

/-!
# An involution sum-of-squares inequality for the H11 fourth jet

The remaining three-trace inequality in the block reduction has a purely
finite-dimensional source.  If `J` is a Hermitian involution and `X` is
Hermitian, put `Y = J X J`.  Cyclicity of trace gives the exact identity

`Tr((XJ)^4) + 3 Tr(X^4) - 4 Tr(X^3 J X J)`

`= (1/2) Tr((X-Y)^4) + Tr((X^2-Y^2)^2)`.

The right side is a sum of two nonnegative Hermitian-square traces.  This is
the deterministic inequality behind the centered H11 sign; it uses no
probability or scientific input.
-/

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open scoped ComplexOrder
open LogdetLean.GramHafnian.UltimateHiding.Dense

set_option maxHeartbeats 1200000

private theorem trace_square_re_nonneg_of_isHermitian
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    0 ≤ (Matrix.trace (A ^ 2)).re := by
  have hpos := Matrix.posSemidef_conjTranspose_mul_self A
  have htrace := (Complex.nonneg_iff.mp hpos.trace_nonneg).1
  simpa only [hA.eq, pow_two] using htrace

private theorem trace_four_gap_eq_sum_squares_of_trace_symmetry
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X Y : Matrix ι ι ℂ)
    (hfour : Matrix.trace (Y ^ 4) = Matrix.trace (X ^ 4))
    (hthree : Matrix.trace (X * Y ^ 3) = Matrix.trace (X ^ 3 * Y)) :
    Matrix.trace ((X * Y) ^ 2) + 3 * Matrix.trace (X ^ 4) -
          4 * Matrix.trace (X ^ 3 * Y) =
      ((2 : ℂ)⁻¹) * Matrix.trace ((X - Y) ^ 4) +
        Matrix.trace ((X ^ 2 - Y ^ 2) ^ 2) := by
  have hExpandFour : (X - Y) ^ 4 =
      X ^ 4 -
        (X ^ 3 * Y + X ^ 2 * Y * X + X * Y * X ^ 2 + Y * X ^ 3) +
        (X ^ 2 * Y ^ 2 + X * Y * X * Y + X * Y ^ 2 * X +
          Y * X ^ 2 * Y + Y * X * Y * X + Y ^ 2 * X ^ 2) -
        (X * Y ^ 3 + Y * X * Y ^ 2 + Y ^ 2 * X * Y + Y ^ 3 * X) +
        Y ^ 4 := by
    noncomm_ring
  have hExpandTwo : (X ^ 2 - Y ^ 2) ^ 2 =
      X ^ 4 - X ^ 2 * Y ^ 2 - Y ^ 2 * X ^ 2 + Y ^ 4 := by
    noncomm_ring
  have hx2yx : Matrix.trace (X ^ 2 * Y * X) =
      Matrix.trace (X ^ 3 * Y) := by
    calc
      Matrix.trace (X ^ 2 * Y * X) =
          Matrix.trace (X * (X ^ 2 * Y)) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace (X ^ 3 * Y) := by
        congr 1 <;> noncomm_ring
  have hxyx2 : Matrix.trace (X * Y * X ^ 2) =
      Matrix.trace (X ^ 3 * Y) := by
    calc
      Matrix.trace (X * Y * X ^ 2) =
          Matrix.trace (X ^ 2 * (X * Y)) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace (X ^ 3 * Y) := by
        congr 1 <;> noncomm_ring
  have hyx3 : Matrix.trace (Y * X ^ 3) =
      Matrix.trace (X ^ 3 * Y) := Matrix.trace_mul_comm _ _
  have hyxy2 : Matrix.trace (Y * X * Y ^ 2) =
      Matrix.trace (X * Y ^ 3) := by
    calc
      Matrix.trace (Y * X * Y ^ 2) =
          Matrix.trace (Y * (X * Y ^ 2)) := by
            simp only [Matrix.mul_assoc]
      _ = Matrix.trace ((X * Y ^ 2) * Y) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace (X * Y ^ 3) := by
        congr 1 <;> noncomm_ring
  have hy2xy : Matrix.trace (Y ^ 2 * X * Y) =
      Matrix.trace (X * Y ^ 3) := by
    calc
      Matrix.trace (Y ^ 2 * X * Y) =
          Matrix.trace (Y * (Y ^ 2 * X)) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace (Y ^ 3 * X) := by
        congr 1 <;> noncomm_ring
      _ = Matrix.trace (X * Y ^ 3) := Matrix.trace_mul_comm _ _
  have hy3x : Matrix.trace (Y ^ 3 * X) =
      Matrix.trace (X * Y ^ 3) := Matrix.trace_mul_comm _ _
  have hxy2x : Matrix.trace (X * Y ^ 2 * X) =
      Matrix.trace (X ^ 2 * Y ^ 2) := by
    calc
      Matrix.trace (X * Y ^ 2 * X) =
          Matrix.trace (X * (X * Y ^ 2)) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace (X ^ 2 * Y ^ 2) := by
        congr 1 <;> noncomm_ring
  have hyx2y : Matrix.trace (Y * X ^ 2 * Y) =
      Matrix.trace (X ^ 2 * Y ^ 2) := by
    calc
      Matrix.trace (Y * X ^ 2 * Y) =
          Matrix.trace ((X ^ 2 * Y) * Y) := by
            rw [show Y * X ^ 2 * Y = Y * (X ^ 2 * Y) by
              simp only [Matrix.mul_assoc]]
            exact Matrix.trace_mul_comm _ _
      _ = Matrix.trace (X ^ 2 * Y ^ 2) := by
        congr 1 <;> noncomm_ring
  have hyxyx : Matrix.trace (Y * X * Y * X) =
      Matrix.trace ((X * Y) ^ 2) := by
    calc
      Matrix.trace (Y * X * Y * X) =
          Matrix.trace ((X * Y * X) * Y) := by
            rw [show Y * X * Y * X = Y * (X * Y * X) by
              simp only [Matrix.mul_assoc]]
            exact Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((X * Y) ^ 2) := by
        congr 1 <;> noncomm_ring
  have hy2x2 : Matrix.trace (Y ^ 2 * X ^ 2) =
      Matrix.trace (X ^ 2 * Y ^ 2) := Matrix.trace_mul_comm _ _
  have hxyxy : Matrix.trace (X * Y * X * Y) =
      Matrix.trace ((X * Y) ^ 2) := by
    congr 1 <;> noncomm_ring
  rw [hExpandFour, hExpandTwo]
  simp only [Matrix.trace_add, Matrix.trace_sub]
  rw [hx2yx, hxyx2, hyx3, hyxy2, hy2xy, hy3x, hxy2x, hyx2y,
    hyxyx, hy2x2, hxyxy, hfour, hthree]
  ring

/-- Exact sum-of-squares identity for conjugation by an involution. -/
theorem trace_involution_fourth_gap_eq_sum_squares
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X J : Matrix ι ι ℂ) (hJ2 : J * J = 1) :
    Matrix.trace ((X * J) ^ 4) + 3 * Matrix.trace (X ^ 4) -
          4 * Matrix.trace (X ^ 3 * J * X * J) =
      ((2 : ℂ)⁻¹) * Matrix.trace ((X - J * X * J) ^ 4) +
        Matrix.trace ((X ^ 2 - (J * X * J) ^ 2) ^ 2) := by
  let Y : Matrix ι ι ℂ := J * X * J
  have hYpow (r : ℕ) : Y ^ r = J * X ^ r * J := by
    induction r with
    | zero =>
        simp only [pow_zero, Matrix.mul_one]
        exact hJ2.symm
    | succ r ihr =>
        rw [pow_succ, ihr]
        simp only [Y]
        calc
          J * X ^ r * J * (J * X * J) =
              J * X ^ r * (J * J) * X * J := by
                simp only [Matrix.mul_assoc]
          _ = J * X ^ (r + 1) * J := by
            simp only [hJ2, Matrix.mul_one, Matrix.one_mul, pow_succ,
              Matrix.mul_assoc]
  have hfour : Matrix.trace (Y ^ 4) = Matrix.trace (X ^ 4) := by
    rw [hYpow]
    calc
      Matrix.trace (J * X ^ 4 * J) =
          Matrix.trace ((X ^ 4 * J) * J) := by
            rw [show J * X ^ 4 * J = J * (X ^ 4 * J) by
              noncomm_ring]
            exact Matrix.trace_mul_comm _ _
      _ = Matrix.trace (X ^ 4) := by
        simp only [Matrix.mul_assoc, hJ2, Matrix.mul_one]
  have hthree : Matrix.trace (X * Y ^ 3) =
      Matrix.trace (X ^ 3 * Y) := by
    rw [hYpow]
    change Matrix.trace (X * (J * X ^ 3 * J)) =
      Matrix.trace (X ^ 3 * (J * X * J))
    calc
      Matrix.trace (X * (J * X ^ 3 * J)) =
          Matrix.trace ((X * J) * (X ^ 3 * J)) := by
            congr 1 <;> noncomm_ring
      _ = Matrix.trace ((X ^ 3 * J) * (X * J)) :=
        Matrix.trace_mul_comm _ _
      _ = Matrix.trace (X ^ 3 * (J * X * J)) := by
        congr 1 <;> noncomm_ring
  have hbase := trace_four_gap_eq_sum_squares_of_trace_symmetry
    X Y hfour hthree
  have hXY : Matrix.trace ((X * Y) ^ 2) =
      Matrix.trace ((X * J) ^ 4) := by
    simp only [Y]
    congr 1
    noncomm_ring
  rw [hXY] at hbase
  simpa only [Y, Matrix.mul_assoc] using hbase

/-- The fourth involution trace gap is nonnegative for Hermitian data. -/
theorem trace_involution_fourth_gap_re_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X J : Matrix ι ι ℂ)
    (hX : X.IsHermitian) (hJ : J.IsHermitian) (hJ2 : J * J = 1) :
    0 ≤ (Matrix.trace ((X * J) ^ 4) + 3 * Matrix.trace (X ^ 4) -
      4 * Matrix.trace (X ^ 3 * J * X * J)).re := by
  let Y : Matrix ι ι ℂ := J * X * J
  have hY : Y.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_mul, hJ.eq, hX.eq]
    simp only [Y, Matrix.mul_assoc]
  have hdiff : (X - Y).IsHermitian := hX.sub hY
  have hsqdiff : (X ^ 2 - Y ^ 2).IsHermitian :=
    (hX.pow 2).sub (hY.pow 2)
  have hfour : 0 ≤ (Matrix.trace ((X - Y) ^ 4)).re := by
    have h := trace_square_re_nonneg_of_isHermitian
      ((X - Y) ^ 2) (hdiff.pow 2)
    simpa only [← pow_mul] using h
  have htwo : 0 ≤ (Matrix.trace ((X ^ 2 - Y ^ 2) ^ 2)).re :=
    trace_square_re_nonneg_of_isHermitian _ hsqdiff
  rw [trace_involution_fourth_gap_eq_sum_squares X J hJ2]
  norm_num [Complex.mul_re, Complex.add_re]
  exact add_nonneg (mul_nonneg (by norm_num) hfour) htwo

/-- Young-form consequence used by the H11 Cayley reduction. -/
theorem four_trace_X_cube_JXJ_le_trace_XJ_four_add_three_trace_X_four
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X J : Matrix ι ι ℂ)
    (hX : X.IsHermitian) (hJ : J.IsHermitian) (hJ2 : J * J = 1) :
    4 * (Matrix.trace (X ^ 3 * J * X * J)).re ≤
      (Matrix.trace ((X * J) ^ 4)).re +
        3 * (Matrix.trace (X ^ 4)).re := by
  have h := trace_involution_fourth_gap_re_nonneg X J hX hJ hJ2
  norm_num [Complex.add_re, Complex.sub_re, Complex.mul_re] at h ⊢
  linarith

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
