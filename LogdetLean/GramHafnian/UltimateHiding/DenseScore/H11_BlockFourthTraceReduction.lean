import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ConcreteCOEStatistics
import Mathlib.Tactic

/-!
# Algebraic reduction of the centered block log-determinant fourth jet

For a positive block matrix `M = I + R`, put `W = M⁻¹` and use the
Cayley variable `S = 2W-I`, so `W = (I+S)/2`.  The fourth Jacobi trace
polynomial initially has five noncommutative terms.  This file proves that,
after cyclicity of the finite matrix trace, it collapses to only three:

`-2 Tr(E⁴) + 8 Tr(E³ S E S) - 6 Tr((E S)⁴)`.

This is the exact algebraic frontier for the H11 support sign.  No positivity,
probability, density, or scientific input is used here.
-/

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

set_option maxHeartbeats 4000000

/-- The fourth derivative supplied by Jacobi's log-determinant formula when
the block curve has derivatives `M⁽ᵏ⁾(0)=2ᵏ Eᵏ`. -/
def h11BlockFourthJacobiMatrix
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W E : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (16 : ℂ) • (W * E ^ 4) -
    (64 : ℂ) • (W * E * W * E ^ 3) -
    (48 : ℂ) • (W * E ^ 2 * W * E ^ 2) +
    (192 : ℂ) • (W * E * W * E * W * E ^ 2) -
    (96 : ℂ) • ((W * E) ^ 4)

private theorem trace_rotate_h11_block
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B T : Matrix ι ι ℂ) (hAB : A * B = T) :
    Matrix.trace (B * A) = Matrix.trace T := by
  rw [Matrix.trace_mul_comm]
  rw [hAB]

private theorem trace_cycle_ses_e2_se_h11_block
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E S : Matrix ι ι ℂ) :
    Matrix.trace (S * E * S * E ^ 2 * S * E) =
      Matrix.trace (E ^ 2 * S * E * S * E * S) := by
  calc
    Matrix.trace (S * E * S * E ^ 2 * S * E) =
        Matrix.trace ((S * E * S) * (E ^ 2 * S * E)) := by
          simp only [Matrix.mul_assoc]
    _ = Matrix.trace ((E ^ 2 * S * E) * (S * E * S)) :=
      Matrix.trace_mul_comm _ _
    _ = Matrix.trace (E ^ 2 * S * E * S * E * S) := by
      simp only [Matrix.mul_assoc]

/-- Substitution `W=(I+S)/2`, followed only by cyclicity of trace, reduces the
five-term fourth Jacobi polynomial to a three-term trace expression. -/
theorem trace_h11BlockFourthJacobiMatrix_half_one_add
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E S : Matrix ι ι ℂ) :
    Matrix.trace
        (h11BlockFourthJacobiMatrix
          (((2 : ℂ)⁻¹) • (1 + S)) E) =
      -2 * Matrix.trace (E ^ 4) +
        8 * Matrix.trace (E ^ 3 * S * E * S) -
        6 * Matrix.trace ((E * S) ^ 4) := by
  let W : Matrix ι ι ℂ := ((2 : ℂ)⁻¹) • (1 + S)
  have hExpand : h11BlockFourthJacobiMatrix W E =
      (-2 : ℂ) • E ^ 4 +
      ((-2 : ℂ) • (S * E ^ 4) +
      ((2 : ℂ) • (E * S * E ^ 3) +
      ((6 : ℂ) • (E ^ 2 * S * E ^ 2) +
      ((-6 : ℂ) • (E ^ 3 * S * E) +
      ((2 : ℂ) • (S * E * S * E ^ 3) +
      ((18 : ℂ) • (E * S * E * S * E ^ 2) +
      ((-6 : ℂ) • (E ^ 2 * S * E * S * E) +
      ((-6 : ℂ) • (S * E ^ 3 * S * E) +
      ((6 : ℂ) • (S * E ^ 2 * S * E ^ 2) +
      ((-6 : ℂ) • (E * S * E ^ 2 * S * E) +
      ((18 : ℂ) • (S * E * S * E * S * E ^ 2) +
      ((-6 : ℂ) • (E * S * E * S * E * S * E) +
      ((-6 : ℂ) • (S * E ^ 2 * S * E * S * E) +
      ((-6 : ℂ) • (S * E * S * E ^ 2 * S * E) +
        (-6 : ℂ) • (S * E * S * E * S * E * S * E))))))))))))))) := by
    dsimp only [h11BlockFourthJacobiMatrix, W]
    noncomm_ring
    module
  have h1 : Matrix.trace (S * E ^ 4) = Matrix.trace (E ^ 4 * S) :=
    Matrix.trace_mul_comm _ _
  have h2 : Matrix.trace (E * S * E ^ 3) = Matrix.trace (E ^ 4 * S) := by
    calc
      Matrix.trace (E * S * E ^ 3) =
          Matrix.trace ((E * S) * E ^ 3) := rfl
      _ = Matrix.trace (E ^ 3 * (E * S)) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace (E ^ 4 * S) := by
        simp only [pow_succ, pow_zero, Matrix.one_mul, Matrix.mul_assoc]
  have h3 : Matrix.trace (E ^ 2 * S * E ^ 2) =
      Matrix.trace (E ^ 4 * S) := by
    calc
      Matrix.trace (E ^ 2 * S * E ^ 2) =
          Matrix.trace ((E ^ 2 * S) * E ^ 2) := rfl
      _ = Matrix.trace (E ^ 2 * (E ^ 2 * S)) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace (E ^ 4 * S) := by
        simp only [pow_succ, pow_zero, Matrix.one_mul, Matrix.mul_assoc]
  have h4 : Matrix.trace (E ^ 3 * S * E) =
      Matrix.trace (E ^ 4 * S) := by
    calc
      Matrix.trace (E ^ 3 * S * E) =
          Matrix.trace ((E ^ 3 * S) * E) := rfl
      _ = Matrix.trace (E * (E ^ 3 * S)) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace (E ^ 4 * S) := by
        simp only [pow_succ, pow_zero, Matrix.one_mul, Matrix.mul_assoc]
  have h5 : Matrix.trace (S * E * S * E ^ 3) =
      Matrix.trace (E ^ 3 * S * E * S) := by
    calc
      Matrix.trace (S * E * S * E ^ 3) =
          Matrix.trace ((S * E * S) * E ^ 3) := rfl
      _ = Matrix.trace (E ^ 3 * (S * E * S)) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace (E ^ 3 * S * E * S) := by
        simp only [Matrix.mul_assoc]
  have h6 : Matrix.trace (E * S * E * S * E ^ 2) =
      Matrix.trace (E ^ 3 * S * E * S) := by
    calc
      Matrix.trace (E * S * E * S * E ^ 2) =
          Matrix.trace ((E * S * E * S) * E ^ 2) := rfl
      _ = Matrix.trace (E ^ 2 * (E * S * E * S)) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace (E ^ 3 * S * E * S) := by
        simp only [pow_succ, pow_zero, Matrix.one_mul, Matrix.mul_assoc]
  have h7 : Matrix.trace (E ^ 2 * S * E * S * E) =
      Matrix.trace (E ^ 3 * S * E * S) := by
    calc
      Matrix.trace (E ^ 2 * S * E * S * E) =
          Matrix.trace ((E ^ 2 * S * E * S) * E) := rfl
      _ = Matrix.trace (E * (E ^ 2 * S * E * S)) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace (E ^ 3 * S * E * S) := by
        simp only [pow_succ, pow_zero, Matrix.one_mul, Matrix.mul_assoc]
  have h8 : Matrix.trace (S * E ^ 3 * S * E) =
      Matrix.trace (E ^ 3 * S * E * S) := by
    calc
      Matrix.trace (S * E ^ 3 * S * E) =
          Matrix.trace (S * (E ^ 3 * S * E)) := by
            simp only [Matrix.mul_assoc]
      _ = Matrix.trace ((E ^ 3 * S * E) * S) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace (E ^ 3 * S * E * S) := rfl
  have h9 : Matrix.trace (S * E ^ 2 * S * E ^ 2) =
      Matrix.trace (E ^ 2 * S * E ^ 2 * S) := by
    calc
      Matrix.trace (S * E ^ 2 * S * E ^ 2) =
          Matrix.trace (S * (E ^ 2 * S * E ^ 2)) := by
            simp only [Matrix.mul_assoc]
      _ = Matrix.trace ((E ^ 2 * S * E ^ 2) * S) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace (E ^ 2 * S * E ^ 2 * S) := rfl
  have h10 : Matrix.trace (E * S * E ^ 2 * S * E) =
      Matrix.trace (E ^ 2 * S * E ^ 2 * S) := by
    calc
      Matrix.trace (E * S * E ^ 2 * S * E) =
          Matrix.trace ((E * S * E ^ 2 * S) * E) := rfl
      _ = Matrix.trace (E * (E * S * E ^ 2 * S)) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace (E ^ 2 * S * E ^ 2 * S) := by
        simp only [pow_two, Matrix.mul_assoc]
  have h11 : Matrix.trace (S * E * S * E * S * E ^ 2) =
      Matrix.trace (E ^ 2 * S * E * S * E * S) := by
    calc
      Matrix.trace (S * E * S * E * S * E ^ 2) =
          Matrix.trace ((S * E * S * E * S) * E ^ 2) := by
            simp only [Matrix.mul_assoc]
      _ = Matrix.trace (E ^ 2 * (S * E * S * E * S)) :=
        Matrix.trace_mul_comm _ _
      _ = Matrix.trace (E ^ 2 * S * E * S * E * S) := by
        simp only [Matrix.mul_assoc]
  have h12 : Matrix.trace (E * S * E * S * E * S * E) =
      Matrix.trace (E ^ 2 * S * E * S * E * S) := by
    calc
      Matrix.trace (E * S * E * S * E * S * E) =
          Matrix.trace ((E * S * E * S * E * S) * E) := by
            rfl
      _ = Matrix.trace (E * (E * S * E * S * E * S)) :=
        Matrix.trace_mul_comm _ _
      _ = Matrix.trace (E ^ 2 * S * E * S * E * S) := by
        simp only [pow_two, Matrix.mul_assoc]
  have h13 : Matrix.trace (S * E ^ 2 * S * E * S * E) =
      Matrix.trace (E ^ 2 * S * E * S * E * S) := by
    calc
      Matrix.trace (S * E ^ 2 * S * E * S * E) =
          Matrix.trace (S * (E ^ 2 * S * E * S * E)) := by
            simp only [Matrix.mul_assoc]
      _ = Matrix.trace ((E ^ 2 * S * E * S * E) * S) :=
        Matrix.trace_mul_comm _ _
      _ = Matrix.trace (E ^ 2 * S * E * S * E * S) := by
        rfl
  have h14 : Matrix.trace (S * E * S * E ^ 2 * S * E) =
      Matrix.trace (E ^ 2 * S * E * S * E * S) :=
    trace_cycle_ses_e2_se_h11_block E S
  have h15 : Matrix.trace (S * E * S * E * S * E * S * E) =
      Matrix.trace ((E * S) ^ 4) := by
    calc
      Matrix.trace (S * E * S * E * S * E * S * E) =
          Matrix.trace (S * ((E * S) ^ 3 * E)) := by
            simp only [pow_succ, pow_zero, Matrix.one_mul, Matrix.mul_assoc]
      _ = Matrix.trace (((E * S) ^ 3 * E) * S) :=
        Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((E * S) ^ 4) := by
        simp only [pow_succ, pow_zero, Matrix.one_mul, Matrix.mul_assoc]
  change Matrix.trace (h11BlockFourthJacobiMatrix W E) = _
  rw [hExpand]
  simp only [Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]
  ring

/-- The exact deterministic inequality needed after the Cayley reduction.

The hypotheses `S > 0`, `J S J = S⁻¹`, and `[J,E]=0` coming from the COE
block matrix are deliberately not mentioned here: this lemma records that the
single displayed trace inequality is sufficient for nonpositivity of the
fourth Jacobi jet. -/
theorem re_trace_h11BlockFourthJacobiMatrix_half_one_add_nonpos_of_cayley_ineq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E S : Matrix ι ι ℂ)
    (hineq :
      4 * (Matrix.trace (E ^ 3 * S * E * S)).re ≤
        (Matrix.trace (E ^ 4)).re +
          3 * (Matrix.trace ((E * S) ^ 4)).re) :
    (Matrix.trace
      (h11BlockFourthJacobiMatrix (((2 : ℂ)⁻¹) • (1 + S)) E)).re ≤ 0 := by
  rw [trace_h11BlockFourthJacobiMatrix_half_one_add]
  norm_num [Complex.mul_re, Complex.add_re, Complex.sub_re]
  linarith

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
