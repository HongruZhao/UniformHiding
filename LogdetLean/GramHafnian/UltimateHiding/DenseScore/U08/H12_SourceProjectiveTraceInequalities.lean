import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.BetaPrimeTraceTwoCounterexample
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic

/-!
# Pointwise projective trace inequalities on the Gaussian source

The beta-prime source matrix is trace-similar to a positive-semidefinite
sandwich.  Consequently its two first power sums satisfy both
`T2 <= T1^2` and `T1^2 <= N*T2`.  Together these inequalities retain the
projective factor `(N-1)/N` instead of discarding it.
-/

open scoped BigOperators MatrixOrder

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08

noncomputable section

open Matrix Unitary
open LogdetLean.GramHafnian.Wishart

/-- For a real positive-semidefinite matrix, the sum of squared eigenvalues
is bounded by the square of their sum. -/
theorem trace_sq_le_sq_trace_of_posSemidef_real
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A.PosSemidef) :
    Matrix.trace (A ^ 2) ≤ Matrix.trace A ^ 2 := by
  let hH : A.IsHermitian := hA.isHermitian
  have htrace : Matrix.trace A = ∑ i, hH.eigenvalues i :=
    hH.trace_eq_sum_eigenvalues
  have htrace2 : Matrix.trace (A ^ 2) =
      ∑ i, hH.eigenvalues i ^ 2 := by
    conv_lhs => rw [hH.spectral_theorem]
    rw [← map_pow]
    rw [conjStarAlgAut_apply, Matrix.trace_mul_cycle,
      Unitary.coe_star_mul_self, one_mul]
    rw [Matrix.diagonal_pow, Matrix.trace_diagonal]
    rfl
  rw [htrace, htrace2]
  exact Finset.sum_sq_le_sq_sum_of_nonneg
    (fun i _ ↦ hA.eigenvalues_nonneg i)

/-- A product of two positive-semidefinite real matrices is trace-similar to
the positive-semidefinite sandwich `sqrt(C) * A * sqrt(C)`. -/
theorem trace_mul_sq_le_sq_trace_mul
    {n : Type*} [Fintype n] [DecidableEq n]
    (C A : Matrix n n ℝ) (hC : C.PosSemidef) (hA : A.PosSemidef) :
    Matrix.trace ((C * A) ^ 2) ≤ Matrix.trace (C * A) ^ 2 := by
  let S : Matrix n n ℝ := CFC.sqrt C
  let P : Matrix n n ℝ := S * A * S
  have hS : S.PosSemidef := by
    exact (CFC.sqrt_nonneg C).posSemidef
  have hSstar : Sᴴ = S := hS.isHermitian.eq
  have hP : P.PosSemidef := by
    have h := hA.mul_mul_conjTranspose_same S
    rw [hSstar] at h
    exact h
  have hSS : S * S = C := by
    simpa only [S, pow_two] using CFC.sq_sqrt C
  have htrace : Matrix.trace P = Matrix.trace (C * A) := by
    calc
      Matrix.trace P = Matrix.trace ((S * A) * S) := by rfl
      _ = Matrix.trace (S * S * A) := Matrix.trace_mul_cycle S A S
      _ = Matrix.trace (C * A) := by rw [hSS]
  have htrace2 : Matrix.trace (P ^ 2) = Matrix.trace ((C * A) ^ 2) := by
    calc
      Matrix.trace (P ^ 2) =
          Matrix.trace ((S * A * S * S * A) * S) := by
            simp only [P, pow_two, mul_assoc]
      _ = Matrix.trace (S * (A * S * S * A) * S) := by
        simp only [mul_assoc]
      _ = Matrix.trace (S * S * (A * S * S * A)) :=
        Matrix.trace_mul_cycle S (A * S * S * A) S
      _ = Matrix.trace ((S * S) * A * (S * S) * A) := by
        simp only [mul_assoc]
      _ = Matrix.trace (C * A * C * A) := by rw [hSS]
      _ = Matrix.trace ((C * A) ^ 2) := by simp only [pow_two, mul_assoc]
  rw [← htrace, ← htrace2]
  exact trace_sq_le_sq_trace_of_posSemidef_real P hP

/-- Source-level reverse trace inequality `T2 <= T1^2`. -/
theorem betaPrimeTraceTwoSource_le_traceOneSource_sq
    {N K : ℕ} (hc : 0 ≤ concreteCOEExponent N K)
    (source : BetaPrimeGaussianSource N K) :
    betaPrimeTraceTwoSource N K source ≤
      betaPrimeTraceOneSource N K source ^ 2 := by
  let C := scaledInverseWishartDenominator N K source
  let A := realWishartGram source.1
  have hC : C.PosSemidef := by
    dsimp only [C, scaledInverseWishartDenominator]
    exact (realWishartGram_inv_posSemidef source.2).smul hc
  have hA : A.PosSemidef := realWishartGram_posSemidef source.1
  have h := trace_mul_sq_le_sq_trace_mul C A hC hA
  simpa only [C, A,
    betaPrimeTraceOneSource_eq_scaledInverseWishart_trace,
    betaPrimeTraceTwoSource_eq_scaledInverseWishart_trace,
    pow_two, mul_assoc] using h

/-- The traceless bracket is nonnegative and retains the exact projective
factor `(N-1)/N` against the second trace. -/
theorem betaPrimeTracelessSourceBracket_nonneg_le_projectiveTraceTwo
    {N K : ℕ} (hN : 1 ≤ N) (hc : 0 ≤ concreteCOEExponent N K)
    (source : BetaPrimeGaussianSource N K) :
    0 ≤ betaPrimeTraceTwoSource N K source -
          (N : ℝ)⁻¹ * betaPrimeTraceOneSource N K source ^ 2 ∧
      betaPrimeTraceTwoSource N K source -
          (N : ℝ)⁻¹ * betaPrimeTraceOneSource N K source ^ 2 ≤
        (((N : ℝ) - 1) / (N : ℝ)) *
          betaPrimeTraceTwoSource N K source := by
  let n : ℝ := N
  let tOne : ℝ := betaPrimeTraceOneSource N K source
  let tTwo : ℝ := betaPrimeTraceTwoSource N K source
  have hn : 0 < n := by
    dsimp only [n]
    exact_mod_cast (show 0 < N by omega)
  have hdim : tOne ^ 2 ≤ n * tTwo := by
    simpa only [n, tOne, tTwo] using
      betaPrimeTraceOneSource_sq_le_dimension_mul_traceTwoSource hc source
  have hrev : tTwo ≤ tOne ^ 2 := by
    simpa only [tOne, tTwo] using
      betaPrimeTraceTwoSource_le_traceOneSource_sq hc source
  have htTwo : 0 ≤ tTwo := by
    nlinarith [sq_nonneg tOne]
  have hscaledLower : n⁻¹ * tOne ^ 2 ≤ tTwo := by
    calc
      n⁻¹ * tOne ^ 2 ≤ n⁻¹ * (n * tTwo) :=
        mul_le_mul_of_nonneg_left hdim (inv_nonneg.mpr hn.le)
      _ = tTwo := by field_simp [ne_of_gt hn]
  have hscaledUpper : n⁻¹ * tTwo ≤ n⁻¹ * tOne ^ 2 :=
    mul_le_mul_of_nonneg_left hrev (inv_nonneg.mpr hn.le)
  change 0 ≤ tTwo - n⁻¹ * tOne ^ 2 ∧
    tTwo - n⁻¹ * tOne ^ 2 ≤ ((n - 1) / n) * tTwo
  constructor
  · exact sub_nonneg.mpr hscaledLower
  · calc
      tTwo - n⁻¹ * tOne ^ 2 ≤ tTwo - n⁻¹ * tTwo :=
        sub_le_sub_left hscaledUpper tTwo
      _ = ((n - 1) / n) * tTwo := by
        field_simp [ne_of_gt hn]

/-- Squared form used by the H12 radial integration. -/
theorem betaPrimeTracelessSourceBracket_sq_le_projectiveTraceTwo_sq
    {N K : ℕ} (hN : 1 ≤ N) (hc : 0 ≤ concreteCOEExponent N K)
    (source : BetaPrimeGaussianSource N K) :
    (betaPrimeTraceTwoSource N K source -
        (N : ℝ)⁻¹ * betaPrimeTraceOneSource N K source ^ 2) ^ 2 ≤
      ((((N : ℝ) - 1) / (N : ℝ)) *
        betaPrimeTraceTwoSource N K source) ^ 2 := by
  have h := betaPrimeTracelessSourceBracket_nonneg_le_projectiveTraceTwo
    hN hc source
  have hNnonneg : 0 ≤ ((N : ℝ) - 1) / (N : ℝ) := by
    have hn : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    have hnone : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    exact div_nonneg (by linarith) hn.le
  have htTwo : 0 ≤ betaPrimeTraceTwoSource N K source := by
    have hdim := betaPrimeTraceOneSource_sq_le_dimension_mul_traceTwoSource hc source
    have hn : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    nlinarith [sq_nonneg (betaPrimeTraceOneSource N K source)]
  exact (sq_le_sq₀ h.1 (mul_nonneg hNnonneg htTwo)).2 h.2

/-- In dimension one the projective bracket vanishes pointwise. -/
theorem betaPrimeTracelessSourceBracket_eq_zero_of_dimension_one
    {K : ℕ} (hc : 0 ≤ concreteCOEExponent 1 K)
    (source : BetaPrimeGaussianSource 1 K) :
    betaPrimeTraceTwoSource 1 K source -
        (1 : ℝ)⁻¹ * betaPrimeTraceOneSource 1 K source ^ 2 = 0 := by
  have h := betaPrimeTracelessSourceBracket_nonneg_le_projectiveTraceTwo
    (N := 1) (K := K) (by omega) hc source
  norm_num at h ⊢
  linarith

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08
