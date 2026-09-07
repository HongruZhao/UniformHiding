import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H13_BilinearSupportTraceLedger
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.PositiveTraceMomentInternal
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Tactic

/-!
# Trace comparison for the H13 cross-bilinear factors

The cross terms pair `T` with `(I+2Z)T`.  Bounding their two `L4` norms by
their sum would create a fifth radial degree.  Instead we prove the exact
Gram comparison

`Tr(((I+2Z)T)((I+2Z)T)^*) <= (1+2 Tr Z)^2 Tr(TT^*)`.

This preserves radial degree four after multiplication by the outer first
score.
-/

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open Matrix Unitary
open LogdetLean.GramHafnian.UltimateHiding.Dense

set_option maxHeartbeats 2400000

private theorem sum_cube_le_sum_mul_sum_sq_h13
    {n : Type*} [Fintype n] (x : n → ℝ) (hx : ∀ i, 0 ≤ x i) :
    ∑ i, x i ^ 3 ≤ (∑ i, x i) * (∑ i, x i ^ 2) := by
  have hsum : 0 ≤ ∑ i, x i := Finset.sum_nonneg fun i _ => hx i
  calc
    ∑ i, x i ^ 3 ≤ ∑ i, (∑ j, x j) * x i ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      have hxi : x i ≤ ∑ j, x j :=
        Finset.single_le_sum (fun j _ => hx j) (Finset.mem_univ i)
      nlinarith [sq_nonneg (x i)]
    _ = (∑ i, x i) * (∑ i, x i ^ 2) := by
      rw [Finset.mul_sum]

private theorem sum_four_le_sum_sq_mul_sum_sq_h13
    {n : Type*} [Fintype n] (x : n → ℝ) (hx : ∀ i, 0 ≤ x i) :
    ∑ i, x i ^ 4 ≤ (∑ i, x i) ^ 2 * (∑ i, x i ^ 2) := by
  have hsum : 0 ≤ ∑ i, x i := Finset.sum_nonneg fun i _ => hx i
  calc
    ∑ i, x i ^ 4 ≤ ∑ i, (∑ j, x j) ^ 2 * x i ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      have hxi : x i ≤ ∑ j, x j :=
        Finset.single_le_sum (fun j _ => hx j) (Finset.mem_univ i)
      have hsqi := mul_self_le_mul_self (hx i) hxi
      nlinarith [sq_nonneg (x i)]
    _ = (∑ i, x i) ^ 2 * (∑ i, x i ^ 2) := by
      rw [Finset.mul_sum]

/-- For a PSD matrix, the third trace power is bounded by the product of its
first two trace powers. -/
theorem posSemidef_trace_cube_re_le_trace_re_mul_trace_square_re_h13
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.PosSemidef) :
    (Matrix.trace (A ^ 3)).re ≤
      (Matrix.trace A).re * (Matrix.trace (A ^ 2)).re := by
  let hH : A.IsHermitian := hA.isHermitian
  have hspectral := hH.spectral_theorem
  have htrace : Matrix.trace A = ∑ i, (hH.eigenvalues i : ℂ) :=
    hH.trace_eq_sum_eigenvalues
  have htrace2 : Matrix.trace (A ^ 2) =
      ∑ i, ((hH.eigenvalues i : ℂ) ^ 2) := by
    conv_lhs => rw [hspectral]
    rw [← map_pow, conjStarAlgAut_apply, Matrix.trace_mul_cycle,
      Unitary.coe_star_mul_self, one_mul]
    rw [Matrix.diagonal_pow, Matrix.trace_diagonal]
    rfl
  have htrace3 : Matrix.trace (A ^ 3) =
      ∑ i, ((hH.eigenvalues i : ℂ) ^ 3) := by
    conv_lhs => rw [hspectral]
    rw [← map_pow, conjStarAlgAut_apply, Matrix.trace_mul_cycle,
      Unitary.coe_star_mul_self, one_mul]
    rw [Matrix.diagonal_pow, Matrix.trace_diagonal]
    rfl
  rw [htrace, htrace2, htrace3]
  simp only [Complex.re_sum]
  norm_cast
  exact sum_cube_le_sum_mul_sum_sq_h13 _ hA.eigenvalues_nonneg

/-- The fourth trace power is bounded by `Tr(A)^2 Tr(A^2)`. -/
theorem posSemidef_trace_four_re_le_trace_re_sq_mul_trace_square_re_h13
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.PosSemidef) :
    (Matrix.trace (A ^ 4)).re ≤
      (Matrix.trace A).re ^ 2 * (Matrix.trace (A ^ 2)).re := by
  let hH : A.IsHermitian := hA.isHermitian
  have hspectral := hH.spectral_theorem
  have htrace : Matrix.trace A = ∑ i, (hH.eigenvalues i : ℂ) :=
    hH.trace_eq_sum_eigenvalues
  have htrace2 : Matrix.trace (A ^ 2) =
      ∑ i, ((hH.eigenvalues i : ℂ) ^ 2) := by
    conv_lhs => rw [hspectral]
    rw [← map_pow, conjStarAlgAut_apply, Matrix.trace_mul_cycle,
      Unitary.coe_star_mul_self, one_mul]
    rw [Matrix.diagonal_pow, Matrix.trace_diagonal]
    rfl
  have htrace4 : Matrix.trace (A ^ 4) =
      ∑ i, ((hH.eigenvalues i : ℂ) ^ 4) := by
    conv_lhs => rw [hspectral]
    rw [← map_pow, conjStarAlgAut_apply, Matrix.trace_mul_cycle,
      Unitary.coe_star_mul_self, one_mul]
    rw [Matrix.diagonal_pow, Matrix.trace_diagonal]
    rfl
  rw [htrace, htrace2, htrace4]
  simp only [Complex.re_sum]
  norm_cast
  exact sum_four_le_sum_sq_mul_sum_sq_h13 _ hA.eigenvalues_nonneg

/-- The Gram of `(I+2Z)T` is at most `(1+2 Tr Z)^2` times the Gram of `T`.
This is the degree-preserving comparison used in the mixed H13 Holder step. -/
theorem trace_h13LedgerOneAddTwoZMulT_gram_re_le_factor_mul_T_gram_h13
    {N : ℕ} (C : ConcreteMatrixState N)
    (hsupport : coeCornerSupport C) :
    (Matrix.trace
      ((((1 : ConcreteMatrixState N) + 2 • h13LedgerZ C) * h13LedgerT C) *
        (((1 : ConcreteMatrixState N) + 2 • h13LedgerZ C) *
          h13LedgerT C).conjTranspose)).re ≤
      (1 + 2 * (Matrix.trace (h13LedgerZ C)).re) ^ 2 *
        (Matrix.trace
          (h13LedgerT C * (h13LedgerT C).conjTranspose)).re := by
  let Z := h13LedgerZ C
  let x := (Matrix.trace Z).re
  let y := (Matrix.trace (Z ^ 2)).re
  let z := (Matrix.trace (Z ^ 3)).re
  let q := (Matrix.trace (Z ^ 4)).re
  have hZ : Z.PosSemidef := by
    simpa only [Z] using h13LedgerZ_posSemidef C hsupport
  have hx : 0 ≤ x := (Complex.nonneg_iff.mp hZ.trace_nonneg).1
  have hy : 0 ≤ y := by
    exact (Complex.nonneg_iff.mp (hZ.pow 2).trace_nonneg).1
  have hz : 0 ≤ z := by
    exact (Complex.nonneg_iff.mp (hZ.pow 3).trace_nonneg).1
  have hq : 0 ≤ q := by
    exact (Complex.nonneg_iff.mp (hZ.pow 4).trace_nonneg).1
  have hyx : y ≤ x ^ 2 := by
    simpa only [x, y] using
      posSemidef_trace_square_re_le_trace_re_sq Z hZ
  have hzy : z ≤ x * y := by
    simpa only [x, y, z] using
      posSemidef_trace_cube_re_le_trace_re_mul_trace_square_re_h13 Z hZ
  have hqy : q ≤ x ^ 2 * y := by
    simpa only [x, y, q] using
      posSemidef_trace_four_re_le_trace_re_sq_mul_trace_square_re_h13 Z hZ
  rw [trace_h13LedgerOneAddTwoZMulT_gram_re_eq C hsupport,
    trace_h13LedgerT_gram_re_eq C hsupport]
  change x + 5 * y + 8 * z + 4 * q ≤ (1 + 2 * x) ^ 2 * (x + y)
  nlinarith [mul_nonneg hx (sub_nonneg.mpr hyx)]

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
