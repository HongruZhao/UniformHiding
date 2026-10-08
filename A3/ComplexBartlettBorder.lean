import A3.ComplexBartlettSchur
import A3.ComplexGaussianGramLaplace
import A3.WishartCholeskyBlock

open Matrix
open scoped BigOperators ComplexOrder

noncomputable section
namespace A3Research

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem trace_complexMatrixBorder {d : ℕ}
    (theta : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) (c : ℂ)
    (b : Fin d → ℂ) (D : Matrix (Fin d) (Fin d) ℂ) :
    (theta * complexMatrixBorder c b D).trace = theta 0 0 * c +
      (∑ i, theta 0 i.succ * star (b i)) +
      (∑ i, theta i.succ 0 * b i) + (complexMatrixTail theta * D).trace := by
  change (∑ i, ∑ j, theta i j * complexMatrixBorder c b D j i) = _
  rw [Fin.sum_univ_succ]
  simp only [Fin.sum_univ_succ, complexMatrixBorder, Matrix.of_apply,
    Fin.cons_zero, Fin.cons_succ]
  rw [Finset.sum_add_distrib]
  change (theta 0 0 * c + ∑ i, theta 0 i.succ * star (b i)) +
    ((∑ i, theta i.succ 0 * b i) + ∑ i, ∑ j, theta i.succ j.succ * D j i) = _
  simp only [complexMatrixTail, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.submatrix,
    Matrix.of_apply]
  ring

theorem trace_hermitian_complexMatrixBorder_re {d : ℕ}
    {theta : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ} (htheta : theta.IsHermitian)
    (c : ℝ) (b : Fin d → ℂ) (D : Matrix (Fin d) (Fin d) ℂ) :
    ((theta * complexMatrixBorder (c : ℂ) b D).trace).re = (theta 0 0).re * c +
      2 * (star (fun i ↦ theta 0 i.succ) ⬝ᵥ b).re + (complexMatrixTail theta * D).trace.re := by
  rw [trace_complexMatrixBorder]
  have hleft : (∑ i, theta 0 i.succ * star (b i)) =
      star (star (fun i ↦ theta 0 i.succ) ⬝ᵥ b) := by
    simp only [dotProduct, star_sum, star_mul, Pi.star_apply, star_star]
    exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
  have hright : (∑ i, theta i.succ 0 * b i) =
      star (fun i ↦ theta 0 i.succ) ⬝ᵥ b := by
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun t ↦ t * b i) (htheta.apply i.succ 0).symm
  rw [hleft, hright]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, Complex.star_def, Complex.conj_re]
  ring

theorem trace_complex_rankOne {d : ℕ} (theta : Matrix (Fin d) (Fin d) ℂ) (z : Fin d → ℂ) :
    (theta * Matrix.vecMulVec (star z) z).trace = star z ⬝ᵥ (theta.transpose *ᵥ z) := by
  change (∑ i, ∑ j, theta i j * (star (z j) * z i)) =
    ∑ i, star (z i) * ∑ j, theta j i * z j
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem wishartGramMatrix_cons_succ_zero {d : ℕ} (p : ℝ) (z : Fin d → ℂ)
    (y : HermitianCoordinates d ℂ) (i : Fin d) :
    (wishartCholeskyMatrix (wishartCoordinatesCons p z y) *
      (wishartCholeskyMatrix (wishartCoordinatesCons p z y)).conjTranspose) i.succ 0 =
        (Real.sqrt p : ℂ) * star (z i) := by
  rw [Matrix.mul_apply, Fin.sum_univ_succ]
  simp only [Matrix.conjTranspose_apply, wishartCholeskyMatrix_cons_succ_zero,
    wishartCholeskyMatrix_cons_zero_zero, wishartCholeskyMatrix_cons_zero_succ,
    star_zero, mul_zero, Finset.sum_const_zero, add_zero,
    RCLike.star_def, RCLike.conj_ofReal]
  ring
  rfl

theorem wishartGramCoordinates_cons_complexBorder {d : ℕ} (p : ℝ) (z : Fin d → ℂ)
    (y : HermitianCoordinates d ℂ) (hp : 0 ≤ p) :
    hermitianMatrixOfCoordinates (wishartGramCoordinates (wishartCoordinatesCons p z y)) =
      complexMatrixBorder (p : ℂ) (Real.sqrt p • z)
        (hermitianMatrixOfCoordinates (wishartGramCoordinates y) + Matrix.vecMulVec (star z) z) := by
  rw [hermitianMatrixOf_wishartGramCoordinates, hermitianMatrixOf_wishartGramCoordinates]
  ext i j
  refine Fin.cases ?_ (fun i ↦ ?_) i
  · refine Fin.cases ?_ (fun j ↦ ?_) j
    · simpa [complexMatrixBorder] using wishartGramMatrix_cons_zero_zero p z y hp
    · simpa [complexMatrixBorder, RCLike.real_smul_eq_coe_mul] using
        wishartGramMatrix_cons_zero_succ p z y j
  · refine Fin.cases ?_ (fun j ↦ ?_) j
    · rw [wishartGramMatrix_cons_succ_zero]
      simp [complexMatrixBorder, RCLike.real_smul_eq_coe_mul]
    · simpa [complexMatrixBorder, Matrix.vecMulVec, add_comm] using
        wishartGramMatrix_cons_succ_succ p z y i j

theorem complexBartlettBorderTilt_factor {d : ℕ}
    {theta : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ} (htheta : theta.IsHermitian)
    (p : ℝ) (z : Fin d → ℂ) (y : HermitianCoordinates d ℂ) (hp : 0 ≤ p) :
    Real.exp ((theta * hermitianMatrixOfCoordinates
      (wishartGramCoordinates (wishartCoordinatesCons p z y))).trace).re =
      complexBartlettColumnTilt (theta 0 0).re (complexMatrixTail theta).transpose
        (fun i ↦ theta 0 i.succ) p z *
        Real.exp ((complexMatrixTail theta * hermitianMatrixOfCoordinates
          (wishartGramCoordinates y)).trace).re := by
  rw [wishartGramCoordinates_cons_complexBorder p z y hp,
    trace_hermitian_complexMatrixBorder_re htheta, Matrix.mul_add, Matrix.trace_add,
    Complex.add_re, trace_complex_rankOne, dotProduct_smul, Complex.smul_re,
    smul_eq_mul, complexBartlettColumnTilt, ← Real.exp_add]
  congr 1
  ring

end A3Research
