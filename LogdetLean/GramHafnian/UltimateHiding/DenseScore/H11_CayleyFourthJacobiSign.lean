import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H11_CayleySquareRoot
import Mathlib.Tactic

/-!
# The H11 Cayley identities imply the fourth Jacobi sign

This file composes the checked involution sum-of-squares identity, its
square-root congruence bridge, and the three-word reduction of the complete
five-term Jacobi polynomial.  The only remaining work after this lemma is to
construct the displayed Cayley and grading identities for the literal doubled
COE block.
-/

open scoped ComplexOrder MatrixOrder

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- A positive Cayley matrix with the grading inversion symmetry makes the
real part of the complete fourth Jacobi trace nonpositive. -/
theorem trace_h11BlockFourthJacobiMatrix_re_nonpos_of_cayley_grading
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E S J : Matrix ι ι ℂ)
    (hE : E.IsHermitian) (hS : S.PosDef) (hJ : J.IsHermitian)
    (hJ2 : J * J = 1) (hJSJ : J * S * J = S⁻¹)
    (hEJ : E * J = J * E) :
    (Matrix.trace
      (h11BlockFourthJacobiMatrix
        (((2 : ℂ)⁻¹) • (1 + S)) E)).re ≤ 0 := by
  let R : Matrix ι ι ℂ := CFC.sqrt S
  have hR : R.IsHermitian := by
    rw [Matrix.IsHermitian]
    exact (CFC.sqrt_nonneg S).isSelfAdjoint
  have hRsq : R ^ 2 = S := by
    rw [pow_two]
    simpa only [R] using
      CFC.sqrt_mul_sqrt_self S hS.posSemidef.nonneg
  have hRJR : R * J * R = J := by
    simpa only [R] using
      cfc_sqrt_mul_grading_mul_cfc_sqrt_eq_grading
        S J hS hJ hJ2 hJSJ
  have hineq :=
    four_trace_E_cube_Rsq_E_Rsq_le_of_grading_square_root
      E R J hE hR hJ hJ2 hRJR hEJ
  rw [hRsq] at hineq
  have hreduce :
      (Matrix.trace
        (h11BlockFourthJacobiMatrix
          (((2 : ℂ)⁻¹) • (1 + S)) E)).re =
        -2 * (Matrix.trace (E ^ 4)).re +
          8 * (Matrix.trace (E ^ 3 * S * E * S)).re -
          6 * (Matrix.trace ((E * S) ^ 4)).re := by
    rw [trace_h11BlockFourthJacobiMatrix_half_one_add]
    norm_num [Complex.add_re, Complex.sub_re, Complex.mul_re]
  rw [hreduce]
  linarith

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
