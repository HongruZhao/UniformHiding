import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H11_CayleyInvolutionBridge
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic

/-!
# Positive Cayley square roots preserve the grading form

This module closes the spectral-calculus hypothesis left explicit in
`H11_CayleyInvolutionBridge`.  If a positive-definite matrix `S` obeys
`J S J = S⁻¹` for a Hermitian involution `J`, then its canonical positive
square root `R = sqrt S` obeys `R J R = J`.
-/

open scoped ComplexOrder MatrixOrder

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- The positive square root of a positive Cayley matrix preserves the
indefinite grading form. -/
theorem cfc_sqrt_mul_grading_mul_cfc_sqrt_eq_grading
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S J : Matrix ι ι ℂ)
    (hS : S.PosDef) (hJ : J.IsHermitian)
    (hJ2 : J * J = 1) (hJSJ : J * S * J = S⁻¹) :
    CFC.sqrt S * J * CFC.sqrt S = J := by
  let R : Matrix ι ι ℂ := CFC.sqrt S
  have hRnonneg : 0 ≤ R := by
    exact CFC.sqrt_nonneg S
  have hRsq : R * R = S := by
    simpa only [R] using CFC.sqrt_mul_sqrt_self S hS.posSemidef.nonneg
  have hRunit : IsUnit R := by
    exact (CFC.isUnit_sqrt_iff S hS.posSemidef.nonneg).mpr hS.isUnit
  letI : Invertible R := hRunit.invertible
  have hJRJnonneg : 0 ≤ J * R * J := by
    exact hJ.isSelfAdjoint.conjugate_nonneg hRnonneg
  have hJRJsq : (J * R * J) * (J * R * J) = S⁻¹ := by
    calc
      (J * R * J) * (J * R * J) = J * (R * R) * J := by
        rw [show (J * R * J) * (J * R * J) =
          J * R * (J * J) * R * J by noncomm_ring, hJ2]
        noncomm_ring
      _ = J * S * J := by rw [hRsq]
      _ = S⁻¹ := hJSJ
  have hJRJsqrt : CFC.sqrt S⁻¹ = J * R * J := by
    exact CFC.sqrt_unique hJRJsq hJRJnonneg
  have hRinv : R⁻¹ = CFC.sqrt S⁻¹ := by
    simpa only [R] using hS.posSemidef.inv_sqrt
  have hJRJinv : J * R * J = R⁻¹ := by
    rw [← hJRJsqrt, hRinv]
  change R * J * R = J
  calc
    R * J * R = J * (J * R * J) * R := by
      symm
      calc
        J * (J * R * J) * R = (J * J) * R * J * R := by noncomm_ring
        _ = R * J * R := by rw [hJ2, Matrix.one_mul]
    _ = J * R⁻¹ * R := by rw [hJRJinv]
    _ = J := by
      rw [show J * R⁻¹ * R = J * (R⁻¹ * R) by
        simp only [Matrix.mul_assoc], Matrix.inv_mul_of_invertible,
        Matrix.mul_one]

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
