import LogdetLean.GramHafnian.UltimateHiding.Dense.CentralOneColumnCommutation
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ClassicalCOEExternal
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Data.Sym.Card
import Mathlib.Data.Sym.Sym2.Order
import Mathlib.Tactic

/-!
# Scalar transport on complex-symmetric coordinates

This file records the elementary finite-dimensional transport facts needed
to rewrite the central matrix path on independent complex-symmetric
coordinates.  In particular, it identifies the real dimension and the exact
Lebesgue Jacobian of scalar multiplication.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.H3H4Central

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.UltimateHiding.DenseScore

/-- The central congruence is scalar multiplication by `exp (2s)`. -/
theorem concreteCentralMatrixUpdate_eq_exp_two_smul
    (N : ℕ) (s : ℝ) (A : ConcreteMatrixState N) :
    concreteCentralMatrixUpdate N s A =
      (((Real.exp (2 * s) : ℝ) : ℂ)) • A := by
  rw [concreteCentralMatrixUpdate_eq_smul]
  congr 1
  norm_cast
  rw [show 2 * s = s + s by ring, Real.exp_add, pow_two]

/-- Reconstructing a symmetric matrix commutes with complex scalar
multiplication of its independent coordinates. -/
theorem complexSymmetricMatrixOfCoordinates_smul
    {N : ℕ} (z : ℂ) (x : ComplexSymmetricCoordinates N) :
    complexSymmetricMatrixOfCoordinates (z • x) =
      z • complexSymmetricMatrixOfCoordinates x := by
  ext i j
  simp only [complexSymmetricMatrixOfCoordinates, Pi.smul_apply,
    Matrix.smul_apply]
  split <;> rfl

/-- The upper-triangular coordinate index has `N choose 2` plus the
diagonal, equivalently `(N+1) choose 2`, entries. -/
theorem card_complexSymmetricCoordinateIndex (N : ℕ) :
    Fintype.card (ComplexSymmetricCoordinateIndex N) = Nat.choose (N + 1) 2 := by
  calc
    _ = Fintype.card (Sym2 (Fin N)) :=
      (Fintype.card_congr (Sym2.sortEquiv (α := Fin N))).symm
    _ = _ := by simpa using (Sym2.card (α := Fin N))

/-- Elementary doubled-binomial identity used in the real-dimension
calculation. -/
theorem nat_choose_succ_two_mul_two (N : ℕ) :
    Nat.choose (N + 1) 2 * 2 = N * (N + 1) := by
  rw [Nat.choose_two_right]
  rw [Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self (N + 1))]
  simp
  ring

/-- The real dimension of the independent complex-symmetric coordinate
space is `N(N+1)`. -/
theorem finrank_complexSymmetricCoordinates (N : ℕ) :
    Module.finrank ℝ (ComplexSymmetricCoordinates N) = N * (N + 1) := by
  rw [Module.finrank_pi_fintype]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [show Module.finrank ℝ ℂ = 2 by simp,
    card_complexSymmetricCoordinateIndex]
  change Nat.choose (N + 1) 2 * 2 = N * (N + 1)
  exact nat_choose_succ_two_mul_two N

/-- Product Lebesgue measure on the independent complex-symmetric
coordinates is an additive Haar measure. -/
theorem complexSymmetricCoordinateVolume_isAddHaarMeasure (N : ℕ) :
    (complexSymmetricCoordinateVolume N).IsAddHaarMeasure := by
  unfold complexSymmetricCoordinateVolume
  infer_instance

/-- Exact Jacobian for real scalar multiplication on independent
complex-symmetric coordinates. -/
theorem map_smul_complexSymmetricCoordinateVolume
    (N : ℕ) {r : ℝ} (hr : r ≠ 0) :
    Measure.map (fun x : ComplexSymmetricCoordinates N ↦ r • x)
        (complexSymmetricCoordinateVolume N) =
      ENNReal.ofReal (abs (r ^ (N * (N + 1)))⁻¹) •
        complexSymmetricCoordinateVolume N := by
  letI : (complexSymmetricCoordinateVolume N).IsAddHaarMeasure :=
    complexSymmetricCoordinateVolume_isAddHaarMeasure N
  simpa [finrank_complexSymmetricCoordinates] using
    (Measure.map_addHaar_smul (complexSymmetricCoordinateVolume N) hr)

/-- Integral transport under real scalar multiplication on independent
complex-symmetric coordinates. -/
theorem integral_comp_smul_complexSymmetricCoordinateVolume
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (N : ℕ) (f : ComplexSymmetricCoordinates N → F) (r : ℝ) :
    ∫ x, f (r • x) ∂complexSymmetricCoordinateVolume N =
      |(r ^ (N * (N + 1)))⁻¹| •
        ∫ x, f x ∂complexSymmetricCoordinateVolume N := by
  letI : (complexSymmetricCoordinateVolume N).IsAddHaarMeasure :=
    complexSymmetricCoordinateVolume_isAddHaarMeasure N
  simpa [finrank_complexSymmetricCoordinates] using
    (Measure.integral_comp_smul (complexSymmetricCoordinateVolume N) f r)

end

end LogdetLean.GramHafnian.UltimateHiding.H3H4Central
