import A3.BetaMatrixStatistic

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section
namespace A3Research

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem complex_cfc_sqrt_smul {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosSemidef) {c : ℝ} (hc : 0 ≤ c) :
    CFC.sqrt (c • A) = Real.sqrt c • CFC.sqrt A := by
  have hs : (CFC.sqrt A).PosSemidef := (CFC.sqrt_nonneg A).posSemidef
  apply (CFC.sqrt_eq_iff (c • A) (Real.sqrt c • CFC.sqrt A)
    (hA.smul hc).nonneg (hs.smul (Real.sqrt_nonneg c)).nonneg).mpr
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Real.mul_self_sqrt hc, CFC.sqrt_mul_sqrt_self A hA.nonneg]

theorem complex_jacobiMatrix_commonScale {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℂ) (hsum : (A + B).PosDef)
    {c : ℝ} (hc : 0 < c) :
    (CFC.sqrt (c • A + c • B))⁻¹ * (c • A) *
        ((CFC.sqrt (c • A + c • B))⁻¹).conjTranspose =
      (CFC.sqrt (A + B))⁻¹ * A * ((CFC.sqrt (A + B))⁻¹).conjTranspose := by
  rw [← smul_add, complex_cfc_sqrt_smul hsum.posSemidef hc.le]
  let S := CFC.sqrt (A + B)
  have hS : S.PosDef := hsum.isStrictlyPositive.sqrt.posDef
  have hr : Real.sqrt c ≠ 0 := (Real.sqrt_pos.mpr hc).ne'
  have hi : (Real.sqrt c • S)⁻¹ = (Real.sqrt c)⁻¹ • S⁻¹ := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      mul_inv_cancel₀ hr, one_smul,
      Matrix.mul_nonsing_inv S ((Matrix.isUnit_iff_isUnit_det S).mp hS.isUnit)]
  change (Real.sqrt c • S)⁻¹ * (c • A) * ((Real.sqrt c • S)⁻¹).conjTranspose = _
  rw [hi, Matrix.conjTranspose_smul]
  simp only [star_trivial, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hcancel : (Real.sqrt c)⁻¹ * c * (Real.sqrt c)⁻¹ = 1 := by
    calc
      _ = (Real.sqrt c)⁻¹ * (Real.sqrt c * Real.sqrt c) * (Real.sqrt c)⁻¹ := by
        rw [Real.mul_self_sqrt hc.le]
      _ = 1 := by field_simp
  rw [← mul_assoc, hcancel, one_smul]

theorem betaMatrixJacobiCoordinates_commonScale_complex {n : ℕ}
    (p : HermitianCoordinates n ℂ × HermitianCoordinates n ℂ)
    (hsum : (hermitianMatrixOfCoordinates p.1 + hermitianMatrixOfCoordinates p.2).PosDef)
    {c : ℝ} (hc : 0 < c) :
    betaMatrixJacobiCoordinates (c • p.1, c • p.2) = betaMatrixJacobiCoordinates p := by
  unfold betaMatrixJacobiCoordinates hermitianCoordinateConjugationLinearMap
    hermitianMatrixConjugationLinearMap
  change hermitianCoordinateProjection
    ((CFC.sqrt (hermitianMatrixOfCoordinates (c • p.1) +
      hermitianMatrixOfCoordinates (c • p.2)))⁻¹ *
      hermitianMatrixOfCoordinates (c • p.1) *
      ((CFC.sqrt (hermitianMatrixOfCoordinates (c • p.1) +
        hermitianMatrixOfCoordinates (c • p.2)))⁻¹).conjTranspose) = _
  have hmap (x : HermitianCoordinates n ℂ) :
      hermitianMatrixOfCoordinates (c • x) = c • hermitianMatrixOfCoordinates x :=
    (hermitianMatrixOfCoordinatesLinearMap n ℂ).map_smul c x
  rw [hmap, hmap]
  exact congrArg hermitianCoordinateProjection
    (complex_jacobiMatrix_commonScale _ _ hsum hc)

end A3Research
