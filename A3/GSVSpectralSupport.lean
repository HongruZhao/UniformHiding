import A3.GSVMeasurable

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open Matrix MeasureTheory

noncomputable section
namespace A3Research

/-- Strict positivity of the complement bounds every literal Hermitian eigenvalue. -/
theorem hermitian_eigenvalues_lt_one {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian)
    (hcomp : (1 - A).PosDef) (i : Fin n) : hA.eigenvalues i < 1 := by
  let v : Fin n → ℂ := hA.eigenvectorBasis i
  have hnorm : star v ⬝ᵥ v = 1 := by
    change star (⇑(hA.eigenvectorBasis i)) ⬝ᵥ ⇑(hA.eigenvectorBasis i) = 1
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct,
      inner_self_eq_norm_sq_to_K]
    simp [hA.eigenvectorBasis.orthonormal.1 i]
  have hv : v ≠ 0 := by
    intro hz
    simpa [hz] using hnorm
  have hp := hcomp.re_dotProduct_pos hv
  have heq : RCLike.re (star v ⬝ᵥ ((1 - A) *ᵥ v)) = 1 - hA.eigenvalues i := by
    rw [sub_mulVec, one_mulVec, dotProduct_sub, map_sub, hnorm]
    simp only [RCLike.one_re]
    rw [hA.eigenvalues_eq]
  rw [heq] at hp
  linarith

end A3Research

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

theorem a3_edelmanSuttonJacobiMatrix_posSemidef {n a b : ℕ}
    (omega : EdelmanSuttonGaussianPair n a b) :
    (edelmanSuttonJacobiMatrix omega).PosSemidef :=
  (a3_edelmanSuttonFirstGram_posSemidef omega).mul_mul_conjTranspose_same _

/-- Squaring the literal generalized singular values recovers the eigenvalues. -/
theorem edelmanSuttonSquaredGSVCoordinates_eq_eigenvalues {n a b : ℕ} (beta : ℝ)
    (omega : EdelmanSuttonGaussianPair n a b) :
    edelmanSuttonSquaredGSVCoordinates n a b beta omega =
      (edelmanSuttonJacobiMatrix_isHermitian omega).eigenvalues := by
  funext i
  exact Real.sq_sqrt ((a3_edelmanSuttonJacobiMatrix_posSemidef omega).eigenvalues_nonneg i)

theorem edelmanSuttonSquaredGSVCoordinates_nonneg {n a b : ℕ} (beta : ℝ)
    (omega : EdelmanSuttonGaussianPair n a b) (i : Fin n) :
    0 ≤ edelmanSuttonSquaredGSVCoordinates n a b beta omega i := by
  rw [edelmanSuttonSquaredGSVCoordinates_eq_eigenvalues]
  exact (a3_edelmanSuttonJacobiMatrix_posSemidef omega).eigenvalues_nonneg i

theorem edelmanSuttonTotalGramSqrt_posDef {n a b : ℕ}
    (omega : EdelmanSuttonGaussianPair n a b)
    (hfirst : (edelmanSuttonFirstGram omega).PosDef) :
    (edelmanSuttonTotalGramSqrt omega).PosDef := by
  have htotal := hfirst.add_posSemidef (a3_edelmanSuttonSecondGram_posSemidef omega)
  exact htotal.isStrictlyPositive.sqrt.posDef

theorem edelmanSuttonJacobiMatrix_posDef {n a b : ℕ}
    (omega : EdelmanSuttonGaussianPair n a b)
    (hfirst : (edelmanSuttonFirstGram omega).PosDef) :
    (edelmanSuttonJacobiMatrix omega).PosDef := by
  have hs := edelmanSuttonTotalGramSqrt_posDef omega hfirst
  exact hfirst.mul_mul_conjTranspose_same
    (Matrix.vecMul_injective_iff_isUnit.mpr hs.inv.isUnit)

theorem edelmanSuttonJacobiMatrix_complement {n a b : ℕ}
    (omega : EdelmanSuttonGaussianPair n a b)
    (hfirst : (edelmanSuttonFirstGram omega).PosDef) :
    1 - edelmanSuttonJacobiMatrix omega =
      (edelmanSuttonTotalGramSqrt omega)⁻¹ * edelmanSuttonSecondGram omega *
        ((edelmanSuttonTotalGramSqrt omega)⁻¹).conjTranspose := by
  let S := edelmanSuttonTotalGramSqrt omega
  have hs : S.PosDef := edelmanSuttonTotalGramSqrt_posDef omega hfirst
  have hS : S * S = edelmanSuttonFirstGram omega + edelmanSuttonSecondGram omega :=
    CFC.sqrt_mul_sqrt_self _
      ((a3_edelmanSuttonFirstGram_posSemidef omega).add
        (a3_edelmanSuttonSecondGram_posSemidef omega)).nonneg
  have hi : S⁻¹ * (edelmanSuttonFirstGram omega + edelmanSuttonSecondGram omega) *
      (S⁻¹).conjTranspose = 1 := by
    rw [← hS, hs.inv.isHermitian.eq, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul S ((Matrix.isUnit_iff_isUnit_det S).mp hs.isUnit), Matrix.one_mul,
      Matrix.mul_nonsing_inv S ((Matrix.isUnit_iff_isUnit_det S).mp hs.isUnit)]
  rw [Matrix.mul_add, Matrix.add_mul] at hi
  change 1 - S⁻¹ * edelmanSuttonFirstGram omega * (S⁻¹).conjTranspose = _
  rw [← hi]
  exact add_sub_cancel_left _ _

theorem edelmanSuttonJacobiMatrix_complement_posDef {n a b : ℕ}
    (omega : EdelmanSuttonGaussianPair n a b)
    (hfirst : (edelmanSuttonFirstGram omega).PosDef)
    (hsecond : (edelmanSuttonSecondGram omega).PosDef) :
    (1 - edelmanSuttonJacobiMatrix omega).PosDef := by
  rw [edelmanSuttonJacobiMatrix_complement omega hfirst]
  exact hsecond.mul_mul_conjTranspose_same
    (Matrix.vecMul_injective_iff_isUnit.mpr
      (edelmanSuttonTotalGramSqrt_posDef omega hfirst).inv.isUnit)

/-- Actual full-rank Gram inputs put the literal A3 coordinates in the open cube. -/
theorem edelmanSuttonSquaredGSVCoordinates_mem_openUnitCube {n a b : ℕ}
    (beta : ℝ) (omega : EdelmanSuttonGaussianPair n a b)
    (hfirst : (edelmanSuttonFirstGram omega).PosDef)
    (hsecond : (edelmanSuttonSecondGram omega).PosDef) :
    edelmanSuttonSquaredGSVCoordinates n a b beta omega ∈ H6CoordinateAlgebra.openUnitCube n := by
  rw [edelmanSuttonSquaredGSVCoordinates_eq_eigenvalues]
  intro i
  exact ⟨(edelmanSuttonJacobiMatrix_posDef omega hfirst).eigenvalues_pos i,
    A3Research.hermitian_eigenvalues_lt_one
      (edelmanSuttonJacobiMatrix_isHermitian omega)
      (edelmanSuttonJacobiMatrix_complement_posDef omega hfirst hsecond) i⟩

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
