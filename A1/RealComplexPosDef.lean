import A3.WishartCholeskyFactorization

open Matrix
open scoped ComplexOrder BigOperators

noncomputable section
namespace A1Research

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

variable {I J K : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] [RCLike K]

theorem posDef_submatrix_equiv_rclike (e : I ≃ J) (M : Matrix J J K) :
    (M.submatrix e e).PosDef ↔ M.PosDef := by
  constructor
  · intro h
    have hPSD := (Matrix.posSemidef_submatrix_equiv e).mp h.posSemidef
    apply hPSD.posDef_iff_det_ne_zero.mpr
    have hd := h.det_pos.ne'
    rwa [Matrix.det_submatrix_equiv_self e M] at hd
  · intro h
    have hPSD := h.posSemidef.submatrix e
    apply hPSD.posDef_iff_det_ne_zero.mpr
    rw [Matrix.det_submatrix_equiv_self e M]
    exact h.det_pos.ne'

omit [Fintype J] [DecidableEq J] [RCLike K] in
/-- A complex-positive real matrix is positive on the actual real quadratic tests. -/
theorem real_posDef_of_complexMap (W : Matrix I I ℝ)
    (hW : (W.map Complex.ofReal).PosDef) : W.PosDef := by
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  refine ⟨?_, ?_⟩
  · apply Matrix.IsHermitian.ext
    intro i j
    have h := congrArg Complex.re (hW.isHermitian.apply i j)
    simpa [Matrix.map, Complex.star_def] using h
  · intro x hx
    have hcx : (fun i ↦ (x i : ℂ)) ≠ 0 := by
      intro h
      apply hx
      funext i
      have hi := congrArg (fun z : I → ℂ ↦ z i) h
      simpa using hi
    have hp := hW.dotProduct_mulVec_pos hcx
    have hr := (Complex.pos_iff.mp hp).1
    simpa [dotProduct, Matrix.mulVec, Matrix.map, Complex.star_def,
      Finset.mul_sum] using hr

omit [Fintype J] [DecidableEq J] [RCLike K] [DecidableEq I] in
/-- Positive real matrices stay positive after extension of the scalar field. -/
theorem complexMap_posDef_of_real [LinearOrder I] [WellFoundedLT I] [LocallyFiniteOrderBot I]
    (W : Matrix I I ℝ) (hW : W.PosDef) : (W.map Complex.ofReal).PosDef := by
  let L := A3Research.wishartCholesky hW
  let C := L.map Complex.ofReal
  have hu : IsUnit C :=
    (A3Research.wishartCholesky_isUnit hW).map Complex.ofRealHom.mapMatrix
  have heq : W.map Complex.ofReal = C * C.conjTranspose := by
    rw [← A3Research.wishartCholesky_mul_conjTranspose hW]
    change (L * L.conjTranspose).map (Complex.ofRealHom : ℝ → ℂ) = _
    rw [Matrix.map_mul]
    congr 1
    exact Matrix.conjTranspose_map Complex.ofReal (fun r ↦ by simp [Complex.star_def])
  rw [heq]
  simpa only [Matrix.mul_one, Matrix.star_eq_conjTranspose] using
    hu.posDef_star_right_conjugate_iff.mpr (show (1 : Matrix I I ℂ).PosDef from Matrix.PosDef.one)

omit [Fintype J] [DecidableEq J] [RCLike K] [DecidableEq I] in
theorem real_posDef_iff_complexMap [LinearOrder I] [WellFoundedLT I] [LocallyFiniteOrderBot I]
    (W : Matrix I I ℝ) : W.PosDef ↔ (W.map Complex.ofReal).PosDef :=
  ⟨complexMap_posDef_of_real W, real_posDef_of_complexMap W⟩

end A1Research
