import LogdetLean.GramHafnian.UltimateHiding.Sparse.H19HaarCornerDensityInduction
import LogdetLean.GramHafnian.UltimateHiding.Sparse.H19DensityLimit
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Interior of the complex matrix ball

The right and left contraction defects are simultaneously positive
semidefinite.  Consequently, Jiang support together with a nonzero defect
determinant makes the left defect positive definite.  This is the elementary
fact needed to ignore the singular square-root fiber under a positive
determinant-power density.
-/

open Matrix MeasureTheory
open scoped ComplexOrder MatrixOrder

namespace LogdetLean.GramHafnian.UltimateHiding.Sparse

noncomputable section

/-- A rectangular complex matrix is a contraction from the right exactly
when it is a contraction from the left.  This follows by applying the two
Schur-complement criteria to the same Hermitian block matrix
`[[I,X],[X*,I]]`. -/
theorem posSemidef_one_sub_conjTranspose_mul_iff_one_sub_mul_conjTranspose
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (X : Matrix m n ℂ) :
    (1 - X.conjTranspose * X).PosSemidef ↔
      (1 - X * X.conjTranspose).PosSemidef := by
  let H : Matrix (m ⊕ n) (m ⊕ n) ℂ :=
    Matrix.fromBlocks (1 : Matrix m m ℂ) X X.conjTranspose
      (1 : Matrix n n ℂ)
  have hleft : H.PosSemidef ↔
      (1 - X.conjTranspose * X).PosSemidef := by
    letI : Invertible (1 : Matrix m m ℂ) := invertibleOne
    simpa [H] using
      (Matrix.PosDef.fromBlocks₁₁ X (1 : Matrix n n ℂ)
        (Matrix.PosDef.one : (1 : Matrix m m ℂ).PosDef))
  have hright : H.PosSemidef ↔
      (1 - X * X.conjTranspose).PosSemidef := by
    letI : Invertible (1 : Matrix n n ℂ) := invertibleOne
    simpa [H] using
      (Matrix.PosDef.fromBlocks₂₂ (1 : Matrix m m ℂ) X
        (Matrix.PosDef.one : (1 : Matrix n n ℂ).PosDef))
  exact hleft.symm.trans hright

/-- On Jiang support, a nonzero right-defect determinant places the left
defect in the strict interior of the matrix ball. -/
theorem haarCornerLeftDefect_posDef_of_support_det_ne_zero
    {K N : ℕ} (X : Matrix (Fin K) (Fin N) ℂ)
    (hsupport : jiangUnscaledTallHaarCornerSupport X)
    (hdet : Matrix.det (1 - X.conjTranspose * X) ≠ 0) :
    (haarCornerLeftDefect X).PosDef := by
  have hright : (1 - X.conjTranspose * X).PosSemidef :=
    (jiangUnscaledTallHaarCornerSupport_iff_posSemidef X).mp hsupport
  have hleft : (1 - X * X.conjTranspose).PosSemidef :=
    (posSemidef_one_sub_conjTranspose_mul_iff_one_sub_mul_conjTranspose X).mp
      hright
  change (1 - X * X.conjTranspose).PosDef
  apply hleft.posDef_iff_det_ne_zero.mpr
  simpa using
    (show Matrix.det (1 - X * X.conjTranspose) ≠ 0 by
      rw [Matrix.det_one_sub_mul_comm X X.conjTranspose]
      exact hdet)

/-- In the successor-size regime, every point where the old Jiang density is
nonzero has a strictly positive left defect.  The extra column supplies the
strictly positive old determinant exponent. -/
theorem haarCornerLeftDefect_posDef_of_jiangPDF_ne_zero
    {M K N : ℕ} (hsize : K + (N + 1) ≤ M)
    (X : Matrix (Fin K) (Fin N) ℂ)
    (hpdf : jiangUnscaledTallHaarCornerPDF M K N X ≠ 0) :
    (haarCornerLeftDefect X).PosDef := by
  have hexp : 0 < M - K - N := by omega
  have hsupport : jiangUnscaledTallHaarCornerSupport X := by
    by_contra hs
    apply hpdf
    simp [jiangUnscaledTallHaarCornerPDF, hs]
  apply haarCornerLeftDefect_posDef_of_support_det_ne_zero X hsupport
  intro hdet
  apply hpdf
  simp [jiangUnscaledTallHaarCornerPDF, hsupport, hdet,
    Nat.ne_of_gt hexp]

/-- The singular square-root fibers have zero mass under the old Jiang
with-density law.  This uses vanishing of the density itself, not a separate
polynomial-hypersurface null theorem. -/
theorem ae_haarCornerLeftDefect_posDef_under_jiangDensity
    {M K N : ℕ} (hsize : K + (N + 1) ≤ M) :
    ∀ᵐ X ∂(complexRectangularLebesgueVolume K N).withDensity
        (jiangUnscaledTallHaarCornerPDF M K N),
      (haarCornerLeftDefect X).PosDef := by
  rw [ae_withDensity_iff
    (measurable_jiangUnscaledTallHaarCornerPDF M K N)]
  filter_upwards [] with X hpdf
  exact haarCornerLeftDefect_posDef_of_jiangPDF_ne_zero hsize X hpdf

end

end LogdetLean.GramHafnian.UltimateHiding.Sparse
