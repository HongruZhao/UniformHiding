import A4.InverseSteinGramDerivative
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Tactic

open scoped BigOperators Matrix.Norms.Elementwise

noncomputable section
namespace A4Research.InverseStein

set_option backward.isDefEq.respectTransparency false

def inverseWishartEntryTest {k p : ℕ} (l m : Fin p)
    (R : Matrix (Fin k) (Fin p) ℝ) : ℝ :=
  (realWishartGram R)⁻¹ l m

def inverseWishartEntryTestDerivative {k p : ℕ} (l m : Fin p)
    (R : Matrix (Fin k) (Fin p) ℝ) :
    Matrix (Fin k) (Fin p) ℝ →L[ℝ] ℝ :=
  fderiv ℝ (inverseWishartEntryTest l m) R

theorem hasFDerivAt_inverseWishartEntryTest
    {k p : ℕ} (l m : Fin p) (R : Matrix (Fin k) (Fin p) ℝ)
    (hfull : IsUnit (realWishartGram R).det) :
    HasFDerivAt (inverseWishartEntryTest l m)
      (inverseWishartEntryTestDerivative l m R) R := by
  have hinv := hasFDerivAt_matrix_nonsing_inv (realWishartGram R) hfull
  have hentry := (squareMatrixEntryCLM l m).hasFDerivAt.comp
    (realWishartGram R) hinv
  have hcomp := hentry.comp R (hasFDerivAt_realWishartGram R)
  exact hcomp.differentiableAt.hasFDerivAt

theorem inverseWishartEntryTestDerivative_apply
    {k p : ℕ} (l m : Fin p) (R E : Matrix (Fin k) (Fin p) ℝ)
    (hfull : IsUnit (realWishartGram R).det) :
    inverseWishartEntryTestDerivative l m R E =
      -(((realWishartGram R)⁻¹ *
        (E.transpose * R + R.transpose * E) *
        (realWishartGram R)⁻¹) l m) := by
  have hlocal := (hasFDerivAt_inverseWishartEntryTest l m R hfull).hasLineDerivAt E
  have hline := hasDerivAt_inverse_realWishartGram_entry_matrixLine R E hfull l m
  exact hlocal.unique hline

def inverseEntryProduct {k p q : ℕ} (indices : Fin q → Fin p × Fin p)
    (R : Matrix (Fin k) (Fin p) ℝ) : ℝ :=
  ∏ r, (realWishartGram R)⁻¹ (indices r).1 (indices r).2

def inverseEntryProductDerivative {k p q : ℕ} (indices : Fin q → Fin p × Fin p)
    (R : Matrix (Fin k) (Fin p) ℝ) : Matrix (Fin k) (Fin p) ℝ →L[ℝ] ℝ :=
  fderiv ℝ (inverseEntryProduct indices) R

theorem hasFDerivAt_inverseEntryProduct
    {k p q : ℕ} (indices : Fin q → Fin p × Fin p)
    (R : Matrix (Fin k) (Fin p) ℝ)
    (hfull : IsUnit (realWishartGram R).det) :
    HasFDerivAt (inverseEntryProduct indices)
      (inverseEntryProductDerivative indices R) R := by
  have h : DifferentiableAt ℝ (inverseEntryProduct indices) R := by
    exact (HasFDerivAt.finsetProd (u := (Finset.univ : Finset (Fin q)))
      (fun r _ ↦ hasFDerivAt_inverseWishartEntryTest
        (indices r).1 (indices r).2 R hfull)).differentiableAt
  exact h.hasFDerivAt

theorem inverseEntryProductDerivative_apply
    {k p q : ℕ} (indices : Fin q → Fin p × Fin p)
    (R E : Matrix (Fin k) (Fin p) ℝ)
    (hfull : IsUnit (realWishartGram R).det) :
    inverseEntryProductDerivative indices R E =
      -∑ r, (((realWishartGram R)⁻¹ *
          (E.transpose * R + R.transpose * E) *
          (realWishartGram R)⁻¹) (indices r).1 (indices r).2) *
        ∏ s ∈ Finset.univ.erase r,
          (realWishartGram R)⁻¹ (indices s).1 (indices s).2 := by
  have hlocal := (hasFDerivAt_inverseEntryProduct indices R hfull).hasLineDerivAt E
  have hline := HasDerivAt.fun_finsetProd
    (u := (Finset.univ : Finset (Fin q)))
    (fun r _ ↦ hasDerivAt_inverse_realWishartGram_entry_matrixLine
      R E hfull (indices r).1 (indices r).2)
  have heq := hlocal.unique hline
  apply heq.trans
  simp only [matrixLine, zero_smul, add_zero, smul_eq_mul, Matrix.neg_apply,
    mul_neg, Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  ring

/-- The exact all-degree derivative used by the inverse-entry Stein recursion. -/
theorem inverseEntryProductDerivative_steinVectorFieldValue
    {k p q : ℕ} (indices : Fin q → Fin p × Fin p)
    (R : Matrix (Fin k) (Fin p) ℝ)
    (D : Matrix (Fin p) (Fin p) ℝ) (hD : D.IsSymm)
    (hfull : IsUnit (realWishartGram R).det) :
    inverseEntryProductDerivative indices R (steinVectorFieldValue R D) =
      -∑ r, (((realWishartGram R)⁻¹ * D *
          (realWishartGram R)⁻¹) (indices r).1 (indices r).2) *
        ∏ s ∈ Finset.univ.erase r,
          (realWishartGram R)⁻¹ (indices s).1 (indices s).2 := by
  rw [inverseEntryProductDerivative_apply indices R _ hfull,
    gram_firstVariation_steinVectorFieldValue R hD hfull]

end A4Research.InverseStein
