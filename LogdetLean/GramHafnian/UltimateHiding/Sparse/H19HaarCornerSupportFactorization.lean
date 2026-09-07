import LogdetLean.GramHafnian.UltimateHiding.Sparse.H19HaarCornerWithDensityInduction
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Support factorization for the Haar-corner column induction

This file supplies the positive-semidefinite counterpart of the determinant
factorization: a rank-one unit-ball defect is positive semidefinite exactly
when the column norm square is at most one.
-/

open Matrix
open scoped ComplexOrder MatrixOrder BigOperators

namespace LogdetLean.GramHafnian.UltimateHiding.Sparse

noncomputable section

/-- The Hermitian rank-one defect `I-u u*` is positive semidefinite exactly
on the closed complex unit ball. -/
theorem posSemidef_one_sub_complexColumnMatrix_outer_iff
    {K : ℕ} (u : Fin K → ℂ) :
    (1 - complexColumnMatrix u *
        (complexColumnMatrix u).conjTranspose).PosSemidef ↔
      complexColumnNormSq u ≤ 1 := by
  let c := complexColumnMatrix u
  let H : Matrix (Fin K ⊕ Fin 1) (Fin K ⊕ Fin 1) ℂ :=
    Matrix.fromBlocks (1 : Matrix (Fin K) (Fin K) ℂ) c c.conjTranspose
      (1 : Matrix (Fin 1) (Fin 1) ℂ)
  have htop : H.PosSemidef ↔
      (1 - c.conjTranspose * c).PosSemidef := by
    letI : Invertible (1 : Matrix (Fin K) (Fin K) ℂ) := invertibleOne
    simpa [H] using
      (Matrix.PosDef.fromBlocks₁₁ c (1 : Matrix (Fin 1) (Fin 1) ℂ)
        (Matrix.PosDef.one : (1 : Matrix (Fin K) (Fin K) ℂ).PosDef))
  have hbottom : H.PosSemidef ↔
      (1 - c * c.conjTranspose).PosSemidef := by
    letI : Invertible (1 : Matrix (Fin 1) (Fin 1) ℂ) := invertibleOne
    simpa [H] using
      (Matrix.PosDef.fromBlocks₂₂ (1 : Matrix (Fin K) (Fin K) ℂ) c
        (Matrix.PosDef.one : (1 : Matrix (Fin 1) (Fin 1) ℂ).PosDef))
  have houterScalar :
      (1 - c * c.conjTranspose).PosSemidef ↔
        (1 - c.conjTranspose * c).PosSemidef :=
    hbottom.symm.trans htop
  rw [houterScalar]
  have hscalar :
      1 - c.conjTranspose * c =
        Matrix.diagonal
          (fun _ : Fin 1 ↦ (((1 - complexColumnNormSq u : ℝ) : ℂ))) := by
    ext i j
    fin_cases i
    fin_cases j
    simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, c, complexColumnMatrix_apply,
      Fin.isValue, if_true, Matrix.diagonal_apply_eq]
    have hsum : (∑ q, star (u q) * u q) =
        (((complexColumnNormSq u : ℝ) : ℂ)) := by
      calc
        ∑ q, star (u q) * u q =
            ∑ q, ((Complex.normSq (u q) : ℝ) : ℂ) := by
          apply Finset.sum_congr rfl
          intro q _
          exact (Complex.normSq_eq_conj_mul_self (z := u q)).symm
        _ = (((∑ q, Complex.normSq (u q) : ℝ) : ℂ)) := by
          exact (Complex.ofReal_sum Finset.univ
            (fun q ↦ Complex.normSq (u q))).symm
        _ = (((complexColumnNormSq u : ℝ) : ℂ)) := rfl
    rw [hsum]
    push_cast
    rfl
  rw [hscalar, Matrix.posSemidef_diagonal_iff]
  simp only [forall_const]
  constructor
  · intro h
    exact sub_nonneg.mp ((RCLike.ofReal_nonneg (K := ℂ)).mp h)
  · intro h
    exact (RCLike.ofReal_nonneg (K := ℂ)).mpr (sub_nonneg.mpr h)

end

end LogdetLean.GramHafnian.UltimateHiding.Sparse
