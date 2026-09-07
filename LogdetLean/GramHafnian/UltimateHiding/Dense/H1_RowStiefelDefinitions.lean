import LogdetLean.GramHafnian.UltimateHiding.Dense.OneColumnConcrete
import LogdetLean.GramHafnian.UltimateHiding.Sparse.HaarBlockLaw

/-!
# Row-Stiefel deletion definitions for H1

This module contains only the concrete maps used in row-Stiefel deletion and
their measurability proofs.  It is deliberately independent of the external
Bourgade recursion and of the row-Stiefel disintegration interface.
-/

open MeasureTheory ProbabilityTheory

namespace LogdetLean.GramHafnian.UltimateHiding.Dense

noncomputable section

open LogdetLean.GramHafnian.CurrentPRL
open LogdetLean.GramHafnian.UltimateHiding.Sparse

/-- The complete first-`N`-row block of an `m x m` Haar unitary, scaled by
`sqrt m`. -/
def sqrtScaledFullTopRows {N m : ℕ} (hNm : N ≤ m)
    (U : Matrix.unitaryGroup (Fin m) ℂ) : Matrix (Fin N) (Fin m) ℂ :=
  sqrtScaledHaarBlockMatrix hNm (le_refl m) U

/-- Delete the last column from the first `N` rows of an `(m+1) x (m+1)`
unitary and scale the remaining `N x m` block by `sqrt (m+1)`. -/
def sqrtScaledDeleteLastTopRows {N m : ℕ} (hNsucc : N ≤ m + 1)
    (U : Matrix.unitaryGroup (Fin (m + 1)) ℂ) :
    Matrix (Fin N) (Fin m) ℂ :=
  sqrtScaledHaarBlockMatrix hNsucc (Nat.le_succ m) U

/-- Structural row update in the Stiefel deletion theorem. -/
def scaledRowStiefelDeletionUpdate {N m : ℕ} (hNm : N ≤ m) :
    Matrix.unitaryGroup (Fin m) ℂ ×
        (ℝ × ComplexUnitSphere N) →
      Matrix (Fin N) (Fin m) ℂ :=
  fun p ↦ concreteOneColumnFactor m N p.2.1 p.2.2 *
    sqrtScaledFullTopRows hNm p.1

theorem measurable_sqrtScaledFullTopRows {N m : ℕ} (hNm : N ≤ m) :
    Measurable (sqrtScaledFullTopRows hNm) :=
  measurable_sqrtScaledHaarBlockMatrix hNm (le_refl m)

theorem measurable_sqrtScaledDeleteLastTopRows {N m : ℕ}
    (hNsucc : N ≤ m + 1) :
    Measurable (sqrtScaledDeleteLastTopRows hNsucc) :=
  measurable_sqrtScaledHaarBlockMatrix hNsucc (Nat.le_succ m)

theorem measurable_scaledRowStiefelDeletionUpdate {N m : ℕ}
    (hNm : N ≤ m) :
    Measurable (scaledRowStiefelDeletionUpdate hNm) := by
  have hF : Measurable fun p :
      Matrix.unitaryGroup (Fin m) ℂ × (ℝ × ComplexUnitSphere N) ↦
      concreteOneColumnFactor m N p.2.1 p.2.2 :=
    (measurable_concreteOneColumnFactor m N).comp measurable_snd
  have hX : Measurable fun p :
      Matrix.unitaryGroup (Fin m) ℂ × (ℝ × ComplexUnitSphere N) ↦
      sqrtScaledFullTopRows hNm p.1 :=
    (measurable_sqrtScaledFullTopRows hNm).comp measurable_fst
  exact measurable_complexMatrix_mul hF hX

end

end LogdetLean.GramHafnian.UltimateHiding.Dense
