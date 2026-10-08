import A1.CornerMeasurable

open Matrix MeasureTheory
open LogdetLean.GramHafnian.UltimateHiding.DenseScore
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

noncomputable section
namespace A1Research

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- The actual totalized nonnegative CFC square root is globally Borel measurable.
It is continuous on the closed nonnegative cone and zero on its complement. -/
theorem measurable_complexMatrix_cfc_sqrt (m : ℕ) :
    Measurable (CFC.sqrt : Matrix (Fin m) (Fin m) ℂ → Matrix (Fin m) (Fin m) ℂ) := by
  classical
  let s : Set (Matrix (Fin m) (Fin m) ℂ) := {A | 0 ≤ A}
  have hs : MeasurableSet s := CStarAlgebra.isClosed_nonneg.measurableSet
  have h : Measurable (s.piecewise CFC.sqrt (fun _ ↦ 0)) :=
    CFC.continuousOn_sqrt.measurable_piecewise continuous_const.continuousOn hs
  have heq : s.piecewise CFC.sqrt (fun _ ↦ 0) =
      (CFC.sqrt : Matrix (Fin m) (Fin m) ℂ → Matrix (Fin m) (Fin m) ℂ) := by
    funext A
    by_cases hA : 0 ≤ A
    · simp [s, hA]
    · simp [s, hA, CFC.sqrt_of_not_nonneg hA]
  rwa [heq] at h

/-- Global measurability of the literal normalized pair overlap, with no positivity
or nonsingularity premise. -/
theorem measurable_normalizedComplexPairOverlap (m : ℕ) :
    Measurable (fun p : Matrix (Fin m) (Fin m) ℂ × Matrix (Fin m) (Fin m) ℂ ↦
      normalizedComplexPairOverlap p.1 p.2) := by
  have hi : Measurable (fun p : Matrix (Fin m) (Fin m) ℂ × Matrix (Fin m) (Fin m) ℂ ↦
      (CFC.sqrt p.1)⁻¹) :=
    (measurable_complexMatrix_nonsing_inv m).comp
      ((measurable_complexMatrix_cfc_sqrt m).comp measurable_fst)
  have ht : Measurable (fun A : Matrix (Fin m) (Fin m) ℂ ↦ A.transpose) :=
    continuous_id.matrix_transpose.measurable
  have hfirst := measurable_rectangular_matrix_mul
    (fun p : Matrix (Fin m) (Fin m) ℂ × Matrix (Fin m) (Fin m) ℂ ↦
      ((CFC.sqrt p.1)⁻¹).transpose) Prod.snd (ht.comp hi) measurable_snd
  have hprod := measurable_rectangular_matrix_mul
    (fun p : Matrix (Fin m) (Fin m) ℂ × Matrix (Fin m) (Fin m) ℂ ↦
      ((CFC.sqrt p.1)⁻¹).transpose * p.2)
    (fun p ↦ (CFC.sqrt p.1)⁻¹) hfirst hi
  simpa only [normalizedComplexPairOverlap, Matrix.transpose_nonsing_inv] using hprod

end A1Research
