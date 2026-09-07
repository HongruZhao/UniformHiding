import LogdetLean.GramHafnian.UltimateHiding.Sparse.H19HaarCornerWithDensityInduction

/-!
# Measurability of the Haar-corner defect square root

This file isolates the Borel-measurability facts used by the exact Haar-corner
successor representation.  The continuous functional-calculus square root is
continuous on the closed nonnegative cone and is definitionally extended by
zero off that cone.  Consequently it is measurable on the whole matrix space.

No probabilistic or scientific interface is used here.
-/

open MeasureTheory Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace LogdetLean.GramHafnian.UltimateHiding.Sparse

noncomputable section

local instance h19HaarCornerSqrtMatrixBorelSpace (K N : ℕ) :
    BorelSpace (Matrix (Fin K) (Fin N) ℂ) := by
  exact inferInstanceAs (BorelSpace (Fin K → Fin N → ℂ))

private theorem measurable_of_continuousOn_closed_zeroOutside
    {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    [Zero E] (f : E → E) (s : Set E) (hs : IsClosed s)
    (hf : ContinuousOn f s) (hzero : ∀ x, x ∉ s → f x = 0) :
    Measurable f := by
  classical
  have hp : Measurable (s.piecewise f (fun _ : E ↦ 0)) :=
    hf.measurable_piecewise continuous_const.continuousOn hs.measurableSet
  convert hp using 1
  funext x
  by_cases hx : x ∈ s
  · simp [Set.piecewise, hx]
  · simp [Set.piecewise, hx, hzero x hx]

/-- The continuous-functional-calculus square root, extended by zero off the
nonnegative cone, is Borel measurable on the whole complex matrix space. -/
theorem measurable_cfcSqrt_complexMatrix (K : ℕ) :
    Measurable
      (CFC.sqrt : Matrix (Fin K) (Fin K) ℂ →
        Matrix (Fin K) (Fin K) ℂ) := by
  let s : Set (Matrix (Fin K) (Fin K) ℂ) := {A | 0 ≤ A}
  exact measurable_of_continuousOn_closed_zeroOutside
    (CFC.sqrt : Matrix (Fin K) (Fin K) ℂ →
      Matrix (Fin K) (Fin K) ℂ) s
    (CStarAlgebra.isClosed_nonneg (A := Matrix (Fin K) (Fin K) ℂ))
    (CFC.continuousOn_sqrt (A := Matrix (Fin K) (Fin K) ℂ))
    (fun _ hA ↦ CFC.sqrt_of_not_nonneg hA)

/-- The positive-semidefinite defect square root of a rectangular Haar corner
is a measurable function of the corner. -/
theorem measurable_haarCornerDefectSqrt (K N : ℕ) :
    Measurable (@haarCornerDefectSqrt K N) := by
  have hdef : Measurable (@haarCornerLeftDefect K N) := by
    unfold haarCornerLeftDefect
    refine measurable_pi_lambda _ fun i ↦
      measurable_pi_lambda _ fun j ↦ ?_
    simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply]
    refine measurable_const.sub (Finset.measurable_sum _ fun q _ ↦ ?_)
    have hi : Measurable
        (fun A : Matrix (Fin K) (Fin N) ℂ ↦ A i q) :=
      (measurable_pi_apply q).comp (measurable_pi_apply i)
    have hj : Measurable
        (fun A : Matrix (Fin K) (Fin N) ℂ ↦ A j q) :=
      (measurable_pi_apply q).comp (measurable_pi_apply j)
    exact hi.mul (continuous_star.measurable.comp hj)
  exact (measurable_cfcSqrt_complexMatrix K).comp hdef

/-- Appending a column after multiplying it by the defect square root is a
measurable map. -/
theorem measurable_haarCornerAppendSqrtColumn (K N : ℕ) :
    Measurable (@haarCornerAppendSqrtColumn K N) := by
  have hsqrt : Measurable
      (fun z : Matrix (Fin K) (Fin N) ℂ × (Fin K → ℂ) ↦
        haarCornerDefectSqrt z.1) :=
    (measurable_haarCornerDefectSqrt K N).comp measurable_fst
  have hmul : Measurable
      (fun z : Matrix (Fin K) (Fin N) ℂ × (Fin K → ℂ) ↦
        haarCornerDefectSqrt z.1 *ᵥ z.2) := by
    refine measurable_pi_lambda _ fun i ↦ ?_
    unfold Matrix.mulVec dotProduct
    refine Finset.measurable_sum _ fun j _ ↦ ?_
    exact ((measurable_pi_apply j).comp
        ((measurable_pi_apply i).comp hsqrt)).mul
      ((measurable_pi_apply j).comp measurable_snd)
  rw [haarCornerAppendSqrtColumn_eq_appendColumnEquiv]
  exact (haarCornerAppendColumnMeasurableEquiv K N).measurable.comp
    (measurable_fst.prodMk hmul)

end

end LogdetLean.GramHafnian.UltimateHiding.Sparse
