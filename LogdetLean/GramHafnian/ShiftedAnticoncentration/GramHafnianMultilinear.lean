import LogdetLean.GramHafnian.ShiftedAnticoncentration.Definitions
import LogdetLean.GramHafnian.WickRegrouping
import Mathlib.Analysis.Normed.Module.Multilinear.Basic

/-!
# The Gram hafnian as a continuous multilinear map of its columns

The matching-coloring expansion contains exactly one coordinate from every
column.  Each colored matching monomial is therefore obtained by composing
the continuous product multilinear map with coordinate projections.  Summing
these maps gives a continuous multilinear realization of the literal Gram
hafnian observable.
-/

open scoped BigOperators

namespace LogdetLean.GramHafnian

noncomputable section

private noncomputable def coloredMatchingContinuousMultilinear
    (r k : ℕ) (M : PerfectMatching r) (c : PairColoring M k) :
    ContinuousMultilinearMap ℂ
      (fun _ : Fin (2 * r) => Fin k → ℂ) ℂ :=
  (ContinuousMultilinearMap.mkPiAlgebra ℂ (Fin (2 * r)) ℂ).compContinuousLinearMap
    (fun i =>
      (ContinuousLinearMap.proj (R := ℂ)
        (vertexColoringOfPairColoring M c i) :
          (Fin k → ℂ) →L[ℂ] ℂ))

private theorem coloredMatchingContinuousMultilinear_apply
    (r k : ℕ) (M : PerfectMatching r) (c : PairColoring M k)
    (X : ComplexColumnMatrix r k) :
    coloredMatchingContinuousMultilinear r k M c X =
      coloredMatchingMonomial (rowMatrix X) M c := by
  simpa [coloredMatchingContinuousMultilinear,
    complexColoringCoefficient, rowMatrix] using
    (complexColoringCoefficient_vertexColoringOfPairColoring
      (rowMatrix X) M c)

/-- The Gram hafnian, viewed as a continuous multilinear map in its `2*r`
complex columns. -/
noncomputable def gramHafnianContinuousMultilinear (r k : ℕ) :
    ContinuousMultilinearMap ℂ
      (fun _ : Fin (2 * r) => Fin k → ℂ) ℂ :=
  ∑ M : PerfectMatching r, ∑ c : PairColoring M k,
    coloredMatchingContinuousMultilinear r k M c

/-- Evaluation of `gramHafnianContinuousMultilinear` is exactly the literal
Gram hafnian observable. -/
@[simp] theorem gramHafnianContinuousMultilinear_apply
    (r k : ℕ) (X : ComplexColumnMatrix r k) :
    gramHafnianContinuousMultilinear r k X =
      gramHafnianObservable r k X := by
  simp only [gramHafnianContinuousMultilinear,
    gramHafnianObservable, sum_apply]
  simp_rw [coloredMatchingContinuousMultilinear_apply]
  exact (gramHafnian_eq_sum_coloredMatchings (rowMatrix X)).symm

end

end LogdetLean.GramHafnian
