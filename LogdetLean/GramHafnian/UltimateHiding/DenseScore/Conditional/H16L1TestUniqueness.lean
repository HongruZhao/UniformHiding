import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Function.L1Space.AEEqFun

/-!
# Compact-test uniqueness in `L1`

This is the generic distribution-to-`L1` uniqueness bridge used after the
H16 weak-generator calculation.  It contains no determinant, COE, event, or
H5 data.
-/

open MeasureTheory
open scoped ContDiff

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E}

/-- Two `L1` classes are equal if all of their pairings with compactly
supported smooth real tests agree. -/
theorem h16_l1_eq_of_integral_test_mul_eq
    (f g : E →₁[μ] ℝ)
    (h : ∀ phi : E → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi →
      (∫ x, phi x * f x ∂μ) = ∫ x, phi x * g x ∂μ) :
    f = g := by
  apply Lp.ext
  exact ae_eq_of_integral_contDiff_smul_eq
    (L1.integrable_coeFn f).locallyIntegrable
    (L1.integrable_coeFn g).locallyIntegrable fun phi hphi hsupp ↦ by
      simpa [smul_eq_mul] using h phi hphi hsupp

/-- Zero is the special case needed for the defect in a Bochner orbit
fundamental identity. -/
theorem h16_l1_eq_zero_of_integral_test_mul_eq_zero
    (f : E →₁[μ] ℝ)
    (h : ∀ phi : E → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi →
      (∫ x, phi x * f x ∂μ) = 0) :
    f = 0 := by
  apply Lp.ext
  have hf0 : (fun x ↦ f x) =ᵐ[μ] (0 : E → ℝ) :=
    ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (L1.integrable_coeFn f).locallyIntegrable fun phi hphi hsupp ↦ by
      simpa [smul_eq_mul] using h phi hphi hsupp
  exact Filter.EventuallyEq.trans hf0
    (Lp.coeFn_zero (E := ℝ) (p := 1) (μ := μ)).symm

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional
