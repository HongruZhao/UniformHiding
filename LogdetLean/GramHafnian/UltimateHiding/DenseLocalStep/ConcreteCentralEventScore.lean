import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ConcreteCentralScore
import LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep.ConcreteCorrelatedPath
import LogdetLean.GramHafnian.UltimateHiding.H3H4Central.H4_Proof

/-!
# Central event-score bridge for the concrete square COE base

This release file contains only the proved event-score bridge.  The regularity
and differentiation formulas used below are supplied by the A1 derivations in
`H3H4Central`; obsolete duplicate external declarations have been removed.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.UltimateHiding.DenseScore
open LogdetLean.GramHafnian.LocalAnticoncentration

/-- Scalar congruence updates form an additive one-parameter action. -/
theorem concreteCentralMatrixUpdate_add
    (N : ℕ) (s t : ℝ) :
    concreteCentralMatrixUpdate N s ∘ concreteCentralMatrixUpdate N t =
      concreteCentralMatrixUpdate N (s + t) := by
  funext A
  ext i j
  simp [concreteCentralMatrixUpdate, concreteCentralFactor,
    Matrix.mul_apply, Real.exp_add, Finset.mul_sum, Finset.sum_mul]
  ring

/-- Shifting path time is the same as replacing the event by its measurable
preimage.  This is the step that makes the origin score bounds uniform in
the Taylor interval. -/
theorem concreteCentralEventPath_add
    (N : ℕ) (mu : Measure (ConcreteMatrixState N))
    (event : Set (ConcreteMatrixState N)) (hevent : MeasurableSet event)
    (y t : ℝ) :
    concreteCentralEventPath N mu event (y + t) =
      concreteCentralEventPath N mu
        (concreteCentralMatrixUpdate N y ⁻¹' event) t := by
  unfold concreteCentralEventPath concreteCentralAction
  rw [map_measureReal_apply (measurable_concreteCentralMatrixUpdate N (y + t)) hevent,
    map_measureReal_apply (measurable_concreteCentralMatrixUpdate N t)
      ((measurable_concreteCentralMatrixUpdate N y) hevent)]
  congr 1
  ext X
  simp only [Set.mem_preimage]
  have hcomp := congrFun (concreteCentralMatrixUpdate_add N y t) X
  exact iff_of_eq ((congrArg (fun Z ↦ Z ∈ event) hcomp).symm)

/-- The `r`th derivative at arbitrary time is an origin derivative for the
shifted measurable event. -/
theorem iteratedDeriv_concreteCentralEventPath_eq_zero_shift
    (r N : ℕ) (mu : Measure (ConcreteMatrixState N))
    (event : Set (ConcreteMatrixState N)) (hevent : MeasurableSet event)
    (y : ℝ) :
    iteratedDeriv r (concreteCentralEventPath N mu event) y =
      iteratedDeriv r
        (concreteCentralEventPath N mu
          (concreteCentralMatrixUpdate N y ⁻¹' event)) 0 := by
  let F := concreteCentralEventPath N mu event
  let B := concreteCentralMatrixUpdate N y ⁻¹' event
  have hfun : (fun t ↦ F (y + t)) = concreteCentralEventPath N mu B := by
    funext t
    exact concreteCentralEventPath_add N mu event hevent y t
  have hshift := congrFun (iteratedDeriv_comp_const_add r F y) 0
  rw [hfun] at hshift
  simpa only [add_zero, F, B] using hshift.symm

/-- An event-restricted integral is bounded by the full `L^1` norm. -/
theorem abs_integral_indicator_le_lpNorm_one
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {f : Omega → ℝ} (hf : MemLp f 1 mu)
    {event : Set Omega} (hevent : MeasurableSet event) :
    |∫ x, event.indicator f x ∂mu| ≤ lpNorm f 1 mu := by
  have hfint : Integrable f mu := memLp_one_iff_integrable.mp hf
  have hind : Integrable (event.indicator f) mu := hfint.indicator hevent
  calc
    |∫ x, event.indicator f x ∂mu| ≤
        ∫ x, |event.indicator f x| ∂mu := abs_integral_le_integral_abs
    _ ≤ ∫ x, |f x| ∂mu := by
      apply integral_mono hind.abs hfint.abs
      intro x
      by_cases hx : x ∈ event <;> simp [Set.indicator, hx]
    _ = lpNorm f 1 mu := by
      rw [lpNorm_one_eq_integral_norm hf.aestronglyMeasurable]
      rfl

/-- Concrete smoothness field for the square COE base. -/
theorem concreteBaseCentralEventPath_smooth
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K)
    (event : Set (ConcreteMatrixState N)) (hevent : MeasurableSet event) :
    ContDiff ℝ 2
      (concreteCentralEventPath N
        (concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K) event) :=
  LogdetLean.GramHafnian.UltimateHiding.H3H4Central.coeCorner_centralEventPath_contDiff_external_derived_of_A1
    hN (by omega) event hevent

/-- The base central first event derivative is uniformly `O(N)`. -/
theorem abs_iteratedDeriv_one_concreteBaseCentralEventPath_le
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K)
    (event : Set (ConcreteMatrixState N)) (hevent : MeasurableSet event) :
    |iteratedDeriv 1
        (concreteCentralEventPath N
          (concreteScaledCOECornerLaw
            canonicalUnitaryHaarProbabilityFamily N K) event) 0| ≤
      concreteCentralScoreOneConstant * (N : ℝ) := by
  have hgap : 2 * N + 8 ≤ K := by omega
  rw [(LogdetLean.GramHafnian.UltimateHiding.H3H4Central.coeCorner_centralEventPath_derivatives_external_derived_of_A1
    hN hgap event hevent).1]
  exact (abs_integral_indicator_le_lpNorm_one
    (concreteCentralLogScoreOne_memLp_one hN hgap) hevent).trans
      (concreteCentralLogScoreOne_lpNorm_one_le hN hdense)

/-- The base central second event derivative is uniformly `O(N^2)` at every
path time, not merely at the origin. -/
theorem abs_iteratedDeriv_two_concreteBaseCentralEventPath_le
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K)
    (event : Set (ConcreteMatrixState N)) (hevent : MeasurableSet event)
    (y : ℝ) :
    |iteratedDeriv 2
        (concreteCentralEventPath N
          (concreteScaledCOECornerLaw
            canonicalUnitaryHaarProbabilityFamily N K) event) y| ≤
      concreteCentralScoreTwoConstant * (N : ℝ) ^ 2 := by
  let mu := concreteScaledCOECornerLaw
    canonicalUnitaryHaarProbabilityFamily N K
  let shifted := concreteCentralMatrixUpdate N y ⁻¹' event
  have hshifted : MeasurableSet shifted :=
    (measurable_concreteCentralMatrixUpdate N y) hevent
  rw [iteratedDeriv_concreteCentralEventPath_eq_zero_shift
    2 N mu event hevent y]
  have hgap : 2 * N + 8 ≤ K := by omega
  rw [(LogdetLean.GramHafnian.UltimateHiding.H3H4Central.coeCorner_centralEventPath_derivatives_external_derived_of_A1
    hN hgap shifted hshifted).2]
  exact (abs_integral_indicator_le_lpNorm_one
    (concreteCentralDensityScoreTwo_memLp_one hN hdense) hshifted).trans
      (concreteCentralDensityScoreTwo_lpNorm_one_le hN hdense)

end

end LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep
