import LogdetLean.GramHafnian.ExactGramFirstMoment
import LogdetLean.GramHafnian.ShiftedAnticoncentration.LastColumnProduct

/-!
# First moment of the literal past cofactor energy

This experimental module identifies the mean conditional variance after the
last-column decomposition with the already verified exact hafnian second
moment.
-/

open MeasureTheory
open scoped ComplexConjugate

namespace LogdetLean.GramHafnian

noncomputable section

/-- A paper-normalized circular Gaussian has unit squared norm in mean. -/
theorem integral_normSq_circularGaussian :
    (∫ z : ℂ, Complex.normSq z ∂circularGaussian) = 1 := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simpa [Complex.mul_conj] using integral_mul_conj_circularGaussian

/-- Conditional on a coefficient vector, the exposed circular Gaussian
transpose form has second absolute moment equal to its coefficient energy. -/
theorem integral_normSq_iidCircularTransposeLinearForm
    {k : ℕ} (y : Fin k → ℂ) :
    (∫ x : Fin k → ℂ,
        Complex.normSq (iidCircularTransposeLinearForm y x)
        ∂(Measure.pi fun _ : Fin k ↦ circularGaussian)) =
      circularCoefficientEnergy y := by
  rw [← integral_map
      (measurable_iidCircularTransposeLinearForm y).aemeasurable (by fun_prop),
    map_iidCircularTransposeLinearForm_eq_scaled_circular,
    integral_map (by fun_prop) (by fun_prop)]
  simp_rw [Complex.normSq_eq_norm_sq, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (circularCoefficientEnergy_nonneg y)]
  rw [integral_const_mul]
  have hnorm : (∫ z : ℂ, ‖z‖ ^ 2 ∂circularGaussian) = 1 := by
    simpa [Complex.normSq_eq_norm_sq] using integral_normSq_circularGaussian
  rw [hnorm, mul_one]

/-- The mean literal conditional variance is exactly the full Gram-hafnian
second absolute moment. -/
theorem integral_pastCofactorV_eq_actualGramFirstMomentReal
    {r k : ℕ} (hr : 1 ≤ r) (hk : 0 < k) :
    (∫ A : OddCofactorIndex r hr → (Fin k → ℂ),
        pastCofactorV hr A
        ∂(Measure.pi fun _ : OddCofactorIndex r hr ↦
          circularGaussianVector k)) =
      actualGramFirstMomentReal k r := by
  let ν : Measure (OddCofactorIndex r hr → (Fin k → ℂ)) :=
    Measure.pi fun _ : OddCofactorIndex r hr ↦ circularGaussianVector k
  let μ : Measure (Fin k → ℂ) := circularGaussianVector k
  let e := lastColumnProductEquiv r k hr
  let g :
      ((OddCofactorIndex r hr → (Fin k → ℂ)) × (Fin k → ℂ)) → ℝ :=
    fun p ↦ Complex.normSq
      (gramHafnianObservable r k (e p))
  have hfull : Integrable
      (fun X : ComplexColumnMatrix r k ↦
        Complex.normSq (gramHafnianObservable r k X))
      (circularGaussianColumnMatrixMeasure r k) := by
    apply Integrable.of_integral_ne_zero
    change actualGramFirstMomentReal k r ≠ 0
    rw [actualGramFirstMomentReal_eq_closedFirstMoment k r hk]
    exact (closedFirstMoment_pos k r hk).ne'
  have hg : Integrable g (ν.prod μ) := by
    have htransport := MeasurePreserving.integrable_comp_of_integrable
      (measurePreserving_lastColumnProductEquiv r k hr) hfull
    simpa [g, e, ν, μ, Function.comp_def] using htransport
  have hpoint (A : OddCofactorIndex r hr → (Fin k → ℂ)) :
      (∫ x : Fin k → ℂ,
          Complex.normSq
            (conditionalCircularLinearForm
              (pastCofactorCombination hr) (A, x)) ∂μ) =
        pastCofactorV hr A := by
    calc
      (∫ x : Fin k → ℂ,
          Complex.normSq
            (conditionalCircularLinearForm
              (pastCofactorCombination hr) (A, x)) ∂μ) =
          circularCoefficientEnergy (pastCofactorCombination hr A) := by
            simpa [μ, circularGaussianVector,
              conditionalCircularLinearForm, iidCircularTransposeLinearForm,
              mul_comm] using
              integral_normSq_iidCircularTransposeLinearForm
                (pastCofactorCombination hr A)
      _ = pastCofactorV hr A :=
        (pastCofactorV_eq_coefficientEnergy hr A).symm
  calc
    (∫ A : OddCofactorIndex r hr → (Fin k → ℂ),
        pastCofactorV hr A ∂
          (Measure.pi fun _ : OddCofactorIndex r hr ↦
            circularGaussianVector k)) =
        ∫ A, ∫ x,
          Complex.normSq
            (conditionalCircularLinearForm
              (pastCofactorCombination hr) (A, x)) ∂μ ∂ν := by
          apply integral_congr_ae
          filter_upwards [] with A
          exact (hpoint A).symm
    _ = ∫ p, g p ∂(ν.prod μ) := by
      rw [integral_prod g hg]
      apply integral_congr_ae
      filter_upwards [] with A
      apply integral_congr_ae
      filter_upwards [] with x
      dsimp only [g, e]
      exact congrArg Complex.normSq
        (gramHafnian_lastColumnProductEquiv_eq_conditionalLinearForm
          hr (A, x)).symm
    _ = actualGramFirstMomentReal k r := by
      have htransport :=
        (measurePreserving_lastColumnProductEquiv r k hr).integral_comp'
          (fun X : ComplexColumnMatrix r k ↦
            Complex.normSq (gramHafnianObservable r k X))
      change (∫ p, g p ∂(ν.prod μ)) = _
      rw [show (∫ p, g p ∂(ν.prod μ)) =
          ∫ X : ComplexColumnMatrix r k,
            Complex.normSq (gramHafnianObservable r k X)
              ∂(circularGaussianColumnMatrixMeasure r k) by
        simpa [g, e, ν, μ] using htransport]
      rfl

/-- Closed-form restatement of the preceding exact mean identity. -/
theorem integral_pastCofactorV_eq_closedFirstMoment
    {r k : ℕ} (hr : 1 ≤ r) (hk : 0 < k) :
    (∫ A : OddCofactorIndex r hr → (Fin k → ℂ),
        pastCofactorV hr A
        ∂(Measure.pi fun _ : OddCofactorIndex r hr ↦
          circularGaussianVector k)) =
      closedFirstMoment k r := by
  rw [integral_pastCofactorV_eq_actualGramFirstMomentReal hr hk,
    actualGramFirstMomentReal_eq_closedFirstMoment k r hk]

end

end LogdetLean.GramHafnian
