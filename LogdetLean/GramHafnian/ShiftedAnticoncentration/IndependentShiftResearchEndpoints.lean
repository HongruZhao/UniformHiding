import LogdetLean.GramHafnian.ShiftedAnticoncentration.IndependentShiftMultilinear
import LogdetLean.GramHafnian.ShiftedAnticoncentration.IndependentShiftGaussianKernel
import LogdetLean.GramHafnian.ShiftedAnticoncentration.LaplaceSmallBall
import LogdetLean.GramHafnian.ShiftedAnticoncentration.LastColumnProduct
import LogdetLean.GramHafnian.ShiftedAnticoncentration.CofactorAlmostSurePositivity

/-!
# Public independent-shift research endpoints

This module joins the finite multilinear replacement theorem to the exact
last-column Gaussian kernel and the generic reciprocal-kernel
Laplace-to-small-ball transfer.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LogdetLean.GramHafnian

noncomputable section

/-- The centered Gram-hafnian radial Laplace transform is exactly the mixture
of reciprocal scalar Gaussian kernels indexed by the past cofactor variance. -/
theorem centered_gramHafnian_laplace_eq_pastCofactorV_reciprocal
    {r k : ℕ} (hr : 1 ≤ r) (t : ℝ) (ht : 0 ≤ t) :
    (∫ X : ComplexColumnMatrix r k,
        Real.exp (-t * ‖gramHafnianObservable r k X‖ ^ 2)
        ∂circularGaussianColumnMatrixMeasure r k) =
      ∫ A : OddCofactorIndex r hr -> (Fin k -> ℂ),
        (1 + t * pastCofactorV hr A)⁻¹
        ∂(Measure.pi fun _ : OddCofactorIndex r hr =>
          circularGaussianVector k) := by
  let past : Measure (OddCofactorIndex r hr -> (Fin k -> ℂ)) :=
    Measure.pi fun _ : OddCofactorIndex r hr => circularGaussianVector k
  let fresh : Measure (Fin k -> ℂ) := circularGaussianVector k
  let g :
      (OddCofactorIndex r hr -> (Fin k -> ℂ)) × (Fin k -> ℂ) -> ℝ :=
    fun p => Real.exp
      (-t * ‖conditionalCircularLinearForm (pastCofactorCombination hr) p‖ ^ 2)
  have hg : Integrable g (past.prod fresh) := by
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards [] with p
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr ht) (sq_nonneg _))
  calc
    (∫ X : ComplexColumnMatrix r k,
        Real.exp (-t * ‖gramHafnianObservable r k X‖ ^ 2)
        ∂circularGaussianColumnMatrixMeasure r k) =
      ∫ p :
          (OddCofactorIndex r hr -> (Fin k -> ℂ)) × (Fin k -> ℂ),
        Real.exp
          (-t * ‖gramHafnianObservable r k
            (lastColumnProductEquiv r k hr p)‖ ^ 2)
        ∂(past.prod fresh) := by
          simpa [past, fresh] using
            ((measurePreserving_lastColumnProductEquiv r k hr).integral_comp'
              (fun X : ComplexColumnMatrix r k =>
                Real.exp (-(t * ‖gramHafnianObservable r k X‖ ^ 2)))).symm
    _ = ∫ p :
          (OddCofactorIndex r hr -> (Fin k -> ℂ)) × (Fin k -> ℂ),
        g p ∂(past.prod fresh) := by
          apply integral_congr_ae
          filter_upwards [] with p
          dsimp [g]
          rw [gramHafnian_lastColumnProductEquiv_eq_conditionalLinearForm]
    _ = ∫ A : OddCofactorIndex r hr -> (Fin k -> ℂ),
          ∫ x : Fin k -> ℂ, g (A, x) ∂fresh ∂past :=
      integral_prod g hg
    _ = ∫ A : OddCofactorIndex r hr -> (Fin k -> ℂ),
        (1 + t * pastCofactorV hr A)⁻¹ ∂past := by
          apply integral_congr_ae
          filter_upwards [] with A
          simpa [g, fresh, circularGaussianVector,
            conditionalCircularLinearForm,
            pastCofactorV_eq_coefficientEnergy] using
            integral_exp_neg_norm_sq_iidCircularTransposeLinearForm
              (pastCofactorCombination hr A) t ht
    _ = ∫ A : OddCofactorIndex r hr -> (Fin k -> ℂ),
        (1 + t * pastCofactorV hr A)⁻¹
        ∂(Measure.pi fun _ : OddCofactorIndex r hr =>
          circularGaussianVector k) := by rfl

/-- Averaging an arbitrary independent matrix shift cannot increase the
Gram-hafnian radial Laplace transform beyond the exact centered reciprocal
cofactor-variance mixture. -/
theorem independentShift_gramHafnian_laplace_le_pastCofactorV_reciprocal
    {r k : ℕ} (hr : 1 ≤ r)
    (nu : Measure (ComplexColumnMatrix r k)) [IsProbabilityMeasure nu]
    (w : ℂ) (t : ℝ) (ht : 0 ≤ t) :
    (∫ p : ComplexColumnMatrix r k × ComplexColumnMatrix r k,
        Real.exp
          (-t * ‖gramHafnianObservable r k
            (fun i => p.1 i + p.2 i) - w‖ ^ 2)
        ∂((circularGaussianColumnMatrixMeasure r k).prod nu)) ≤
      ∫ A : OddCofactorIndex r hr -> (Fin k -> ℂ),
        (1 + t * pastCofactorV hr A)⁻¹
        ∂(Measure.pi fun _ : OddCofactorIndex r hr =>
          circularGaussianVector k) := by
  calc
    (∫ p : ComplexColumnMatrix r k × ComplexColumnMatrix r k,
        Real.exp
          (-t * ‖gramHafnianObservable r k
            (fun i => p.1 i + p.2 i) - w‖ ^ 2)
        ∂((circularGaussianColumnMatrixMeasure r k).prod nu)) ≤
      ∫ X : ComplexColumnMatrix r k,
        Real.exp (-t * ‖gramHafnianObservable r k X‖ ^ 2)
        ∂circularGaussianColumnMatrixMeasure r k :=
      independentShift_gramHafnian_laplace_le hr nu w t ht
    _ = ∫ A : OddCofactorIndex r hr -> (Fin k -> ℂ),
        (1 + t * pastCofactorV hr A)⁻¹
        ∂(Measure.pi fun _ : OddCofactorIndex r hr =>
          circularGaussianVector k) :=
      centered_gramHafnian_laplace_eq_pastCofactorV_reciprocal hr t ht

/-- An arbitrary matrix shift independent of the Gaussian matrix obeys the
quadratic small-ball bound controlled by the exact past cofactor inverse
moment.  Dependence among all columns of the shift is allowed. -/
theorem independentShift_gramHafnian_smallBall_le_exp_one_mul_sq_mul_ennInverseMoment
    {r k : ℕ} (hr : 1 ≤ r) (hk : 2 * r - 1 ≤ k)
    (nu : Measure (ComplexColumnMatrix r k)) [IsProbabilityMeasure nu]
    (w : ℂ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ((circularGaussianColumnMatrixMeasure r k).prod nu)
        {p | ‖gramHafnianObservable r k
          (fun i => p.1 i + p.2 i) - w‖ ≤ epsilon} ≤
      ENNReal.ofReal (Real.exp 1 * epsilon ^ 2) *
        ennInverseMoment
          (Measure.pi fun _ : OddCofactorIndex r hr =>
            circularGaussianVector k)
          (pastCofactorV hr) := by
  let joint : Measure
      (ComplexColumnMatrix r k × ComplexColumnMatrix r k) :=
    (circularGaussianColumnMatrixMeasure r k).prod nu
  let past : Measure (OddCofactorIndex r hr -> (Fin k -> ℂ)) :=
    Measure.pi fun _ : OddCofactorIndex r hr => circularGaussianVector k
  let Y : ComplexColumnMatrix r k × ComplexColumnMatrix r k -> ℂ :=
    fun p => gramHafnianObservable r k (fun i => p.1 i + p.2 i)
  let V : (OddCofactorIndex r hr -> (Fin k -> ℂ)) -> ℝ :=
    pastCofactorV hr
  have hY : Measurable Y := by
    dsimp [Y]
    exact (measurable_gramHafnianObservable r k).comp (by fun_prop)
  have hV : Measurable V := by
    simpa [V] using measurable_pastCofactorV (k := k) hr
  have hVfull :=
    ae_oddCofactorV_pos_circularGaussianColumnMatrix hr hk
  have hVpast :=
    ae_pastCofactorV_pos_of_ae_oddCofactorV_pos hr hVfull
  have hVpos : ∀ᵐ A ∂past, 0 < V A := by
    simpa [past, V] using hVpast
  have hLap : ∀ t : ℝ, 0 ≤ t ->
      ennLaplaceTransform joint (fun p => ‖Y p - w‖ ^ 2) t ≤
        ∫⁻ A, ENNReal.ofReal ((1 + t * V A)⁻¹) ∂past := by
    intro t ht
    have hU : Measurable (fun p => ‖Y p - w‖ ^ 2) := by
      fun_prop
    have hUnonneg : ∀ p, 0 ≤ ‖Y p - w‖ ^ 2 := fun p => sq_nonneg _
    have hkernel_pos (A : OddCofactorIndex r hr -> (Fin k -> ℂ)) :
        0 < 1 + t * V A := by
      have hnonneg : 0 ≤ V A := by
        dsimp [V]
        rw [pastCofactorV_eq_coefficientEnergy]
        exact circularCoefficientEnergy_nonneg _
      nlinarith [mul_nonneg ht hnonneg]
    have hkernel_nonneg :
        0 ≤ᵐ[past] (fun A => (1 + t * V A)⁻¹) :=
      Filter.Eventually.of_forall fun A =>
        inv_nonneg.mpr (hkernel_pos A).le
    have hkernel_integrable :
        Integrable (fun A => (1 + t * V A)⁻¹) past := by
      apply Integrable.of_bound (by fun_prop) 1
      filter_upwards [] with A
      rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hkernel_pos A))]
      exact (inv_le_one₀ (hkernel_pos A)).2 (by
        have hnonneg : 0 ≤ V A := by
          dsimp [V]
          rw [pastCofactorV_eq_coefficientEnergy]
          exact circularCoefficientEnergy_nonneg _
        nlinarith [mul_nonneg ht hnonneg])
    calc
      ennLaplaceTransform joint (fun p => ‖Y p - w‖ ^ 2) t =
          ENNReal.ofReal
            (∫ p, Real.exp (-t * ‖Y p - w‖ ^ 2) ∂joint) :=
        ennLaplaceTransform_eq_ofReal_integral
          joint (fun p => ‖Y p - w‖ ^ 2) hU hUnonneg t ht
      _ ≤ ENNReal.ofReal
          (∫ A, (1 + t * V A)⁻¹ ∂past) := by
        apply ENNReal.ofReal_le_ofReal
        simpa [joint, past, Y, V] using
          independentShift_gramHafnian_laplace_le_pastCofactorV_reciprocal
            hr nu w t ht
      _ = ∫⁻ A, ENNReal.ofReal ((1 + t * V A)⁻¹) ∂past :=
        ofReal_integral_eq_lintegral_ofReal
          hkernel_integrable hkernel_nonneg
  simpa [joint, past, Y, V] using
    measure_norm_sub_le_exp_one_mul_sq_mul_ennInverseMoment_of_reciprocalLaplace_le
      joint past Y hY V hV hVpos w epsilon hepsilon hLap

/-- Finite real-valued form of the independent-shift small-ball estimate. -/
theorem independentShift_gramHafnian_smallBallReal_le_exp_one_mul_sq_mul_ennInverseMoment_toReal
    {r k : ℕ} (hr : 1 ≤ r) (hk : 2 * r - 1 ≤ k)
    (nu : Measure (ComplexColumnMatrix r k)) [IsProbabilityMeasure nu]
    (hVfinite :
      ennInverseMoment
        (Measure.pi fun _ : OddCofactorIndex r hr => circularGaussianVector k)
        (pastCofactorV hr) ≠ ⊤)
    (w : ℂ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ((circularGaussianColumnMatrixMeasure r k).prod nu).real
        {p | ‖gramHafnianObservable r k
          (fun i => p.1 i + p.2 i) - w‖ ≤ epsilon} ≤
      Real.exp 1 * epsilon ^ 2 *
        (ennInverseMoment
          (Measure.pi fun _ : OddCofactorIndex r hr => circularGaussianVector k)
          (pastCofactorV hr)).toReal := by
  have henn :=
    independentShift_gramHafnian_smallBall_le_exp_one_mul_sq_mul_ennInverseMoment
      hr hk nu w epsilon hepsilon
  have hfactor_nonneg : 0 ≤ Real.exp 1 * epsilon ^ 2 :=
    mul_nonneg (Real.exp_pos 1).le (sq_nonneg epsilon)
  have hrhs_ne_top :
      ENNReal.ofReal (Real.exp 1 * epsilon ^ 2) *
          ennInverseMoment
            (Measure.pi fun _ : OddCofactorIndex r hr => circularGaussianVector k)
            (pastCofactorV hr) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVfinite
  have hreal := ENNReal.toReal_mono hrhs_ne_top henn
  rw [Measure.real_def]
  simpa [ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hfactor_nonneg, mul_assoc] using hreal

end

end LogdetLean.GramHafnian
