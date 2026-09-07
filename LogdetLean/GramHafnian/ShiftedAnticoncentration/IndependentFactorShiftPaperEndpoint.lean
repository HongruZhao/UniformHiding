import LogdetLean.GramHafnian.ShiftedAnticoncentration.IndependentShiftResearchEndpoints
import LogdetLean.GramHafnian.CurrentPRL.CoreEquations
import LogdetLean.GramHafnian.CurrentPRL.CoefficientPaperEndpoints

/-!
# Paper-facing independent shifts of the Gaussian factor

This module combines the arbitrary independent matrix-shift Laplace comparison
with the Article's finite inverse-variance and normalization endpoints.  It
introduces no distributional assumption on the shift beyond independence from
the complete circular-Gaussian matrix.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LogdetLean.GramHafnian

noncomputable section

/-- Equation `eq:independent-matrix-shift-observable`: the shifted
transpose gram hafnian appearing in Corollary I.2. -/
def independentFactorShiftObservable (n k : ℕ)
    (X Delta : ComplexColumnMatrix n k) : ℂ :=
  gramHafnianObservable n k (fun i ↦ X i + Delta i)

/-- The exact scalar Gaussian calculation printed at the beginning of the
proof of Corollary I.2. -/
theorem independentFactorShift_scalarGaussian_laplace_chain
    {k : ℕ} (a : Fin k → ℂ) (b : ℂ) (t : ℝ) (ht : 0 ≤ t) :
    let mu : Measure (Fin k → ℂ) :=
      Measure.pi fun _ : Fin k ↦ circularGaussian
    let kernel := (1 + t * circularCoefficientEnergy a)⁻¹
    (∫ g, Real.exp
        (-t * ‖iidCircularTransposeLinearForm a g + b‖ ^ 2) ∂mu) =
        kernel * Real.exp
          (-t * ‖b‖ ^ 2 / (1 + t * circularCoefficientEnergy a)) ∧
      (∫ g, Real.exp
        (-t * ‖iidCircularTransposeLinearForm a g + b‖ ^ 2) ∂mu) ≤
        kernel ∧
      kernel = ∫ h, Real.exp
        (-t * ‖iidCircularTransposeLinearForm a h‖ ^ 2) ∂mu := by
  dsimp only
  exact ⟨integral_exp_neg_norm_sq_iidCircularTransposeLinearForm_add
      a b t ht,
    integral_exp_neg_norm_sq_iidCircularTransposeLinearForm_add_le
      a b t ht,
    (integral_exp_neg_norm_sq_iidCircularTransposeLinearForm a t ht).symm⟩

/-- The exact one column Gaussian replacement inequality displayed in the
proof of the independent factor shift corollary. -/
theorem independentFactorShift_oneColumn_laplace_le
    {k : ℕ} (L : (Fin k → ℂ) →L[ℂ] ℂ)
    (b : ℂ) (t : ℝ) (ht : 0 ≤ t) :
    (∫ x : Fin k → ℂ,
        Real.exp (-t * ‖L x + b‖ ^ 2) ∂circularGaussianVector k) ≤
      ∫ x : Fin k → ℂ,
        Real.exp (-t * ‖L x‖ ^ 2) ∂circularGaussianVector k := by
  exact continuousLinear_circularGaussian_add_laplace_le L b t ht

/-- Exact three-term Laplace chain used in the Article. -/
theorem independentFactorShift_laplace_chain
    {n k : ℕ} (hn : 1 ≤ n)
    (nu : Measure (ComplexColumnMatrix n k)) [IsProbabilityMeasure nu]
    (w : ℂ) (t : ℝ) (ht : 0 ≤ t) :
    (∫ p : ComplexColumnMatrix n k × ComplexColumnMatrix n k,
        Real.exp
          (-t * ‖gramHafnianObservable n k
            (fun i => p.1 i + p.2 i) - w‖ ^ 2)
        ∂((circularGaussianColumnMatrixMeasure n k).prod nu)) ≤
      ∫ X : ComplexColumnMatrix n k,
        Real.exp (-t * ‖gramHafnianObservable n k X‖ ^ 2)
        ∂circularGaussianColumnMatrixMeasure n k ∧
    (∫ X : ComplexColumnMatrix n k,
        Real.exp (-t * ‖gramHafnianObservable n k X‖ ^ 2)
        ∂circularGaussianColumnMatrixMeasure n k) =
      ∫ A : OddCofactorIndex n hn -> (Fin k -> ℂ),
        (1 + t * pastCofactorV hn A)⁻¹
        ∂(Measure.pi fun _ : OddCofactorIndex n hn =>
          circularGaussianVector k) := by
  exact ⟨independentShift_gramHafnian_laplace_le hn nu w t ht,
    centered_gramHafnian_laplace_eq_pastCofactorV_reciprocal hn t ht⟩

/-- The two sharp finite radius inequalities before the reciprocal kernel is
discarded in favor of the full inverse moment. -/
theorem independentFactorShift_resolvent_chain
    {n k : ℕ} (hn : 1 ≤ n) (hk : 2 * n - 1 ≤ k)
    (nu : Measure (ComplexColumnMatrix n k)) [IsProbabilityMeasure nu]
    (w : ℂ) (rho : ℝ) (hrho : 0 < rho) :
    let joint : Measure
        (ComplexColumnMatrix n k × ComplexColumnMatrix n k) :=
      (circularGaussianColumnMatrixMeasure n k).prod nu
    let past : Measure (OddCofactorIndex n hn → (Fin k → ℂ)) :=
      Measure.pi fun _ : OddCofactorIndex n hn ↦ circularGaussianVector k
    let kernel := ∫⁻ A, ENNReal.ofReal
      ((1 + (rho ^ 2)⁻¹ * pastCofactorV hn A)⁻¹) ∂past
    joint {p | ‖gramHafnianObservable n k
        (fun i ↦ p.1 i + p.2 i) - w‖ ≤ rho} ≤
        ENNReal.ofReal (Real.exp 1) * kernel ∧
      kernel ≤ ENNReal.ofReal (rho ^ 2) *
        ennInverseMoment past (pastCofactorV hn) := by
  dsimp only
  let joint : Measure
      (ComplexColumnMatrix n k × ComplexColumnMatrix n k) :=
    (circularGaussianColumnMatrixMeasure n k).prod nu
  let past : Measure (OddCofactorIndex n hn → (Fin k → ℂ)) :=
    Measure.pi fun _ : OddCofactorIndex n hn ↦ circularGaussianVector k
  let Y : ComplexColumnMatrix n k × ComplexColumnMatrix n k → ℂ :=
    fun p ↦ gramHafnianObservable n k (fun i ↦ p.1 i + p.2 i)
  let V : (OddCofactorIndex n hn → (Fin k → ℂ)) → ℝ :=
    pastCofactorV hn
  have hY : Measurable Y := by
    dsimp [Y]
    exact (measurable_gramHafnianObservable n k).comp (by fun_prop)
  have hV : Measurable V := by
    simpa [V] using measurable_pastCofactorV (k := k) hn
  have hVpos : ∀ᵐ A ∂past, 0 < V A := by
    simpa [past, V] using
      ae_pastCofactorV_pos_of_ae_oddCofactorV_pos hn
        (ae_oddCofactorV_pos_circularGaussianColumnMatrix hn hk)
  have hLap : ∀ t : ℝ, 0 ≤ t →
      ennLaplaceTransform joint (fun p ↦ ‖Y p - w‖ ^ 2) t ≤
        ∫⁻ A, ENNReal.ofReal ((1 + t * V A)⁻¹) ∂past := by
    intro t ht
    have hU : Measurable (fun p ↦ ‖Y p - w‖ ^ 2) := by fun_prop
    have hUnonneg : ∀ p, 0 ≤ ‖Y p - w‖ ^ 2 := fun p ↦ sq_nonneg _
    have hkernel_pos (A : OddCofactorIndex n hn → (Fin k → ℂ)) :
        0 < 1 + t * V A := by
      have hnonneg : 0 ≤ V A := by
        dsimp [V]
        rw [pastCofactorV_eq_coefficientEnergy]
        exact circularCoefficientEnergy_nonneg _
      nlinarith [mul_nonneg ht hnonneg]
    have hkernel_nonneg :
        0 ≤ᵐ[past] (fun A ↦ (1 + t * V A)⁻¹) :=
      Filter.Eventually.of_forall fun A ↦
        inv_nonneg.mpr (hkernel_pos A).le
    have hkernel_integrable :
        Integrable (fun A ↦ (1 + t * V A)⁻¹) past := by
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
      ennLaplaceTransform joint (fun p ↦ ‖Y p - w‖ ^ 2) t =
          ENNReal.ofReal
            (∫ p, Real.exp (-t * ‖Y p - w‖ ^ 2) ∂joint) :=
        ennLaplaceTransform_eq_ofReal_integral
          joint (fun p ↦ ‖Y p - w‖ ^ 2) hU hUnonneg t ht
      _ ≤ ENNReal.ofReal (∫ A, (1 + t * V A)⁻¹ ∂past) := by
        apply ENNReal.ofReal_le_ofReal
        simpa [joint, past, Y, V] using
          independentShift_gramHafnian_laplace_le_pastCofactorV_reciprocal
            hn nu w t ht
      _ = ∫⁻ A, ENNReal.ofReal ((1 + t * V A)⁻¹) ∂past :=
        ofReal_integral_eq_lintegral_ofReal
          hkernel_integrable hkernel_nonneg
  constructor
  · simpa [joint, past, Y, V] using
      measure_norm_sub_le_exp_one_mul_reciprocalKernel_of_reciprocalLaplace_le
        joint past Y hY V w rho hrho hLap
  · simpa [past, V] using
      reciprocalKernel_lintegral_le_sq_mul_ennInverseMoment
        past V hV hVpos rho hrho

/-- Unnormalized finite independent-factor-shift small-ball bound after the
Article's inverse-variance estimate. -/
theorem independentFactorShift_rawSmallBall_le_inverseVarianceBound
    {n k : ℕ} (hn : 1 ≤ n) (hk : 4 * n ≤ k)
    (nu : Measure (ComplexColumnMatrix n k)) [IsProbabilityMeasure nu]
    (w : ℂ) (rho : ℝ) (hrho : 0 < rho) :
    ((circularGaussianColumnMatrixMeasure n k).prod nu).real
        {p | ‖gramHafnianObservable n k
          (fun i => p.1 i + p.2 i) - w‖ ≤ rho} ≤
      Real.exp 1 * rho ^ 2 * inverseVarianceBound k n := by
  let mu : Measure
      (ComplexColumnMatrix n k × ComplexColumnMatrix n k) :=
    (circularGaussianColumnMatrixMeasure n k).prod nu
  let event := {p : ComplexColumnMatrix n k × ComplexColumnMatrix n k |
    ‖gramHafnianObservable n k (fun i => p.1 i + p.2 i) - w‖ ≤ rho}
  have hshift :=
    independentShift_gramHafnian_smallBall_le_exp_one_mul_sq_mul_ennInverseMoment
      hn (by omega : 2 * n - 1 ≤ k) nu w rho hrho
  have h11 := CurrentPRL.eq11_inverse_variance k n hn hk
  rw [pastCofactorVInverseMoment_eq hn] at h11
  have hENN : mu event ≤
      ENNReal.ofReal (Real.exp 1 * rho ^ 2) *
        ENNReal.ofReal (inverseVarianceBound k n) := by
    calc
      mu event ≤ ENNReal.ofReal (Real.exp 1 * rho ^ 2) *
          ennInverseMoment
            (Measure.pi fun _ : OddCofactorIndex n hn =>
              circularGaussianVector k)
            (pastCofactorV hn) := by
        simpa [mu, event] using hshift
      _ ≤ ENNReal.ofReal (Real.exp 1 * rho ^ 2) *
          ENNReal.ofReal (inverseVarianceBound k n) := by gcongr
  have htop : ENNReal.ofReal (Real.exp 1 * rho ^ 2) *
      ENNReal.ofReal (inverseVarianceBound k n) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hreal := ENNReal.toReal_mono htop hENN
  change mu.real event ≤ _
  rw [measureReal_def]
  calc
    (mu event).toReal ≤
        (ENNReal.ofReal (Real.exp 1 * rho ^ 2) *
          ENNReal.ofReal (inverseVarianceBound k n)).toReal := hreal
    _ = Real.exp 1 * rho ^ 2 * inverseVarianceBound k n := by
      rw [ENNReal.toReal_mul,
        ENNReal.toReal_ofReal
          (mul_nonneg (Real.exp_pos 1).le (sq_nonneg rho)),
        ENNReal.toReal_ofReal
          (inverseVarianceBound_nonneg_of_le hk hn le_rfl)]

/-- Probability-capped normalized independent-factor-shift bound in the
Article's `k ≥ 4n` regime. -/
theorem independentFactorShift_normalizedSmallBall
    {n k : ℕ} (hn : 1 ≤ n) (hk : 4 * n ≤ k)
    (nu : Measure (ComplexColumnMatrix n k)) [IsProbabilityMeasure nu]
    (w : ℂ) (eps : ℝ) (heps : 0 < eps) :
    ((circularGaussianColumnMatrixMeasure n k).prod nu).real
        {p | ‖gramHafnianObservable n k
          (fun i => p.1 i + p.2 i) - w‖ ≤
            eps * gramHafnianSigma k n} ≤
      min 1 (Real.exp 1 * CurrentPRL.paperBkn k n * eps ^ 2) := by
  apply le_min
  · exact measureReal_le_one
  · have hkpos : 0 < k := by omega
    have hsigma : 0 < gramHafnianSigma k n :=
      gramHafnianSigma_pos k n hkpos
    have hraw := independentFactorShift_rawSmallBall_le_inverseVarianceBound
      hn hk nu w (eps * gramHafnianSigma k n) (mul_pos heps hsigma)
    calc
      ((circularGaussianColumnMatrixMeasure n k).prod nu).real
          {p | ‖gramHafnianObservable n k
            (fun i => p.1 i + p.2 i) - w‖ ≤
              eps * gramHafnianSigma k n} ≤
        Real.exp 1 * (eps * gramHafnianSigma k n) ^ 2 *
          inverseVarianceBound k n := hraw
      _ = Real.exp 1 * CurrentPRL.paperBkn k n * eps ^ 2 := by
        have hsigmaSq : gramHafnianSigma k n ^ 2 =
            closedFirstMoment k n := gramHafnianSigma_sq k n hkpos
        have hcoefficient := CurrentPRL.eq3_mul_eq11_is_eq5 k n hn
        calc
          Real.exp 1 * (eps * gramHafnianSigma k n) ^ 2 *
              inverseVarianceBound k n =
            Real.exp 1 *
              (gramHafnianSigma k n ^ 2 * inverseVarianceBound k n) *
              eps ^ 2 := by ring
          _ = Real.exp 1 * CurrentPRL.paperBkn k n * eps ^ 2 := by
            rw [hsigmaSq, hcoefficient]

end

end LogdetLean.GramHafnian
