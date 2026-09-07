import LogdetLean.GramHafnian.ShiftedAnticoncentration.Experimental.ConditionalInverseDensity.Endpoints
import LogdetLean.GramHafnian.ShiftedAnticoncentration.Experimental.RadialLowerBound.LiteralEndpointAlt

/-!
# Conditional radial--angular factorization

This file removes the sufficient paper-range condition `4 * n ≤ k` from the
radial--angular lemma.  It assumes instead the exact analytic facts used by
the proof: almost-everywhere positivity and integrability of the reciprocal
conditional variance.  The only numerical condition is `2 ≤ k`, which is
needed for the reciprocal radial moment.
-/

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal NNReal Real BigOperators

namespace LogdetLean.GramHafnian

noncomputable section

namespace RadialLowerBoundAlt

variable {n k : ℕ} (hn : 1 ≤ n)

/-- Integrability of the full reciprocal conditional variance implies
integrability of its reciprocal angular factor once `k ≥ 2`. -/
theorem integrable_inv_angularEnergy_of_inverse
    (hk2 : 2 ≤ k)
    (hVpos :
      ∀ᵐ A : CofactorIdx n hn → (Fin k → ℂ)
        ∂(Measure.pi fun _ : CofactorIdx n hn ↦ circularGaussianVector k),
        0 < pastCofactorV hn A)
    (hInv : Integrable
      (fun A : CofactorIdx n hn → (Fin k → ℂ) ↦
        (pastCofactorV hn A)⁻¹)
      (Measure.pi fun _ : CofactorIdx n hn ↦ circularGaussianVector k)) :
    Integrable (fun u ↦ (angularEnergy (n := n) (k := k) hn u)⁻¹)
      (angularMeasure hn) := by
  have hkpos : 0 < k := by omega
  apply Integrable.of_integral_ne_zero
  intro hzero
  have hsplit := integral_inv_pastCofactorV_eq_angular_mul_radial hn hkpos
  rw [hzero, zero_mul] at hsplit
  have hnonneg :
      0 ≤ᵐ[(Measure.pi fun _ : CofactorIdx n hn ↦ circularGaussianVector k)]
        (fun A ↦ (pastCofactorV hn A)⁻¹) := by
    filter_upwards [hVpos] with A hA
    exact inv_nonneg.mpr hA.le
  have hne :
      (∫ A : CofactorIdx n hn → (Fin k → ℂ),
        (pastCofactorV hn A)⁻¹
        ∂(Measure.pi fun _ : CofactorIdx n hn ↦ circularGaussianVector k)) ≠ 0 := by
    intro hz
    have hae := (integral_eq_zero_iff_of_nonneg_ae hnonneg hInv).mp hz
    obtain ⟨A, hA0, hApos⟩ := (hae.and hVpos).exists
    have hinvpos : 0 < (pastCofactorV hn A)⁻¹ := inv_pos.mpr hApos
    exact hinvpos.ne' hA0
  exact hne hsplit

/-- Almost-everywhere positivity of the full conditional variance descends
to the angular energy for every `k > 0`. -/
theorem ae_angularEnergy_pos_of_ae
    (hkpos : 0 < k)
    (hVpos :
      ∀ᵐ A : CofactorIdx n hn → (Fin k → ℂ)
        ∂(Measure.pi fun _ : CofactorIdx n hn ↦ circularGaussianVector k),
        0 < pastCofactorV hn A) :
    ∀ᵐ u ∂angularMeasure (n := n) (k := k) hn,
      0 < angularEnergy (n := n) (k := k) hn u := by
  letI : ∀ _ : CofactorIdx n hn,
      IsProbabilityMeasure (circularGaussianSphereProbability k) :=
    fun _ ↦ ⟨circularGaussianSphereProbability_apply_univ hkpos⟩
  letI : ∀ _ : CofactorIdx n hn,
      IsProbabilityMeasure (circularGaussianPositiveRadiusMeasure k) :=
    fun _ ↦ isProbabilityMeasure_circularGaussianPositiveRadiusMeasure hkpos
  letI : IsProbabilityMeasure (angularMeasure (k := k) hn) := by
    unfold angularMeasure
    infer_instance
  letI : IsProbabilityMeasure (radiusMeasure (k := k) hn) := by
    unfold radiusMeasure
    infer_instance
  let hT : MeasurePreserving
      (splitPolarReconstruct (n := n) (k := k) hn)
      (splitPolarMeasure (k := k) hn)
      (Measure.pi fun _ : CofactorIdx n hn ↦ circularGaussianVector k) :=
    ⟨measurable_splitPolarReconstruct hn,
      map_splitPolarReconstruct hn hkpos⟩
  have hpull : ∀ᵐ z ∂splitPolarMeasure (k := k) hn,
      0 < pastCofactorV hn (splitPolarReconstruct hn z) :=
    hT.quasiMeasurePreserving.ae hVpos
  have hprod : ∀ᵐ z ∂splitPolarMeasure (k := k) hn,
      0 < squaredRadiusProduct hn z.2 * angularEnergy hn z.1 := by
    filter_upwards [hpull] with z hz
    rw [pastCofactorV_splitPolarReconstruct hn] at hz
    exact hz
  have hsections := Measure.ae_ae_of_ae_prod hprod
  filter_upwards [hsections] with u hu
  obtain ⟨r, hr⟩ := hu.exists
  have hrad : 0 < squaredRadiusProduct (n := n) hn r := by
    unfold squaredRadiusProduct
    exact Finset.prod_pos fun j _ ↦ sq_pos_of_pos (r j).2
  exact pos_of_mul_pos_right hr hrad.le

/-- Exact radial--angular factorization of the two ordinary moments for all
`k ≥ 2`.  The analytic hypotheses below are not required for the algebraic
identity itself, but are used by the lower-bound corollaries. -/
theorem literalMomentProduct_eq_radial_mul_angularMomentProduct_of_k_ge_two
    (hk2 : 2 ≤ k) :
    ((∫ A : CofactorIdx n hn → (Fin k → ℂ), pastCofactorV hn A
        ∂(Measure.pi fun _ : CofactorIdx n hn ↦ circularGaussianVector k)) *
      ∫ A : CofactorIdx n hn → (Fin k → ℂ), (pastCofactorV hn A)⁻¹
        ∂(Measure.pi fun _ : CofactorIdx n hn ↦ circularGaussianVector k)) =
      cofactorRadialFactor k n *
        ((∫ u, angularEnergy (n := n) (k := k) hn u ∂angularMeasure hn) *
          ∫ u, (angularEnergy (n := n) (k := k) hn u)⁻¹
            ∂angularMeasure hn) := by
  have hkpos : 0 < k := by omega
  rw [integral_pastCofactorV_eq_angular_mul_radial hn hkpos,
    integral_squaredRadiusProduct hn hkpos,
    integral_inv_pastCofactorV_eq_angular_mul_radial hn hkpos,
    integral_inv_squaredRadiusProduct hn hk2]
  unfold cofactorRadialFactor
  rw [div_pow]
  ring

/-- Exact factorization of the paper coefficient `Lambda_{k,n}` for every
`k ≥ 2`, with no `4n` assumption. -/
theorem literalLambda_eq_radial_mul_angularMomentProduct_of_k_ge_two
    (hk2 : 2 ≤ k) :
    (closedFirstMoment k n *
      ∫ A : CofactorIdx n hn → (Fin k → ℂ), (pastCofactorV hn A)⁻¹
        ∂(Measure.pi fun _ : CofactorIdx n hn ↦ circularGaussianVector k)) =
      cofactorRadialFactor k n *
        ((∫ u, angularEnergy (n := n) (k := k) hn u ∂angularMeasure hn) *
          ∫ u, (angularEnergy (n := n) (k := k) hn u)⁻¹
            ∂angularMeasure hn) := by
  have hkpos : 0 < k := by omega
  rw [← integral_pastCofactorV_eq_closedFirstMoment hn hkpos]
  exact literalMomentProduct_eq_radial_mul_angularMomentProduct_of_k_ge_two
    hn hk2

/-- Under the exact positivity and inverse-integrability hypotheses, the
angular condition number is at least one and hence the radial factor lower
bounds the full moment product. -/
theorem cofactorRadialFactor_le_literalMomentProduct_of_inverse
    (hk2 : 2 ≤ k)
    (hVpos :
      ∀ᵐ A : CofactorIdx n hn → (Fin k → ℂ)
        ∂(Measure.pi fun _ : CofactorIdx n hn ↦ circularGaussianVector k),
        0 < pastCofactorV hn A)
    (hInv : Integrable
      (fun A : CofactorIdx n hn → (Fin k → ℂ) ↦
        (pastCofactorV hn A)⁻¹)
      (Measure.pi fun _ : CofactorIdx n hn ↦ circularGaussianVector k)) :
    cofactorRadialFactor k n ≤
      closedFirstMoment k n *
        (∫ A : CofactorIdx n hn → (Fin k → ℂ),
          (pastCofactorV hn A)⁻¹
          ∂(Measure.pi fun _ : CofactorIdx n hn ↦ circularGaussianVector k)) := by
  have hkpos : 0 < k := by omega
  letI : ∀ _ : CofactorIdx n hn,
      IsProbabilityMeasure (circularGaussianSphereProbability k) :=
    fun _ ↦ ⟨circularGaussianSphereProbability_apply_univ hkpos⟩
  letI : IsProbabilityMeasure (angularMeasure (k := k) hn) := by
    unfold angularMeasure
    infer_instance
  have hang : 1 ≤
      (∫ u, angularEnergy (n := n) (k := k) hn u ∂angularMeasure hn) *
        ∫ u, (angularEnergy (n := n) (k := k) hn u)⁻¹
          ∂angularMeasure hn :=
    one_le_integral_mul_integral_inv
      (angularMeasure (n := n) (k := k) hn)
      (angularEnergy (n := n) (k := k) hn)
      (measurable_angularEnergy hn).aestronglyMeasurable
      (ae_angularEnergy_pos_of_ae hn hkpos hVpos)
      (integrable_angularEnergy hn hkpos)
      (integrable_inv_angularEnergy_of_inverse hn hk2 hVpos hInv)
  rw [← integral_pastCofactorV_eq_closedFirstMoment hn hkpos]
  rw [literalMomentProduct_eq_radial_mul_angularMomentProduct_of_k_ge_two
    hn hk2]
  have hbase : 0 ≤ (k : ℝ) / ((k : ℝ) - 1) := by
    apply div_nonneg
    · positivity
    · have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
      linarith
  exact le_mul_of_one_le_right (pow_nonneg hbase _) hang

/-- Conditional version of the complete radial lower-bound chain. -/
theorem literalRadialLowerBound_fullChain_of_inverse
    (hk2 : 2 ≤ k)
    (hVpos :
      ∀ᵐ A : CofactorIdx n hn → (Fin k → ℂ)
        ∂(Measure.pi fun _ : CofactorIdx n hn ↦ circularGaussianVector k),
        0 < pastCofactorV hn A)
    (hInv : Integrable
      (fun A : CofactorIdx n hn → (Fin k → ℂ) ↦
        (pastCofactorV hn A)⁻¹)
      (Measure.pi fun _ : CofactorIdx n hn ↦ circularGaussianVector k)) :
    Real.exp ((n : ℝ) / (k : ℝ)) ≤
        Real.exp (((2 * n - 1 : ℕ) : ℝ) / (k : ℝ)) ∧
      Real.exp (((2 * n - 1 : ℕ) : ℝ) / (k : ℝ)) ≤
        cofactorRadialFactor k n ∧
      cofactorRadialFactor k n ≤
        ((∫ A : CofactorIdx n hn → (Fin k → ℂ), pastCofactorV hn A
            ∂(Measure.pi fun _ : CofactorIdx n hn ↦ circularGaussianVector k)) *
          ∫ A : CofactorIdx n hn → (Fin k → ℂ), (pastCofactorV hn A)⁻¹
            ∂(Measure.pi fun _ : CofactorIdx n hn ↦ circularGaussianVector k)) := by
  constructor
  · apply Real.exp_le_exp.mpr
    have hkR : (0 : ℝ) < (k : ℝ) := by positivity
    apply (div_le_div_iff_of_pos_right hkR).2
    exact_mod_cast (show n ≤ 2 * n - 1 by omega)
  constructor
  · exact exp_two_mul_sub_one_div_le_cofactorRadialFactor k n hk2
  · rw [integral_pastCofactorV_eq_closedFirstMoment hn (by omega : 0 < k)]
    exact cofactorRadialFactor_le_literalMomentProduct_of_inverse
      hn hk2 hVpos hInv

end RadialLowerBoundAlt

end

end LogdetLean.GramHafnian
