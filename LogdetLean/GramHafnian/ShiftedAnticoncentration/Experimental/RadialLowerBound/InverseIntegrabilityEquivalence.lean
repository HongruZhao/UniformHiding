import LogdetLean.GramHafnian.ShiftedAnticoncentration.Experimental.ConditionalInverseDensity.RadialAngular

/-!
# Exact radial--angular inverse-integrability reduction

The reciprocal radial product has a finite moment exactly when `2 ≤ k`.
In that range, polar reconstruction reduces integrability of the reciprocal
Gaussian cofactor variance to integrability of the reciprocal angular energy.

Lean's field inverse satisfies `0⁻¹ = 0`.  The algebraic integrability
equivalence below is therefore valid without a positivity assumption.  To
interpret the reciprocal as the extended random variable used in the paper,
one additionally assumes almost-everywhere positivity of `pastCofactorV`;
the final paper-facing theorem records that hypothesis and transports it to
the angular energy.
-/

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal NNReal Real BigOperators

namespace LogdetLean.GramHafnian

noncomputable section

namespace RadialLowerBoundAlt

variable {n k : ℕ} (hn : 1 ≤ n)

/-- Integrability of the reciprocal Gaussian cofactor variance implies
integrability of the reciprocal angular energy.  This algebraic implication
only needs `k > 0`; it does not use positivity of the cofactor variance because
Lean defines `0⁻¹ = 0`. -/
theorem integrable_inv_angularEnergy_of_full
    (hkpos : 0 < k)
    (hInv : Integrable
      (fun A : CofactorIdx n hn → (Fin k → ℂ) ↦
        (pastCofactorV hn A)⁻¹)
      (Measure.pi fun _ : CofactorIdx n hn ↦ circularGaussianVector k)) :
    Integrable (fun u ↦ (angularEnergy (n := n) (k := k) hn u)⁻¹)
      (angularMeasure hn) := by
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
  have hpull : Integrable
      ((fun A : CofactorIdx n hn → (Fin k → ℂ) ↦
        (pastCofactorV hn A)⁻¹) ∘ splitPolarReconstruct hn)
      (splitPolarMeasure (k := k) hn) :=
    hT.integrable_comp_of_integrable hInv
  have hprod : Integrable
      (fun z ↦ (angularEnergy (n := n) (k := k) hn z.1)⁻¹ *
        (squaredRadiusProduct (n := n) hn z.2)⁻¹)
      (splitPolarMeasure (k := k) hn) := by
    apply hpull.congr
    filter_upwards [] with z
    simp only [Function.comp_apply]
    rw [pastCofactorV_splitPolarReconstruct hn]
    simp [mul_inv_rev, mul_comm]
  have hsections := hprod.prod_left_ae
  obtain ⟨r, hr⟩ := hsections.exists
  have hradpos : 0 < (squaredRadiusProduct (n := n) hn r)⁻¹ := by
    apply inv_pos.mpr
    unfold squaredRadiusProduct
    exact Finset.prod_pos fun j _ ↦ sq_pos_of_pos (r j).2
  have hscale : Integrable
      (fun u ↦ ((squaredRadiusProduct (n := n) hn r)⁻¹)⁻¹ *
        ((angularEnergy (n := n) (k := k) hn u)⁻¹ *
          (squaredRadiusProduct (n := n) hn r)⁻¹))
      (angularMeasure hn) := hr.const_mul _
  apply hscale.congr
  filter_upwards [] with u
  have hradne : squaredRadiusProduct (n := n) hn r ≠ 0 := by
    intro hzero
    simp [hzero] at hradpos
  simp only [inv_inv]
  calc
    squaredRadiusProduct hn r *
        ((angularEnergy hn u)⁻¹ * (squaredRadiusProduct hn r)⁻¹) =
      (angularEnergy hn u)⁻¹ *
        (squaredRadiusProduct hn r * (squaredRadiusProduct hn r)⁻¹) := by
          ring
    _ = (angularEnergy hn u)⁻¹ := by rw [mul_inv_cancel₀ hradne, mul_one]

/-- If the reciprocal angular energy is integrable and `k ≥ 2`, then the
reciprocal Gaussian cofactor variance is integrable. -/
theorem integrable_inv_pastCofactorV_of_angularEnergy
    (hk2 : 2 ≤ k)
    (hAng : Integrable
      (fun u ↦ (angularEnergy (n := n) (k := k) hn u)⁻¹)
      (angularMeasure hn)) :
    Integrable
      (fun A : CofactorIdx n hn → (Fin k → ℂ) ↦
        (pastCofactorV hn A)⁻¹)
      (Measure.pi fun _ : CofactorIdx n hn ↦ circularGaussianVector k) := by
  have hkpos : 0 < k := by omega
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
  have hrad := integrable_inv_squaredRadiusProduct hn hk2
  have hprod : Integrable
      (fun z ↦ (angularEnergy (n := n) (k := k) hn z.1)⁻¹ *
        (squaredRadiusProduct (n := n) hn z.2)⁻¹)
      (splitPolarMeasure (k := k) hn) :=
    hAng.mul_prod hrad
  have hpull : Integrable
      ((fun A : CofactorIdx n hn → (Fin k → ℂ) ↦
        (pastCofactorV hn A)⁻¹) ∘ splitPolarReconstruct hn)
      (splitPolarMeasure (k := k) hn) := by
    apply hprod.congr
    filter_upwards [] with z
    simp only [Function.comp_apply]
    rw [pastCofactorV_splitPolarReconstruct hn]
    simp [mul_inv_rev, mul_comm]
  exact (hT.integrable_comp
    (measurable_pastCofactorV hn).inv.aestronglyMeasurable).mp hpull

/-- Exact inverse-integrability equivalence for `k ≥ 2`.  This theorem uses
Lean's ordinary inverse (`0⁻¹ = 0`); the paper-facing corollary below supplies
the almost-everywhere positivity needed for the extended reciprocal-moment
interpretation. -/
theorem integrable_inv_pastCofactorV_iff_angularEnergy
    (hk2 : 2 ≤ k) :
    Integrable
      (fun A : CofactorIdx n hn → (Fin k → ℂ) ↦
        (pastCofactorV hn A)⁻¹)
      (Measure.pi fun _ : CofactorIdx n hn ↦ circularGaussianVector k) ↔
    Integrable
      (fun u ↦ (angularEnergy (n := n) (k := k) hn u)⁻¹)
      (angularMeasure hn) := by
  constructor
  · exact integrable_inv_angularEnergy_of_full hn (by omega)
  · exact integrable_inv_pastCofactorV_of_angularEnergy hn hk2

/-- Whenever the reciprocal moment is finite, its exact radial factor is
`(k - 1)^{-(2n-1)}` and all remaining integrability is angular. -/
theorem integral_inv_pastCofactorV_eq_radial_inverse_mul_angular
    (hk2 : 2 ≤ k)
    (_hInv : Integrable
      (fun A : CofactorIdx n hn → (Fin k → ℂ) ↦
        (pastCofactorV hn A)⁻¹)
      (Measure.pi fun _ : CofactorIdx n hn ↦ circularGaussianVector k)) :
    (∫ A : CofactorIdx n hn → (Fin k → ℂ),
        (pastCofactorV hn A)⁻¹
      ∂(Measure.pi fun _ : CofactorIdx n hn ↦ circularGaussianVector k)) =
      ((((k : ℝ) - 1)⁻¹) ^ (2 * n - 1)) *
        ∫ u, (angularEnergy (n := n) (k := k) hn u)⁻¹
          ∂angularMeasure hn := by
  have hkpos : 0 < k := by omega
  rw [integral_inv_pastCofactorV_eq_angular_mul_radial hn hkpos,
    integral_inv_squaredRadiusProduct hn hk2]
  ring

/-- Paper-facing reduction.  The full variance is assumed positive almost
surely, so the ordinary inverse coincides almost surely with the extended
reciprocal random variable.  Positivity also descends to the angular energy. -/
theorem paperInverseIntegrabilityReduction
    (hk2 : 2 ≤ k)
    (hVpos :
      ∀ᵐ A : CofactorIdx n hn → (Fin k → ℂ)
        ∂(Measure.pi fun _ : CofactorIdx n hn ↦ circularGaussianVector k),
        0 < pastCofactorV hn A) :
    (Integrable
        (fun A : CofactorIdx n hn → (Fin k → ℂ) ↦
          (pastCofactorV hn A)⁻¹)
        (Measure.pi fun _ : CofactorIdx n hn ↦ circularGaussianVector k) ↔
      Integrable
        (fun u ↦ (angularEnergy (n := n) (k := k) hn u)⁻¹)
        (angularMeasure hn)) ∧
    (∀ᵐ u ∂angularMeasure (n := n) (k := k) hn,
      0 < angularEnergy (n := n) (k := k) hn u) := by
  exact ⟨integrable_inv_pastCofactorV_iff_angularEnergy hn hk2,
    ae_angularEnergy_pos_of_ae hn (by omega) hVpos⟩

end RadialLowerBoundAlt

end

end LogdetLean.GramHafnian
