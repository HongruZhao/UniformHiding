import LogdetLean.GramHafnian.ShiftedAnticoncentration.Experimental.WickAngularLowerBound.WickSqrtBound
import LogdetLean.GramHafnian.ShiftedAnticoncentration.Experimental.WickAngularLowerBound.ScalarMomentBridge
import LogdetLean.GramHafnian.ShiftedAnticoncentration.Experimental.ConditionalInverseDensity.RadialAngular

/-!
# Paper endpoints for the Wick angular obstruction

These declarations combine the unconditional actual-law square-root theorem
with the exact rational finite-range certificate.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

namespace LogdetLean.GramHafnian.WickAngularLowerBound

noncomputable section

private lemma one_le_of_thousand_le {n : ℕ} (hn : 1000 ≤ n) : 1 ≤ n := by
  omega

/-- The real and extended-valued Wick ratios agree in positive dimension. -/
theorem ofReal_wickAngularRatio_eq_wickAngularRatioENN
    (k n : ℕ) (hk : 0 < k) :
    ENNReal.ofReal (wickAngularRatio k n) = wickAngularRatioENN k n := by
  have hbound : 0 < wickSqrtMomentBound k n := by
    rw [wickSqrtMomentBound_eq_sphereMean_pow_mul_dimensionProduct hk]
    exact mul_pos (pow_pos (sphereCoordinateAbsMean_pos hk) _)
      (dimensionProduct_pos k n hk)
  unfold wickAngularRatio wickAngularRatioENN
  rw [ENNReal.ofReal_div_of_pos (sq_pos_of_pos hbound),
    ENNReal.ofReal_pow hbound.le]

/-- Fully finite, actual-law negative result.  If `n ≥ 1000` and
`2 ≤ k ≤ n/3`, the extended angular condition number grows at least as
`exp(n/500)`.  No inverse-integrability assumption is needed. -/
theorem exp_n_div_500_le_angularConditionNumberENN
    {k n : ℕ} (hn : 1000 ≤ n) (hklo : 2 ≤ k) (hkhi : 3 * k ≤ n) :
    ENNReal.ofReal (Real.exp ((n : ℝ) / 500)) ≤
      angularConditionNumberENN (k := k) (by omega : 1 ≤ n) := by
  calc
    ENNReal.ofReal (Real.exp ((n : ℝ) / 500)) ≤
        ENNReal.ofReal (wickAngularRatio k n) :=
      ENNReal.ofReal_le_ofReal
        (exp_n_div_500_le_wickAngularRatio hn hklo hkhi)
    _ = wickAngularRatioENN k n :=
      ofReal_wickAngularRatio_eq_wickAngularRatioENN k n (by omega)
    _ ≤ angularConditionNumberENN (k := k) (by omega : 1 ≤ n) :=
      wickAngularRatioENN_le_angularConditionNumberENN (by omega) (by omega)

/-- Ordinary-moment form of the negative result.  Once positivity and
inverse integrability of the full conditional variance are available, the
exact radial--angular factorization transfers the unconditional extended
angular obstruction to the paper coefficient `Lambda`. -/
theorem exp_n_div_500_le_literalLambda_of_inverse
    {k n : ℕ} (hn : 1000 ≤ n) (hklo : 2 ≤ k) (hkhi : 3 * k ≤ n)
    (hVpos :
      ∀ᵐ A : RadialLowerBoundAlt.CofactorIdx n (one_le_of_thousand_le hn) →
          (Fin k → ℂ)
        ∂(Measure.pi fun _ : RadialLowerBoundAlt.CofactorIdx n
          (one_le_of_thousand_le hn) ↦ circularGaussianVector k),
        0 < pastCofactorV (one_le_of_thousand_le hn) A)
    (hInv : Integrable
      (fun A : RadialLowerBoundAlt.CofactorIdx n (one_le_of_thousand_le hn) →
          (Fin k → ℂ) ↦ (pastCofactorV (one_le_of_thousand_le hn) A)⁻¹)
      (Measure.pi fun _ : RadialLowerBoundAlt.CofactorIdx n
        (one_le_of_thousand_le hn) ↦ circularGaussianVector k)) :
    Real.exp ((n : ℝ) / 500) ≤
      closedFirstMoment k n *
        (∫ A : RadialLowerBoundAlt.CofactorIdx n (one_le_of_thousand_le hn) →
            (Fin k → ℂ),
          (pastCofactorV (one_le_of_thousand_le hn) A)⁻¹
          ∂(Measure.pi fun _ : RadialLowerBoundAlt.CofactorIdx n
            (one_le_of_thousand_le hn) ↦ circularGaussianVector k)) := by
  let hn1 : 1 ≤ n := one_le_of_thousand_le hn
  have hkpos : 0 < k := by omega
  have hangPos := RadialLowerBoundAlt.ae_angularEnergy_pos_of_ae
    hn1 hkpos hVpos
  have hangInv := RadialLowerBoundAlt.integrable_inv_angularEnergy_of_inverse
    hn1 hklo hVpos hInv
  have hangular : Real.exp ((n : ℝ) / 500) ≤
      (∫ u, RadialLowerBoundAlt.angularEnergy
          (n := n) (k := k) hn1 u
        ∂(RadialLowerBoundAlt.angularMeasure hn1)) *
      (∫ u, (RadialLowerBoundAlt.angularEnergy
          (n := n) (k := k) hn1 u)⁻¹
        ∂(RadialLowerBoundAlt.angularMeasure hn1)) :=
    (exp_n_div_500_le_wickAngularRatio hn hklo hkhi).trans
      (wickAngularRatio_le_literalAngularMomentProduct_of_sqrt_bound
        hn1 hkpos hangPos hangInv
        (integral_sqrt_angularEnergy_le_wickSqrtMomentBound hn1 hkpos)
        (wickSqrtMomentBound_pos hn1 hkpos))
  rw [RadialLowerBoundAlt.literalLambda_eq_radial_mul_angularMomentProduct_of_k_ge_two
    hn1 hklo]
  have hrad : 1 ≤ cofactorRadialFactor k n := by
    unfold cofactorRadialFactor
    have hbase : (1 : ℝ) ≤ (k : ℝ) / ((k : ℝ) - 1) := by
      have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hklo
      apply (le_div_iff₀ (by linarith)).2
      linarith
    exact one_le_pow₀ hbase
  have hangNonneg : 0 ≤
      (∫ u, RadialLowerBoundAlt.angularEnergy
          (n := n) (k := k) hn1 u
        ∂(RadialLowerBoundAlt.angularMeasure hn1)) *
      (∫ u, (RadialLowerBoundAlt.angularEnergy
          (n := n) (k := k) hn1 u)⁻¹
        ∂(RadialLowerBoundAlt.angularMeasure hn1)) :=
    (Real.exp_pos _).le.trans hangular
  exact hangular.trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hrad hangNonneg)

end

end LogdetLean.GramHafnian.WickAngularLowerBound
