import LogdetLean.GramHafnian.ShiftedAnticoncentration.Experimental.WickAngularLowerBound.WickVector

/-!
# Actual-law Wick square-root estimate

This file assembles the literal Wick vector representation, the exact first
absolute moment of a spherical transpose form, and the exact even radial
moment of a real Gaussian vector.
-/

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal NNReal Real BigOperators

namespace LogdetLean.GramHafnian

noncomputable section

namespace WickAngularLowerBound

/-- The spherical coordinate mean is strictly positive in positive
dimension. -/
theorem sphereCoordinateAbsMean_pos {k : ℕ} (hk : 0 < k) :
    0 < sphereCoordinateAbsMean k := by
  unfold sphereCoordinateAbsMean
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hthree : (0 : ℝ) < 3 / 2 := by norm_num
  have hkh : (0 : ℝ) < (k : ℝ) + 1 / 2 := by positivity
  exact div_pos (mul_pos (Real.Gamma_pos_of_pos hthree)
    (Real.Gamma_pos_of_pos hkR)) (Real.Gamma_pos_of_pos hkh)

/-- A spherical transpose form has finite first absolute moment. -/
theorem integrable_norm_sphereTransposeLinearForm
    {k : ℕ} (hk : 0 < k) (y : Fin k → ℂ) :
    Integrable (fun u ↦ ‖sphereTransposeLinearForm y u‖)
      (circularGaussianSphereProbability k) := by
  by_cases hy : y = 0
  · subst y
    simpa [sphereTransposeLinearForm] using
      (integrable_zero (μ := circularGaussianSphereProbability k)
        (E := ℝ))
  · apply Integrable.of_integral_ne_zero
    rw [integral_norm_sphereTransposeLinearForm hk y]
    apply mul_ne_zero (sphereCoordinateAbsMean_pos hk).ne'
    apply (Real.sqrt_pos.2 ?_).ne'
    unfold circularCoefficientEnergy
    obtain ⟨p, hp⟩ := Function.ne_iff.mp hy
    have hpNorm : 0 < ‖y p‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hp)
    exact lt_of_lt_of_le hpNorm
      (Finset.single_le_sum (fun q _hq ↦ sq_nonneg ‖y q‖)
        (Finset.mem_univ p))

/-- For a real coordinate vector, circular coefficient energy is its
Euclidean norm squared. -/
theorem sqrt_circularCoefficientEnergy_complexified_real
    {k : ℕ} (g : Fin k → ℝ) :
    Real.sqrt (circularCoefficientEnergy (fun p ↦ (g p : ℂ))) =
      ‖WithLp.toLp 2 g‖ := by
  rw [PiLp.norm_eq_of_L2]
  unfold circularCoefficientEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro p _hp
  simp

/-- Exact product-sphere first moment for the odd family of transpose
forms. -/
theorem integral_oddSphereLinearNormProduct
    {n k : ℕ} (hn : 1 ≤ n) (hk : 0 < k) (g : Fin k → ℝ) :
    (∫ u, ∏ j, ‖sphereTransposeLinearForm
        (fun p ↦ (g p : ℂ)) (u j)‖
      ∂(RadialLowerBoundAlt.angularMeasure hn)) =
      (sphereCoordinateAbsMean k * ‖WithLp.toLp 2 g‖) ^
        (2 * n - 1) := by
  letI : IsProbabilityMeasure (circularGaussianSphereProbability k) :=
    ⟨circularGaussianSphereProbability_apply_univ hk⟩
  unfold RadialLowerBoundAlt.angularMeasure
  calc
    (∫ u : RadialLowerBoundAlt.CofactorIdx n hn →
        RadialLowerBoundAlt.Direction k,
        ∏ j, ‖sphereTransposeLinearForm
          (fun p ↦ (g p : ℂ)) (u j)‖
        ∂(Measure.pi fun _ : RadialLowerBoundAlt.CofactorIdx n hn ↦
          circularGaussianSphereProbability k)) =
        ∏ _j : RadialLowerBoundAlt.CofactorIdx n hn,
          ∫ v : RadialLowerBoundAlt.Direction k,
            ‖sphereTransposeLinearForm (fun p ↦ (g p : ℂ)) v‖
            ∂circularGaussianSphereProbability k := by
      exact integral_fintype_prod_eq_prod
        (μ := fun _ : RadialLowerBoundAlt.CofactorIdx n hn ↦
          circularGaussianSphereProbability k)
        (fun _j : RadialLowerBoundAlt.CofactorIdx n hn ↦
          fun v : RadialLowerBoundAlt.Direction k ↦
            ‖sphereTransposeLinearForm (fun p ↦ (g p : ℂ)) v‖)
    _ = (sphereCoordinateAbsMean k * ‖WithLp.toLp 2 g‖) ^
          (2 * n - 1) := by
      simp_rw [integral_norm_sphereTransposeLinearForm hk,
        sqrt_circularCoefficientEnergy_complexified_real]
      rw [Finset.prod_const, Finset.card_univ, card_oddCofactorIndex]

/-- The odd product is integrable under the literal angular law. -/
theorem integrable_oddSphereLinearNormProduct
    {n k : ℕ} (hn : 1 ≤ n) (hk : 0 < k) (g : Fin k → ℝ) :
    Integrable
      (fun u ↦ ∏ j, ‖sphereTransposeLinearForm
        (fun p ↦ (g p : ℂ)) (u j)‖)
      (RadialLowerBoundAlt.angularMeasure hn) := by
  letI : IsProbabilityMeasure (circularGaussianSphereProbability k) :=
    ⟨circularGaussianSphereProbability_apply_univ hk⟩
  unfold RadialLowerBoundAlt.angularMeasure
  exact Integrable.fintype_prod fun _j ↦
    integrable_norm_sphereTransposeLinearForm hk _

/-- The nonnegative joint norm integrand used in the Fubini step. -/
def wickNormIntegrand
    {n k : ℕ} (hn : 1 ≤ n)
    (z : (Fin k → ℝ) ×
      (RadialLowerBoundAlt.CofactorIdx n hn →
        RadialLowerBoundAlt.Direction k)) : ℝ :=
  ‖WithLp.toLp 2 z.1‖ *
    ∏ j, ‖sphereTransposeLinearForm
      (fun p ↦ (z.1 p : ℂ)) (z.2 j)‖

@[fun_prop]
theorem measurable_wickNormIntegrand
    {n k : ℕ} (hn : 1 ≤ n) :
    Measurable (wickNormIntegrand (n := n) (k := k) hn) := by
  unfold wickNormIntegrand sphereTransposeLinearForm
  fun_prop

/-- Algebraic form of the angularly integrated Wick norm. -/
theorem norm_mul_sphereMeanNorm_pow_odd
    {n k : ℕ} (hn : 1 ≤ n) (g : Fin k → ℝ) :
    ‖WithLp.toLp 2 g‖ *
        (sphereCoordinateAbsMean k * ‖WithLp.toLp 2 g‖) ^
          (2 * n - 1) =
      sphereCoordinateAbsMean k ^ (2 * n - 1) *
        ‖WithLp.toLp 2 g‖ ^ (2 * n) := by
  rw [mul_pow]
  have hsucc : 2 * n - 1 + 1 = 2 * n := by omega
  calc
    ‖WithLp.toLp 2 g‖ *
        (sphereCoordinateAbsMean k ^ (2 * n - 1) *
          ‖WithLp.toLp 2 g‖ ^ (2 * n - 1)) =
        sphereCoordinateAbsMean k ^ (2 * n - 1) *
          (‖WithLp.toLp 2 g‖ *
            ‖WithLp.toLp 2 g‖ ^ (2 * n - 1)) := by ring
    _ = sphereCoordinateAbsMean k ^ (2 * n - 1) *
          ‖WithLp.toLp 2 g‖ ^ (2 * n - 1 + 1) := by
      rw [pow_succ']
    _ = sphereCoordinateAbsMean k ^ (2 * n - 1) *
          ‖WithLp.toLp 2 g‖ ^ (2 * n) := by rw [hsucc]

/-- Every required even radial moment of the coordinate real Gaussian is
integrable. -/
theorem integrable_norm_pow_two_mul_standardRealGaussianVector
    {k : ℕ} (hk : 0 < k) (n : ℕ) :
    Integrable (fun g : Fin k → ℝ ↦ ‖WithLp.toLp 2 g‖ ^ (2 * n))
      (standardRealGaussianVector k) := by
  let E := EuclideanSpace ℝ (Fin k)
  letI : NeZero k := ⟨Nat.ne_of_gt hk⟩
  have hstd : Integrable (fun x : E ↦ ‖x‖ ^ (2 * n))
      (stdGaussian E) := by
    simpa only [id_eq] using
      (ProbabilityTheory.IsGaussian.memLp_id (stdGaussian E)
        ((2 * n : ℕ) : ℝ≥0∞) ENNReal.coe_ne_top).integrable_norm_pow'
  have hmap : Measure.map (WithLp.toLp 2)
      (standardRealGaussianVector k) = stdGaussian E := by
    unfold standardRealGaussianVector
    exact map_pi_eq_stdGaussian
  rw [← hmap] at hstd
  simpa [Function.comp_def] using
    (integrable_map_measure (by fun_prop) (by fun_prop)).1 hstd

/-- Exact even radial moment under the coordinate real Gaussian. -/
theorem integral_norm_pow_two_mul_standardRealGaussianVector
    {k : ℕ} (hk : 0 < k) (n : ℕ) :
    (∫ g : Fin k → ℝ, ‖WithLp.toLp 2 g‖ ^ (2 * n)
        ∂standardRealGaussianVector k) = dimensionProduct k n := by
  let E := EuclideanSpace ℝ (Fin k)
  letI : NeZero k := ⟨Nat.ne_of_gt hk⟩
  have hmap : Measure.map (WithLp.toLp 2)
      (standardRealGaussianVector k) = stdGaussian E := by
    unfold standardRealGaussianVector
    exact map_pi_eq_stdGaussian
  calc
    (∫ g : Fin k → ℝ, ‖WithLp.toLp 2 g‖ ^ (2 * n)
        ∂standardRealGaussianVector k) =
        ∫ x : E, ‖x‖ ^ (2 * n)
          ∂Measure.map (WithLp.toLp 2) (standardRealGaussianVector k) := by
      rw [integral_map (by fun_prop) (by fun_prop)]
    _ = ∫ x : E, ‖x‖ ^ (2 * n) ∂stdGaussian E := by rw [hmap]
    _ = dimensionProduct k n := by
      simpa [E] using
        (integral_norm_pow_two_mul_stdGaussian (E := E) n)

/-- The joint Wick norm is integrable on the product of the real Gaussian
and literal angular laws. -/
theorem integrable_wickNormIntegrand
    {n k : ℕ} (hn : 1 ≤ n) (hk : 0 < k) :
    Integrable (wickNormIntegrand (n := n) (k := k) hn)
      ((standardRealGaussianVector k).prod
        (RadialLowerBoundAlt.angularMeasure hn)) := by
  letI : IsProbabilityMeasure (circularGaussianSphereProbability k) :=
    ⟨circularGaussianSphereProbability_apply_univ hk⟩
  letI : IsProbabilityMeasure
      (RadialLowerBoundAlt.angularMeasure (n := n) (k := k) hn) := by
    unfold RadialLowerBoundAlt.angularMeasure
    infer_instance
  apply (integrable_prod_iff
    (measurable_wickNormIntegrand hn).aestronglyMeasurable).2
  constructor
  · exact ae_of_all _ fun g ↦ by
      simpa [wickNormIntegrand] using
        (integrable_oddSphereLinearNormProduct hn hk g).const_mul
          ‖WithLp.toLp 2 g‖
  · have hrad :=
      (integrable_norm_pow_two_mul_standardRealGaussianVector hk n).const_mul
        (sphereCoordinateAbsMean k ^ (2 * n - 1))
    apply hrad.congr
    filter_upwards [] with g
    symm
    have hnonneg (u : RadialLowerBoundAlt.CofactorIdx n hn →
        RadialLowerBoundAlt.Direction k) :
        0 ≤ wickNormIntegrand hn (g, u) := by
      unfold wickNormIntegrand
      positivity
    calc
      (∫ u, ‖wickNormIntegrand hn (g, u)‖
          ∂(RadialLowerBoundAlt.angularMeasure hn)) =
          ∫ u, ‖WithLp.toLp 2 g‖ *
            (∏ j, ‖sphereTransposeLinearForm
              (fun p ↦ (g p : ℂ)) (u j)‖)
            ∂(RadialLowerBoundAlt.angularMeasure hn) := by
        apply integral_congr_ae
        filter_upwards [] with u
        rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg u)]
        rfl
      _ = ‖WithLp.toLp 2 g‖ *
          (sphereCoordinateAbsMean k * ‖WithLp.toLp 2 g‖) ^
            (2 * n - 1) := by
        rw [integral_const_mul,
          integral_oddSphereLinearNormProduct hn hk g]
      _ = sphereCoordinateAbsMean k ^ (2 * n - 1) *
          ‖WithLp.toLp 2 g‖ ^ (2 * n) :=
        norm_mul_sphereMeanNorm_pow_odd hn g

/-- Integrating the joint Wick norm in the angular variables first gives
the exact spherical factor times the exact Gaussian radial moment. -/
theorem integral_realGaussian_integral_angular_wickNorm
    {n k : ℕ} (hn : 1 ≤ n) (hk : 0 < k) :
    (∫ g : Fin k → ℝ,
        ∫ u, wickNormIntegrand hn (g, u)
          ∂(RadialLowerBoundAlt.angularMeasure hn)
        ∂standardRealGaussianVector k) =
      sphereCoordinateAbsMean k ^ (2 * n - 1) *
        dimensionProduct k n := by
  calc
    (∫ g : Fin k → ℝ,
        ∫ u, wickNormIntegrand hn (g, u)
          ∂(RadialLowerBoundAlt.angularMeasure hn)
        ∂standardRealGaussianVector k) =
        ∫ g : Fin k → ℝ,
          sphereCoordinateAbsMean k ^ (2 * n - 1) *
            ‖WithLp.toLp 2 g‖ ^ (2 * n)
          ∂standardRealGaussianVector k := by
      apply integral_congr_ae
      filter_upwards [] with g
      unfold wickNormIntegrand
      simp only [Prod.fst, Prod.snd]
      rw [integral_const_mul,
        integral_oddSphereLinearNormProduct hn hk g,
        norm_mul_sphereMeanNorm_pow_odd hn g]
    _ = sphereCoordinateAbsMean k ^ (2 * n - 1) *
        (∫ g : Fin k → ℝ, ‖WithLp.toLp 2 g‖ ^ (2 * n)
          ∂standardRealGaussianVector k) := by
      rw [integral_const_mul]
    _ = sphereCoordinateAbsMean k ^ (2 * n - 1) *
        dimensionProduct k n := by
      rw [integral_norm_pow_two_mul_standardRealGaussianVector hk n]

/-- The gamma-ratio normalization in `wickSqrtMomentBound` is exactly the
elementary dimension product. -/
theorem wickSqrtMomentBound_eq_sphereMean_pow_mul_dimensionProduct
    {n k : ℕ} (hk : 0 < k) :
    wickSqrtMomentBound k n =
      sphereCoordinateAbsMean k ^ (2 * n - 1) *
        dimensionProduct k n := by
  have htwo : (2 : ℝ) ^ n =
      (1 / 2 : ℝ) ^ (-(n : ℝ)) := by
    calc
      (2 : ℝ) ^ n = ((1 / 2 : ℝ)⁻¹) ^ n := by norm_num
      _ = ((1 / 2 : ℝ) ^ (-1 : ℝ)) ^ n := by
        rw [Real.rpow_neg_one]
      _ = ((1 / 2 : ℝ) ^ (-1 : ℝ)) ^ (n : ℝ) := by
        rw [Real.rpow_natCast]
      _ = (1 / 2 : ℝ) ^ ((-1 : ℝ) * n) := by
        rw [Real.rpow_mul (by norm_num)]
      _ = (1 / 2 : ℝ) ^ (-(n : ℝ)) := by ring_nf
  unfold wickSqrtMomentBound
  rw [htwo]
  have hgamma := gammaRatio_half_eq_dimensionProduct k n hk
  rw [show (n : ℝ) + (k : ℝ) / 2 = (k : ℝ) / 2 + n by ring]
  calc
    sphereCoordinateAbsMean k ^ (2 * n - 1) *
          (1 / 2 : ℝ) ^ (-(n : ℝ)) *
          Real.Gamma ((k : ℝ) / 2 + n) /
          Real.Gamma ((k : ℝ) / 2) =
        sphereCoordinateAbsMean k ^ (2 * n - 1) *
          ((1 / 2 : ℝ) ^ (-(n : ℝ)) *
            Real.Gamma ((k : ℝ) / 2 + n) /
            Real.Gamma ((k : ℝ) / 2)) := by ring
    _ = sphereCoordinateAbsMean k ^ (2 * n - 1) *
          dimensionProduct k n := by rw [hgamma]

/-- Unconditional actual-law Wick square-root estimate. -/
theorem integral_sqrt_angularEnergy_le_wickSqrtMomentBound
    {n k : ℕ} (hn : 1 ≤ n) (hk : 0 < k) :
    (∫ u, Real.sqrt (RadialLowerBoundAlt.angularEnergy
        (n := n) (k := k) hn u)
      ∂(RadialLowerBoundAlt.angularMeasure hn)) ≤
      wickSqrtMomentBound k n := by
  letI : IsProbabilityMeasure (circularGaussianSphereProbability k) :=
    ⟨circularGaussianSphereProbability_apply_univ hk⟩
  letI : IsProbabilityMeasure
      (RadialLowerBoundAlt.angularMeasure (n := n) (k := k) hn) := by
    unfold RadialLowerBoundAlt.angularMeasure
    infer_instance
  have hjoint := integrable_wickNormIntegrand hn hk
  have hright : Integrable
      (fun u ↦ ∫ g : Fin k → ℝ, wickNormIntegrand hn (g, u)
        ∂standardRealGaussianVector k)
      (RadialLowerBoundAlt.angularMeasure hn) :=
    hjoint.integral_prod_right
  calc
    (∫ u, Real.sqrt (RadialLowerBoundAlt.angularEnergy
        (n := n) (k := k) hn u)
      ∂(RadialLowerBoundAlt.angularMeasure hn)) ≤
        ∫ u, ∫ g : Fin k → ℝ, wickNormIntegrand hn (g, u)
          ∂standardRealGaussianVector k
          ∂(RadialLowerBoundAlt.angularMeasure hn) := by
      apply integral_mono (integrable_sqrt_angularEnergy hn hk) hright
      intro u
      simpa [wickNormIntegrand] using
        sqrt_angularEnergy_le_integral_wickNorm hn u
    _ = ∫ g : Fin k → ℝ,
          ∫ u, wickNormIntegrand hn (g, u)
            ∂(RadialLowerBoundAlt.angularMeasure hn)
          ∂standardRealGaussianVector k := by
      have hjoint' : Integrable
          (Function.uncurry fun g u ↦ wickNormIntegrand hn (g, u))
          ((standardRealGaussianVector k).prod
            (RadialLowerBoundAlt.angularMeasure hn)) := by
        apply hjoint.congr
        filter_upwards [] with z
        rfl
      have hswap := integral_integral_swap
        (μ := standardRealGaussianVector k)
        (ν := RadialLowerBoundAlt.angularMeasure hn)
        (f := fun g u ↦ wickNormIntegrand hn (g, u))
        hjoint'
      exact hswap.symm
    _ = sphereCoordinateAbsMean k ^ (2 * n - 1) *
          dimensionProduct k n :=
      integral_realGaussian_integral_angular_wickNorm hn hk
    _ = wickSqrtMomentBound k n :=
      (wickSqrtMomentBound_eq_sphereMean_pow_mul_dimensionProduct hk).symm

/-- The Wick bound itself is strictly positive. -/
theorem wickSqrtMomentBound_pos
    {n k : ℕ} (hn : 1 ≤ n) (hk : 0 < k) :
    0 < wickSqrtMomentBound k n := by
  rw [wickSqrtMomentBound_eq_sphereMean_pow_mul_dimensionProduct hk]
  exact mul_pos (pow_pos (sphereCoordinateAbsMean_pos hk) _)
    (dimensionProduct_pos k n hk)

/-- Unconditional extended-valued actual-law angular lower bound.  No
inverse-integrability assumption is present. -/
theorem wickAngularRatioENN_le_angularConditionNumberENN
    {n k : ℕ} (hn : 1 ≤ n) (hk : 0 < k) :
    wickAngularRatioENN k n ≤ angularConditionNumberENN (k := k) hn := by
  exact wickAngularRatioENN_le_angularConditionNumberENN_of_sqrt_bound
    hn hk (integral_sqrt_angularEnergy_le_wickSqrtMomentBound hn hk)
    (wickSqrtMomentBound_pos hn hk)

/-- The extended angular condition number is always at least one.  This is
valid even when the inverse angular moment diverges. -/
theorem one_le_angularConditionNumberENN
    {n k : ℕ} (hn : 1 ≤ n) (hk : 0 < k) :
    1 ≤ angularConditionNumberENN (k := k) hn := by
  letI : ∀ _ : RadialLowerBoundAlt.CofactorIdx n hn,
      IsProbabilityMeasure (circularGaussianSphereProbability k) :=
    fun _ ↦ ⟨circularGaussianSphereProbability_apply_univ hk⟩
  letI : IsProbabilityMeasure
      (RadialLowerBoundAlt.angularMeasure (k := k) hn) := by
    unfold RadialLowerBoundAlt.angularMeasure
    infer_instance
  let X : (RadialLowerBoundAlt.CofactorIdx n hn →
      RadialLowerBoundAlt.Direction k) → ENNReal :=
    fun u ↦ ENNReal.ofReal (RadialLowerBoundAlt.angularEnergy hn u)
  have hX : AEMeasurable X (RadialLowerBoundAlt.angularMeasure hn) :=
    (RadialLowerBoundAlt.measurable_angularEnergy hn).ennreal_ofReal.aemeasurable
  have hXtop : ∀ᵐ u ∂(RadialLowerBoundAlt.angularMeasure
      (n := n) (k := k) hn), X u ≠ ⊤ :=
    ae_of_all _ fun _ ↦ ENNReal.ofReal_ne_top
  have hEsqrt0 :
      (∫⁻ u, (X u) ^ (1 / 2 : ℝ)
        ∂(RadialLowerBoundAlt.angularMeasure hn)) ≠ 0 := by
    rw [show (∫⁻ u, (X u) ^ (1 / 2 : ℝ)
        ∂(RadialLowerBoundAlt.angularMeasure hn)) =
      ENNReal.ofReal
        (∫ u, Real.sqrt (RadialLowerBoundAlt.angularEnergy hn u)
          ∂(RadialLowerBoundAlt.angularMeasure hn)) by
      simpa [X] using
        lintegral_rpow_half_angularEnergy_eq_ofReal_integral_sqrt hn hk]
    exact (ENNReal.ofReal_pos.mpr
      (integral_sqrt_angularEnergy_pos hn hk)).ne'
  have hcore := one_le_sq_lintegral_sqrt_mul_lintegral_inv
    (RadialLowerBoundAlt.angularMeasure (n := n) (k := k) hn)
    X hX hXtop hEsqrt0
  have hsq := sq_lintegral_le_lintegral_sq
    (RadialLowerBoundAlt.angularMeasure (n := n) (k := k) hn)
    (fun u ↦ (X u) ^ (1 / 2 : ℝ)) (hX.pow_const _)
  have hsqPoint (x : ENNReal) :
      (x ^ (1 / 2 : ℝ)) ^ (2 : ℕ) = x := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hsq' :
      (∫⁻ u, (X u) ^ (1 / 2 : ℝ)
        ∂(RadialLowerBoundAlt.angularMeasure hn)) ^ 2 ≤
      ∫⁻ u, X u ∂(RadialLowerBoundAlt.angularMeasure hn) := by
    simpa only [hsqPoint] using hsq
  unfold angularConditionNumberENN
  apply hcore.trans
  simpa [mul_comm, X] using (mul_le_mul_right hsq'
    (∫⁻ u, (X u)⁻¹ ∂(RadialLowerBoundAlt.angularMeasure hn)))

end WickAngularLowerBound

end

end LogdetLean.GramHafnian
