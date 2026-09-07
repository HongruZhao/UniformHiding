import LogdetLean.GramHafnian.ShiftedAnticoncentration.Experimental.GaussianPolar.CircularGaussianPolarPi
import LogdetLean.GramHafnian.ShiftedAnticoncentration.Experimental.GaussianPolar.PositiveRadiusMoments
import LogdetLean.GramHafnian.ShiftedAnticoncentration.Experimental.RadialCofactorSeparateHomogeneity
import LogdetLean.GramHafnian.ShiftedAnticoncentration.Experimental.RadialCofactorFirstMoment
import LogdetLean.GramHafnian.ShiftedAnticoncentration.Experimental.RadialLowerBound.InverseIntegrabilityBridge
import LogdetLean.GramHafnian.ShiftedAnticoncentration.Experimental.RadialLowerBound.ExtendedCauchySchwarz
import LogdetLean.GramHafnian.ShiftedAnticoncentration.Experimental.RadialMoment.Factorization
import LogdetLean.GramHafnian.ShiftedAnticoncentration.Experimental.RadialScalarBounds
import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.LiteralRegularizedLimit
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Literal radial lower bound for the Gram-hafnian cofactor mixture

This file combines the exact circular-Gaussian polar law, deterministic
separate-column homogeneity, and the already proved finite inverse moment in
the paper range.  It is isolated until its statement and axiom audit have been
matched to the manuscript.
-/

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal NNReal Real BigOperators

namespace LogdetLean.GramHafnian

noncomputable section

namespace RadialLowerBoundAlt

variable {n k : ℕ} (hn : 1 ≤ n)

abbrev CofactorIdx (n : ℕ) (hn : 1 ≤ n) := OddCofactorIndex n hn
abbrev Direction (k : ℕ) := sphere (0 : CircularEuclideanSpace k) 1
abbrev PositiveRadius := Ioi (0 : ℝ)

def angularMeasure : Measure (CofactorIdx n hn → Direction k) :=
  Measure.pi fun _ : CofactorIdx n hn ↦ circularGaussianSphereProbability k

def radiusMeasure : Measure (CofactorIdx n hn → PositiveRadius) :=
  Measure.pi fun _ : CofactorIdx n hn ↦ circularGaussianPositiveRadiusMeasure k

def splitPolarMeasure : Measure
    ((CofactorIdx n hn → Direction k) × (CofactorIdx n hn → PositiveRadius)) :=
  (angularMeasure hn).prod (radiusMeasure (k := k) hn)

def directionColumns (u : CofactorIdx n hn → Direction k) :
    CofactorIdx n hn → (Fin k → ℂ) :=
  fun j p ↦ WithLp.ofLp (u j).1 p

def splitPolarReconstruct
    (z : (CofactorIdx n hn → Direction k) ×
      (CofactorIdx n hn → PositiveRadius)) :
    CofactorIdx n hn → (Fin k → ℂ) :=
  fun j ↦ circularGaussianPolarRawReconstruct k (z.1 j, z.2 j)

def squaredRadiusProduct (r : CofactorIdx n hn → PositiveRadius) : ℝ :=
  ∏ j, (r j : ℝ) ^ 2

def angularEnergy (u : CofactorIdx n hn → Direction k) : ℝ :=
  pastCofactorV hn (directionColumns hn u)

@[fun_prop]
theorem measurable_directionColumns :
    Measurable (directionColumns (n := n) (k := k) hn) := by
  unfold directionColumns
  fun_prop

@[fun_prop]
theorem measurable_splitPolarReconstruct :
    Measurable (splitPolarReconstruct (n := n) (k := k) hn) := by
  unfold splitPolarReconstruct
  fun_prop

@[fun_prop]
theorem measurable_squaredRadiusProduct :
    Measurable (squaredRadiusProduct (n := n) hn :
      (CofactorIdx n hn → PositiveRadius) → ℝ) := by
  unfold squaredRadiusProduct
  fun_prop

@[fun_prop]
theorem measurable_angularEnergy :
    Measurable (angularEnergy (n := n) (k := k) hn) := by
  unfold angularEnergy
  exact (measurable_pastCofactorV hn).comp
    (measurable_directionColumns (n := n) (k := k) hn)

theorem splitPolarReconstruct_apply
    (u : CofactorIdx n hn → Direction k)
    (r : CofactorIdx n hn → PositiveRadius)
    (j : CofactorIdx n hn) (p : Fin k) :
    splitPolarReconstruct hn (u, r) j p =
      ((r j : ℝ) : ℂ) * directionColumns hn u j p := by
  simp [splitPolarReconstruct, directionColumns,
    circularGaussianPolarRawReconstruct_apply]

theorem pastCofactorV_splitPolarReconstruct
    (u : CofactorIdx n hn → Direction k)
    (r : CofactorIdx n hn → PositiveRadius) :
    pastCofactorV hn (splitPolarReconstruct hn (u, r)) =
      squaredRadiusProduct hn r * angularEnergy hn u := by
  have hfun : splitPolarReconstruct hn (u, r) =
      fun j p ↦ (((r j : ℝ) : ℂ) * directionColumns hn u j p) := by
    funext j p
    exact splitPolarReconstruct_apply hn u r j p
  rw [hfun, pastCofactorV_separateColumnScale]
  simp only [Complex.normSq_ofReal]
  simp [squaredRadiusProduct, angularEnergy, pow_two]

theorem map_splitPolarReconstruct (hk : 0 < k) :
    Measure.map (splitPolarReconstruct (n := n) (k := k) hn)
        (splitPolarMeasure (k := k) hn) =
      Measure.pi (fun _ : CofactorIdx n hn ↦ circularGaussianVector k) := by
  letI : ∀ _ : CofactorIdx n hn,
      IsProbabilityMeasure (circularGaussianSphereProbability k) :=
    fun _ ↦ ⟨circularGaussianSphereProbability_apply_univ hk⟩
  letI : ∀ _ : CofactorIdx n hn,
      IsProbabilityMeasure (circularGaussianPositiveRadiusMeasure k) :=
    fun _ ↦ isProbabilityMeasure_circularGaussianPositiveRadiusMeasure hk
  letI : IsProbabilityMeasure (angularMeasure (k := k) hn) := by
    unfold angularMeasure
    infer_instance
  letI : IsProbabilityMeasure (radiusMeasure (k := k) hn) := by
    unfold radiusMeasure
    infer_instance
  let E := MeasurableEquiv.arrowProdEquivProdArrow
    (Direction k) PositiveRadius (CofactorIdx n hn)
  let pairMu : Measure (CofactorIdx n hn → Direction k × PositiveRadius) :=
    Measure.pi fun _ : CofactorIdx n hn ↦
      (circularGaussianSphereProbability k).prod
        (circularGaussianPositiveRadiusMeasure k)
  have hregroup : MeasurePreserving E pairMu (splitPolarMeasure (k := k) hn) := by
    exact measurePreserving_arrowProdEquivProdArrow
      (Direction k) PositiveRadius (CofactorIdx n hn)
      (fun _ ↦ circularGaussianSphereProbability k)
      (fun _ ↦ circularGaussianPositiveRadiusMeasure k)
  have hpair := map_pi_circularGaussianPolarFamilyReconstruct
    (ι := CofactorIdx n hn) hk
  have hcomp : splitPolarReconstruct (n := n) (k := k) hn =
      circularGaussianPolarFamilyReconstruct k ∘ E.symm := by
    funext z
    rfl
  rw [hcomp, ← Measure.map_map
    (measurable_circularGaussianPolarFamilyReconstruct k) E.symm.measurable]
  rw [hregroup.symm.map_eq]
  exact hpair

theorem integrable_sq_positiveRadius (hk : 0 < k) :
    Integrable (fun r : PositiveRadius ↦ (r.1 : ℝ) ^ 2)
      (circularGaussianPositiveRadiusMeasure k) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_sq_circularGaussianPositiveRadiusMeasure hk]
  exact_mod_cast (Nat.ne_of_gt hk)

theorem integrable_inv_sq_positiveRadius (hk : 2 ≤ k) :
    Integrable (fun r : PositiveRadius ↦ ((r.1 : ℝ) ^ 2)⁻¹)
      (circularGaussianPositiveRadiusMeasure k) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_inv_sq_circularGaussianPositiveRadiusMeasure hk]
  apply inv_ne_zero
  have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  linarith

theorem integrable_squaredRadiusProduct (hk : 0 < k) :
    Integrable (squaredRadiusProduct (n := n) hn)
      (radiusMeasure (k := k) hn) := by
  letI : ∀ _ : CofactorIdx n hn,
      IsProbabilityMeasure (circularGaussianPositiveRadiusMeasure k) :=
    fun _ ↦ isProbabilityMeasure_circularGaussianPositiveRadiusMeasure hk
  exact Integrable.fintype_prod
    (f := fun _ : CofactorIdx n hn ↦
      fun r : PositiveRadius ↦ (r.1 : ℝ) ^ 2)
    (fun _ ↦ integrable_sq_positiveRadius (k := k) hk)

theorem integrable_inv_squaredRadiusProduct (hk : 2 ≤ k) :
    Integrable (fun r ↦ (squaredRadiusProduct (n := n) hn r)⁻¹)
      (radiusMeasure (k := k) hn) := by
  have hkpos : 0 < k := by omega
  letI : ∀ _ : CofactorIdx n hn,
      IsProbabilityMeasure (circularGaussianPositiveRadiusMeasure k) :=
    fun _ ↦ isProbabilityMeasure_circularGaussianPositiveRadiusMeasure hkpos
  simp_rw [squaredRadiusProduct, ← Finset.prod_inv_distrib]
  exact Integrable.fintype_prod
    (f := fun _ : CofactorIdx n hn ↦
      fun r : PositiveRadius ↦ ((r.1 : ℝ) ^ 2)⁻¹)
    (fun _ ↦ integrable_inv_sq_positiveRadius (k := k) hk)

theorem integral_squaredRadiusProduct (hk : 0 < k) :
    (∫ r, squaredRadiusProduct (n := n) hn r
      ∂radiusMeasure (k := k) hn) = (k : ℝ) ^ (2 * n - 1) := by
  letI : ∀ _ : CofactorIdx n hn,
      IsProbabilityMeasure (circularGaussianPositiveRadiusMeasure k) :=
    fun _ ↦ isProbabilityMeasure_circularGaussianPositiveRadiusMeasure hk
  unfold squaredRadiusProduct radiusMeasure
  rw [integral_fintype_prod_eq_prod
    (fun _ : CofactorIdx n hn ↦
      fun r : PositiveRadius ↦ (r.1 : ℝ) ^ 2)]
  simp_rw [integral_sq_circularGaussianPositiveRadiusMeasure hk]
  rw [Finset.prod_const, Finset.card_univ, card_oddCofactorIndex n hn]

theorem integral_inv_squaredRadiusProduct (hk : 2 ≤ k) :
    (∫ r, (squaredRadiusProduct (n := n) hn r)⁻¹
      ∂radiusMeasure (k := k) hn) =
      (((k : ℝ) - 1)⁻¹) ^ (2 * n - 1) := by
  have hkpos : 0 < k := by omega
  letI : ∀ _ : CofactorIdx n hn,
      IsProbabilityMeasure (circularGaussianPositiveRadiusMeasure k) :=
    fun _ ↦ isProbabilityMeasure_circularGaussianPositiveRadiusMeasure hkpos
  simp_rw [squaredRadiusProduct, ← Finset.prod_inv_distrib]
  unfold radiusMeasure
  rw [integral_fintype_prod_eq_prod
    (fun _ : CofactorIdx n hn ↦
      fun r : PositiveRadius ↦ ((r.1 : ℝ) ^ 2)⁻¹)]
  simp_rw [integral_inv_sq_circularGaussianPositiveRadiusMeasure hk]
  rw [Finset.prod_const, Finset.card_univ, card_oddCofactorIndex n hn]

theorem lintegral_squaredRadiusProduct (hk : 0 < k) :
    (∫⁻ r, ENNReal.ofReal (squaredRadiusProduct (n := n) hn r)
      ∂radiusMeasure (k := k) hn) =
      ENNReal.ofReal ((k : ℝ) ^ (2 * n - 1)) := by
  have hnonneg : 0 ≤ᵐ[radiusMeasure (k := k) hn]
      squaredRadiusProduct (n := n) hn := by
    exact ae_of_all _ fun r ↦ Finset.prod_nonneg fun j _ ↦ sq_nonneg (r j).1
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_squaredRadiusProduct hn hk) hnonneg]
  rw [integral_squaredRadiusProduct hn hk]

theorem lintegral_inv_squaredRadiusProduct (hk : 2 ≤ k) :
    (∫⁻ r, ENNReal.ofReal ((squaredRadiusProduct (n := n) hn r)⁻¹)
      ∂radiusMeasure (k := k) hn) =
      ENNReal.ofReal ((((k : ℝ) - 1)⁻¹) ^ (2 * n - 1)) := by
  have hnonneg : 0 ≤ᵐ[radiusMeasure (k := k) hn]
      (fun r ↦ (squaredRadiusProduct (n := n) hn r)⁻¹) := by
    exact ae_of_all _ fun r ↦ inv_nonneg.mpr
      (Finset.prod_nonneg fun j _ ↦ sq_nonneg (r j).1)
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_inv_squaredRadiusProduct hn hk) hnonneg]
  rw [integral_inv_squaredRadiusProduct hn hk]

/-- The literal Gaussian first moment splits into its radial and angular
factors under the exact finite-family polar reconstruction. -/
theorem integral_pastCofactorV_eq_angular_mul_radial (hk : 0 < k) :
    (∫ A : CofactorIdx n hn → (Fin k → ℂ), pastCofactorV hn A
        ∂(Measure.pi fun _ : CofactorIdx n hn ↦ circularGaussianVector k)) =
      (∫ u, angularEnergy (n := n) (k := k) hn u ∂angularMeasure hn) *
        ∫ r, squaredRadiusProduct (n := n) hn r
          ∂radiusMeasure (k := k) hn := by
  letI : ∀ _ : CofactorIdx n hn,
      IsProbabilityMeasure (circularGaussianSphereProbability k) :=
    fun _ ↦ ⟨circularGaussianSphereProbability_apply_univ hk⟩
  letI : ∀ _ : CofactorIdx n hn,
      IsProbabilityMeasure (circularGaussianPositiveRadiusMeasure k) :=
    fun _ ↦ isProbabilityMeasure_circularGaussianPositiveRadiusMeasure hk
  letI : IsProbabilityMeasure (angularMeasure (k := k) hn) := by
    unfold angularMeasure
    infer_instance
  letI : IsProbabilityMeasure (radiusMeasure (k := k) hn) := by
    unfold radiusMeasure
    infer_instance
  have hmap := map_splitPolarReconstruct (n := n) (k := k) hn hk
  calc
    (∫ A : CofactorIdx n hn → (Fin k → ℂ), pastCofactorV hn A
        ∂(Measure.pi fun _ : CofactorIdx n hn ↦ circularGaussianVector k)) =
        ∫ A, pastCofactorV hn A
          ∂Measure.map (splitPolarReconstruct hn) (splitPolarMeasure hn) := by
            rw [hmap]
    _ = ∫ z, pastCofactorV hn (splitPolarReconstruct hn z)
          ∂splitPolarMeasure hn := by
            rw [integral_map (measurable_splitPolarReconstruct hn).aemeasurable
              (measurable_pastCofactorV hn).aestronglyMeasurable]
    _ = ∫ z, angularEnergy hn z.1 * squaredRadiusProduct hn z.2
          ∂splitPolarMeasure hn := by
            apply integral_congr_ae
            filter_upwards [] with z
            rw [pastCofactorV_splitPolarReconstruct hn]
            ring
    _ = (∫ u, angularEnergy hn u ∂angularMeasure hn) *
          ∫ r, squaredRadiusProduct hn r ∂radiusMeasure (k := k) hn := by
            exact integral_prod_mul (angularEnergy hn) (squaredRadiusProduct hn)

/-- The literal Gaussian reciprocal moment has the same split form. -/
theorem integral_inv_pastCofactorV_eq_angular_mul_radial (hk : 0 < k) :
    (∫ A : CofactorIdx n hn → (Fin k → ℂ), (pastCofactorV hn A)⁻¹
        ∂(Measure.pi fun _ : CofactorIdx n hn ↦ circularGaussianVector k)) =
      (∫ u, (angularEnergy (n := n) (k := k) hn u)⁻¹ ∂angularMeasure hn) *
        ∫ r, (squaredRadiusProduct (n := n) hn r)⁻¹
          ∂radiusMeasure (k := k) hn := by
  letI : ∀ _ : CofactorIdx n hn,
      IsProbabilityMeasure (circularGaussianSphereProbability k) :=
    fun _ ↦ ⟨circularGaussianSphereProbability_apply_univ hk⟩
  letI : ∀ _ : CofactorIdx n hn,
      IsProbabilityMeasure (circularGaussianPositiveRadiusMeasure k) :=
    fun _ ↦ isProbabilityMeasure_circularGaussianPositiveRadiusMeasure hk
  letI : IsProbabilityMeasure (angularMeasure (k := k) hn) := by
    unfold angularMeasure
    infer_instance
  letI : IsProbabilityMeasure (radiusMeasure (k := k) hn) := by
    unfold radiusMeasure
    infer_instance
  have hmap := map_splitPolarReconstruct (n := n) (k := k) hn hk
  calc
    (∫ A : CofactorIdx n hn → (Fin k → ℂ), (pastCofactorV hn A)⁻¹
        ∂(Measure.pi fun _ : CofactorIdx n hn ↦ circularGaussianVector k)) =
        ∫ A, (pastCofactorV hn A)⁻¹
          ∂Measure.map (splitPolarReconstruct hn) (splitPolarMeasure hn) := by
            rw [hmap]
    _ = ∫ z, (pastCofactorV hn (splitPolarReconstruct hn z))⁻¹
          ∂splitPolarMeasure hn := by
            exact integral_map
              (measurable_splitPolarReconstruct (n := n) (k := k) hn).aemeasurable
              (measurable_pastCofactorV hn).inv.aestronglyMeasurable
    _ = ∫ z, (angularEnergy hn z.1)⁻¹ *
          (squaredRadiusProduct hn z.2)⁻¹ ∂splitPolarMeasure hn := by
            apply integral_congr_ae
            filter_upwards [] with z
            rw [pastCofactorV_splitPolarReconstruct hn]
            simp [mul_inv_rev, mul_comm]
    _ = (∫ u, (angularEnergy hn u)⁻¹ ∂angularMeasure hn) *
          ∫ r, (squaredRadiusProduct hn r)⁻¹
            ∂radiusMeasure (k := k) hn := by
            exact integral_prod_mul
              (fun u ↦ (angularEnergy hn u)⁻¹)
              (fun r ↦ (squaredRadiusProduct hn r)⁻¹)

/-- The angular energy is integrable.  This is extracted from the positive
closed Gaussian first moment and the exact polar factorization. -/
theorem integrable_angularEnergy (hk : 0 < k) :
    Integrable (angularEnergy (n := n) (k := k) hn) (angularMeasure hn) := by
  apply Integrable.of_integral_ne_zero
  intro hzero
  have hsplit := integral_pastCofactorV_eq_angular_mul_radial hn hk
  rw [hzero, zero_mul] at hsplit
  rw [integral_pastCofactorV_eq_closedFirstMoment hn hk] at hsplit
  exact (closedFirstMoment_pos k n hk).ne' hsplit

/-- The reciprocal angular energy is integrable in the paper range. -/
theorem integrable_inv_angularEnergy
    (hkn : 4 * n ≤ k) :
    Integrable (fun u ↦ (angularEnergy (n := n) (k := k) hn u)⁻¹)
      (angularMeasure hn) := by
  have hk2 : 2 ≤ k := by omega
  have hkpos : 0 < k := by omega
  apply Integrable.of_integral_ne_zero
  intro hzero
  have hsplit := integral_inv_pastCofactorV_eq_angular_mul_radial hn hkpos
  rw [hzero, zero_mul] at hsplit
  have hint := integrable_inv_pastCofactorV_paperRange k n hn hkn
  have hposV := Wishart.ae_pastCofactorV_pos_paperRange hn hkn
  have hnonneg : 0 ≤ᵐ[(Measure.pi fun _ : CofactorIdx n hn ↦
      circularGaussianVector k)]
      (fun A ↦ (pastCofactorV hn A)⁻¹) := by
    filter_upwards [hposV] with A hA
    exact inv_nonneg.mpr hA.le
  have hne : (∫ A : CofactorIdx n hn → (Fin k → ℂ),
      (pastCofactorV hn A)⁻¹
      ∂(Measure.pi fun _ : CofactorIdx n hn ↦ circularGaussianVector k)) ≠ 0 := by
    intro hz
    have hae := (integral_eq_zero_iff_of_nonneg_ae hnonneg hint).mp hz
    obtain ⟨A, hA0, hApos⟩ := (hae.and hposV).exists
    have hinvpos : 0 < (pastCofactorV hn A)⁻¹ := inv_pos.mpr hApos
    exact hinvpos.ne' hA0
  exact hne hsplit

/-- Almost-sure positivity descends from the literal Gaussian cofactor energy
to the angular factor because every positive polar radius product is strictly
positive. -/
theorem ae_angularEnergy_pos (hkn : 4 * n ≤ k) :
    ∀ᵐ u ∂angularMeasure (n := n) (k := k) hn,
      0 < angularEnergy (n := n) (k := k) hn u := by
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
  have hgauss := Wishart.ae_pastCofactorV_pos_paperRange hn hkn
  have hpull : ∀ᵐ z ∂splitPolarMeasure (k := k) hn,
      0 < pastCofactorV hn (splitPolarReconstruct hn z) :=
    hT.quasiMeasurePreserving.ae hgauss
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

/-- Literal finite-real radial lower bound in the paper's dimension range. -/
theorem cofactorRadialFactor_le_literalMomentProduct
    (hkn : 4 * n ≤ k) :
    cofactorRadialFactor k n ≤
      closedFirstMoment k n *
        (∫ A : CofactorIdx n hn → (Fin k → ℂ),
          (pastCofactorV hn A)⁻¹
          ∂(Measure.pi fun _ : CofactorIdx n hn ↦ circularGaussianVector k)) := by
  have hk2 : 2 ≤ k := by omega
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
      (ae_angularEnergy_pos hn hkn)
      (integrable_angularEnergy hn hkpos)
      (integrable_inv_angularEnergy hn hkn)
  rw [← integral_pastCofactorV_eq_closedFirstMoment hn hkpos]
  rw [integral_pastCofactorV_eq_angular_mul_radial hn hkpos,
    integral_squaredRadiusProduct hn hkpos,
    integral_inv_pastCofactorV_eq_angular_mul_radial hn hkpos,
    integral_inv_squaredRadiusProduct hn hk2]
  have hbase : 0 ≤ (k : ℝ) / ((k : ℝ) - 1) := by
    apply div_nonneg
    · positivity
    · have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
      linarith
  calc
    cofactorRadialFactor k n ≤
        cofactorRadialFactor k n *
          ((∫ u, angularEnergy hn u ∂angularMeasure hn) *
            ∫ u, (angularEnergy hn u)⁻¹ ∂angularMeasure hn) := by
      exact le_mul_of_one_le_right (pow_nonneg hbase _) hang
    _ = ((∫ u, angularEnergy hn u ∂angularMeasure hn) *
          (k : ℝ) ^ (2 * n - 1)) *
        ((∫ u, (angularEnergy hn u)⁻¹ ∂angularMeasure hn) *
          (((k : ℝ) - 1)⁻¹) ^ (2 * n - 1)) := by
      unfold cofactorRadialFactor
      rw [div_pow]
      ring

/-- Paper-ready exponential consequence of the literal radial factor. -/
theorem exp_n_div_le_literalMomentProduct
    (hkn : 4 * n ≤ k) :
    Real.exp ((n : ℝ) / (k : ℝ)) ≤
      closedFirstMoment k n *
        (∫ A : CofactorIdx n hn → (Fin k → ℂ),
          (pastCofactorV hn A)⁻¹
          ∂(Measure.pi fun _ : CofactorIdx n hn ↦ circularGaussianVector k)) := by
  have hk2 : 2 ≤ k := by omega
  exact (exp_n_div_le_cofactorRadialFactor k n hn hk2).trans
    (cofactorRadialFactor_le_literalMomentProduct hn hkn)

/-- Exact separation of the radial and angular contributions to the literal
moment product. -/
theorem literalMomentProduct_eq_radial_mul_angularMomentProduct
    (hkn : 4 * n ≤ k) :
    ((∫ A : CofactorIdx n hn → (Fin k → ℂ), pastCofactorV hn A
        ∂(Measure.pi fun _ : CofactorIdx n hn ↦ circularGaussianVector k)) *
      ∫ A : CofactorIdx n hn → (Fin k → ℂ), (pastCofactorV hn A)⁻¹
        ∂(Measure.pi fun _ : CofactorIdx n hn ↦ circularGaussianVector k)) =
      cofactorRadialFactor k n *
        ((∫ u, angularEnergy (n := n) (k := k) hn u ∂angularMeasure hn) *
          ∫ u, (angularEnergy (n := n) (k := k) hn u)⁻¹
            ∂angularMeasure hn) := by
  have hk2 : 2 ≤ k := by omega
  have hkpos : 0 < k := by omega
  rw [integral_pastCofactorV_eq_angular_mul_radial hn hkpos,
    integral_squaredRadiusProduct hn hkpos,
    integral_inv_pastCofactorV_eq_angular_mul_radial hn hkpos,
    integral_inv_squaredRadiusProduct hn hk2]
  unfold cofactorRadialFactor
  rw [div_pow]
  ring

/-- Exact radial--angular identity with the first Gaussian moment written in
the closed form used to define the paper's `Lambda_{k,n}`. -/
theorem literalLambda_eq_radial_mul_angularMomentProduct
    (hkn : 4 * n ≤ k) :
    (closedFirstMoment k n *
      ∫ A : CofactorIdx n hn → (Fin k → ℂ), (pastCofactorV hn A)⁻¹
        ∂(Measure.pi fun _ : CofactorIdx n hn ↦ circularGaussianVector k)) =
      cofactorRadialFactor k n *
        ((∫ u, angularEnergy (n := n) (k := k) hn u ∂angularMeasure hn) *
          ∫ u, (angularEnergy (n := n) (k := k) hn u)⁻¹
            ∂angularMeasure hn) := by
  have hkpos : 0 < k := by omega
  rw [← integral_pastCofactorV_eq_closedFirstMoment hn hkpos]
  exact literalMomentProduct_eq_radial_mul_angularMomentProduct hn hkn

/-- The paper statement with both ordinary Gaussian moments displayed. -/
theorem cofactorRadialFactor_le_integralMomentProduct
    (hkn : 4 * n ≤ k) :
    cofactorRadialFactor k n ≤
      ((∫ A : CofactorIdx n hn → (Fin k → ℂ), pastCofactorV hn A
          ∂(Measure.pi fun _ : CofactorIdx n hn ↦ circularGaussianVector k)) *
        ∫ A : CofactorIdx n hn → (Fin k → ℂ), (pastCofactorV hn A)⁻¹
          ∂(Measure.pi fun _ : CofactorIdx n hn ↦ circularGaussianVector k)) := by
  have hkpos : 0 < k := by omega
  rw [integral_pastCofactorV_eq_closedFirstMoment hn hkpos]
  exact cofactorRadialFactor_le_literalMomentProduct hn hkn

/-- Complete literal chain used in the paper. -/
theorem literalRadialLowerBound_fullChain
    (hkn : 4 * n ≤ k) :
    Real.exp ((n : ℝ) / (k : ℝ)) ≤
        Real.exp (((2 * n - 1 : ℕ) : ℝ) / (k : ℝ)) ∧
      Real.exp (((2 * n - 1 : ℕ) : ℝ) / (k : ℝ)) ≤
        cofactorRadialFactor k n ∧
      cofactorRadialFactor k n ≤
        ((∫ A : CofactorIdx n hn → (Fin k → ℂ), pastCofactorV hn A
            ∂(Measure.pi fun _ : CofactorIdx n hn ↦ circularGaussianVector k)) *
          ∫ A : CofactorIdx n hn → (Fin k → ℂ), (pastCofactorV hn A)⁻¹
            ∂(Measure.pi fun _ : CofactorIdx n hn ↦ circularGaussianVector k)) := by
  have hk2 : 2 ≤ k := by omega
  constructor
  · apply Real.exp_le_exp.mpr
    have hkR : (0 : ℝ) < (k : ℝ) := by positivity
    apply (div_le_div_iff_of_pos_right hkR).2
    exact_mod_cast (show n ≤ 2 * n - 1 by omega)
  constructor
  · exact exp_two_mul_sub_one_div_le_cofactorRadialFactor k n hk2
  · exact cofactorRadialFactor_le_integralMomentProduct hn hkn

end RadialLowerBoundAlt

end

end LogdetLean.GramHafnian
