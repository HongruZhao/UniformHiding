import LogdetLean.GramHafnian.LocalAnticoncentration.CoreEquations
import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.LiteralRegularizedLimit
import Mathlib.Probability.Density
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-!
# Density and local sharpness for the current manuscript

This module formalizes the exact circular Gaussian density used after the
last column decomposition.  It then records the literal conditional law of
the Gram hafnian on each past column fibre.
-/

open MeasureTheory ProbabilityTheory Set Metric Filter
open scoped ENNReal ComplexConjugate Topology

namespace LogdetLean.GramHafnian

noncomputable section

/-! ## Transporting a density through a measurable equivalence -/

theorem map_measurableEquiv_withDensity_localAnticoncentration
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (μ : Measure α) (f : α → ENNReal)
    (hf : Measurable f) :
    Measure.map e (μ.withDensity f) =
      (Measure.map e μ).withDensity (f ∘ e.symm) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs,
    withDensity_apply _ (hs.preimage e.measurable),
    withDensity_apply _ hs]
  rw [← lintegral_indicator hs]
  rw [lintegral_map]
  · rw [← lintegral_indicator (hs.preimage e.measurable)]
    congr 1
    funext x
    by_cases hx : e x ∈ s
    · simp [Set.indicator, hx]
    · simp [Set.indicator, hx]
  · exact (hf.comp e.symm.measurable).indicator hs
  · exact e.measurable

/-! ## Exact density of the paper normalized circular Gaussian -/

def localAnticoncentrationCircularGaussianMeasurableEquiv : (ℝ × ℝ) ≃ᵐ ℂ :=
  Complex.measurableEquivRealProd.symm.trans
    (show ℂ ≃ᵐ ℂ from
      (Homeomorph.smulOfNeZero ((Real.sqrt 2)⁻¹ : ℝ)
        (inv_ne_zero (ne_of_gt (Real.sqrt_pos.2 (by norm_num)))) :
          ℂ ≃ₜ ℂ).toMeasurableEquiv)

@[simp] theorem localAnticoncentrationCircularGaussianMeasurableEquiv_apply
    (q : ℝ × ℝ) :
    localAnticoncentrationCircularGaussianMeasurableEquiv q =
      circularGaussianCoordinate q := by
  have hsqrt : Real.sqrt 2 ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  apply Complex.ext <;>
    simp [localAnticoncentrationCircularGaussianMeasurableEquiv,
      circularGaussianCoordinate, div_eq_mul_inv] <;>
    field_simp [hsqrt]

@[simp] theorem localAnticoncentrationCircularGaussianMeasurableEquiv_symm_apply_re
    (z : ℂ) :
    (localAnticoncentrationCircularGaussianMeasurableEquiv.symm z).1 =
      Real.sqrt 2 * z.re := by
  have hsqrt : Real.sqrt 2 ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have h := congrArg Complex.re
    (localAnticoncentrationCircularGaussianMeasurableEquiv.apply_symm_apply z)
  rw [localAnticoncentrationCircularGaussianMeasurableEquiv_apply] at h
  have h' :
      (localAnticoncentrationCircularGaussianMeasurableEquiv.symm z).1 /
          Real.sqrt 2 = z.re := by
    simpa [circularGaussianCoordinate] using h
  calc
    (localAnticoncentrationCircularGaussianMeasurableEquiv.symm z).1 =
        Real.sqrt 2 *
          ((localAnticoncentrationCircularGaussianMeasurableEquiv.symm z).1 /
            Real.sqrt 2) := by field_simp [hsqrt]
    _ = Real.sqrt 2 * z.re := by rw [h']

@[simp] theorem localAnticoncentrationCircularGaussianMeasurableEquiv_symm_apply_im
    (z : ℂ) :
    (localAnticoncentrationCircularGaussianMeasurableEquiv.symm z).2 =
      Real.sqrt 2 * z.im := by
  have hsqrt : Real.sqrt 2 ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have h := congrArg Complex.im
    (localAnticoncentrationCircularGaussianMeasurableEquiv.apply_symm_apply z)
  rw [localAnticoncentrationCircularGaussianMeasurableEquiv_apply] at h
  have h' :
      (localAnticoncentrationCircularGaussianMeasurableEquiv.symm z).2 /
          Real.sqrt 2 = z.im := by
    simpa [circularGaussianCoordinate] using h
  calc
    (localAnticoncentrationCircularGaussianMeasurableEquiv.symm z).2 =
        Real.sqrt 2 *
          ((localAnticoncentrationCircularGaussianMeasurableEquiv.symm z).2 /
            Real.sqrt 2) := by field_simp [hsqrt]
    _ = Real.sqrt 2 * z.im := by rw [h']

/-- The exact `ENNReal` density `π⁻¹ exp (-|z|²)` of `CN(0,1)`. -/
def localAnticoncentrationCircularGaussianDensity (z : ℂ) : ENNReal :=
  ENNReal.ofReal (Real.pi⁻¹ * Real.exp (-‖z‖ ^ 2))

theorem measurable_localAnticoncentrationCircularGaussianDensity :
    Measurable localAnticoncentrationCircularGaussianDensity := by
  unfold localAnticoncentrationCircularGaussianDensity
  fun_prop

/-- The literal circular Gaussian used by the Gram hafnian development has
exact density `π⁻¹ exp (-|z|²)` with respect to complex Lebesgue measure. -/
theorem circularGaussian_eq_withDensity_localAnticoncentration :
    circularGaussian =
      (volume : Measure ℂ).withDensity localAnticoncentrationCircularGaussianDensity := by
  let g : ℝ × ℝ → ENNReal :=
    fun q ↦ gaussianPDF 0 1 q.1 * gaussianPDF 0 1 q.2
  have hg : Measurable g := by
    unfold g
    fun_prop
  have hsource :
      (gaussianReal 0 1).prod (gaussianReal 0 1) =
        ((volume : Measure ℝ).prod (volume : Measure ℝ)).withDensity g := by
    rw [gaussianReal_of_var_ne_zero 0 one_ne_zero]
    exact prod_withDensity (measurable_gaussianPDF 0 1)
      (measurable_gaussianPDF 0 1)
  rw [circularGaussian]
  have hefun :
      (localAnticoncentrationCircularGaussianMeasurableEquiv : ℝ × ℝ → ℂ) =
        circularGaussianCoordinate := by
    funext q
    exact localAnticoncentrationCircularGaussianMeasurableEquiv_apply q
  rw [← hefun]
  change Measure.map localAnticoncentrationCircularGaussianMeasurableEquiv
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) = _
  rw [hsource, map_measurableEquiv_withDensity_localAnticoncentration]
  · have hmap :
        Measure.map localAnticoncentrationCircularGaussianMeasurableEquiv
            ((volume : Measure ℝ).prod (volume : Measure ℝ)) =
          (2 : ENNReal) • (volume : Measure ℂ) := by
      rw [hefun]
      exact map_circularGaussianCoordinate_volume
    rw [hmap, withDensity_smul_measure,
      ← withDensity_smul (2 : ENNReal)
        (hg.comp localAnticoncentrationCircularGaussianMeasurableEquiv.symm.measurable)]
    · congr 1
      funext z
      change (2 : ENNReal) *
          g (localAnticoncentrationCircularGaussianMeasurableEquiv.symm z) =
        localAnticoncentrationCircularGaussianDensity z
      unfold g gaussianPDF localAnticoncentrationCircularGaussianDensity gaussianPDFReal
      rw [show (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) by norm_num,
        ← mul_assoc,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
        ← ENNReal.ofReal_mul (by positivity : 0 ≤
          (2 : ℝ) * ((Real.sqrt (2 * Real.pi * (1 : NNReal)))⁻¹ *
            Real.exp
              (-((localAnticoncentrationCircularGaussianMeasurableEquiv.symm z).1 - 0) ^ 2 /
                (2 * (1 : NNReal)))))]
      apply congrArg ENNReal.ofReal
      rw [localAnticoncentrationCircularGaussianMeasurableEquiv_symm_apply_re,
        localAnticoncentrationCircularGaussianMeasurableEquiv_symm_apply_im]
      norm_num
      have hsqrt2 : (Real.sqrt 2) ^ 2 = 2 :=
        Real.sq_sqrt (by norm_num)
      have hpi : 0 < Real.pi := Real.pi_pos
      have hre : -(Real.sqrt 2 * z.re) ^ 2 / 2 = -(z.re ^ 2) := by
        rw [mul_pow, hsqrt2]
        ring
      have him : -(Real.sqrt 2 * z.im) ^ 2 / 2 = -(z.im ^ 2) := by
        rw [mul_pow, hsqrt2]
        ring
      rw [hre, him]
      rw [show
          2 * ((Real.sqrt Real.pi)⁻¹ * (Real.sqrt 2)⁻¹ *
                Real.exp (-z.re ^ 2)) *
              ((Real.sqrt Real.pi)⁻¹ * (Real.sqrt 2)⁻¹ *
                Real.exp (-z.im ^ 2)) =
            (2 * (Real.sqrt Real.pi)⁻¹ * (Real.sqrt 2)⁻¹ *
              (Real.sqrt Real.pi)⁻¹ * (Real.sqrt 2)⁻¹) *
              (Real.exp (-z.re ^ 2) * Real.exp (-z.im ^ 2)) by ring,
        ← Real.exp_add]
      have hnorm : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        ring
      rw [hnorm]
      have hsqrtpi_sq : (Real.sqrt Real.pi) ^ 2 = Real.pi :=
        Real.sq_sqrt hpi.le
      have hcoeff :
          2 * (Real.sqrt Real.pi)⁻¹ * (Real.sqrt 2)⁻¹ *
              (Real.sqrt Real.pi)⁻¹ * (Real.sqrt 2)⁻¹ = Real.pi⁻¹ := by
        field_simp [ne_of_gt hpi, ne_of_gt (Real.sqrt_pos.2 hpi),
          ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2))]
        nlinarith
      rw [hcoeff]
      congr 2
      ring
  · exact hg

/-! ## Exact density after a positive variance rescaling -/

/-- Density of `sqrt V • Z`, where `Z ~ CN(0,1)`.  This transport form is
totalized at nonpositive `V`; all probabilistic uses assume `0 < V`. -/
def localAnticoncentrationScaledCircularGaussianDensity (V : ℝ) (z : ℂ) : ENNReal :=
  ENNReal.ofReal V⁻¹ *
    localAnticoncentrationCircularGaussianDensity ((Real.sqrt V)⁻¹ • z)

theorem measurable_localAnticoncentrationScaledCircularGaussianDensity (V : ℝ) :
    Measurable (localAnticoncentrationScaledCircularGaussianDensity V) := by
  unfold localAnticoncentrationScaledCircularGaussianDensity
  exact measurable_const.mul
    (measurable_localAnticoncentrationCircularGaussianDensity.comp
      (measurable_const_smul (Real.sqrt V)⁻¹))

/-- Paper formula for the scaled circular Gaussian density. -/
theorem localAnticoncentrationScaledCircularGaussianDensity_eq
    {V : ℝ} (hV : 0 < V) (z : ℂ) :
    localAnticoncentrationScaledCircularGaussianDensity V z =
      ENNReal.ofReal
        (Real.pi⁻¹ * V⁻¹ * Real.exp (-‖z‖ ^ 2 / V)) := by
  unfold localAnticoncentrationScaledCircularGaussianDensity
  rw [show ENNReal.ofReal V⁻¹ *
      localAnticoncentrationCircularGaussianDensity ((Real.sqrt V)⁻¹ • z) =
      ENNReal.ofReal
        (V⁻¹ * (Real.pi⁻¹ *
          Real.exp (-‖(Real.sqrt V)⁻¹ • z‖ ^ 2))) by
    rw [localAnticoncentrationCircularGaussianDensity,
      ← ENNReal.ofReal_mul (inv_nonneg.mpr hV.le)]]
  apply congrArg ENNReal.ofReal
  rw [norm_smul, Real.norm_eq_abs,
    abs_inv, abs_of_pos (Real.sqrt_pos.2 hV), mul_pow,
    inv_pow, Real.sq_sqrt hV.le]
  field_simp [hV.ne']

/-- Exact density of a positive variance circular Gaussian. -/
theorem map_sqrt_smul_circularGaussian_eq_withDensity
    {V : ℝ} (hV : 0 < V) :
    circularGaussian.map (fun z : ℂ ↦ Real.sqrt V • z) =
      (volume : Measure ℂ).withDensity
        (localAnticoncentrationScaledCircularGaussianDensity V) := by
  let s : ℝ := Real.sqrt V
  have hs : s ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hV)
  let e : ℂ ≃ᵐ ℂ :=
    ((Homeomorph.smulOfNeZero s hs : ℂ ≃ₜ ℂ).toMeasurableEquiv)
  have he : (e : ℂ → ℂ) = fun z : ℂ ↦ s • z := by
    rfl
  have hesymm : (e.symm : ℂ → ℂ) = fun z : ℂ ↦ s⁻¹ • z := by
    rfl
  rw [circularGaussian_eq_withDensity_localAnticoncentration]
  change Measure.map e
      ((volume : Measure ℂ).withDensity localAnticoncentrationCircularGaussianDensity) = _
  rw [map_measurableEquiv_withDensity_localAnticoncentration e
    (volume : Measure ℂ) localAnticoncentrationCircularGaussianDensity
    measurable_localAnticoncentrationCircularGaussianDensity]
  have hmap : Measure.map e (volume : Measure ℂ) =
      ENNReal.ofReal V⁻¹ • (volume : Measure ℂ) := by
    rw [he, Measure.map_addHaar_smul (volume : Measure ℂ) hs]
    congr 1
    rw [show Module.finrank ℝ ℂ = 2 by simp,
      abs_of_pos (inv_pos.mpr (sq_pos_of_ne_zero hs))]
    change ENNReal.ofReal (s ^ 2)⁻¹ = ENNReal.ofReal V⁻¹
    rw [show s ^ 2 = V by
      dsimp [s]
      exact Real.sq_sqrt hV.le]
  rw [hmap, withDensity_smul_measure,
    ← withDensity_smul (ENNReal.ofReal V⁻¹)
      (measurable_localAnticoncentrationCircularGaussianDensity.comp e.symm.measurable)]
  congr 1

/-! ## Conditional law on the literal past column fibre -/

/-- Equation (12), in its exact measure theoretic form before quotienting the
past by `V`: for every fixed past, the Gram hafnian is a circular Gaussian
scaled by the square root of the literal conditional variance. -/
theorem gramHafnian_lastColumn_conditionalLaw
    {r k : ℕ} (hr : 1 ≤ r)
    (A : OddCofactorIndex r hr → (Fin k → ℂ)) :
    (circularGaussianVector k).map
        (fun x ↦ gramHafnianObservable r k
          (lastColumnProductEquiv r k hr (A, x))) =
      circularGaussian.map
        (fun z : ℂ ↦ Real.sqrt (pastCofactorV hr A) • z) := by
  have hfun :
      (fun x ↦ gramHafnianObservable r k
        (lastColumnProductEquiv r k hr (A, x))) =
        iidCircularTransposeLinearForm (pastCofactorCombination hr A) := by
    funext x
    rw [gramHafnian_lastColumnProductEquiv_eq_conditionalLinearForm]
    rfl
  rw [hfun, circularGaussianVector,
    map_iidCircularTransposeLinearForm_eq_scaled_circular,
    ← pastCofactorV_eq_coefficientEnergy]

/-- The fibre law depends on the past only through `V`.  This is the precise
content of conditioning on `V_n` needed in Equation (12). -/
theorem gramHafnian_lastColumn_conditionalLaw_eq_of_variance_eq
    {r k : ℕ} (hr : 1 ≤ r)
    {A A' : OddCofactorIndex r hr → (Fin k → ℂ)}
    (hV : pastCofactorV hr A = pastCofactorV hr A') :
    (circularGaussianVector k).map
        (fun x ↦ gramHafnianObservable r k
          (lastColumnProductEquiv r k hr (A, x))) =
      (circularGaussianVector k).map
        (fun x ↦ gramHafnianObservable r k
          (lastColumnProductEquiv r k hr (A', x))) := by
  rw [gramHafnian_lastColumn_conditionalLaw hr A,
    gramHafnian_lastColumn_conditionalLaw hr A', hV]

/-- Equation (12) together with its exact conditional density on every
positive variance fibre. -/
theorem gramHafnian_lastColumn_conditionalDensity
    {r k : ℕ} (hr : 1 ≤ r)
    (A : OddCofactorIndex r hr → (Fin k → ℂ))
    (hV : 0 < pastCofactorV hr A) :
    (circularGaussianVector k).map
        (fun x ↦ gramHafnianObservable r k
          (lastColumnProductEquiv r k hr (A, x))) =
      (volume : Measure ℂ).withDensity
        (localAnticoncentrationScaledCircularGaussianDensity (pastCofactorV hr A)) := by
  rw [gramHafnian_lastColumn_conditionalLaw hr A,
    map_sqrt_smul_circularGaussian_eq_withDensity hV]

/-! ## The actual Gram hafnian mixture density -/

/-- The `ENNReal` form of the density in Equation (13), on the literal iid
past column probability space. -/
def localAnticoncentrationGramHafnianMixtureDensity
    {r k : ℕ} (hr : 1 ≤ r) (w : ℂ) : ENNReal :=
  ∫⁻ A : OddCofactorIndex r hr → (Fin k → ℂ),
    localAnticoncentrationScaledCircularGaussianDensity (pastCofactorV hr A) w
      ∂(Measure.pi fun _ : OddCofactorIndex r hr ↦ circularGaussianVector k)

theorem measurable_localAnticoncentrationScaledCircularGaussianDensity_uncurry
    {Ω : Type*} [MeasurableSpace Ω]
    {V : Ω → ℝ} (hV : Measurable V) :
    Measurable (fun p : Ω × ℂ ↦
      localAnticoncentrationScaledCircularGaussianDensity (V p.1) p.2) := by
  unfold localAnticoncentrationScaledCircularGaussianDensity
  exact ((hV.comp measurable_fst).inv.ennreal_ofReal).mul
    (measurable_localAnticoncentrationCircularGaussianDensity.comp
      ((Real.continuous_sqrt.measurable.comp
        (hV.comp measurable_fst)).inv.smul measurable_snd))

theorem measurable_localAnticoncentrationGramHafnianMixtureDensity
    {r k : ℕ} (hr : 1 ≤ r) :
    Measurable (localAnticoncentrationGramHafnianMixtureDensity (k := k) hr) := by
  unfold localAnticoncentrationGramHafnianMixtureDensity
  exact (measurable_localAnticoncentrationScaledCircularGaussianDensity_uncurry
    (measurable_pastCofactorV hr)).lintegral_prod_left'

/-- Equation (13) as an equality of measures: the law of the literal Gaussian
Gram hafnian is complex Lebesgue measure weighted by the variance mixture
density. -/
theorem map_gramHafnianObservable_eq_withDensity_mixture
    {r k : ℕ} (hr : 1 ≤ r) (hk : 4 * r ≤ k) :
    (circularGaussianColumnMatrixMeasure r k).map
        (gramHafnianObservable r k) =
      (volume : Measure ℂ).withDensity
        (localAnticoncentrationGramHafnianMixtureDensity (k := k) hr) := by
  let ν : Measure (OddCofactorIndex r hr → (Fin k → ℂ)) :=
    Measure.pi fun _ : OddCofactorIndex r hr ↦ circularGaussianVector k
  let μ : Measure (Fin k → ℂ) := circularGaussianVector k
  let e := lastColumnProductEquiv r k hr
  have htransport := (measurePreserving_lastColumnProductEquiv r k hr).map_eq
  rw [← htransport]
  rw [Measure.map_map (measurable_gramHafnianObservable r k) e.measurable]
  have hfun : gramHafnianObservable r k ∘ e =
      conditionalCircularLinearForm
        (pastCofactorCombination (k := k) hr) := by
    funext p
    exact gramHafnian_lastColumnProductEquiv_eq_conditionalLinearForm hr p
  rw [hfun]
  ext s hs
  have hconditional :
      Measurable
        (conditionalCircularLinearForm
          (pastCofactorCombination (k := k) hr)) :=
    measurable_conditionalCircularLinearForm
      (measurable_pastCofactorCombination (k := k) hr)
  rw [Measure.map_apply hconditional hs,
    Measure.prod_apply (hs.preimage hconditional), withDensity_apply _ hs]
  have hVpos : ∀ᵐ A ∂ν, 0 < pastCofactorV hr A := by
    simpa [ν] using Wishart.ae_pastCofactorV_pos_paperRange hr hk
  have hjoint : Measurable (fun p :
      (OddCofactorIndex r hr → (Fin k → ℂ)) × ℂ ↦
      localAnticoncentrationScaledCircularGaussianDensity
        (pastCofactorV hr p.1) p.2) :=
    measurable_localAnticoncentrationScaledCircularGaussianDensity_uncurry
      (measurable_pastCofactorV hr)
  calc
    (∫⁻ A, μ (Prod.mk A ⁻¹'
        (conditionalCircularLinearForm
          (pastCofactorCombination (k := k) hr) ⁻¹' s)) ∂ν) =
        ∫⁻ A, ∫⁻ w in s,
          localAnticoncentrationScaledCircularGaussianDensity
            (pastCofactorV hr A) w ∂volume ∂ν := by
      apply lintegral_congr_ae
      filter_upwards [hVpos] with A hA
      have hsection :
          Prod.mk A ⁻¹'
              (conditionalCircularLinearForm
                (pastCofactorCombination (k := k) hr) ⁻¹' s) =
            (fun x ↦ gramHafnianObservable r k
              (lastColumnProductEquiv r k hr (A, x))) ⁻¹' s := by
        ext x
        change (conditionalCircularLinearForm
            (pastCofactorCombination (k := k) hr) (A, x) ∈ s) ↔
          gramHafnianObservable r k
            (lastColumnProductEquiv r k hr (A, x)) ∈ s
        rw [gramHafnian_lastColumnProductEquiv_eq_conditionalLinearForm]
      rw [hsection]
      let F : (Fin k → ℂ) → ℂ := fun x ↦
        gramHafnianObservable r k
          (lastColumnProductEquiv r k hr (A, x))
      have hF : Measurable F :=
        (measurable_gramHafnianObservable r k).comp
          ((lastColumnProductEquiv r k hr).measurable.comp
            (measurable_const.prodMk measurable_id))
      calc
        μ (F ⁻¹' s) = (μ.map F) s :=
          (Measure.map_apply hF hs).symm
        _ = ((volume : Measure ℂ).withDensity
              (localAnticoncentrationScaledCircularGaussianDensity
                (pastCofactorV hr A))) s := by
          simpa [μ, F] using congrArg (fun m : Measure ℂ ↦ m s)
            (gramHafnian_lastColumn_conditionalDensity hr A hA)
        _ = ∫⁻ w in s,
              localAnticoncentrationScaledCircularGaussianDensity
                (pastCofactorV hr A) w ∂volume := by
          rw [withDensity_apply _ hs]
    _ = ∫⁻ w in s, ∫⁻ A,
          localAnticoncentrationScaledCircularGaussianDensity
            (pastCofactorV hr A) w ∂ν ∂volume := by
      rw [lintegral_lintegral_swap hjoint.aemeasurable]
    _ = ∫⁻ w in s,
          localAnticoncentrationGramHafnianMixtureDensity (k := k) hr w ∂volume := by
      rfl

/-! ## The real density in the notation of Equation (13) -/

def localAnticoncentrationGramHafnianDensityIntegrand
    {r k : ℕ} (hr : 1 ≤ r)
    (A : OddCofactorIndex r hr → (Fin k → ℂ)) (w : ℂ) : ℝ :=
  Real.pi⁻¹ * (pastCofactorV hr A)⁻¹ *
    Real.exp (-‖w‖ ^ 2 / pastCofactorV hr A)

/-- The real valued density from Equation (13). -/
def localAnticoncentrationGramHafnianDensity
    {r k : ℕ} (hr : 1 ≤ r) (w : ℂ) : ℝ :=
  ∫ A : OddCofactorIndex r hr → (Fin k → ℂ),
    localAnticoncentrationGramHafnianDensityIntegrand hr A w
      ∂(Measure.pi fun _ : OddCofactorIndex r hr ↦ circularGaussianVector k)

theorem measurable_localAnticoncentrationGramHafnianDensityIntegrand_uncurry
    {r k : ℕ} (hr : 1 ≤ r) :
    Measurable (fun p :
      (OddCofactorIndex r hr → (Fin k → ℂ)) × ℂ ↦
      localAnticoncentrationGramHafnianDensityIntegrand hr p.1 p.2) := by
  unfold localAnticoncentrationGramHafnianDensityIntegrand
  fun_prop

theorem localAnticoncentrationGramHafnianDensityIntegrand_nonneg
    {r k : ℕ} (hr : 1 ≤ r)
    (A : OddCofactorIndex r hr → (Fin k → ℂ)) (w : ℂ) :
    0 ≤ localAnticoncentrationGramHafnianDensityIntegrand hr A w := by
  unfold localAnticoncentrationGramHafnianDensityIntegrand
  positivity [pastCofactorV_nonneg hr A]

/-- The paper range gives integrability of the reciprocal conditional
variance, as a real random variable. -/
theorem integrable_pastCofactorV_inv_localAnticoncentration
    {r k : ℕ} (hr : 1 ≤ r) (hk : 4 * r ≤ k) :
    Integrable (fun A : OddCofactorIndex r hr → (Fin k → ℂ) ↦
      (pastCofactorV hr A)⁻¹)
      (Measure.pi fun _ : OddCofactorIndex r hr ↦ circularGaussianVector k) := by
  let ν : Measure (OddCofactorIndex r hr → (Fin k → ℂ)) :=
    Measure.pi fun _ : OddCofactorIndex r hr ↦ circularGaussianVector k
  have hVpos : ∀ᵐ A ∂ν, 0 < pastCofactorV hr A := by
    simpa [ν] using Wishart.ae_pastCofactorV_pos_paperRange hr hk
  have hnonneg : ∀ᵐ A ∂ν, 0 ≤ (pastCofactorV hr A)⁻¹ :=
    hVpos.mono fun _ hA ↦ (inv_pos.mpr hA).le
  have hbound := LocalAnticoncentration.eq11_inverse_variance k r hr hk
  rw [pastCofactorVInverseMoment_eq hr] at hbound
  unfold ennInverseMoment at hbound
  have hfinite :
      (∫⁻ A, ENNReal.ofReal (pastCofactorV hr A)⁻¹ ∂ν) ≠ ⊤ := by
    apply ne_of_lt
    exact lt_of_le_of_lt (by simpa [ν] using hbound) ENNReal.ofReal_lt_top
  exact (lintegral_ofReal_ne_top_iff_integrable
    ((measurable_pastCofactorV hr).inv.aestronglyMeasurable)
    hnonneg).mp hfinite

theorem integrable_localAnticoncentrationGramHafnianDensityIntegrand
    {r k : ℕ} (hr : 1 ≤ r) (hk : 4 * r ≤ k) (w : ℂ) :
    Integrable (fun A : OddCofactorIndex r hr → (Fin k → ℂ) ↦
      localAnticoncentrationGramHafnianDensityIntegrand hr A w)
      (Measure.pi fun _ : OddCofactorIndex r hr ↦ circularGaussianVector k) := by
  let ν : Measure (OddCofactorIndex r hr → (Fin k → ℂ)) :=
    Measure.pi fun _ : OddCofactorIndex r hr ↦ circularGaussianVector k
  have hVpos : ∀ᵐ A ∂ν, 0 < pastCofactorV hr A := by
    simpa [ν] using Wishart.ae_pastCofactorV_pos_paperRange hr hk
  have hdom : Integrable (fun A : OddCofactorIndex r hr → (Fin k → ℂ) ↦
      Real.pi⁻¹ * (pastCofactorV hr A)⁻¹) ν := by
    exact (integrable_pastCofactorV_inv_localAnticoncentration hr hk).const_mul Real.pi⁻¹
  apply hdom.mono
  · exact ((measurable_localAnticoncentrationGramHafnianDensityIntegrand_uncurry hr).comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  · filter_upwards [hVpos] with A hA
    have hcoef : 0 < Real.pi⁻¹ * (pastCofactorV hr A)⁻¹ :=
      mul_pos (inv_pos.mpr Real.pi_pos) (inv_pos.mpr hA)
    calc
      ‖localAnticoncentrationGramHafnianDensityIntegrand hr A w‖ =
          localAnticoncentrationGramHafnianDensityIntegrand hr A w :=
        Real.norm_of_nonneg
          (localAnticoncentrationGramHafnianDensityIntegrand_nonneg hr A w)
      _ ≤ Real.pi⁻¹ * (pastCofactorV hr A)⁻¹ := by
        unfold localAnticoncentrationGramHafnianDensityIntegrand
        apply mul_le_of_le_one_right hcoef.le
        exact Real.exp_le_one_iff.mpr
          (div_nonpos_of_nonpos_of_nonneg
            (neg_nonpos.mpr (sq_nonneg ‖w‖)) hA.le)
      _ = ‖Real.pi⁻¹ * (pastCofactorV hr A)⁻¹‖ :=
        (Real.norm_of_nonneg hcoef.le).symm

/-- Equation (13): the measure density above is exactly the real expectation
`π⁻¹ E[V⁻¹ exp (-|w|²/V)]`. -/
theorem localAnticoncentrationGramHafnianMixtureDensity_eq_ofReal
    {r k : ℕ} (hr : 1 ≤ r) (hk : 4 * r ≤ k) (w : ℂ) :
    localAnticoncentrationGramHafnianMixtureDensity (k := k) hr w =
      ENNReal.ofReal (localAnticoncentrationGramHafnianDensity (k := k) hr w) := by
  let ν : Measure (OddCofactorIndex r hr → (Fin k → ℂ)) :=
    Measure.pi fun _ : OddCofactorIndex r hr ↦ circularGaussianVector k
  have hVpos : ∀ᵐ A ∂ν, 0 < pastCofactorV hr A := by
    simpa [ν] using Wishart.ae_pastCofactorV_pos_paperRange hr hk
  have hint := integrable_localAnticoncentrationGramHafnianDensityIntegrand hr hk w
  have hnonneg : ∀ᵐ A ∂ν,
      0 ≤ localAnticoncentrationGramHafnianDensityIntegrand hr A w :=
    ae_of_all _ fun A ↦ localAnticoncentrationGramHafnianDensityIntegrand_nonneg hr A w
  rw [localAnticoncentrationGramHafnianMixtureDensity, localAnticoncentrationGramHafnianDensity,
    ofReal_integral_eq_lintegral_ofReal (by simpa [ν] using hint) hnonneg]
  apply lintegral_congr_ae
  filter_upwards [hVpos] with A hA
  rw [localAnticoncentrationScaledCircularGaussianDensity_eq hA]
  rfl

theorem localAnticoncentrationGramHafnianDensity_nonneg
    {r k : ℕ} (hr : 1 ≤ r) (w : ℂ) :
    0 ≤ localAnticoncentrationGramHafnianDensity (k := k) hr w := by
  unfold localAnticoncentrationGramHafnianDensity
  exact integral_nonneg fun A ↦
    localAnticoncentrationGramHafnianDensityIntegrand_nonneg hr A w

/-- The density in Equation (13) is continuous.  The dominating function is
`π⁻¹ V⁻¹`, whose integrability follows from Equation (11). -/
theorem continuous_localAnticoncentrationGramHafnianDensity
    {r k : ℕ} (hr : 1 ≤ r) (hk : 4 * r ≤ k) :
    Continuous (localAnticoncentrationGramHafnianDensity (k := k) hr) := by
  let ν : Measure (OddCofactorIndex r hr → (Fin k → ℂ)) :=
    Measure.pi fun _ : OddCofactorIndex r hr ↦ circularGaussianVector k
  have hVpos : ∀ᵐ A ∂ν, 0 < pastCofactorV hr A := by
    simpa [ν] using Wishart.ae_pastCofactorV_pos_paperRange hr hk
  have hdom : Integrable (fun A : OddCofactorIndex r hr → (Fin k → ℂ) ↦
      Real.pi⁻¹ * (pastCofactorV hr A)⁻¹) ν := by
    exact (integrable_pastCofactorV_inv_localAnticoncentration hr hk).const_mul Real.pi⁻¹
  rw [continuous_iff_continuousAt]
  intro w
  unfold localAnticoncentrationGramHafnianDensity
  apply tendsto_integral_filter_of_dominated_convergence
    (fun A : OddCofactorIndex r hr → (Fin k → ℂ) ↦
      Real.pi⁻¹ * (pastCofactorV hr A)⁻¹)
  · filter_upwards [] with u
    exact ((measurable_localAnticoncentrationGramHafnianDensityIntegrand_uncurry hr).comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  · filter_upwards [] with u
    filter_upwards [hVpos] with A hA
    have hcoef : 0 < Real.pi⁻¹ * (pastCofactorV hr A)⁻¹ :=
      mul_pos (inv_pos.mpr Real.pi_pos) (inv_pos.mpr hA)
    calc
      ‖localAnticoncentrationGramHafnianDensityIntegrand hr A u‖ =
          localAnticoncentrationGramHafnianDensityIntegrand hr A u :=
        Real.norm_of_nonneg
          (localAnticoncentrationGramHafnianDensityIntegrand_nonneg hr A u)
      _ ≤ Real.pi⁻¹ * (pastCofactorV hr A)⁻¹ := by
        unfold localAnticoncentrationGramHafnianDensityIntegrand
        apply mul_le_of_le_one_right hcoef.le
        exact Real.exp_le_one_iff.mpr
          (div_nonpos_of_nonpos_of_nonneg
            (neg_nonpos.mpr (sq_nonneg ‖u‖)) hA.le)
  · exact hdom
  · filter_upwards [hVpos] with A hA
    have hcont : Continuous (fun u : ℂ ↦
        localAnticoncentrationGramHafnianDensityIntegrand hr A u) := by
      unfold localAnticoncentrationGramHafnianDensityIntegrand
      fun_prop
    exact hcont.continuousAt

/-- The density is strictly positive at every fixed complex center. -/
theorem localAnticoncentrationGramHafnianDensity_pos
    {r k : ℕ} (hr : 1 ≤ r) (hk : 4 * r ≤ k) (w : ℂ) :
    0 < localAnticoncentrationGramHafnianDensity (k := k) hr w := by
  let ν : Measure (OddCofactorIndex r hr → (Fin k → ℂ)) :=
    Measure.pi fun _ : OddCofactorIndex r hr ↦ circularGaussianVector k
  let g : (OddCofactorIndex r hr → (Fin k → ℂ)) → ℝ :=
    fun A ↦ localAnticoncentrationGramHafnianDensityIntegrand hr A w
  have hint : Integrable g ν := by
    simpa [ν, g] using
      integrable_localAnticoncentrationGramHafnianDensityIntegrand hr hk w
  have hnonneg : 0 ≤ᵐ[ν] g :=
    ae_of_all _ fun A ↦
      localAnticoncentrationGramHafnianDensityIntegrand_nonneg hr A w
  rw [localAnticoncentrationGramHafnianDensity,
    integral_pos_iff_support_of_nonneg_ae hnonneg hint]
  have hVpos : ∀ᵐ A ∂ν, 0 < pastCofactorV hr A := by
    simpa [ν] using Wishart.ae_pastCofactorV_pos_paperRange hr hk
  have hsupport : ∀ᵐ A ∂ν, A ∈ Function.support g := by
    filter_upwards [hVpos] with A hA
    change g A ≠ 0
    apply ne_of_gt
    dsimp [g, localAnticoncentrationGramHafnianDensityIntegrand]
    positivity
  have hfull : ν (Function.support g) = 1 := by
    apply le_antisymm
    · simpa using
        (measure_mono (μ := ν) (Set.subset_univ (Function.support g)))
    have hle : ν Set.univ ≤ ν (Function.support g) := by
      apply measure_mono_ae
      filter_upwards [hsupport] with A hA
      intro _hmem
      exact hA
    simpa using hle
  rw [show
      (Measure.pi fun _ : OddCofactorIndex r hr ↦ circularGaussianVector k)
          (Function.support g) = ν (Function.support g) by rfl,
    hfull]
  norm_num

/-- The density is radial. -/
theorem localAnticoncentrationGramHafnianDensity_eq_of_norm_eq
    {r k : ℕ} (hr : 1 ≤ r) {z w : ℂ} (hzw : ‖z‖ = ‖w‖) :
    localAnticoncentrationGramHafnianDensity (k := k) hr z =
      localAnticoncentrationGramHafnianDensity (k := k) hr w := by
  unfold localAnticoncentrationGramHafnianDensity
  apply integral_congr_ae
  filter_upwards [] with A
  unfold localAnticoncentrationGramHafnianDensityIntegrand
  rw [hzw]

/-- The radial density decreases with the radius. -/
theorem localAnticoncentrationGramHafnianDensity_antitone_norm
    {r k : ℕ} (hr : 1 ≤ r) (hk : 4 * r ≤ k)
    {z w : ℂ} (hzw : ‖z‖ ≤ ‖w‖) :
    localAnticoncentrationGramHafnianDensity (k := k) hr w ≤
      localAnticoncentrationGramHafnianDensity (k := k) hr z := by
  let ν : Measure (OddCofactorIndex r hr → (Fin k → ℂ)) :=
    Measure.pi fun _ : OddCofactorIndex r hr ↦ circularGaussianVector k
  have hVpos : ∀ᵐ A ∂ν, 0 < pastCofactorV hr A := by
    simpa [ν] using Wishart.ae_pastCofactorV_pos_paperRange hr hk
  unfold localAnticoncentrationGramHafnianDensity
  apply integral_mono_ae
    (by simpa [ν] using
      integrable_localAnticoncentrationGramHafnianDensityIntegrand hr hk w)
    (by simpa [ν] using
      integrable_localAnticoncentrationGramHafnianDensityIntegrand hr hk z)
  filter_upwards [hVpos] with A hA
  unfold localAnticoncentrationGramHafnianDensityIntegrand
  apply mul_le_mul_of_nonneg_left
  · apply Real.exp_le_exp.mpr
    have hsq : ‖z‖ ^ 2 ≤ ‖w‖ ^ 2 := by
      nlinarith [norm_nonneg z, norm_nonneg w]
    simpa only [neg_div] using
      neg_le_neg (div_le_div_of_nonneg_right hsq hA.le)
  · exact mul_nonneg (inv_nonneg.mpr Real.pi_pos.le)
      (inv_nonneg.mpr hA.le)

theorem localAnticoncentrationGramHafnianDensity_le_at_zero
    {r k : ℕ} (hr : 1 ≤ r) (hk : 4 * r ≤ k) (w : ℂ) :
    localAnticoncentrationGramHafnianDensity (k := k) hr w ≤
      localAnticoncentrationGramHafnianDensity (k := k) hr 0 := by
  exact localAnticoncentrationGramHafnianDensity_antitone_norm hr hk
    (by simp : ‖(0 : ℂ)‖ ≤ ‖w‖)

/-- Real form of Equation (11): `E[V⁻¹]` is at most the explicit inverse
variance product. -/
theorem integral_pastCofactorV_inv_le_inverseVarianceBound_localAnticoncentration
    {r k : ℕ} (hr : 1 ≤ r) (hk : 4 * r ≤ k) :
    (∫ A : OddCofactorIndex r hr → (Fin k → ℂ),
        (pastCofactorV hr A)⁻¹
        ∂(Measure.pi fun _ : OddCofactorIndex r hr ↦ circularGaussianVector k)) ≤
      inverseVarianceBound k r := by
  let ν : Measure (OddCofactorIndex r hr → (Fin k → ℂ)) :=
    Measure.pi fun _ : OddCofactorIndex r hr ↦ circularGaussianVector k
  have hint := integrable_pastCofactorV_inv_localAnticoncentration hr hk
  have hVpos : ∀ᵐ A ∂ν, 0 < pastCofactorV hr A := by
    simpa [ν] using Wishart.ae_pastCofactorV_pos_paperRange hr hk
  have hnonneg : ∀ᵐ A ∂ν, 0 ≤ (pastCofactorV hr A)⁻¹ :=
    hVpos.mono fun _ hA ↦ (inv_pos.mpr hA).le
  have hbound := LocalAnticoncentration.eq11_inverse_variance k r hr hk
  rw [pastCofactorVInverseMoment_eq hr] at hbound
  unfold ennInverseMoment at hbound
  have hENN :
      ENNReal.ofReal
          (∫ A, (pastCofactorV hr A)⁻¹ ∂ν) ≤
        ENNReal.ofReal (inverseVarianceBound k r) := by
    rw [ofReal_integral_eq_lintegral_ofReal (by simpa [ν] using hint) hnonneg]
    simpa [ν] using hbound
  exact (ENNReal.ofReal_le_ofReal_iff
    (inverseVarianceBound_nonneg_of_le hk hr le_rfl)).mp hENN

/-- Pointwise bound behind `‖f‖∞` in Equation (13). -/
theorem localAnticoncentrationGramHafnianDensity_le_inverseVarianceBound
    {r k : ℕ} (hr : 1 ≤ r) (hk : 4 * r ≤ k) (w : ℂ) :
    localAnticoncentrationGramHafnianDensity (k := k) hr w ≤
      Real.pi⁻¹ * inverseVarianceBound k r := by
  let ν : Measure (OddCofactorIndex r hr → (Fin k → ℂ)) :=
    Measure.pi fun _ : OddCofactorIndex r hr ↦ circularGaussianVector k
  have hVpos : ∀ᵐ A ∂ν, 0 < pastCofactorV hr A := by
    simpa [ν] using Wishart.ae_pastCofactorV_pos_paperRange hr hk
  calc
    localAnticoncentrationGramHafnianDensity (k := k) hr w =
        ∫ A, localAnticoncentrationGramHafnianDensityIntegrand hr A w ∂ν := by
      rfl
    _ ≤ ∫ A, Real.pi⁻¹ * (pastCofactorV hr A)⁻¹ ∂ν := by
      apply integral_mono_ae
        (by simpa [ν] using
          integrable_localAnticoncentrationGramHafnianDensityIntegrand hr hk w)
        ((by simpa [ν] using
          (integrable_pastCofactorV_inv_localAnticoncentration hr hk).const_mul Real.pi⁻¹) :
          Integrable (fun A ↦ Real.pi⁻¹ * (pastCofactorV hr A)⁻¹) ν)
      filter_upwards [hVpos] with A hA
      unfold localAnticoncentrationGramHafnianDensityIntegrand
      apply mul_le_of_le_one_right
      · exact mul_nonneg (inv_nonneg.mpr Real.pi_pos.le)
          (inv_nonneg.mpr hA.le)
      · exact Real.exp_le_one_iff.mpr
          (div_nonpos_of_nonpos_of_nonneg
            (neg_nonpos.mpr (sq_nonneg ‖w‖)) hA.le)
    _ = Real.pi⁻¹ * ∫ A, (pastCofactorV hr A)⁻¹ ∂ν := by
      rw [integral_const_mul]
    _ ≤ Real.pi⁻¹ * inverseVarianceBound k r := by
      exact mul_le_mul_of_nonneg_left
        (by simpa [ν] using
          integral_pastCofactorV_inv_le_inverseVarianceBound_localAnticoncentration hr hk)
        (inv_nonneg.mpr Real.pi_pos.le)

/-- The paper's normalized density bound, pointwise in the center.  Taking
the supremum gives `π σ² ‖f‖∞ ≤ B`. -/
theorem pi_sigma_sq_mul_localAnticoncentrationGramHafnianDensity_le
    {r k : ℕ} (hr : 1 ≤ r) (hk : 4 * r ≤ k) (w : ℂ) :
    Real.pi * gramHafnianSigma k r ^ 2 *
        localAnticoncentrationGramHafnianDensity (k := k) hr w ≤
      shiftedAnticoncentrationConstant k r := by
  have hkpos : 0 < k := by omega
  calc
    Real.pi * gramHafnianSigma k r ^ 2 *
        localAnticoncentrationGramHafnianDensity (k := k) hr w ≤
      Real.pi * gramHafnianSigma k r ^ 2 *
        (Real.pi⁻¹ * inverseVarianceBound k r) := by
      exact mul_le_mul_of_nonneg_left
        (localAnticoncentrationGramHafnianDensity_le_inverseVarianceBound hr hk w)
        (mul_nonneg Real.pi_pos.le (sq_nonneg _))
    _ = closedFirstMoment k r * inverseVarianceBound k r := by
      rw [gramHafnianSigma_sq k r hkpos]
      field_simp [Real.pi_ne_zero]
    _ = shiftedAnticoncentrationConstant k r :=
      LocalAnticoncentration.eq3_mul_eq11_is_eq5 k r hr

end

end LogdetLean.GramHafnian
