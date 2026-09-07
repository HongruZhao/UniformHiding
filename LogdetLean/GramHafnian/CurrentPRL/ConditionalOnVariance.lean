import LogdetLean.GramHafnian.CurrentPRL.MixtureDensity
import Mathlib.Probability.HasCondDistrib

/-!
# Conditional circular Gaussian law given the cofactor variance

This module gives Equation (12) its literal conditional distribution meaning.
The kernel at `v` is the law of `sqrt v * Z`, where `Z` is the standard
circular complex Gaussian.  The final theorem disintegrates the joint law of
the cofactor variance and the Gram hafnian through this kernel.
-/

open MeasureTheory ProbabilityTheory

namespace LogdetLean.GramHafnian

noncomputable section

/-- The Markov kernel `v ↦ Law(sqrt(v) Z)` used in Equation (12). -/
def currentPRLVarianceGaussianKernel : Kernel ℝ ℂ :=
  ((Kernel.id : Kernel ℝ ℝ) ×ₖ
      Kernel.const ℝ circularGaussian).map
    (fun p : ℝ × ℂ ↦ Real.sqrt p.1 • p.2)

theorem measurable_currentPRLVarianceGaussianScale :
    Measurable (fun p : ℝ × ℂ ↦ Real.sqrt p.1 • p.2) := by
  fun_prop

instance : IsMarkovKernel currentPRLVarianceGaussianKernel :=
  Kernel.IsMarkovKernel.map
    ((Kernel.id : Kernel ℝ ℝ) ×ₖ
      Kernel.const ℝ circularGaussian)
    measurable_currentPRLVarianceGaussianScale

/-- Evaluation of the variance kernel is exactly the scaled circular
Gaussian measure, including at `v = 0`. -/
theorem currentPRLVarianceGaussianKernel_apply (v : ℝ) :
    currentPRLVarianceGaussianKernel v =
      circularGaussian.map (fun z : ℂ ↦ Real.sqrt v • z) := by
  have hscalev : Measurable (fun z : ℂ ↦ Real.sqrt v • z) := by
    fun_prop
  rw [currentPRLVarianceGaussianKernel,
    Kernel.map_apply _ measurable_currentPRLVarianceGaussianScale]
  ext s hs
  rw [Measure.map_apply measurable_currentPRLVarianceGaussianScale hs,
    Kernel.id_prod_apply' _ v
      (hs.preimage measurable_currentPRLVarianceGaussianScale),
    Kernel.const_apply,
    Measure.map_apply hscalev hs]
  rfl

/-! ## Literal random variables in the last column product representation -/

/-- The probability space consisting of the past columns and the independent
last Gaussian column. -/
def currentPRLPastLastColumnMeasure
    {r k : ℕ} (hr : 1 ≤ r) :
    Measure
      ((OddCofactorIndex r hr → (Fin k → ℂ)) × (Fin k → ℂ)) :=
  (Measure.pi fun _ : OddCofactorIndex r hr ↦
      circularGaussianVector k).prod (circularGaussianVector k)

/-- The cofactor variance, regarded as a random variable on the literal
past and last column product space. -/
def currentPRLConditionalVariance
    {r k : ℕ} (hr : 1 ≤ r)
    (p : (OddCofactorIndex r hr → (Fin k → ℂ)) × (Fin k → ℂ)) : ℝ :=
  pastCofactorV hr p.1

/-- The Gram hafnian, regarded as a random variable on the literal past and
last column product space. -/
def currentPRLConditionalHafnian
    {r k : ℕ} (hr : 1 ≤ r)
    (p : (OddCofactorIndex r hr → (Fin k → ℂ)) × (Fin k → ℂ)) : ℂ :=
  gramHafnianObservable r k (lastColumnProductEquiv r k hr p)

theorem measurable_currentPRLConditionalVariance
    {r k : ℕ} (hr : 1 ≤ r) :
    Measurable (currentPRLConditionalVariance (k := k) hr) := by
  exact (measurable_pastCofactorV hr).comp measurable_fst

theorem measurable_currentPRLConditionalHafnian
    {r k : ℕ} (hr : 1 ≤ r) :
    Measurable (currentPRLConditionalHafnian (k := k) hr) := by
  exact (measurable_gramHafnianObservable r k).comp
    (lastColumnProductEquiv r k hr).measurable

/-- **Equation (12), literal conditional distribution statement.**

Under the independent past and last column probability measure, the regular
conditional distribution of the Gram hafnian given its cofactor variance is
the Markov kernel `v ↦ Law(sqrt(v) Z)`.  In particular this is the exact
measure theoretic content of `H_{k,n} | V_n ~ CN(0,V_n)`.
-/
theorem gramHafnian_hasCondDistrib_given_pastCofactorV
    {r k : ℕ} (hr : 1 ≤ r) :
    HasCondDistrib
      (currentPRLConditionalHafnian (k := k) hr)
      (currentPRLConditionalVariance (k := k) hr)
      currentPRLVarianceGaussianKernel
      (currentPRLPastLastColumnMeasure (k := k) hr) := by
  let ν : Measure (OddCofactorIndex r hr → (Fin k → ℂ)) :=
    Measure.pi fun _ : OddCofactorIndex r hr ↦ circularGaussianVector k
  let μ : Measure (Fin k → ℂ) := circularGaussianVector k
  let V :
      ((OddCofactorIndex r hr → (Fin k → ℂ)) × (Fin k → ℂ)) → ℝ :=
    currentPRLConditionalVariance (k := k) hr
  let H :
      ((OddCofactorIndex r hr → (Fin k → ℂ)) × (Fin k → ℂ)) → ℂ :=
    currentPRLConditionalHafnian (k := k) hr
  have hV : Measurable V :=
    measurable_currentPRLConditionalVariance hr
  have hH : Measurable H :=
    measurable_currentPRLConditionalHafnian hr
  have hVH : Measurable (fun p ↦ (V p, H p)) := hV.prodMk hH
  have hmapV :
      (ν.prod μ).map V = ν.map (pastCofactorV hr) := by
    change (ν.prod μ).map (pastCofactorV hr ∘ Prod.fst) =
      ν.map (pastCofactorV hr)
    rw [← Measure.map_map (measurable_pastCofactorV hr) measurable_fst,
      Measure.map_fst_prod]
    simp [μ]
  refine ⟨hVH.aemeasurable, ?_⟩
  change (ν.prod μ).map (fun p ↦ (V p, H p)) =
    ((ν.prod μ).map V) ⊗ₘ currentPRLVarianceGaussianKernel
  rw [hmapV]
  ext s hs
  rw [Measure.map_apply hVH hs,
    Measure.prod_apply (hs.preimage hVH),
    Measure.compProd_apply hs,
    lintegral_map
      (Kernel.measurable_kernel_prodMk_left hs)
      (measurable_pastCofactorV hr)]
  apply lintegral_congr
  intro A
  let F : (Fin k → ℂ) → ℂ := fun x ↦
    gramHafnianObservable r k
      (lastColumnProductEquiv r k hr (A, x))
  have hF : Measurable F :=
    (measurable_gramHafnianObservable r k).comp
      ((lastColumnProductEquiv r k hr).measurable.comp
        (measurable_const.prodMk measurable_id))
  have ht : MeasurableSet (Prod.mk (pastCofactorV hr A) ⁻¹' s) :=
    hs.preimage (measurable_const.prodMk measurable_id)
  change μ (F ⁻¹' (Prod.mk (pastCofactorV hr A) ⁻¹' s)) =
    currentPRLVarianceGaussianKernel (pastCofactorV hr A)
      (Prod.mk (pastCofactorV hr A) ⁻¹' s)
  rw [currentPRLVarianceGaussianKernel_apply,
    ← gramHafnian_lastColumn_conditionalLaw hr A,
    Measure.map_apply hF ht]


end

end LogdetLean.GramHafnian
