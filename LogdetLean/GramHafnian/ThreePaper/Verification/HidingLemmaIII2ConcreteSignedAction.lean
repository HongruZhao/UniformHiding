import LogdetLean.GramHafnian.ThreePaper.Verification.HidingLemmaIII2SignedMeasure
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.MeasureTheory.VectorMeasure.Integral

/-!
# Concrete signed Markov kernel action for Lemma III.2

This file constructs the signed extension of every Markov kernel, proves
sharp variation contraction and positive measure compatibility, and then
instantiates the construction for the transpose congruence kernel used in
Lemma III.2.
-/

open MeasureTheory Set ProbabilityTheory
open scoped ProbabilityTheory

namespace LogdetLean.GramHafnian.ThreePaper.Verification

noncomputable section

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

private lemma kernelEval_integrable_measure
    (κ : Kernel X Y) [IsMarkovKernel κ]
    (μ : Measure X) [IsFiniteMeasure μ]
    {A : Set Y} (hA : MeasurableSet A) :
    Integrable (fun x => (κ x A).toReal) μ := by
  refine Integrable.of_bound
    ((κ.measurable_coe hA).ennreal_toReal.aestronglyMeasurable) 1 ?_
  filter_upwards with x
  change |(κ x).real A| ≤ 1
  rw [abs_of_nonneg measureReal_nonneg]
  exact measureReal_le_one

private lemma kernelEval_integrable_signed
    (κ : Kernel X Y) [IsMarkovKernel κ]
    (s : SignedMeasure X)
    {A : Set Y} (hA : MeasurableSet A) :
    s.Integrable (fun x => (κ x A).toReal) := by
  letI : IsFiniteMeasure s.variation := by
    rw [← SignedMeasure.totalVariation_eq_variation]
    infer_instance
  refine Integrable.of_bound
    ((κ.measurable_coe hA).ennreal_toReal.aestronglyMeasurable) 1 ?_
  filter_upwards with x
  change |(κ x).real A| ≤ 1
  rw [abs_of_nonneg measureReal_nonneg]
  exact measureReal_le_one

/-- The concrete signed extension of a Markov kernel, defined on the Jordan
positive and negative parts. -/
def signedKernelActionRaw (κ : Kernel X Y) [IsMarkovKernel κ]
    (s : SignedMeasure X) : SignedMeasure Y :=
  (κ ∘ₘ s.toJordanDecomposition.posPart).toSignedMeasure -
    (κ ∘ₘ s.toJordanDecomposition.negPart).toSignedMeasure

private lemma comp_measureReal_apply_eq_integral
    (κ : Kernel X Y) [IsMarkovKernel κ]
    (μ : Measure X) [IsFiniteMeasure μ]
    {A : Set Y} (hA : MeasurableSet A) :
    (κ ∘ₘ μ).real A =
      ∫ x, (κ x A).toReal ∂μ := by
  rw [measureReal_def, Measure.bind_apply hA κ.aemeasurable,
    integral_toReal (κ.measurable_coe hA).aemeasurable]
  exact ae_of_all _ fun x => (measure_lt_top (κ x) A)

theorem signedKernelActionRaw_apply
    (κ : Kernel X Y) [IsMarkovKernel κ]
    (s : SignedMeasure X)
    {A : Set Y} (hA : MeasurableSet A) :
    signedKernelActionRaw κ s A =
      ∫ᵛ x, (κ x A).toReal ∂<•s := by
  unfold signedKernelActionRaw
  rw [Measure.toSignedMeasure_sub_apply hA,
    comp_measureReal_apply_eq_integral κ _ hA,
    comp_measureReal_apply_eq_integral κ _ hA]
  calc
    (∫ x, (κ x A).toReal ∂s.toJordanDecomposition.posPart) -
          ∫ x, (κ x A).toReal ∂s.toJordanDecomposition.negPart =
        (∫ᵛ x, (κ x A).toReal ∂<•s.toJordanDecomposition.posPart.toSignedMeasure) -
          ∫ᵛ x, (κ x A).toReal ∂<•s.toJordanDecomposition.negPart.toSignedMeasure := by
            simp
    _ = ∫ᵛ x, (κ x A).toReal ∂<•
          (s.toJordanDecomposition.posPart.toSignedMeasure -
            s.toJordanDecomposition.negPart.toSignedMeasure) := by
            rw [VectorMeasure.integral_sub_vectorMeasure
              (kernelEval_integrable_signed κ _ hA)
              (kernelEval_integrable_signed κ _ hA)]
    _ = ∫ᵛ x, (κ x A).toReal ∂<•s := by
          rw [← JordanDecomposition.toSignedMeasure,
            SignedMeasure.toSignedMeasure_toJordanDecomposition]

theorem signedKernelActionRaw_add
    (κ : Kernel X Y) [IsMarkovKernel κ]
    (s t : SignedMeasure X) :
    signedKernelActionRaw κ (s + t) =
      signedKernelActionRaw κ s + signedKernelActionRaw κ t := by
  ext A hA
  change signedKernelActionRaw κ (s + t) A =
    signedKernelActionRaw κ s A + signedKernelActionRaw κ t A
  rw [signedKernelActionRaw_apply κ _ hA,
    signedKernelActionRaw_apply κ _ hA,
    signedKernelActionRaw_apply κ _ hA,
    VectorMeasure.integral_add_vectorMeasure
      (kernelEval_integrable_signed κ s hA)
      (kernelEval_integrable_signed κ t hA)]

theorem signedKernelActionRaw_smul
    (κ : Kernel X Y) [IsMarkovKernel κ]
    (c : ℝ) (s : SignedMeasure X) :
    signedKernelActionRaw κ (c • s) = c • signedKernelActionRaw κ s := by
  ext A hA
  change signedKernelActionRaw κ (c • s) A =
    c * signedKernelActionRaw κ s A
  rw [signedKernelActionRaw_apply κ _ hA,
    signedKernelActionRaw_apply κ _ hA,
    VectorMeasure.integral_smul_vectorMeasure]
  rfl

theorem signedKernelActionRaw_toSignedMeasure
    (κ : Kernel X Y) [IsMarkovKernel κ]
    (μ : Measure X) [IsFiniteMeasure μ] :
    signedKernelActionRaw κ μ.toSignedMeasure = (κ ∘ₘ μ).toSignedMeasure := by
  ext A hA
  rw [signedKernelActionRaw_apply κ _ hA,
    VectorMeasure.integral_toSignedMeasure,
    Measure.toSignedMeasure_apply_measurable hA,
    comp_measureReal_apply_eq_integral κ μ hA]

/-- The signed kernel action on the variation norm wrappers. -/
def signedKernelAction (κ : Kernel X Y) [IsMarkovKernel κ]
    (s : VariationSignedMeasure X) : VariationSignedMeasure Y :=
  VariationSignedMeasure.ofSignedMeasure <|
    signedKernelActionRaw κ (VariationSignedMeasure.toSignedMeasure s)

@[simp] theorem signedKernelAction_add
    (κ : Kernel X Y) [IsMarkovKernel κ]
    (s t : VariationSignedMeasure X) :
    signedKernelAction κ (s + t) =
      signedKernelAction κ s + signedKernelAction κ t := by
  change signedKernelActionRaw κ (s + t) =
    signedKernelActionRaw κ s + signedKernelActionRaw κ t
  exact signedKernelActionRaw_add κ s t

@[simp] theorem signedKernelAction_smul
    (κ : Kernel X Y) [IsMarkovKernel κ]
    (c : ℝ) (s : VariationSignedMeasure X) :
    signedKernelAction κ (c • s) = c • signedKernelAction κ s := by
  change signedKernelActionRaw κ (c • s) = c • signedKernelActionRaw κ s
  exact signedKernelActionRaw_smul κ c s

theorem signedKernelAction_ofSignedMeasure
    (κ : Kernel X Y) [IsMarkovKernel κ]
    (μ : Measure X) [IsFiniteMeasure μ] :
    signedKernelAction κ
        (VariationSignedMeasure.ofSignedMeasure μ.toSignedMeasure) =
      VariationSignedMeasure.ofSignedMeasure (κ ∘ₘ μ).toSignedMeasure := by
  change signedKernelActionRaw κ μ.toSignedMeasure = (κ ∘ₘ μ).toSignedMeasure
  exact signedKernelActionRaw_toSignedMeasure κ μ

theorem signedKernelAction_contractive
    (κ : Kernel X Y) [IsMarkovKernel κ]
    (s : VariationSignedMeasure X) :
    ‖signedKernelAction κ s‖ ≤ ‖s‖ := by
  let sp := (VariationSignedMeasure.toSignedMeasure s).toJordanDecomposition.posPart
  let sn := (VariationSignedMeasure.toSignedMeasure s).toJordanDecomposition.negPart
  change
    ‖VariationSignedMeasure.ofSignedMeasure
      ((κ ∘ₘ sp).toSignedMeasure - (κ ∘ₘ sn).toSignedMeasure)‖ ≤ ‖s‖
  calc
    ‖VariationSignedMeasure.ofSignedMeasure
        ((κ ∘ₘ sp).toSignedMeasure - (κ ∘ₘ sn).toSignedMeasure)‖ ≤
        ‖VariationSignedMeasure.ofSignedMeasure (κ ∘ₘ sp).toSignedMeasure‖ +
          ‖VariationSignedMeasure.ofSignedMeasure (κ ∘ₘ sn).toSignedMeasure‖ :=
      norm_sub_le _ _
    _ = (κ ∘ₘ sp).real univ + (κ ∘ₘ sn).real univ := by
      simp only [VariationSignedMeasure.norm_eq_variation,
        VariationSignedMeasure.toSignedMeasure_ofSignedMeasure,
        Measure.variation_toSignedMeasure]
    _ = sp.real univ + sn.real univ := by
      rw [measureReal_def, measureReal_def, Measure.comp_apply_univ,
        Measure.comp_apply_univ]
      rfl
    _ = (VariationSignedMeasure.toSignedMeasure s).variation.real univ := by
      rw [← SignedMeasure.totalVariation_eq_variation,
        SignedMeasure.totalVariation, measureReal_add_apply]
    _ = ‖s‖ := rfl

/-- The concrete Markov kernel extension as a real linear map between total
variation norm spaces. -/
def signedKernelLinearMap (κ : Kernel X Y) [IsMarkovKernel κ] :
    VariationSignedMeasure X →ₗ[ℝ] VariationSignedMeasure Y where
  toFun := signedKernelAction κ
  map_add' := signedKernelAction_add κ
  map_smul' := signedKernelAction_smul κ

@[simp] theorem signedKernelLinearMap_apply
    (κ : Kernel X Y) [IsMarkovKernel κ]
    (s : VariationSignedMeasure X) :
    signedKernelLinearMap κ s = signedKernelAction κ s := rfl

/-- A generic Markov kernel gives a bounded real linear contraction between
the total variation spaces. -/
def signedKernelContinuousLinearMap
    (κ : Kernel X Y) [IsMarkovKernel κ] :
    VariationSignedMeasure X →L[ℝ] VariationSignedMeasure Y :=
  (signedKernelLinearMap κ).mkContinuous 1 (fun s => by
    simpa using signedKernelAction_contractive κ s)

theorem signedKernelContinuousLinearMap_norm_le_one
    (κ : Kernel X Y) [IsMarkovKernel κ] :
    ‖signedKernelContinuousLinearMap κ‖ ≤ 1 :=
  (signedKernelLinearMap κ).mkContinuous_norm_le zero_le_one
    (fun s => by simpa using signedKernelAction_contractive κ s)

/-- For an endokernel this is an inhabitant of the operator bundle used by
the derivative transport theorem. -/
def VariationMarkovOperator.ofKernel
    (κ : Kernel X X) [IsMarkovKernel κ] : VariationMarkovOperator X where
  toLinearMap := signedKernelLinearMap κ
  contractive := signedKernelAction_contractive κ

namespace ConcreteCongruenceKernelAdapter

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep

/-- The project transpose congruence update expressed through the generic
independent update kernel with factor law xi. -/
def congruenceUpdateKernel (N : ℕ)
    (xi : Measure (ComplexMatrixGL N)) :
    Kernel (ConcreteMatrixState N) (ConcreteMatrixState N) :=
  independentUpdateKernel xi
    (fun p => complexGLTransposeCongruence N p.2 p.1)

instance congruenceUpdateKernel_isMarkov
    (N : ℕ) (xi : Measure (ComplexMatrixGL N))
    [IsProbabilityMeasure xi] :
    IsMarkovKernel (congruenceUpdateKernel N xi) := by
  exact independentUpdateKernel_isMarkov xi
    (fun p => complexGLTransposeCongruence N p.2 p.1)
    (inferInstance : IsProbabilityMeasure xi)
    (measurable_complexGLTransposeCongruence N)

/-- On positive laws, composition by the concrete independent update kernel
is the project's congruence measure action. -/
theorem congruenceUpdateKernel_comp_eq_congruenceMeasureAction
    (N : ℕ) (xi : Measure (ComplexMatrixGL N))
    (mu : Measure (ConcreteMatrixState N))
    [IsProbabilityMeasure xi] [IsProbabilityMeasure mu] :
    congruenceUpdateKernel N xi ∘ₘ mu =
      congruenceMeasureAction N xi mu := by
  simpa [congruenceUpdateKernel, independentUpdateKernel,
    congruenceMeasureAction] using
    (independentUpdateKernel_comp_eq_map_prod mu xi
      (fun p => complexGLTransposeCongruence N p.2 p.1)
      (measurable_complexGLTransposeCongruence N))

/-- The generic signed kernel extension for factor law xi agrees exactly
with the project's positive congruence action. -/
theorem congruenceSignedKernelAction_toSignedMeasure
    (N : ℕ) (xi : Measure (ComplexMatrixGL N))
    (mu : Measure (ConcreteMatrixState N))
    [IsProbabilityMeasure xi] [IsProbabilityMeasure mu] :
    signedKernelAction (congruenceUpdateKernel N xi)
        (VariationSignedMeasure.ofSignedMeasure mu.toSignedMeasure) =
      VariationSignedMeasure.ofSignedMeasure
        (congruenceMeasureAction N xi mu).toSignedMeasure := by
  rw [signedKernelAction_ofSignedMeasure]
  apply congrArg VariationSignedMeasure.ofSignedMeasure
  exact Measure.toSignedMeasure_congr
    (congruenceUpdateKernel_comp_eq_congruenceMeasureAction N xi mu)

/-- The concrete congruence action bundled in the derivative transport
operator interface. -/
def congruenceKernelVariationMarkovOperator
    (N : ℕ) (xi : Measure (ComplexMatrixGL N))
    [IsProbabilityMeasure xi] :
    VariationMarkovOperator (ConcreteMatrixState N) :=
  VariationMarkovOperator.ofKernel (congruenceUpdateKernel N xi)

theorem congruenceKernelVariationMarkovOperator_toSignedMeasure
    (N : ℕ) (xi : Measure (ComplexMatrixGL N))
    (mu : Measure (ConcreteMatrixState N))
    [IsProbabilityMeasure xi] [IsProbabilityMeasure mu] :
    congruenceKernelVariationMarkovOperator N xi
        (VariationSignedMeasure.ofSignedMeasure mu.toSignedMeasure) =
      VariationSignedMeasure.ofSignedMeasure
        (congruenceMeasureAction N xi mu).toSignedMeasure := by
  exact congruenceSignedKernelAction_toSignedMeasure N xi mu

theorem congruenceKernelVariationMarkovOperator_contractive
    (N : ℕ) (xi : Measure (ComplexMatrixGL N))
    [IsProbabilityMeasure xi]
    (s : VariationSignedMeasure (ConcreteMatrixState N)) :
    ‖congruenceKernelVariationMarkovOperator N xi s‖ ≤ ‖s‖ :=
  (congruenceKernelVariationMarkovOperator N xi).contractive s

/-- The ordinary transpose congruence action preserves probability mass. -/
theorem congruenceMeasureAction_isProbability
    (N : ℕ) (xi : Measure (ComplexMatrixGL N))
    (mu : Measure (ConcreteMatrixState N))
    [IsProbabilityMeasure xi] [IsProbabilityMeasure mu] :
    IsProbabilityMeasure (congruenceMeasureAction N xi mu) := by
  unfold congruenceMeasureAction
  exact Measure.isProbabilityMeasure_map
    (measurable_complexGLTransposeCongruence N).aemeasurable

/-- The centered orbital probability curve embedded in the variation norm
space through the concrete signed kernel extension. -/
def orbitalVariationCurve
    (N : ℕ) (hN : 1 ≤ N)
    (mu : Measure (ConcreteMatrixState N)) [IsProbabilityMeasure mu]
    (u : ℝ) : VariationSignedMeasure (ConcreteMatrixState N) :=
  letI : IsProbabilityMeasure (concreteOrbitalGLFactorLaw N u) :=
    concreteOrbitalGLFactorLaw_isProbability hN u
  congruenceKernelVariationMarkovOperator N
    (concreteOrbitalGLFactorLaw N u)
    (VariationSignedMeasure.ofSignedMeasure mu.toSignedMeasure)

/-- The curve K_u(T_xi mu), represented entirely through the concrete signed
kernel operators. -/
def orbitalAfterCongruenceVariationCurve
    (N : ℕ) (hN : 1 ≤ N)
    (xi : Measure (ComplexMatrixGL N)) [IsProbabilityMeasure xi]
    (mu : Measure (ConcreteMatrixState N)) [IsProbabilityMeasure mu]
    (u : ℝ) : VariationSignedMeasure (ConcreteMatrixState N) :=
  letI : IsProbabilityMeasure (concreteOrbitalGLFactorLaw N u) :=
    concreteOrbitalGLFactorLaw_isProbability hN u
  congruenceKernelVariationMarkovOperator N
    (concreteOrbitalGLFactorLaw N u)
    (congruenceKernelVariationMarkovOperator N xi
      (VariationSignedMeasure.ofSignedMeasure mu.toSignedMeasure))

/-- Paper Eq. III.9b for the concrete transpose congruence Markov kernel.
The probability commutation theorem identifies the left curve with the
concrete signed operator applied to the orbital curve, after which bounded
linearity transports every variation norm derivative. -/
theorem congruenceKernel_eq_hide_commute_derivative
    (N : ℕ) (xi : Measure (ComplexMatrixGL N))
    (mu : Measure (ConcreteMatrixState N))
    [IsProbabilityMeasure xi] [IsProbabilityMeasure mu]
    (hN : 1 ≤ N)
    (hmu : IsUnitaryCongruenceInvariant N mu)
    (hxi : IsUnitaryConjugationInvariant N xi)
    (I : Set ℝ) (hI : IsOpen I) (r j : ℕ)
    (hf : ContDiffOn ℝ r (orbitalVariationCurve N hN mu) I)
    (hj : j ≤ r) (s : ℝ) (hs : s ∈ I) :
    iteratedDerivWithin j
        (orbitalAfterCongruenceVariationCurve N hN xi mu) I s =
        congruenceKernelVariationMarkovOperator N xi
          (iteratedDerivWithin j (orbitalVariationCurve N hN mu) I s) ∧
      ‖iteratedDerivWithin j
          (orbitalAfterCongruenceVariationCurve N hN xi mu) I s‖ ≤
        ‖iteratedDerivWithin j (orbitalVariationCurve N hN mu) I s‖ := by
  let T := congruenceKernelVariationMarkovOperator N xi
  have hcurve : orbitalAfterCongruenceVariationCurve N hN xi mu =
      fun u ↦ T (orbitalVariationCurve N hN mu u) := by
    funext u
    letI : IsProbabilityMeasure (concreteOrbitalGLFactorLaw N u) :=
      concreteOrbitalGLFactorLaw_isProbability hN u
    letI : IsProbabilityMeasure (congruenceMeasureAction N xi mu) :=
      congruenceMeasureAction_isProbability N xi mu
    letI : IsProbabilityMeasure
        (congruenceMeasureAction N (concreteOrbitalGLFactorLaw N u) mu) :=
      congruenceMeasureAction_isProbability N
        (concreteOrbitalGLFactorLaw N u) mu
    letI : IsProbabilityMeasure
        (congruenceMeasureAction N (concreteOrbitalGLFactorLaw N u)
          (congruenceMeasureAction N xi mu)) :=
      congruenceMeasureAction_isProbability N
        (concreteOrbitalGLFactorLaw N u) (congruenceMeasureAction N xi mu)
    letI : IsProbabilityMeasure
        (congruenceMeasureAction N xi
          (congruenceMeasureAction N (concreteOrbitalGLFactorLaw N u) mu)) :=
      congruenceMeasureAction_isProbability N xi
        (congruenceMeasureAction N (concreteOrbitalGLFactorLaw N u) mu)
    have hcomm := congruenceMeasureActions_commute_of_unitary_invariant
      (concreteOrbitalGLFactorLaw N u) xi mu hmu
      (concreteOrbitalGLFactorLaw_preservesUnitaryCongruenceInvariant hN u)
      hxi.preservesUnitaryCongruenceInvariant
    calc
      orbitalAfterCongruenceVariationCurve N hN xi mu u =
          VariationSignedMeasure.ofSignedMeasure
            (congruenceMeasureAction N (concreteOrbitalGLFactorLaw N u)
              (congruenceMeasureAction N xi mu)).toSignedMeasure := by
        unfold orbitalAfterCongruenceVariationCurve
        rw [congruenceKernelVariationMarkovOperator_toSignedMeasure,
          congruenceKernelVariationMarkovOperator_toSignedMeasure]
      _ = VariationSignedMeasure.ofSignedMeasure
            (congruenceMeasureAction N xi
              (congruenceMeasureAction N (concreteOrbitalGLFactorLaw N u) mu)).toSignedMeasure := by
        apply congrArg VariationSignedMeasure.ofSignedMeasure
        exact Measure.toSignedMeasure_congr hcomm
      _ = T (orbitalVariationCurve N hN mu u) := by
        unfold orbitalVariationCurve T
        rw [congruenceKernelVariationMarkovOperator_toSignedMeasure,
          congruenceKernelVariationMarkovOperator_toSignedMeasure]
  rw [hcurve]
  exact (congruenceKernelVariationMarkovOperator N xi).eq_hide_commute_derivative
    (orbitalVariationCurve N hN mu) I hI r j hf hj s hs

end ConcreteCongruenceKernelAdapter

end

end LogdetLean.GramHafnian.ThreePaper.Verification
