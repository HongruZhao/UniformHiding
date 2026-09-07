import LogdetLean.GramHafnian.ThreePaper.GaussianAnticoncentration
import LogdetLean.GramHafnian.ThreePaper.UniformMatrixHiding
import LogdetLean.GramHafnian.ThreePaper.DisjointGaussianRows
import LogdetLean.GramHafnian.LocalAnticoncentration.RowSymmetry
import LogdetLean.GramHafnian.UltimateHiding.SquaredGBS
import Mathlib.Data.Fintype.Sets
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# Axiom-free application endpoints for the interaction Letter

This module contains only elementary probability and real-algebra adapters.
It introduces no scientific input.  In particular, the finite-Haar
truncated-moment theorem transfers a bounded observable through total
variation; its Gaussian negative-moment bound remains an explicit premise
until discharged by the anticoncentration Article endpoint.
-/

open MeasureTheory
open scoped ProbabilityTheory

namespace LogdetLean.GramHafnian.ThreePaper.RelativeAccuracy

noncomputable section

open LocalAnticoncentration UltimateHiding ProbabilityTheory

/-! ## Collision-free labels and finite uniform fractions -/

/-- A law identity after forgetting auxiliary coordinates gives the literal
probability identity for every measurable event in the retained coordinate. -/
theorem measure_preimage_fst_eq_of_map_eq
    {X D : Type*} [MeasurableSpace X] [MeasurableSpace D]
    (μ : Measure (X × D)) (ν : Measure X)
    (hmap : Measure.map Prod.fst μ = ν)
    (E : Set X) (hE : MeasurableSet E) :
    μ (Prod.fst ⁻¹' E) = ν E := by
  rw [← hmap, Measure.map_apply measurable_fst hE]

/-- Uniform average over a finite label type.  It is useful independently
of the particular collision-free realization below. -/
def uniformFiniteAverage {iota : Type*} [Fintype iota]
    (f : iota → Real) : Real :=
  (∑ i, f i) / Fintype.card iota

/-- A common pointwise label bound controls its uniform finite average. -/
theorem uniformFiniteAverage_le
    {iota : Type*} [Fintype iota] [Nonempty iota]
    (f : iota → Real) {e : Real} (hf : ∀ i, f i ≤ e) :
    uniformFiniteAverage f ≤ e := by
  have hcard : (0 : Real) < Fintype.card iota := by positivity
  unfold uniformFiniteAverage
  apply (div_le_iff₀ hcard).2
  calc
    (∑ i, f i) ≤ ∑ _i : iota, e := Finset.sum_le_sum fun i _ ↦ hf i
    _ = e * (Fintype.card iota : Real) := by simp [mul_comm]

/-- The finite set of collision-free `N`-photon labels among `M` output
modes.  A label is represented by the corresponding `N`-element subset of
`Fin M`. -/
def collisionFreeLabelSet (M N : Nat) : Finset (Finset (Fin M)) :=
  (Finset.univ : Finset (Fin M)).powersetCard N

/-- The finite type carried by the collision-free label set. -/
abbrev CollisionFreeLabel (M N : Nat) : Type :=
  ↑(collisionFreeLabelSet M N)

/-- Exact cardinality of the collision-free label space. -/
theorem collisionFreeLabelSpace_card (M N : Nat) :
    Fintype.card (CollisionFreeLabel M N) = Nat.choose M N := by
  simp [CollisionFreeLabel, collisionFreeLabelSet]

/-- The collision-free label type is nonempty whenever `N ≤ M`. -/
theorem collisionFreeLabelSpace_nonempty {M N : Nat} (hNM : N ≤ M) :
    Nonempty (CollisionFreeLabel M N) := by
  rw [← Fintype.card_pos_iff, collisionFreeLabelSpace_card]
  exact Nat.choose_pos hNM

/-- Uniform finite average of indicator events.  This is the exact abstract
form of the dark-label fraction `D_t(U)` and may be instantiated with the
collision-free label type above. -/
def darkLabelFraction {Omega iota : Type*} [Fintype iota]
    (dark : iota → Set Omega) (omega : Omega) : Real :=
  uniformFiniteAverage fun i ↦ (dark i).indicator (fun _ ↦ (1 : Real)) omega

/-- Every dark-label fraction is nonnegative. -/
theorem darkLabelFraction_nonneg
    {Omega iota : Type*} [Fintype iota]
    (dark : iota → Set Omega) (omega : Omega) :
    0 ≤ darkLabelFraction dark omega := by
  unfold darkLabelFraction uniformFiniteAverage
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro i hi
    by_cases homega : omega ∈ dark i <;> simp [homega]
  · positivity

/-- For a nonempty label type, every dark-label fraction is at most one. -/
theorem darkLabelFraction_le_one
    {Omega iota : Type*} [Fintype iota] [Nonempty iota]
    (dark : iota → Set Omega) (omega : Omega) :
    darkLabelFraction dark omega ≤ 1 := by
  apply uniformFiniteAverage_le
  intro i
  by_cases hi : omega ∈ dark i <;> simp [hi]

/-- Measurability of the finite dark-label fraction. -/
theorem darkLabelFraction_measurable
    {Omega iota : Type*} [MeasurableSpace Omega] [Fintype iota]
    (dark : iota → Set Omega) (hdark : ∀ i, MeasurableSet (dark i)) :
    Measurable (darkLabelFraction dark) := by
  unfold darkLabelFraction uniformFiniteAverage
  apply Measurable.div_const
  apply Finset.measurable_fun_sum
  intro i hi
  exact measurable_const.indicator (hdark i)

/-- Exact finite Fubini identity: the expected dark-label fraction is the
uniform average of the one-label marginal probabilities. -/
theorem expectedDarkLabelFraction_eq_uniformMarginal
    {Omega iota : Type*} [MeasurableSpace Omega] [Fintype iota]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (dark : iota → Set Omega) (hdark : ∀ i, MeasurableSet (dark i)) :
    (∫ omega, darkLabelFraction dark omega ∂mu) =
      uniformFiniteAverage (fun i ↦ mu.real (dark i)) := by
  unfold darkLabelFraction uniformFiniteAverage
  rw [integral_div]
  congr 1
  rw [integral_finsetSum Finset.univ]
  · apply Finset.sum_congr rfl
    intro i hi
    exact integral_indicator_one (hdark i)
  · intro i hi
    exact ((integrable_const (1 : Real)).integrableOn).integrable_indicator
      (hdark i)

/-- An explicit common one-label marginal bound (for example, supplied by
Haar row exchangeability and the one-pattern theorem) controls the expected
dark-label fraction. -/
theorem expectedDarkLabelFraction_le
    {Omega iota : Type*} [MeasurableSpace Omega] [Fintype iota]
    [Nonempty iota]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (dark : iota → Set Omega) (hdark : ∀ i, MeasurableSet (dark i))
    {e : Real} (hmarginal : ∀ i, mu.real (dark i) ≤ e) :
    (∫ omega, darkLabelFraction dark omega ∂mu) ≤ e := by
  rw [expectedDarkLabelFraction_eq_uniformMarginal mu dark hdark]
  exact uniformFiniteAverage_le _ hmarginal

/-- The paper's finite dark-error budget, with no probabilistic content
hidden in the definition. -/
def darkLabelError (M N K n : Nat) (t : Real) : Real :=
  min 1 (shiftedAnticoncentrationConstant K n * t +
    UniformMatrixHiding.hidingRemainder M N)

/-! ## Markov tradeoffs -/

/-- The general circuitwise Markov tradeoff used twice in the Letter. -/
theorem generalMarkovTradeoff
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (failureFraction : Omega -> Real)
    (h_nonneg : ∀ᵐ omega ∂mu, 0 <= failureFraction omega)
    (h_int : Integrable failureFraction mu)
    {e a : Real} (ha : 0 < a)
    (h_expect : (∫ omega, failureFraction omega ∂mu) <= e) :
    mu.real {omega | a < failureFraction omega} <= e / a := by
  have hsubset : {omega | a < failureFraction omega} ⊆
      {omega | a <= failureFraction omega} := by
    intro omega homega
    change a < failureFraction omega at homega
    exact homega.le
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    h_nonneg h_int a
  apply (le_div_iff₀ ha).2
  calc
    mu.real {omega | a < failureFraction omega} * a =
        a * mu.real {omega | a < failureFraction omega} := by ring
    _ <= a * mu.real {omega | a <= failureFraction omega} :=
      mul_le_mul_of_nonneg_left (measureReal_mono hsubset) ha.le
    _ <= ∫ omega, failureFraction omega ∂mu := hmarkov
    _ <= e := h_expect

/-- The square-root choice exactly balances the two Markov losses.  Unlike
the earlier positive-error-only adapter, this statement also handles `e=0`. -/
theorem balancedMarkovTradeoff
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (failureFraction : Omega -> Real)
    (h_nonneg : ∀ᵐ omega ∂mu, 0 <= failureFraction omega)
    (h_int : Integrable failureFraction mu)
    {e : Real} (he : 0 <= e)
    (h_expect : (∫ omega, failureFraction omega ∂mu) <= e) :
    mu.real {omega | Real.sqrt e < failureFraction omega} <= Real.sqrt e := by
  rcases he.eq_or_lt with rfl | hepos
  · have hintegral_nonneg : 0 <= ∫ omega, failureFraction omega ∂mu :=
      integral_nonneg_of_ae h_nonneg
    have hintegral_zero : (∫ omega, failureFraction omega ∂mu) = 0 := by
      linarith
    have hae_zero : failureFraction =ᵐ[mu] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae h_nonneg h_int).1 hintegral_zero
    have hnull : mu {omega | 0 < failureFraction omega} = 0 := by
      apply measure_mono_null (t := {omega | failureFraction omega ≠ 0})
      · intro omega homega hzero
        change 0 < failureFraction omega at homega
        simp [hzero] at homega
      · exact ae_iff.mp hae_zero
    simp only [Real.sqrt_zero]
    simp [measureReal_def, hnull]
  · have htrade := generalMarkovTradeoff mu failureFraction
      h_nonneg h_int (Real.sqrt_pos.2 hepos) h_expect
    calc
      mu.real {omega | Real.sqrt e < failureFraction omega} <=
          e / Real.sqrt e := htrade
      _ = Real.sqrt e := by
        rw [div_eq_iff (Real.sqrt_pos.2 hepos).ne']
        exact (Real.mul_self_sqrt hepos.le).symm

/-- Literal most-labels Markov wrapper under the explicit common-marginal
hypothesis.  It includes the zero-error case. -/
theorem mostLabelsNotDark
    {Omega iota : Type*} [MeasurableSpace Omega] [Fintype iota]
    [Nonempty iota]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (dark : iota → Set Omega) (hdark : ∀ i, MeasurableSet (dark i))
    {e : Real} (he : 0 ≤ e) (hmarginal : ∀ i, mu.real (dark i) ≤ e) :
    mu.real {omega | Real.sqrt e < darkLabelFraction dark omega} ≤
      Real.sqrt e := by
  have hmeas := darkLabelFraction_measurable dark hdark
  have hint : Integrable (darkLabelFraction dark) mu := by
    apply (integrable_const (1 : Real)).mono hmeas.aestronglyMeasurable
    filter_upwards [] with omega
    rw [Real.norm_eq_abs, abs_of_nonneg (darkLabelFraction_nonneg dark omega),
      norm_one]
    exact darkLabelFraction_le_one dark omega
  exact balancedMarkovTradeoff mu (darkLabelFraction dark)
    (Filter.Eventually.of_forall (darkLabelFraction_nonneg dark)) hint he
    (expectedDarkLabelFraction_le mu dark hdark hmarginal)

/-! ## Conditional failure fractions -/

/-- For a conditional Markov kernel `kappa`, the conditional probability of
a joint bad event.  This is the rigorous construction underlying the
paper's notation `R_rho(U)`. -/
def conditionalFailureProbability
    {Omega Theta : Type*} [MeasurableSpace Omega] [MeasurableSpace Theta]
    (kappa : ProbabilityTheory.Kernel Omega Theta)
    (bad : Set (Omega × Theta)) (omega : Omega) : Real :=
  ∫ theta, bad.indicator (fun _ ↦ (1 : Real)) (omega, theta) ∂(kappa omega)

/-- The conditional failure construction is literally the real-valued
kernel probability of the corresponding event section. -/
theorem conditionalFailureProbability_eq_measureReal
    {Omega Theta : Type*} [MeasurableSpace Omega] [MeasurableSpace Theta]
    (kappa : ProbabilityTheory.Kernel Omega Theta)
    (bad : Set (Omega × Theta)) (hbad : MeasurableSet bad) (omega : Omega) :
    conditionalFailureProbability kappa bad omega =
      (kappa omega).real (Prod.mk omega ⁻¹' bad) := by
  unfold conditionalFailureProbability
  change (∫ theta, (Prod.mk omega ⁻¹' bad).indicator
    (fun _ ↦ (1 : Real)) theta ∂(kappa omega)) = _
  exact integral_indicator_one (measurable_prodMk_left hbad)

/-- Measurability of a conditional failure fraction. -/
theorem conditionalFailureProbability_measurable
    {Omega Theta : Type*} [MeasurableSpace Omega] [MeasurableSpace Theta]
    (kappa : ProbabilityTheory.Kernel Omega Theta) [IsFiniteKernel kappa]
    (bad : Set (Omega × Theta)) (hbad : MeasurableSet bad) :
    Measurable (conditionalFailureProbability kappa bad) := by
  unfold conditionalFailureProbability
  exact (measurable_const.indicator hbad).stronglyMeasurable
    |>.integral_kernel_prod_right' |>.measurable

/-- Conditional failure probabilities lie in `[0,1]` for a Markov kernel. -/
theorem conditionalFailureProbability_mem_unitInterval
    {Omega Theta : Type*} [MeasurableSpace Omega] [MeasurableSpace Theta]
    (kappa : ProbabilityTheory.Kernel Omega Theta) [IsMarkovKernel kappa]
    (bad : Set (Omega × Theta)) (hbad : MeasurableSet bad) (omega : Omega) :
    conditionalFailureProbability kappa bad omega ∈ Set.Icc (0 : Real) 1 := by
  rw [conditionalFailureProbability_eq_measureReal kappa bad hbad omega]
  exact ⟨measureReal_nonneg, measureReal_le_one⟩

/-- Exact tower identity for the conditional failure construction. -/
theorem expectedConditionalFailureProbability
    {Omega Theta : Type*} [MeasurableSpace Omega] [MeasurableSpace Theta]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (kappa : ProbabilityTheory.Kernel Omega Theta) [IsMarkovKernel kappa]
    (bad : Set (Omega × Theta)) (hbad : MeasurableSet bad) :
    (∫ omega, conditionalFailureProbability kappa bad omega ∂mu) =
      (mu ⊗ₘ kappa).real bad := by
  have hint : Integrable
      (bad.indicator (fun _ ↦ (1 : Real))) (mu ⊗ₘ kappa) :=
    ((integrable_const (1 : Real)).integrableOn).integrable_indicator hbad
  unfold conditionalFailureProbability
  rw [← Measure.integral_compProd hint]
  exact integral_indicator_one hbad

/-- A second Markov step converts a joint conditional-failure budget into a
most-circuits conditional-failure statement. -/
theorem circuitwiseConditionalFailure
    {Omega Theta : Type*} [MeasurableSpace Omega] [MeasurableSpace Theta]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (kappa : ProbabilityTheory.Kernel Omega Theta) [IsMarkovKernel kappa]
    (bad : Set (Omega × Theta)) (hbad : MeasurableSet bad)
    {e : Real} (he : 0 ≤ e) (hjoint : (mu ⊗ₘ kappa).real bad ≤ e) :
    mu.real {omega | Real.sqrt e <
      conditionalFailureProbability kappa bad omega} ≤ Real.sqrt e := by
  have hmeas := conditionalFailureProbability_measurable kappa bad hbad
  have hint : Integrable (conditionalFailureProbability kappa bad) mu := by
    apply (integrable_const (1 : Real)).mono hmeas.aestronglyMeasurable
    filter_upwards [] with omega
    obtain ⟨hnonneg, hle⟩ :=
      conditionalFailureProbability_mem_unitInterval kappa bad hbad omega
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg, norm_one]
    exact hle
  apply balancedMarkovTradeoff mu (conditionalFailureProbability kappa bad)
    (Filter.Eventually.of_forall fun omega ↦
      (conditionalFailureProbability_mem_unitInterval kappa bad hbad omega).1)
    hint he
  rw [expectedConditionalFailureProbability mu kappa bad hbad]
  exact hjoint

/-- The conditional relative-error failure fraction `R_rho(U)`. -/
def conditionalRelativeFailureProbability
    {Omega Theta : Type*} [MeasurableSpace Omega] [MeasurableSpace Theta]
    (kappa : ProbabilityTheory.Kernel Omega Theta)
    (deltaP p : Omega × Theta → Real) (rho : Real) : Omega → Real :=
  conditionalFailureProbability kappa (relativeFailureEvent deltaP p rho)

/-! ## Full discrete TV to uniform-label sampler bounds -/

/-- Total variation for real mass functions on a finite discrete space,
under the convention `d_TV = (1/2) sum_x |p_x-q_x|`. -/
def finiteDiscreteTotalVariation
    {chi : Type*} [Fintype chi] (p q : chi → Real) : Real :=
  (1 / 2 : Real) * ∑ x, |p x - q x|

/-- Mean absolute mass error over a nonempty finite subset of a larger
finite discrete output space. -/
def finiteSubsetMeanAbsError
    {chi : Type*} [Fintype chi] (labels : Finset chi)
    (p q : chi → Real) : Real :=
  (∑ x ∈ labels, |p x - q x|) / labels.card

/-- Restricting a full finite discrete-TV bound to any nonempty label subset
gives the exact uniform-label mean bound `2 eps / |labels|`. -/
theorem finiteDiscreteTV_to_uniformLabelMean
    {chi : Type*} [Fintype chi]
    (labels : Finset chi) (hlabels : labels.Nonempty)
    (p q : chi → Real) {eps : Real}
    (htv : finiteDiscreteTotalVariation p q ≤ eps) :
    finiteSubsetMeanAbsError labels p q ≤
      2 * eps / labels.card := by
  classical
  have hfull : (∑ x, |p x - q x|) ≤ 2 * eps := by
    unfold finiteDiscreteTotalVariation at htv
    linarith
  have hsubset : (∑ x ∈ labels, |p x - q x|) ≤
      ∑ x, |p x - q x| := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ labels) (fun x hx hnot ↦ abs_nonneg (p x - q x))
  have hcard : (0 : Real) ≤ labels.card := by positivity
  unfold finiteSubsetMeanAbsError
  exact (div_le_div_of_nonneg_right (hsubset.trans hfull) hcard)

/-- Finite uniform Markov inequality, written as an exact indicator average. -/
theorem finiteUniformMarkov
    {iota : Type*} [Fintype iota] [Nonempty iota]
    (f : iota → Real) (hf : ∀ i, 0 ≤ f i)
    {a mean : Real} (ha : 0 < a)
    (hmean : uniformFiniteAverage f ≤ mean) :
    uniformFiniteAverage (fun i ↦ if a < f i then (1 : Real) else 0) ≤
      mean / a := by
  have hcard : (0 : Real) < Fintype.card iota := by positivity
  have hpoint (i : iota) :
      a * (if a < f i then (1 : Real) else 0) ≤ f i := by
    by_cases hi : a < f i
    · simp [hi, hi.le]
    · simp [hi, hf i]
  apply (le_div_iff₀ ha).2
  calc
    uniformFiniteAverage (fun i ↦ if a < f i then (1 : Real) else 0) * a =
        a * (∑ i, (if a < f i then (1 : Real) else 0)) /
          Fintype.card iota := by
            unfold uniformFiniteAverage
            ring
    _ = (∑ i, a * (if a < f i then (1 : Real) else 0)) /
          Fintype.card iota := by rw [Finset.mul_sum]
    _ ≤ (∑ i, f i) / Fintype.card iota :=
      div_le_div_of_nonneg_right
        (Finset.sum_le_sum fun i hi ↦ hpoint i) hcard.le
    _ = uniformFiniteAverage f := rfl
    _ ≤ mean := hmean

/-- Full finite discrete TV implies the exact uniform-label additive-error
interface from the Letter.  The left side is literally the fraction of
labels above the displayed threshold. -/
theorem samplerTVToUniformLabelAdditive
    {chi : Type*} [Fintype chi]
    (labels : Finset chi) (hlabels : labels.Nonempty)
    (p q : chi → Real) {eps zeta : Real}
    (heps : 0 < eps) (hzeta : 0 < zeta)
    (htv : finiteDiscreteTotalVariation p q ≤ eps) :
    uniformFiniteAverage (fun x : ↑labels ↦
      if 2 * eps / (zeta * labels.card) < |p x - q x|
      then (1 : Real) else 0) ≤ zeta := by
  haveI : Nonempty ↑labels := ⟨⟨hlabels.choose, hlabels.choose_spec⟩⟩
  have hmean : uniformFiniteAverage (fun x : ↑labels ↦ |p x - q x|) ≤
      2 * eps / labels.card := by
    calc
      uniformFiniteAverage (fun x : ↑labels ↦ |p x - q x|) =
          finiteSubsetMeanAbsError labels p q := by
        unfold uniformFiniteAverage finiteSubsetMeanAbsError
        rw [← Finset.sum_attach labels (fun x ↦ |p x - q x|),
          Finset.attach_eq_univ, Fintype.card_coe]
      _ ≤ 2 * eps / labels.card :=
        finiteDiscreteTV_to_uniformLabelMean labels hlabels p q htv
  have hcard : (0 : Real) < labels.card := by
    exact_mod_cast hlabels.card_pos
  have hthreshold : 0 < 2 * eps / (zeta * labels.card) := by positivity
  have hmarkov := finiteUniformMarkov
    (fun x : ↑labels ↦ |p x - q x|)
    (fun x ↦ abs_nonneg (p x - q x)) hthreshold hmean
  calc
    uniformFiniteAverage (fun x : ↑labels ↦
        if 2 * eps / (zeta * labels.card) < |p x - q x|
        then (1 : Real) else 0) ≤
      (2 * eps / labels.card) /
        (2 * eps / (zeta * labels.card)) := hmarkov
    _ = zeta := by field_simp

/-! ## Eventwise TV on an arbitrary discrete ambient output type -/

/-- Every finite event has mass difference at most `delta`.  Unlike the
older finite discrete definition, this premise does not require the ambient
output type to be finite. -/
def finiteEventTotalVariationLE
    {chi : Type*} (p q : chi → ℝ) (delta : ℝ) : Prop :=
  ∀ s : Finset chi, |∑ x ∈ s, (p x - q x)| ≤ delta

/-- Mean absolute mass error on one finite panel inside an arbitrary ambient
output type. -/
def eventwiseFiniteLabelMeanAbsError
    {chi : Type*} (labels : Finset chi) (p q : chi → ℝ) : ℝ :=
  (∑ x ∈ labels, |p x - q x|) / (labels.card : ℝ)

/-- Fraction of one finite panel above an absolute error threshold. -/
def eventwiseFiniteLabelBadFraction
    {chi : Type*} (labels : Finset chi) (p q : chi → ℝ)
    (threshold : ℝ) : ℝ :=
  ((labels.filter fun x ↦ threshold < |p x - q x|).card : ℝ) /
    (labels.card : ℝ)

/-- An eventwise TV premise controls the `L¹` error on every finite panel
with the sharp factor two, without requiring a finite ambient output type. -/
theorem eventwiseFiniteTV_sum_abs_le_two
    {chi : Type*} (p q : chi → ℝ) {delta : ℝ}
    (htv : finiteEventTotalVariationLE p q delta)
    (labels : Finset chi) :
    (∑ x ∈ labels, |p x - q x|) ≤ 2 * delta := by
  classical
  let d : chi → ℝ := fun x ↦ p x - q x
  let positive := labels.filter fun x ↦ 0 ≤ d x
  let negative := labels.filter fun x ↦ ¬ 0 ≤ d x
  have hsplit :
      (∑ x ∈ labels, |d x|) =
        (∑ x ∈ positive, d x) + (∑ x ∈ negative, -d x) := by
    calc
      (∑ x ∈ labels, |d x|) =
          (∑ x ∈ labels with 0 ≤ d x, |d x|) +
            (∑ x ∈ labels with ¬ 0 ≤ d x, |d x|) :=
        (Finset.sum_filter_add_sum_filter_not labels
          (fun x ↦ 0 ≤ d x) (fun x ↦ |d x|)).symm
      _ = (∑ x ∈ positive, d x) + (∑ x ∈ negative, -d x) := by
        apply congrArg₂ (.+.)
        · unfold positive
          apply Finset.sum_congr rfl
          intro x hx
          exact abs_of_nonneg (Finset.mem_filter.mp hx).2
        · unfold negative
          apply Finset.sum_congr rfl
          intro x hx
          exact abs_of_neg (lt_of_not_ge (Finset.mem_filter.mp hx).2)
  have hpositive : (∑ x ∈ positive, d x) ≤ delta := by
    exact (le_abs_self _).trans (by simpa [d] using htv positive)
  have hnegative : (∑ x ∈ negative, -d x) ≤ delta := by
    rw [Finset.sum_neg_distrib]
    exact (neg_le_abs _).trans (by simpa [d] using htv negative)
  calc
    (∑ x ∈ labels, |p x - q x|) =
        (∑ x ∈ positive, d x) + (∑ x ∈ negative, -d x) := by
      simpa [d] using hsplit
    _ ≤ delta + delta := add_le_add hpositive hnegative
    _ = 2 * delta := by ring

/-- A measure level total variation bound supplies the finite event premise
for singleton masses on every discrete measurable output space. -/
theorem probabilityTotalVariationLE_to_finiteEventTotalVariationLE
    {chi : Type*} [MeasurableSpace chi] [MeasurableSingletonClass chi]
    (mu : Measure chi) [IsProbabilityMeasure mu]
    (nu : Measure chi) [IsProbabilityMeasure nu]
    {delta : ℝ} (htv : probabilityTotalVariationLE mu nu delta) :
    finiteEventTotalVariationLE
      (fun x ↦ mu.real {x}) (fun x ↦ nu.real {x}) delta := by
  intro s
  have hs : MeasurableSet (s : Set chi) := s.measurableSet
  have hevent := htv.2 (s : Set chi) hs
  simpa [Finset.sum_sub_distrib] using hevent

/-- Uniform label mean consequence of eventwise TV on an arbitrary ambient
output type. -/
theorem eventwiseFiniteTV_to_uniformLabelMean
    {chi : Type*} (labels : Finset chi) (hlabels : labels.Nonempty)
    (p q : chi → ℝ) {delta : ℝ}
    (htv : finiteEventTotalVariationLE p q delta) :
    eventwiseFiniteLabelMeanAbsError labels p q ≤
      2 * delta / (labels.card : ℝ) := by
  have hcard : (0 : ℝ) < labels.card := by
    exact_mod_cast hlabels.card_pos
  unfold eventwiseFiniteLabelMeanAbsError
  exact (div_le_div_iff_of_pos_right hcard).2
    (eventwiseFiniteTV_sum_abs_le_two p q htv labels)

/-- Exact uniform label Markov consequence of eventwise TV on an arbitrary
ambient output type. -/
theorem eventwiseFiniteTV_to_uniformLabelMarkov
    {chi : Type*} (labels : Finset chi) (hlabels : labels.Nonempty)
    (p q : chi → ℝ) {delta zeta : ℝ}
    (hdelta : 0 < delta) (hzeta : 0 < zeta)
    (htv : finiteEventTotalVariationLE p q delta) :
    uniformFiniteAverage (fun x : ↑labels ↦
      if 2 * delta / (zeta * labels.card) < |p x - q x|
      then (1 : ℝ) else 0) ≤ zeta := by
  classical
  let _ : Nonempty ↑labels :=
    ⟨⟨hlabels.choose, hlabels.choose_spec⟩⟩
  have hmean :
      uniformFiniteAverage (fun x : ↑labels ↦ |p x - q x|) ≤
        2 * delta / (labels.card : ℝ) := by
    calc
      uniformFiniteAverage (fun x : ↑labels ↦ |p x - q x|) =
          eventwiseFiniteLabelMeanAbsError labels p q := by
        unfold uniformFiniteAverage eventwiseFiniteLabelMeanAbsError
        rw [← Finset.sum_attach labels (fun x ↦ |p x - q x|),
          Finset.attach_eq_univ, Fintype.card_coe]
      _ ≤ 2 * delta / (labels.card : ℝ) :=
        eventwiseFiniteTV_to_uniformLabelMean labels hlabels p q htv
  have hthreshold : 0 < 2 * delta / (zeta * labels.card) := by
    positivity
  have hmarkov := finiteUniformMarkov
    (fun x : ↑labels ↦ |p x - q x|)
    (fun x ↦ abs_nonneg (p x - q x)) hthreshold hmean
  calc
    uniformFiniteAverage (fun x : ↑labels ↦
        if 2 * delta / (zeta * labels.card) < |p x - q x|
        then (1 : ℝ) else 0) ≤
      (2 * delta / (labels.card : ℝ)) /
        (2 * delta / (zeta * labels.card)) := hmarkov
    _ = zeta := by field_simp

/-- Filtered cardinality form of the same Markov consequence. -/
theorem eventwiseFiniteTV_to_badFraction
    {chi : Type*} (labels : Finset chi) (hlabels : labels.Nonempty)
    (p q : chi → ℝ) {delta zeta : ℝ}
    (hdelta : 0 < delta) (hzeta : 0 < zeta)
    (htv : finiteEventTotalVariationLE p q delta) :
    eventwiseFiniteLabelBadFraction labels p q
        (2 * delta / (zeta * labels.card)) ≤ zeta := by
  classical
  let threshold : ℝ := 2 * delta / (zeta * labels.card)
  let bad := labels.filter fun x ↦ threshold < |p x - q x|
  have hcard : (0 : ℝ) < labels.card := by
    exact_mod_cast hlabels.card_pos
  have hthreshold : 0 < threshold := by
    dsimp [threshold]
    positivity
  have hbadLower : threshold * (bad.card : ℝ) ≤
      ∑ x ∈ bad, |p x - q x| := by
    calc
      threshold * (bad.card : ℝ) = ∑ _x ∈ bad, threshold := by
        simp [mul_comm]
      _ ≤ ∑ x ∈ bad, |p x - q x| := by
        apply Finset.sum_le_sum
        intro x hx
        exact (Finset.mem_filter.mp hx).2.le
  have hbadUpper : (∑ x ∈ bad, |p x - q x|) ≤
      ∑ x ∈ labels, |p x - q x| := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun x hx hnot ↦ abs_nonneg (p x - q x))
  have hpanel := eventwiseFiniteTV_sum_abs_le_two p q htv labels
  have hbadProduct : threshold * (bad.card : ℝ) ≤ 2 * delta :=
    hbadLower.trans (hbadUpper.trans hpanel)
  have hbadCard : (bad.card : ℝ) ≤ zeta * (labels.card : ℝ) := by
    calc
      (bad.card : ℝ) ≤ (2 * delta) / threshold := by
        apply (le_div_iff₀ hthreshold).2
        simpa [mul_comm] using hbadProduct
      _ = zeta * (labels.card : ℝ) := by
        dsimp [threshold]
        field_simp
  unfold eventwiseFiniteLabelBadFraction
  change (bad.card : ℝ) / (labels.card : ℝ) ≤ zeta
  exact (div_le_iff₀ hcard).2 (by simpa [mul_comm] using hbadCard)

/-- Uniform-label fraction whose additive mass error exceeds `eta`. -/
def samplerAdditiveFailureFraction
    {Omega iota : Type*} [Fintype iota]
    (p q : Omega → iota → Real) (eta : Real) (omega : Omega) : Real :=
  darkLabelFraction
    (fun i ↦ {omega | eta < |p omega i - q omega i|}) omega

/-- Uniform-label fraction whose ideal mass is at most `eta/rho`. -/
def samplerDarkFraction
    {Omega iota : Type*} [Fintype iota]
    (p : Omega → iota → Real) (eta rho : Real) (omega : Omega) : Real :=
  darkLabelFraction
    (fun i ↦ {omega | p omega i ≤ eta / rho}) omega

/-- Uniform-label relative-error failure fraction. -/
def samplerRelativeFailureFraction
    {Omega iota : Type*} [Fintype iota]
    (p q : Omega → iota → Real) (rho : Real) (omega : Omega) : Real :=
  darkLabelFraction
    (fun i ↦ {omega | rho * p omega i < |p omega i - q omega i|}) omega

/-- The additive/dark event inclusion, averaged exactly over a finite label
type. -/
theorem samplerRelativeFailureFraction_le_additive_add_dark
    {Omega iota : Type*} [Fintype iota] [Nonempty iota]
    (p q : Omega → iota → Real) {eta rho : Real} (hrho : 0 < rho)
    (omega : Omega) :
    samplerRelativeFailureFraction p q rho omega ≤
      samplerAdditiveFailureFraction p q eta omega +
        samplerDarkFraction p eta rho omega := by
  have hcard : (0 : Real) < Fintype.card iota := by positivity
  unfold samplerRelativeFailureFraction samplerAdditiveFailureFraction
    samplerDarkFraction darkLabelFraction uniformFiniteAverage
  apply (div_le_iff₀ hcard).2
  rw [add_mul, div_mul_cancel₀ _ hcard.ne', div_mul_cancel₀ _ hcard.ne']
  calc
    ∑ i, {omega | rho * p omega i < |p omega i - q omega i|}.indicator
        (fun _ ↦ (1 : Real)) omega ≤
      ∑ i, ({omega | eta < |p omega i - q omega i|}.indicator
          (fun _ ↦ (1 : Real)) omega +
        {omega | p omega i ≤ eta / rho}.indicator
          (fun _ ↦ (1 : Real)) omega) := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hrel : rho * p omega i < |p omega i - q omega i|
      · by_cases hadd : eta < |p omega i - q omega i|
        · by_cases hdark : p omega i ≤ eta / rho <;>
            simp [hrel, hadd, hdark]
        · have habs : |p omega i - q omega i| ≤ eta := le_of_not_gt hadd
          have hdark : p omega i ≤ eta / rho := by
            apply (le_div_iff₀ hrho).2
            nlinarith
          simp [hrel, hadd, hdark]
      · by_cases hadd : eta < |p omega i - q omega i| <;>
          by_cases hdark : p omega i ≤ eta / rho <;>
          simp [hrel, hadd, hdark]
    _ = (∑ i, {omega | eta < |p omega i - q omega i|}.indicator
          (fun _ ↦ (1 : Real)) omega) +
        ∑ i, {omega | p omega i ≤ eta / rho}.indicator
          (fun _ ↦ (1 : Real)) omega := Finset.sum_add_distrib

set_option maxHeartbeats 800000 in
/-- The exact sampler composition: a pointwise full-discrete-TV guarantee
and an averaged dark-label bound imply averaged random-label relative
accuracy.  No label independence is used. -/
theorem samplerTVToRandomLabelRelative
    {Omega chi : Type*} [MeasurableSpace Omega] [Fintype chi]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (labels : Finset chi) (hlabels : labels.Nonempty)
    (p q : Omega → chi → Real)
    (hp : ∀ x, Measurable fun omega ↦ p omega x)
    (hq : ∀ x, Measurable fun omega ↦ q omega x)
    {eps zeta rho darkBound : Real}
    (heps : 0 < eps) (hzeta : 0 < zeta) (hrho : 0 < rho)
    (htv : ∀ omega, finiteDiscreteTotalVariation (p omega) (q omega) ≤ eps)
    (hdark : (∫ omega, samplerDarkFraction
      (fun omega (x : ↑labels) ↦ p omega x)
      (2 * eps / (zeta * labels.card)) rho omega ∂mu) ≤ darkBound) :
    (∫ omega, samplerRelativeFailureFraction
      (fun omega (x : ↑labels) ↦ p omega x)
      (fun omega (x : ↑labels) ↦ q omega x) rho omega ∂mu) ≤
      min 1 (zeta + darkBound) := by
  haveI : Nonempty ↑labels := ⟨⟨hlabels.choose, hlabels.choose_spec⟩⟩
  let eta : Real := 2 * eps / (zeta * labels.card)
  let pLabel : Omega → ↑labels → Real := fun omega x ↦ p omega x
  let qLabel : Omega → ↑labels → Real := fun omega x ↦ q omega x
  have hadd (omega : Omega) :
      samplerAdditiveFailureFraction pLabel qLabel eta omega ≤ zeta := by
    have hbase := samplerTVToUniformLabelAdditive labels hlabels
      (p omega) (q omega) heps hzeta (htv omega)
    unfold samplerAdditiveFailureFraction darkLabelFraction
    have heq :
        (fun i : ↑labels ↦
          {omega | eta < |pLabel omega i - qLabel omega i|}.indicator
            (fun _ ↦ (1 : Real)) omega) =
        (fun x : ↑labels ↦
          if 2 * eps / (zeta * labels.card) < |p omega x - q omega x|
          then (1 : Real) else 0) := by
      funext x
      by_cases hx : eta < |p omega x - q omega x| <;>
        simp [hx, eta, pLabel, qLabel]
    rw [heq]
    exact hbase
  have hpoint (omega : Omega) :
      samplerRelativeFailureFraction pLabel qLabel rho omega ≤
        zeta + samplerDarkFraction pLabel eta rho omega := by
    exact (samplerRelativeFailureFraction_le_additive_add_dark
      pLabel qLabel (eta := eta) hrho omega).trans
        (add_le_add (hadd omega) le_rfl)
  have hrelMeas : Measurable
      (samplerRelativeFailureFraction pLabel qLabel rho) := by
    apply darkLabelFraction_measurable
    intro x
    exact measurableSet_lt (measurable_const.mul (hp x))
      ((hp x).sub (hq x)).abs
  have hdarkMeas : Measurable (samplerDarkFraction pLabel eta rho) := by
    apply darkLabelFraction_measurable
    intro x
    exact measurableSet_le (hp x) measurable_const
  have hrelInt : Integrable
      (samplerRelativeFailureFraction pLabel qLabel rho) mu := by
    apply (integrable_const (1 : Real)).mono hrelMeas.aestronglyMeasurable
    filter_upwards [] with omega
    unfold samplerRelativeFailureFraction
    rw [Real.norm_eq_abs,
      abs_of_nonneg (darkLabelFraction_nonneg _ omega), norm_one]
    exact darkLabelFraction_le_one _ omega
  have hdarkInt : Integrable (samplerDarkFraction pLabel eta rho) mu := by
    apply (integrable_const (1 : Real)).mono hdarkMeas.aestronglyMeasurable
    filter_upwards [] with omega
    unfold samplerDarkFraction
    rw [Real.norm_eq_abs,
      abs_of_nonneg (darkLabelFraction_nonneg _ omega), norm_one]
    exact darkLabelFraction_le_one _ omega
  apply le_min
  · calc
      (∫ omega, samplerRelativeFailureFraction pLabel qLabel rho omega ∂mu) ≤
          ∫ _omega, (1 : Real) ∂mu := by
            apply integral_mono hrelInt (integrable_const (1 : Real))
            exact fun omega ↦ darkLabelFraction_le_one _ omega
      _ = 1 := by simp
  · have hsumInt : Integrable
        (fun omega ↦ zeta + samplerDarkFraction pLabel eta rho omega) mu :=
      (integrable_const zeta).add hdarkInt
    calc
      (∫ omega, samplerRelativeFailureFraction pLabel qLabel rho omega ∂mu) ≤
          ∫ omega, zeta + samplerDarkFraction pLabel eta rho omega ∂mu :=
        integral_mono hrelInt hsumInt hpoint
      _ = zeta + ∫ omega, samplerDarkFraction pLabel eta rho omega ∂mu := by
        rw [integral_add (integrable_const zeta) hdarkInt]
        simp
      _ ≤ zeta + darkBound := by
        have hdark' :
            (∫ omega, samplerDarkFraction pLabel eta rho omega ∂mu) ≤
              darkBound := by simpa [eta, pLabel] using hdark
        linarith

set_option maxHeartbeats 800000 in
/-- The same sampler composition from eventwise TV on an arbitrary ambient
output type.  This is the form applicable to the full countable GBS pattern
space because only the finite collision free label panel is averaged. -/
theorem samplerTVToRandomLabelRelative_eventwise
    {Omega chi : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (labels : Finset chi) (hlabels : labels.Nonempty)
    (p q : Omega → chi → Real)
    (hp : ∀ x, Measurable fun omega ↦ p omega x)
    (hq : ∀ x, Measurable fun omega ↦ q omega x)
    {eps zeta rho darkBound : Real}
    (heps : 0 < eps) (hzeta : 0 < zeta) (hrho : 0 < rho)
    (htv : ∀ omega, finiteEventTotalVariationLE (p omega) (q omega) eps)
    (hdark : (∫ omega, samplerDarkFraction
      (fun omega (x : ↑labels) ↦ p omega x)
      (2 * eps / (zeta * labels.card)) rho omega ∂mu) ≤ darkBound) :
    (∫ omega, samplerRelativeFailureFraction
      (fun omega (x : ↑labels) ↦ p omega x)
      (fun omega (x : ↑labels) ↦ q omega x) rho omega ∂mu) ≤
      min 1 (zeta + darkBound) := by
  haveI : Nonempty ↑labels := ⟨⟨hlabels.choose, hlabels.choose_spec⟩⟩
  let eta : Real := 2 * eps / (zeta * labels.card)
  let pLabel : Omega → ↑labels → Real := fun omega x ↦ p omega x
  let qLabel : Omega → ↑labels → Real := fun omega x ↦ q omega x
  have hadd (omega : Omega) :
      samplerAdditiveFailureFraction pLabel qLabel eta omega ≤ zeta := by
    have hbase := eventwiseFiniteTV_to_uniformLabelMarkov labels hlabels
      (p omega) (q omega) heps hzeta (htv omega)
    unfold samplerAdditiveFailureFraction darkLabelFraction
    have heq :
        (fun i : ↑labels ↦
          {omega | eta < |pLabel omega i - qLabel omega i|}.indicator
            (fun _ ↦ (1 : Real)) omega) =
        (fun x : ↑labels ↦
          if 2 * eps / (zeta * labels.card) < |p omega x - q omega x|
          then (1 : Real) else 0) := by
      funext x
      by_cases hx : eta < |p omega x - q omega x| <;>
        simp [hx, eta, pLabel, qLabel]
    rw [heq]
    exact hbase
  have hpoint (omega : Omega) :
      samplerRelativeFailureFraction pLabel qLabel rho omega ≤
        zeta + samplerDarkFraction pLabel eta rho omega := by
    exact (samplerRelativeFailureFraction_le_additive_add_dark
      pLabel qLabel (eta := eta) hrho omega).trans
        (add_le_add (hadd omega) le_rfl)
  have hrelMeas : Measurable
      (samplerRelativeFailureFraction pLabel qLabel rho) := by
    apply darkLabelFraction_measurable
    intro x
    exact measurableSet_lt (measurable_const.mul (hp x))
      ((hp x).sub (hq x)).abs
  have hdarkMeas : Measurable (samplerDarkFraction pLabel eta rho) := by
    apply darkLabelFraction_measurable
    intro x
    exact measurableSet_le (hp x) measurable_const
  have hrelInt : Integrable
      (samplerRelativeFailureFraction pLabel qLabel rho) mu := by
    apply (integrable_const (1 : Real)).mono hrelMeas.aestronglyMeasurable
    filter_upwards [] with omega
    unfold samplerRelativeFailureFraction
    rw [Real.norm_eq_abs,
      abs_of_nonneg (darkLabelFraction_nonneg _ omega), norm_one]
    exact darkLabelFraction_le_one _ omega
  have hdarkInt : Integrable (samplerDarkFraction pLabel eta rho) mu := by
    apply (integrable_const (1 : Real)).mono hdarkMeas.aestronglyMeasurable
    filter_upwards [] with omega
    unfold samplerDarkFraction
    rw [Real.norm_eq_abs,
      abs_of_nonneg (darkLabelFraction_nonneg _ omega), norm_one]
    exact darkLabelFraction_le_one _ omega
  apply le_min
  · calc
      (∫ omega, samplerRelativeFailureFraction pLabel qLabel rho omega ∂mu) ≤
          ∫ _omega, (1 : Real) ∂mu := by
            apply integral_mono hrelInt (integrable_const (1 : Real))
            exact fun omega ↦ darkLabelFraction_le_one _ omega
      _ = 1 := by simp
  · have hsumInt : Integrable
        (fun omega ↦ zeta + samplerDarkFraction pLabel eta rho omega) mu :=
      (integrable_const zeta).add hdarkInt
    calc
      (∫ omega, samplerRelativeFailureFraction pLabel qLabel rho omega ∂mu) ≤
          ∫ omega, zeta + samplerDarkFraction pLabel eta rho omega ∂mu :=
        integral_mono hrelInt hsumInt hpoint
      _ = zeta + ∫ omega, samplerDarkFraction pLabel eta rho omega ∂mu := by
        rw [integral_add (integrable_const zeta) hdarkInt]
        simp
      _ ≤ zeta + darkBound := by
        have hdark' :
            (∫ omega, samplerDarkFraction pLabel eta rho omega ∂mu) ≤
              darkBound := by simpa [eta, pLabel] using hdark
        linarith

/-- The scalar `c_samp` appearing in the Letter's sampler-relative bound. -/
def samplerRelativeConstant
    (B eps rho D pRef : Real) : Real :=
  2 * B * eps / (rho * D * pRef)

set_option maxHeartbeats 800000 in
/-- Paper-form sampler composition.  The explicit dark-fraction premise is
the one-label small-denominator estimate averaged over labels; the conclusion
is exactly `zeta + c_samp/zeta + delta`. -/
theorem samplerTVToRandomLabelRelative_relativeAccuracy
    {Omega chi : Type*} [MeasurableSpace Omega] [Fintype chi]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (labels : Finset chi) (hlabels : labels.Nonempty)
    (p q : Omega → chi → Real)
    (hp : ∀ x, Measurable fun omega ↦ p omega x)
    (hq : ∀ x, Measurable fun omega ↦ q omega x)
    {eps zeta rho pRef B delta : Real}
    (heps : 0 < eps) (hzeta : 0 < zeta) (hrho : 0 < rho)
    (hpRef : 0 < pRef)
    (htv : ∀ omega, finiteDiscreteTotalVariation (p omega) (q omega) ≤ eps)
    (hdark : (∫ omega, samplerDarkFraction
      (fun omega (x : ↑labels) ↦ p omega x)
      (2 * eps / (zeta * labels.card)) rho omega ∂mu) ≤
        B * ((2 * eps / (zeta * labels.card)) / (rho * pRef)) + delta) :
    (∫ omega, samplerRelativeFailureFraction
      (fun omega (x : ↑labels) ↦ p omega x)
      (fun omega (x : ↑labels) ↦ q omega x) rho omega ∂mu) ≤
      min 1 (zeta + samplerRelativeConstant B eps rho labels.card pRef / zeta +
        delta) := by
  have hbase := samplerTVToRandomLabelRelative mu labels hlabels p q hp hq
    heps hzeta hrho htv hdark
  convert hbase using 1
  unfold samplerRelativeConstant
  field_simp
  ring_nf

set_option maxHeartbeats 800000 in
/-- Paper form of the sampler composition from eventwise TV on an arbitrary
ambient output type. -/
theorem samplerTVToRandomLabelRelative_eventwise_relativeAccuracy
    {Omega chi : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (labels : Finset chi) (hlabels : labels.Nonempty)
    (p q : Omega → chi → Real)
    (hp : ∀ x, Measurable fun omega ↦ p omega x)
    (hq : ∀ x, Measurable fun omega ↦ q omega x)
    {eps zeta rho pRef B delta : Real}
    (heps : 0 < eps) (hzeta : 0 < zeta) (hrho : 0 < rho)
    (hpRef : 0 < pRef)
    (htv : ∀ omega, finiteEventTotalVariationLE (p omega) (q omega) eps)
    (hdark : (∫ omega, samplerDarkFraction
      (fun omega (x : ↑labels) ↦ p omega x)
      (2 * eps / (zeta * labels.card)) rho omega ∂mu) ≤
        B * ((2 * eps / (zeta * labels.card)) / (rho * pRef)) + delta) :
    (∫ omega, samplerRelativeFailureFraction
      (fun omega (x : ↑labels) ↦ p omega x)
      (fun omega (x : ↑labels) ↦ q omega x) rho omega ∂mu) ≤
      min 1 (zeta + samplerRelativeConstant B eps rho labels.card pRef / zeta +
        delta) := by
  have hbase := samplerTVToRandomLabelRelative_eventwise
    mu labels hlabels p q hp hq heps hzeta hrho htv hdark
  convert hbase using 1
  unfold samplerRelativeConstant
  field_simp
  ring_nf

/-! ## Sampler square-root optimization -/

/-- At the optimal square-root choice, `zeta + c/zeta` is exactly
`2 sqrt(c)`. -/
theorem samplerSqrtChoice_exact {c : Real} (hc : 0 < c) :
    Real.sqrt c + c / Real.sqrt c = 2 * Real.sqrt c := by
  have hsqrt : Real.sqrt c ≠ 0 := (Real.sqrt_pos.2 hc).ne'
  have hdiv : c / Real.sqrt c = Real.sqrt c :=
    (div_eq_iff hsqrt).2 (Real.mul_self_sqrt hc.le).symm
  rw [hdiv]
  ring

/-- Substitution of the optimal square-root choice in the capped sampler
failure budget. -/
theorem samplerRelativeOptimized
    {failure c delta : Real} (hc : 0 < c)
    (hfailure : failure <=
      min 1 (Real.sqrt c + c / Real.sqrt c + delta)) :
    failure <= min 1 (2 * Real.sqrt c + delta) := by
  rw [samplerSqrtChoice_exact hc] at hfailure
  exact hfailure

/-! ## Bounded expectation transfer and truncated negative moments -/

/-- Probability total variation controls expectations of measurable
statistics taking values in `[0,C]`, with loss `C * delta`. -/
theorem boundedExpectationTransfer
    {alpha : Type*} [MeasurableSpace alpha]
    (mu nu : Measure alpha) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {delta C : Real}
    (htv : probabilityTotalVariationLE mu nu delta)
    (phi : alpha -> Real) (hphi : Measurable phi)
    (hphi_nonneg : ∀ x, 0 <= phi x)
    (hphi_le : ∀ x, phi x <= C) (hC : 0 <= C) :
    abs ((∫ x, phi x ∂mu) - ∫ x, phi x ∂nu) <= C * delta := by
  have hphi_int_mu : Integrable phi mu := by
    apply (integrable_const C).mono hphi.aestronglyMeasurable
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hphi_nonneg x), Real.norm_eq_abs,
      abs_of_nonneg hC]
    exact hphi_le x
  have hphi_int_nu : Integrable phi nu := by
    apply (integrable_const C).mono hphi.aestronglyMeasurable
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hphi_nonneg x), Real.norm_eq_abs,
      abs_of_nonneg hC]
    exact hphi_le x
  have htail_meas (xi : Measure alpha) : Measurable fun t : Real =>
      xi.real {x : alpha | t <= phi x} := by
    apply Measurable.ennreal_toReal
    exact Antitone.measurable fun _ _ hst =>
      measure_mono (fun _ hx => hst.trans hx)
  have htail_int (xi : Measure alpha) [IsProbabilityMeasure xi] :
      Integrable (fun t : Real => xi.real {x : alpha | t <= phi x})
        (volume.restrict (Set.Ioc (0 : Real) C)) := by
    apply (integrable_const (1 : Real)).mono
      (htail_meas xi).aestronglyMeasurable.restrict
    filter_upwards [] with t
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg, norm_one]
    exact measureReal_le_one
  have hmu_layer : (∫ x, phi x ∂mu) =
      ∫ t in Set.Ioc (0 : Real) C, mu.real {x : alpha | t <= phi x} :=
    hphi_int_mu.integral_eq_integral_Ioc_meas_le
      (Filter.Eventually.of_forall hphi_nonneg)
      (Filter.Eventually.of_forall hphi_le)
  have hnu_layer : (∫ x, phi x ∂nu) =
      ∫ t in Set.Ioc (0 : Real) C, nu.real {x : alpha | t <= phi x} :=
    hphi_int_nu.integral_eq_integral_Ioc_meas_le
      (Filter.Eventually.of_forall hphi_nonneg)
      (Filter.Eventually.of_forall hphi_le)
  have hdiff_int : Integrable (fun t : Real =>
      mu.real {x : alpha | t <= phi x} - nu.real {x : alpha | t <= phi x})
      (volume.restrict (Set.Ioc (0 : Real) C)) :=
    (htail_int mu).sub (htail_int nu)
  have habs_int : Integrable (fun t : Real =>
      abs (mu.real {x : alpha | t <= phi x} -
        nu.real {x : alpha | t <= phi x}))
      (volume.restrict (Set.Ioc (0 : Real) C)) := hdiff_int.abs
  have hpoint : ∀ t : Real,
      abs (mu.real {x : alpha | t <= phi x} -
        nu.real {x : alpha | t <= phi x}) <= delta := by
    intro t
    exact htv.2 _ (measurableSet_le measurable_const hphi)
  rw [hmu_layer, hnu_layer, <- integral_sub (htail_int mu) (htail_int nu)]
  calc
    abs (∫ t in Set.Ioc (0 : Real) C,
        mu.real {x : alpha | t <= phi x} -
          nu.real {x : alpha | t <= phi x}) <=
        ∫ t in Set.Ioc (0 : Real) C,
          abs (mu.real {x : alpha | t <= phi x} -
            nu.real {x : alpha | t <= phi x}) :=
      abs_integral_le_integral_abs
    _ <= ∫ _t in Set.Ioc (0 : Real) C, delta := by
      apply integral_mono_ae habs_int (integrable_const delta)
      filter_upwards [] with t
      exact hpoint t
    _ = C * delta := by simp [hC]

/-- The observable used in the finite-Haar truncated inverse-moment bound. -/
def truncatedNegativePower (Z : alpha -> Real) (lambda a : Real) : alpha -> Real :=
  fun x => (max (Z x) lambda) ^ (-a)

/-- A positive truncation makes the negative power measurable and bounded by
`lambda^(-a)`. -/
theorem truncatedNegativePower_measurable_bounded
    {alpha : Type*} [MeasurableSpace alpha]
    (Z : alpha -> Real) (hZ : Measurable Z)
    {lambda a : Real} (hlambda : 0 < lambda) (ha : 0 <= a) :
    Measurable (truncatedNegativePower Z lambda a) /\
      (∀ x, 0 <= truncatedNegativePower Z lambda a x) /\
      (∀ x, truncatedNegativePower Z lambda a x <= lambda ^ (-a)) := by
  have hbase_cont : Continuous fun y : Real => (max y lambda) ^ (-a) :=
    (continuous_id.max continuous_const).rpow_const fun y =>
      Or.inl (ne_of_gt (hlambda.trans_le (le_max_right y lambda)))
  refine ⟨hbase_cont.measurable.comp hZ, ?_, ?_⟩
  · intro x
    exact Real.rpow_nonneg
      (hlambda.le.trans (le_max_right (Z x) lambda)) _
  · intro x
    exact Real.rpow_le_rpow_of_nonpos hlambda
      (le_max_right (Z x) lambda) (neg_nonpos.mpr ha)

/-- Convert an untruncated `lintegral` inverse-moment estimate into the
bounded Bochner integral needed for the finite-Haar TV transfer. -/
theorem truncatedNegativeMoment_le_of_lintegral
    {alpha : Type*} [MeasurableSpace alpha]
    (mu : Measure alpha) [IsProbabilityMeasure mu]
    (Z : alpha → Real) (hZ : Measurable Z)
    {lambda a C : Real} (hlambda : 0 < lambda) (ha : 0 ≤ a)
    (hZpos : ∀ᵐ x ∂mu, 0 < Z x) (hC : 0 ≤ C)
    (hmoment : (∫⁻ x, ENNReal.ofReal ((Z x)⁻¹ ^ a) ∂mu) ≤
      ENNReal.ofReal C) :
    (∫ x, truncatedNegativePower Z lambda a x ∂mu) ≤ C := by
  obtain ⟨hmeas, hnonneg, hbounded⟩ :=
    truncatedNegativePower_measurable_bounded Z hZ hlambda ha
  have hint : Integrable (truncatedNegativePower Z lambda a) mu := by
    apply (integrable_const (lambda ^ (-a))).mono hmeas.aestronglyMeasurable
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg x), Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hlambda.le _)]
    exact hbounded x
  apply (ENNReal.ofReal_le_ofReal_iff hC).1
  rw [ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall hnonneg)]
  calc
    (∫⁻ x, ENNReal.ofReal (truncatedNegativePower Z lambda a x) ∂mu) ≤
        ∫⁻ x, ENNReal.ofReal ((Z x)⁻¹ ^ a) ∂mu := by
      apply lintegral_mono_ae
      filter_upwards [hZpos] with x hx
      apply ENNReal.ofReal_le_ofReal
      unfold truncatedNegativePower
      rw [Real.rpow_neg_eq_inv_rpow]
      have hmax : 0 < max (Z x) lambda :=
        hlambda.trans_le (le_max_right (Z x) lambda)
      exact Real.rpow_le_rpow (inv_nonneg.mpr hmax.le)
        ((inv_le_inv₀ hmax hx).2 (le_max_left (Z x) lambda)) ha
    _ ≤ ENNReal.ofReal C := hmoment

/-- Normalized shifted intensity as a function of the hafnian amplitude law. -/
def normalizedShiftedIntensityFromAmplitude
    (K n : Nat) (z : Complex) (w : Complex) : Real :=
  (‖w - z‖ / LogdetLean.GramHafnian.gramHafnianSigma K n) ^ 2

@[fun_prop]
theorem measurable_normalizedShiftedIntensityFromAmplitude
    (K n : Nat) (z : Complex) :
    Measurable (normalizedShiftedIntensityFromAmplitude K n z) := by
  unfold normalizedShiftedIntensityFromAmplitude
  fun_prop

/-- AC2, transported to the Gaussian hafnian amplitude law, supplies the
exact bounded Gaussian premise needed by the finite-Haar TV theorem. -/
theorem gaussianTruncatedNormalizedIntensityNegativeMoment
    (n K : Nat) (hn : 1 ≤ n) (hK : 4 * n ≤ K) (z : Complex)
    {lambda a : Real} (hlambda : 0 < lambda) (ha : 0 < a) (ha1 : a < 1) :
    (∫ w, truncatedNegativePower
      (normalizedShiftedIntensityFromAmplitude K n z) lambda a w
      ∂(gaussianGramHafnianLaw n K)) ≤
        shiftedAnticoncentrationConstant K n ^ a / (1 - a) := by
  let q : ComplexColumnMatrix n K → Real :=
    GaussianAnticoncentration.normalizedShiftedIntensityObservable K n z
  have hC : 0 ≤ shiftedAnticoncentrationConstant K n ^ a / (1 - a) := by
    exact div_nonneg (Real.rpow_nonneg
      (GaussianAnticoncentration.shiftedAnticoncentrationConstant_pos
        n K hn hK).le a) (by linarith)
  have hsource :
      (∫ X, truncatedNegativePower q lambda a X
        ∂(circularGaussianColumnMatrixMeasure n K)) ≤
          shiftedAnticoncentrationConstant K n ^ a / (1 - a) := by
    apply truncatedNegativeMoment_le_of_lintegral
      (circularGaussianColumnMatrixMeasure n K) q
      (GaussianAnticoncentration.measurable_normalizedShiftedIntensityObservable
        K n z)
      hlambda ha.le
      (GaussianAnticoncentration.ae_normalizedShiftedIntensity_pos n K hn hK z)
      hC
    exact GaussianAnticoncentration.normalizedShiftedIntensity_negativeMoment
      n K hn hK z ha ha1
  rw [gaussianGramHafnianLaw_eq_literal]
  have htargetMeas := (truncatedNegativePower_measurable_bounded
    (normalizedShiftedIntensityFromAmplitude K n z)
    (measurable_normalizedShiftedIntensityFromAmplitude K n z)
    hlambda ha.le).1
  rw [integral_map_of_stronglyMeasurable
    (measurable_gramHafnianObservable n K) htargetMeas.stronglyMeasurable]
  convert hsource using 1
  unfold q normalizedShiftedIntensityFromAmplitude
    GaussianAnticoncentration.normalizedShiftedIntensityObservable
    LogdetLean.GramHafnian.gramHafnianObservable
  rfl

/-- Finite-Haar truncated negative moment: TV costs at most
`delta * lambda^(-a)` because the truncated observable is bounded.  This
statement contains no Gaussian theorem; the latter is the premise
`hgaussian` supplied by AC2. -/
theorem finiteHaarTruncatedNegativeMoment
    {alpha : Type*} [MeasurableSpace alpha]
    (haar gaussian : Measure alpha)
    [IsProbabilityMeasure haar] [IsProbabilityMeasure gaussian]
    {delta B lambda a : Real}
    (htv : probabilityTotalVariationLE haar gaussian delta)
    (Z : alpha -> Real) (hZ : Measurable Z)
    (hlambda : 0 < lambda) (ha0 : 0 <= a) (ha1 : a < 1)
    (hgaussian : (∫ x, truncatedNegativePower Z lambda a x ∂gaussian) <=
      B ^ a / (1 - a)) :
    (∫ x, truncatedNegativePower Z lambda a x ∂haar) <=
      B ^ a / (1 - a) + delta * lambda ^ (-a) := by
  obtain ⟨hmeas, hnonneg, hbounded⟩ :=
    truncatedNegativePower_measurable_bounded Z hZ hlambda ha0
  have hC : 0 <= lambda ^ (-a) :=
    Real.rpow_nonneg hlambda.le _
  have htransfer := boundedExpectationTransfer haar gaussian htv
    (truncatedNegativePower Z lambda a) hmeas hnonneg hbounded hC
  have hone :
      (∫ x, truncatedNegativePower Z lambda a x ∂haar) -
          (∫ x, truncatedNegativePower Z lambda a x ∂gaussian) <=
        lambda ^ (-a) * delta :=
    (le_abs_self _).trans htransfer
  have haDenom : 0 < 1 - a := sub_pos.mpr ha1
  nlinarith

/-- Literal finite-Haar truncated negative-moment display in the Letter.
The Gaussian term is discharged by AC2; the only additional term is the
certified hiding remainder times `lambda^(-a)`. -/
theorem finiteHaarTruncatedNormalizedIntensityNegativeMoment
    (H : UnitaryHaarProbabilityFamily)
    {M n K : Nat} (hn : 1 ≤ n) (hK : 4 * n ≤ K) (hKM : K ≤ M)
    (z : Complex) {lambda a : Real}
    (hlambda : 0 < lambda) (ha : 0 < a) (ha1 : a < 1) :
    (∫ w, truncatedNegativePower
      (normalizedShiftedIntensityFromAmplitude K n z) lambda a w
      ∂(scaledHaarGramHafnianLaw H M n K)) ≤
        shiftedAnticoncentrationConstant K n ^ a / (1 - a) +
          UniformMatrixHiding.hidingRemainder M (2 * n) * lambda ^ (-a) := by
  have hNM : 2 * n ≤ M := by omega
  have hNK : 2 * n ≤ K := by omega
  have hNpos : 1 ≤ 2 * n := by omega
  haveI : IsProbabilityMeasure (scaledHaarGramHafnianLaw H M n K) :=
    scaledHaarGramHafnianLaw_isProbability H hNM hKM
  haveI : IsProbabilityMeasure (gaussianGramHafnianLaw n K) := by
    rw [gaussianGramHafnianLaw_eq_literal]
    exact Measure.isProbabilityMeasure_map
      (measurable_gramHafnianObservable n K).aemeasurable
  have htvMatrix := UniformMatrixHiding.matrixLaw.apply H hNpos hNK hKM
  have htvHafnian := htvMatrix.map (measurable_hafnianMatrixObservable n)
  have htv : probabilityTotalVariationLE
      (scaledHaarGramHafnianLaw H M n K)
      (gaussianGramHafnianLaw n K)
      (UniformMatrixHiding.hidingRemainder M (2 * n)) := by
    simpa [scaledHaarGramHafnianLaw, gaussianGramHafnianLaw,
      UniformMatrixHiding.hidingRemainder] using htvHafnian
  exact finiteHaarTruncatedNegativeMoment
    (scaledHaarGramHafnianLaw H M n K) (gaussianGramHafnianLaw n K)
    htv (normalizedShiftedIntensityFromAmplitude K n z)
    (measurable_normalizedShiftedIntensityFromAmplitude K n z)
    hlambda ha.le ha1
    (gaussianTruncatedNormalizedIntensityNegativeMoment
      n K hn hK z hlambda ha ha1)

/-! ## Finite panels -/

/-- For a finite iid family, the probability that at least one coordinate
falls in a measurable bad set is exactly the product-complement formula.
This is the pure probability identity used by the disjoint-panel refinement. -/
theorem iidFiniteUnionProbability
    {Omega beta : Type*} [MeasurableSpace Omega] [MeasurableSpace beta]
    (mu : Measure Omega) [IsProbabilityMeasure mu] {q : Nat}
    (X : Fin q → Omega → beta) (hXmeas : ∀ j, Measurable (X j))
    (hIndep : iIndepFun X mu)
    (P : Measure beta) [IsProbabilityMeasure P]
    (hLaw : ∀ j, Measure.map (X j) mu = P)
    (bad : Set beta) (hbad : MeasurableSet bad) :
    mu.real {omega | ∃ j, X j omega ∈ bad} =
      1 - (1 - P.real bad) ^ q := by
  have hcompMeas (j : Fin q) :
      MeasurableSet ((X j) ⁻¹' badᶜ) :=
    (hXmeas j) hbad.compl
  have hinterMeas :
      MeasurableSet (⋂ j, (X j) ⁻¹' badᶜ) :=
    MeasurableSet.iInter hcompMeas
  have hinterENN :
      mu (⋂ j, (X j) ⁻¹' badᶜ) =
        ∏ j, mu ((X j) ⁻¹' badᶜ) := by
    simpa using (hIndep.measure_inter_preimage_eq_mul Finset.univ
      (sets := fun _ ↦ badᶜ) (fun _ _ ↦ hbad.compl))
  have hinterReal :
      mu.real (⋂ j, (X j) ⁻¹' badᶜ) =
        ∏ j, mu.real ((X j) ⁻¹' badᶜ) := by
    rw [measureReal_def, hinterENN]
    simp only [ENNReal.toReal_prod, measureReal_def]
  have hsingle (j : Fin q) :
      mu.real ((X j) ⁻¹' badᶜ) = 1 - P.real bad := by
    rw [Set.preimage_compl, measureReal_compl]
    · rw [probReal_univ]
      congr 1
      rw [← map_measureReal_apply (hXmeas j) hbad, hLaw j]
    · exact (hXmeas j) hbad
  have hunion :
      {omega | ∃ j, X j omega ∈ bad} =
        (⋂ j, (X j) ⁻¹' badᶜ)ᶜ := by
    ext omega
    simp
  rw [hunion, measureReal_compl hinterMeas, probReal_univ, hinterReal]
  simp_rw [hsingle]
  simp

/-- Hafnian amplitude obtained from one ordered Gaussian row block. -/
def disjointGaussianBlockAmplitude
    {q n L K : Nat} (rows : Fin q → (Fin (2 * n) ↪ Fin L))
    (j : Fin q) (G : Matrix (Fin L) (Fin K) Complex) : Complex :=
  hafnianMatrixObservable n
    (rectangularTransposeGram
      (DisjointGaussianRows.orderedRowBlock (K := K) (rows j) G))

@[fun_prop]
theorem measurable_disjointGaussianBlockAmplitude
    {q n L K : Nat} (rows : Fin q → (Fin (2 * n) ↪ Fin L))
    (j : Fin q) :
    Measurable (disjointGaussianBlockAmplitude
      (n := n) (L := L) (K := K) rows j) := by
  unfold disjointGaussianBlockAmplitude
  exact (measurable_hafnianMatrixObservable n).comp
    ((measurable_rectangularTransposeGram (2 * n) K).comp
    (DisjointGaussianRows.measurable_orderedRowBlock (K := K) (rows j))
    )

/-- Pairwise-disjoint Gaussian row blocks have mutually independent hafnian
amplitudes.  This is a concrete Gaussian statement, not an independence claim
about finite-Haar outputs. -/
theorem iIndepFun_disjointGaussianBlockAmplitude
    {q n L K : Nat} (rows : Fin q → (Fin (2 * n) ↪ Fin L))
    (hrows : Pairwise fun a b =>
      Disjoint (DisjointGaussianRows.rowRange (rows a))
        (DisjointGaussianRows.rowRange (rows b))) :
    iIndepFun (disjointGaussianBlockAmplitude rows)
      (standardComplexGaussianRectangularMeasure L K) := by
  change iIndepFun
    (fun j G => hafnianMatrixObservable n
      (rectangularTransposeGram
        (DisjointGaussianRows.orderedRowBlock (K := K) (rows j) G)))
    (standardComplexGaussianRectangularMeasure L K)
  simpa [Function.comp_def] using
    ((DisjointGaussianRows.iIndepFun_orderedRowBlocks
      (K := K) rows hrows).comp
        (fun _ => hafnianMatrixObservable n ∘ rectangularTransposeGram)
        (fun _ => (measurable_hafnianMatrixObservable n).comp
          (measurable_rectangularTransposeGram (2 * n) K)))

/-- Every ordered block hafnian has the canonical Gaussian Gram-hafnian law. -/
theorem map_disjointGaussianBlockAmplitude
    {q n L K : Nat} (rows : Fin q → (Fin (2 * n) ↪ Fin L))
    (j : Fin q) :
    Measure.map (disjointGaussianBlockAmplitude rows j)
        (standardComplexGaussianRectangularMeasure L K) =
      gaussianGramHafnianLaw n K := by
  rw [show disjointGaussianBlockAmplitude rows j =
      (hafnianMatrixObservable n ∘ rectangularTransposeGram) ∘
        DisjointGaussianRows.orderedRowBlock (K := K) (rows j) by rfl]
  rw [← Measure.map_map
    ((measurable_hafnianMatrixObservable n).comp
      (measurable_rectangularTransposeGram (2 * n) K))
    (DisjointGaussianRows.measurable_orderedRowBlock
      (K := K) (rows j))]
  rw [DisjointGaussianRows.map_orderedRowBlock]
  unfold gaussianGramHafnianLaw gaussianTransposeGramLaw
  rw [Measure.map_map (measurable_hafnianMatrixObservable n)
    (measurable_rectangularTransposeGram (2 * n) K)]

/-- Exact Gaussian product-complement formula for a disjoint panel of
shifted hafnian disks. -/
theorem disjointGaussianPanelSmallBall_exact
    {q n L K : Nat} (rows : Fin q → (Fin (2 * n) ↪ Fin L))
    (hrows : Pairwise fun a b =>
      Disjoint (DisjointGaussianRows.rowRange (rows a))
        (DisjointGaussianRows.rowRange (rows b)))
    (z : Complex) (eps : Real) :
    (standardComplexGaussianRectangularMeasure L K).real
        {G | ∃ j, disjointGaussianBlockAmplitude rows j G ∈
          shiftedComplexDisk z (eps * gramHafnianSigma K n)} =
      1 - (1 - gramHafnianShiftedSmallBallProbability K n z eps) ^ q := by
  letI : IsProbabilityMeasure (gaussianGramHafnianLaw n K) := by
    unfold gaussianGramHafnianLaw
    exact Measure.isProbabilityMeasure_map
      (measurable_hafnianMatrixObservable n).aemeasurable
  have hproduct := iidFiniteUnionProbability
    (standardComplexGaussianRectangularMeasure L K)
    (disjointGaussianBlockAmplitude rows)
    (measurable_disjointGaussianBlockAmplitude rows)
    (iIndepFun_disjointGaussianBlockAmplitude rows hrows)
    (gaussianGramHafnianLaw n K)
    (map_disjointGaussianBlockAmplitude rows)
    (shiftedComplexDisk z (eps * gramHafnianSigma K n))
    (measurableSet_shiftedComplexDisk z (eps * gramHafnianSigma K n))
  rw [gaussianGramHafnianLaw_shiftedDisk_eq] at hproduct
  exact hproduct

/-- The paper's sharp Gaussian disjoint-panel term: for normalized intensity
threshold `t`, the union probability is at most `1 - (1-a_t)^q`, where
`a_t = min 1 (B*t)`. -/
theorem disjointGaussianPanelSmallBall_le
    {q n L K : Nat} (rows : Fin q → (Fin (2 * n) ↪ Fin L))
    (hrows : Pairwise fun a b =>
      Disjoint (DisjointGaussianRows.rowRange (rows a))
        (DisjointGaussianRows.rowRange (rows b)))
    (hn : 1 ≤ n) (hK : 4 * n ≤ K) {t : Real} (ht : 0 ≤ t) :
    (standardComplexGaussianRectangularMeasure L K).real
        {G | ∃ j, disjointGaussianBlockAmplitude rows j G ∈
          shiftedComplexDisk 0 (Real.sqrt t * gramHafnianSigma K n)} ≤
      1 - (1 - min 1 (shiftedAnticoncentrationConstant K n * t)) ^ q := by
  rw [disjointGaussianPanelSmallBall_exact rows hrows]
  have hp := GaussianAnticoncentration.shiftedSmallBall
    n K hn hK 0 (Real.sqrt t) (Real.sqrt_nonneg t)
  have hp' : gramHafnianShiftedSmallBallProbability K n 0 (Real.sqrt t) ≤
      min 1 (shiftedAnticoncentrationConstant K n * t) := by
    simpa [Real.sq_sqrt ht] using hp
  have haNonneg : 0 ≤ 1 - min 1
      (shiftedAnticoncentrationConstant K n * t) := by
    have hmin : min 1 (shiftedAnticoncentrationConstant K n * t) ≤ 1 :=
      min_le_left _ _
    linarith
  have hpow :
      (1 - min 1 (shiftedAnticoncentrationConstant K n * t)) ^ q ≤
        (1 - gramHafnianShiftedSmallBallProbability K n 0
          (Real.sqrt t)) ^ q := by
    apply pow_le_pow_left₀ haNonneg
    linarith
  linarith

/-- Measurability of the finite disjoint-panel union event. -/
theorem measurableSet_disjointGaussianPanelSmallBall
    {q n L K : Nat} (rows : Fin q → (Fin (2 * n) ↪ Fin L))
    (z : Complex) (eps : Real) :
    MeasurableSet
      {G | ∃ j, disjointGaussianBlockAmplitude
        (n := n) (L := L) (K := K) rows j G ∈
        shiftedComplexDisk z (eps * gramHafnianSigma K n)} := by
  rw [show {G | ∃ j, disjointGaussianBlockAmplitude
      (n := n) (L := L) (K := K) rows j G ∈
        shiftedComplexDisk z (eps * gramHafnianSigma K n)} =
      ⋃ j, (disjointGaussianBlockAmplitude
        (n := n) (L := L) (K := K) rows j) ⁻¹'
          shiftedComplexDisk z (eps * gramHafnianSigma K n) by
    ext G
    simp]
  apply MeasurableSet.iUnion
  intro j
  exact (measurable_disjointGaussianBlockAmplitude rows j)
    (measurableSet_shiftedComplexDisk z (eps * gramHafnianSigma K n))

/-- A total-variation comparison with the concrete iid Gaussian row source
immediately transfers the sharp disjoint-panel Gaussian bound. -/
theorem disjointGaussianPanelSmallBall_transfer
    {q n L K : Nat}
    (haar : Measure (Matrix (Fin L) (Fin K) Complex)) {delta : Real}
    (htv : probabilityTotalVariationLE haar
      (standardComplexGaussianRectangularMeasure L K) delta)
    (rows : Fin q → (Fin (2 * n) ↪ Fin L))
    (hrows : Pairwise fun a b =>
      Disjoint (DisjointGaussianRows.rowRange (rows a))
        (DisjointGaussianRows.rowRange (rows b)))
    (hn : 1 ≤ n) (hK : 4 * n ≤ K) {t : Real} (ht : 0 ≤ t) :
    haar.real
        {G | ∃ j, disjointGaussianBlockAmplitude
          (n := n) (L := L) (K := K) rows j G ∈
          shiftedComplexDisk 0 (Real.sqrt t * gramHafnianSigma K n)} ≤
      1 - (1 - min 1 (shiftedAnticoncentrationConstant K n * t)) ^ q +
        delta := by
  have htransfer := htv.event_le
    (measurableSet_disjointGaussianPanelSmallBall
      (n := n) (L := L) (K := K) rows 0 (Real.sqrt t))
  exact htransfer.trans (add_le_add
    (disjointGaussianPanelSmallBall_le rows hrows hn hK ht) le_rfl)

/-- Hafnian of a normalized Gram matrix after restoring the raw Gaussian
scale.  This is the observable needed to connect normalized hiding with the
manuscript amplitude normalization. -/
def denormalizedHafnianObservable (n K : Nat)
    (A : Matrix (Fin (2 * n)) (Fin (2 * n)) Complex) : Complex :=
  hafnianMatrixObservable n (denormalizeTransposeGram (2 * n) K A)

@[fun_prop]
theorem measurable_denormalizedHafnianObservable (n K : Nat) :
    Measurable (denormalizedHafnianObservable n K) := by
  unfold denormalizedHafnianObservable
  exact (measurable_hafnianMatrixObservable n).comp
    (measurable_denormalizeTransposeGram (2 * n) K)

/-- Restoring the normalization under the normalized Gaussian Gram law gives
exactly the canonical raw Gaussian Gram-hafnian law. -/
theorem map_denormalizedHafnianObservable_normalizedGaussian
    (n K : Nat) (hK : 1 ≤ K) :
    Measure.map (denormalizedHafnianObservable n K)
        (normalizedGaussianTransposeGramLaw (2 * n) K) =
      gaussianGramHafnianLaw n K := by
  unfold normalizedGaussianTransposeGramLaw gaussianGramHafnianLaw
    gaussianTransposeGramLaw
  rw [Measure.map_map (measurable_denormalizedHafnianObservable n K)
    (measurable_normalizeTransposeGram (2 * n) K)]
  rw [Measure.map_map
    ((measurable_denormalizedHafnianObservable n K).comp
      (measurable_normalizeTransposeGram (2 * n) K))
    (measurable_rectangularTransposeGram (2 * n) K)]
  rw [Measure.map_map (measurable_hafnianMatrixObservable n)
    (measurable_rectangularTransposeGram (2 * n) K)]
  apply Measure.map_congr
  apply ae_of_all
  intro G
  simp only [Function.comp_apply, denormalizedHafnianObservable]
  rw [denormalize_normalizeTransposeGram (2 * n) hK]

/-- Coordinatewise denormalized hafnians of a finite normalized-Gram panel. -/
def denormalizedHafnianPanel (q n K : Nat) :
    (Fin q → Matrix (Fin (2 * n)) (Fin (2 * n)) Complex) →
      (Fin q → Complex) :=
  fun A j => denormalizedHafnianObservable n K (A j)

@[fun_prop]
theorem measurable_denormalizedHafnianPanel (q n K : Nat) :
    Measurable (denormalizedHafnianPanel q n K) := by
  unfold denormalizedHafnianPanel
  apply measurable_pi_lambda
  intro j
  exact (measurable_denormalizedHafnianObservable n K).comp
    (measurable_pi_apply j)

/-- A finite product panel has the exact union product-complement formula. -/
theorem iidProductFiniteUnionProbability
    {beta : Type*} [MeasurableSpace beta]
    (P : Measure beta) [IsProbabilityMeasure P] (q : Nat)
    (bad : Set beta) (hbad : MeasurableSet bad) :
    (Measure.pi (fun _ : Fin q => P)).real
        {x | ∃ j, x j ∈ bad} =
      1 - (1 - P.real bad) ^ q := by
  let mu := Measure.pi (fun _ : Fin q => P)
  let X : Fin q → (Fin q → beta) → beta := fun j x => x j
  letI : IsProbabilityMeasure mu := by
    dsimp [mu]
    infer_instance
  have hIndep : iIndepFun X mu := by
    dsimp [X, mu]
    exact iIndepFun_pi (μ := fun _ : Fin q => P)
      (X := fun _ => id) (fun _ => aemeasurable_id)
  have hLaw : ∀ j, Measure.map (X j) mu = P := by
    intro j
    exact (measurePreserving_eval (fun _ : Fin q => P) j).map_eq
  exact iidFiniteUnionProbability mu X (fun _ => measurable_pi_apply _)
    hIndep P hLaw bad hbad

/-- The sharp small-ball union bound for a product of `q` canonical Gaussian
Gram-hafnian amplitudes. -/
theorem gaussianHafnianProductPanelSmallBall_le
    {q n K : Nat} (hn : 1 ≤ n) (hK : 4 * n ≤ K)
    {t : Real} (ht : 0 ≤ t) :
    (Measure.pi (fun _ : Fin q => gaussianGramHafnianLaw n K)).real
        {w | ∃ j, w j ∈ shiftedComplexDisk 0
          (Real.sqrt t * gramHafnianSigma K n)} ≤
      1 - (1 - min 1 (shiftedAnticoncentrationConstant K n * t)) ^ q := by
  letI : IsProbabilityMeasure (gaussianGramHafnianLaw n K) := by
    unfold gaussianGramHafnianLaw
    exact Measure.isProbabilityMeasure_map
      (measurable_hafnianMatrixObservable n).aemeasurable
  rw [iidProductFiniteUnionProbability
    (gaussianGramHafnianLaw n K) q
    (shiftedComplexDisk 0 (Real.sqrt t * gramHafnianSigma K n))
    (measurableSet_shiftedComplexDisk 0
      (Real.sqrt t * gramHafnianSigma K n))]
  rw [gaussianGramHafnianLaw_shiftedDisk_eq]
  have hp := GaussianAnticoncentration.shiftedSmallBall
    n K hn hK 0 (Real.sqrt t) (Real.sqrt_nonneg t)
  have hp' : gramHafnianShiftedSmallBallProbability K n 0 (Real.sqrt t) ≤
      min 1 (shiftedAnticoncentrationConstant K n * t) := by
    simpa [Real.sq_sqrt ht] using hp
  have haNonneg : 0 ≤ 1 - min 1
      (shiftedAnticoncentrationConstant K n * t) := by
    linarith [min_le_left (1 : Real)
      (shiftedAnticoncentrationConstant K n * t)]
  have hpow :
      (1 - min 1 (shiftedAnticoncentrationConstant K n * t)) ^ q ≤
        (1 - gramHafnianShiftedSmallBallProbability K n 0
          (Real.sqrt t)) ^ q := by
    apply pow_le_pow_left₀ haNonneg
    linarith
  linarith

/-- Promote an ordered row embedding inside the common union block to the
corresponding embedding into the ambient Haar unitary. -/
def ambientOrderedRows {N L M : Nat} (hLM : L ≤ M)
    (rows : Fin N ↪ Fin L) : Fin N ↪ Fin M where
  toFun i := Fin.castLE hLM (rows i)
  inj' := Fin.castLE_injective hLM |>.comp rows.injective

/-- The physical ordered panel written directly on the ambient Haar unitary.
This representation is useful for the separate one-pattern union route. -/
def ambientHaarHafnianPanel
    (M K q n L : Nat) (hLM : L ≤ M) (hKM : K ≤ M)
    (rows : Fin q → (Fin (2 * n) ↪ Fin L))
    (U : Matrix.unitaryGroup (Fin M) Complex) : Fin q → Complex :=
  fun j ↦ hafnianMatrixObservable n
    (LocalAnticoncentration.scaledRectangularTransposeGram M (2 * n) K
      (LocalAnticoncentration.selectedRowsUnitaryBlock hKM
        (ambientOrderedRows hLM (rows j)) U))

@[fun_prop]
theorem measurable_ambientHaarHafnianPanel
    (M K q n L : Nat) (hLM : L ≤ M) (hKM : K ≤ M)
    (rows : Fin q → (Fin (2 * n) ↪ Fin L)) :
    Measurable (ambientHaarHafnianPanel M K q n L hLM hKM rows) := by
  unfold ambientHaarHafnianPanel
  apply measurable_pi_lambda
  intro j
  exact (measurable_hafnianMatrixObservable n).comp
    ((LocalAnticoncentration.measurable_scaledRectangularTransposeGram M (2 * n) K).comp
      (LocalAnticoncentration.measurable_selectedRowsUnitaryBlock hKM
        (ambientOrderedRows hLM (rows j))))

/-- The denormalized ordered-pattern construction used by joint hiding is
exactly the direct physical selected-row hafnian panel on the ambient Haar
unitary.  This is a representation theorem, not an additional input. -/
theorem orderedHaarHafnianPanelLaw_eq_ambient
    (H : UnitaryHaarProbabilityFamily)
    (M L K q n : Nat) (hLM : L ≤ M) (hKM : K ≤ M)
    (hKpos : 1 ≤ K)
    (rows : Fin q → (Fin (2 * n) ↪ Fin L)) :
    Measure.map (denormalizedHafnianPanel q n K)
        (UniformMatrixHiding.orderedPatternPanelHaarLaw
          H M L K q (2 * n) rows) =
      Measure.map (ambientHaarHafnianPanel M K q n L hLM hKM rows)
        (H.law M) := by
  unfold UniformMatrixHiding.orderedPatternPanelHaarLaw
    normalizedHaarTransposeGramLaw scaledHaarTransposeGramLaw
  rw [dif_pos ⟨hLM, hKM⟩]
  rw [Measure.map_map (measurable_denormalizedHafnianPanel q n K)
    (UniformMatrixHiding.measurable_orderedPatternPanel rows)]
  rw [Measure.map_map
    ((measurable_denormalizedHafnianPanel q n K).comp
      (UniformMatrixHiding.measurable_orderedPatternPanel rows))
    (UniformMatrixHiding.measurable_preselectedPrincipalSubmatrixTuple
      q L (UniformMatrixHiding.orderedPatternSets rows))]
  rw [Measure.map_map
    (((measurable_denormalizedHafnianPanel q n K).comp
      (UniformMatrixHiding.measurable_orderedPatternPanel rows)).comp
        (UniformMatrixHiding.measurable_preselectedPrincipalSubmatrixTuple
          q L (UniformMatrixHiding.orderedPatternSets rows)))
    (measurable_normalizeTransposeGram L K)]
  rw [Measure.map_map
    ((((measurable_denormalizedHafnianPanel q n K).comp
      (UniformMatrixHiding.measurable_orderedPatternPanel rows)).comp
        (UniformMatrixHiding.measurable_preselectedPrincipalSubmatrixTuple
          q L (UniformMatrixHiding.orderedPatternSets rows))).comp
      (measurable_normalizeTransposeGram L K))
    (measurable_scaledHaarTransposeGramMatrix hLM hKM)]
  apply Measure.map_congr
  apply ae_of_all
  intro U
  ext j
  apply congrArg (hafnianMatrixObservable n)
  ext i k
  have hsqrt : Real.sqrt (K : Real) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast hKpos))
  simp [UniformMatrixHiding.orderedPatternPanel,
    UniformMatrixHiding.preselectedPrincipalSubmatrixTuple,
    UniformMatrixHiding.orderedPatternSets,
    ambientOrderedRows,
    denormalizeTransposeGram, normalizeTransposeGram,
    scaledHaarTransposeGramMatrix,
    LocalAnticoncentration.scaledRectangularTransposeGram,
    LocalAnticoncentration.selectedRowsUnitaryBlock,
    LocalAnticoncentration.topLeftUnitaryBlock,
    LocalAnticoncentration.rectangularTransposeGram, Matrix.mul_apply, hsqrt]

/-- Every coordinate of the ambient ordered Haar panel has the canonical
scaled Haar Gram-hafnian law.  This is the exact fixed-pattern row-symmetry
bridge needed by the one-pattern union route. -/
theorem map_ambientHaarHafnianPanel_eval
    (H : UnitaryHaarProbabilityFamily)
    (M L K q n : Nat) (hLM : L ≤ M) (hNM : 2 * n ≤ M) (hKM : K ≤ M)
    (rows : Fin q → (Fin (2 * n) ↪ Fin L)) (j : Fin q) :
    Measure.map (fun w : Fin q → Complex ↦ w j)
        (Measure.map (ambientHaarHafnianPanel M K q n L hLM hKM rows)
          (H.law M)) =
      scaledHaarGramHafnianLaw H M n K := by
  rw [Measure.map_map (measurable_pi_apply j)
    (measurable_ambientHaarHafnianPanel M K q n L hLM hKM rows)]
  rw [← LocalAnticoncentration.selectedRowsScaledGramHafnianLaw_eq H hNM hKM
    (ambientOrderedRows hLM (rows j))]
  unfold LocalAnticoncentration.selectedRowsScaledGramHafnianLaw
    LocalAnticoncentration.selectedRowsScaledTransposeGramLaw
  rw [Measure.map_map (measurable_hafnianMatrixObservable n)
    (LocalAnticoncentration.measurable_scaledRectangularTransposeGram M (2 * n) K)]
  rw [Measure.map_map
    ((measurable_hafnianMatrixObservable n).comp
      (LocalAnticoncentration.measurable_scaledRectangularTransposeGram M (2 * n) K))
    (LocalAnticoncentration.measurable_selectedRowsUnitaryBlock hKM
      (ambientOrderedRows hLM (rows j)))]
  rfl

/-- The one-pattern route for the same physical Haar panel.  Haar row
symmetry supplies the canonical marginal law, and a finite union bound pays
the single-pattern hiding remainder `q` times. -/
theorem ambientHaarHafnianPanelSmallBall_union_le
    (H : UnitaryHaarProbabilityFamily)
    (M L K q n : Nat) (hLM : L ≤ M) (hKM : K ≤ M)
    (rows : Fin q → (Fin (2 * n) ↪ Fin L))
    (hn : 1 ≤ n) (hKanti : 4 * n ≤ K)
    {t : Real} (ht : 0 ≤ t) :
    (Measure.map (ambientHaarHafnianPanel M K q n L hLM hKM rows)
      (H.law M)).real
        {w | ∃ j, w j ∈ shiftedComplexDisk 0
          (Real.sqrt t * gramHafnianSigma K n)} ≤
      (q : Real) *
        (min 1 (shiftedAnticoncentrationConstant K n * t) +
          UniformMatrixHiding.hidingRemainder M (2 * n)) := by
  let mu := Measure.map
    (ambientHaarHafnianPanel M K q n L hLM hKM rows) (H.law M)
  let bad := shiftedComplexDisk 0 (Real.sqrt t * gramHafnianSigma K n)
  have hNM : 2 * n ≤ M := by omega
  have hNK : 2 * n ≤ K := by omega
  have hNpos : 1 ≤ 2 * n := by omega
  have hcoord (j : Fin q) :
      mu.real ((fun w : Fin q → Complex ↦ w j) ⁻¹' bad) ≤
        min 1 (shiftedAnticoncentrationConstant K n * t) +
          UniformMatrixHiding.hidingRemainder M (2 * n) := by
    have htvMatrix := UniformMatrixHiding.matrixLaw.apply
      H hNpos hNK hKM
    have htvHafnian := htvMatrix.map
      (measurable_hafnianMatrixObservable n)
    have htv : probabilityTotalVariationLE
        (scaledHaarGramHafnianLaw H M n K)
        (gaussianGramHafnianLaw n K)
        (UniformMatrixHiding.hidingRemainder M (2 * n)) := by
      simpa [scaledHaarGramHafnianLaw, gaussianGramHafnianLaw,
        UniformMatrixHiding.hidingRemainder] using htvHafnian
    have htransfer := htv.event_le
      (measurableSet_shiftedComplexDisk 0
        (Real.sqrt t * gramHafnianSigma K n))
    rw [gaussianGramHafnianLaw_shiftedDisk_eq] at htransfer
    have hgaussian := GaussianAnticoncentration.shiftedSmallBall
      n K hn hKanti 0 (Real.sqrt t) (Real.sqrt_nonneg t)
    have hgaussian' :
        gramHafnianShiftedSmallBallProbability K n 0 (Real.sqrt t) ≤
          min 1 (shiftedAnticoncentrationConstant K n * t) := by
      simpa [Real.sq_sqrt ht] using hgaussian
    have hmarginal := map_ambientHaarHafnianPanel_eval
      H M L K q n hLM hNM hKM rows j
    rw [← hmarginal] at htransfer
    rw [map_measureReal_apply (measurable_pi_apply j)
      (measurableSet_shiftedComplexDisk 0
        (Real.sqrt t * gramHafnianSigma K n))] at htransfer
    exact htransfer.trans (add_le_add hgaussian' le_rfl)
  rw [show {w : Fin q → Complex | ∃ j, w j ∈ bad} =
      ⋃ j, (fun w : Fin q → Complex ↦ w j) ⁻¹' bad by
    ext w
    simp]
  calc
    mu.real (⋃ j, (fun w : Fin q → Complex ↦ w j) ⁻¹' bad) ≤
        ∑ j : Fin q, mu.real
          ((fun w : Fin q → Complex ↦ w j) ⁻¹' bad) :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _j : Fin q,
        (min 1 (shiftedAnticoncentrationConstant K n * t) +
          UniformMatrixHiding.hidingRemainder M (2 * n)) :=
      Finset.sum_le_sum fun j _ ↦ hcoord j
    _ = (q : Real) *
        (min 1 (shiftedAnticoncentrationConstant K n * t) +
          UniformMatrixHiding.hidingRemainder M (2 * n)) := by
      simp [mul_add]

/-- One-shot disjoint-pattern manuscript route: ordered joint hiding is pushed
through denormalization and hafnian, then combined with the exact Gaussian
product-complement bound.  The hiding error is paid once at union size `L`. -/
theorem orderedDisjointHaarHafnianPanelSmallBall
    (H : UnitaryHaarProbabilityFamily)
    (M L K q n : Nat) (hL : 1 ≤ L) (hLK : L ≤ K) (hKM : K ≤ M)
    (hKpos : 1 ≤ K)
    (rows : Fin q → (Fin (2 * n) ↪ Fin L))
    (hrows : Pairwise fun a b =>
      Disjoint (DisjointGaussianRows.rowRange (rows a))
        (DisjointGaussianRows.rowRange (rows b)))
    (hn : 1 ≤ n) (hKanti : 4 * n ≤ K)
    {t : Real} (ht : 0 ≤ t) :
    (Measure.map (denormalizedHafnianPanel q n K)
      (Measure.map (UniformMatrixHiding.orderedPatternPanel rows)
        (Measure.map
          (UniformMatrixHiding.preselectedPrincipalSubmatrixTuple q L
            (UniformMatrixHiding.orderedPatternSets rows))
          (normalizedHaarTransposeGramLaw H M L K)))).real
        {w | ∃ j, w j ∈ shiftedComplexDisk 0
          (Real.sqrt t * gramHafnianSigma K n)} ≤
      1 - (1 - min 1 (shiftedAnticoncentrationConstant K n * t)) ^ q +
        UniformMatrixHiding.hidingRemainder M L := by
  have htv := (UniformMatrixHiding.orderedDisjointPatternProductHiding
    H M L K q (2 * n) hL hLK hKM rows hrows).map
      (measurable_denormalizedHafnianPanel q n K)
  have hproductMap :
      Measure.map (denormalizedHafnianPanel q n K)
          (Measure.pi (fun _ : Fin q =>
            normalizedGaussianTransposeGramLaw (2 * n) K)) =
        Measure.pi (fun _ : Fin q => gaussianGramHafnianLaw n K) := by
    unfold denormalizedHafnianPanel
    rw [Measure.pi_map_pi (fun _ =>
      (measurable_denormalizedHafnianObservable n K).aemeasurable)]
    congr 1
    funext j
    exact map_denormalizedHafnianObservable_normalizedGaussian n K hKpos
  rw [hproductMap] at htv
  have hmeas : MeasurableSet
      {w : Fin q → Complex | ∃ j, w j ∈ shiftedComplexDisk 0
        (Real.sqrt t * gramHafnianSigma K n)} := by
    rw [show {w : Fin q → Complex | ∃ j, w j ∈ shiftedComplexDisk 0
        (Real.sqrt t * gramHafnianSigma K n)} =
      ⋃ j, (fun w : Fin q → Complex => w j) ⁻¹'
        shiftedComplexDisk 0 (Real.sqrt t * gramHafnianSigma K n) by
      ext w
      simp]
    exact MeasurableSet.iUnion fun j =>
      (measurable_pi_apply j)
        (measurableSet_shiftedComplexDisk 0
          (Real.sqrt t * gramHafnianSigma K n))
  have htransfer := htv.event_le hmeas
  exact htransfer.trans (add_le_add
    (gaussianHafnianProductPanelSmallBall_le hn hKanti ht) le_rfl)

/-- Taking the better of a one-shot union transfer and `q` individual
transfers gives the minimum hiding remainder in Panel application. -/
theorem finitePanel_min_hiding_remainder
    {failure gaussianUnion deltaUnion deltaSingle q : Real}
    (hprob : failure <= 1)
    (hjoint : failure <= gaussianUnion + deltaUnion)
    (hsingle : failure <= gaussianUnion + q * deltaSingle) :
    failure <=
      min 1 (gaussianUnion + min deltaUnion (q * deltaSingle)) := by
  apply le_min hprob
  by_cases hdelta : deltaUnion <= q * deltaSingle
  · rw [min_eq_left hdelta]
    exact hjoint
  · rw [min_eq_right (le_of_not_ge hdelta)]
    exact hsingle

/-- Pairwise-disjoint panels admit two valid routes: the independent
Gaussian-union route paid with one joint hiding error, and the union of the
one-pattern finite-Haar estimates. -/
theorem disjointPanel_min_of_two
    {failure a deltaJoint deltaSingle : Real} (q : Nat)
    (hprob : failure <= 1)
    (hjoint : failure <= 1 - (1 - a) ^ q + deltaJoint)
    (hsingle : failure <= (q : Real) * (a + deltaSingle)) :
    failure <= min 1
      (min (1 - (1 - a) ^ q + deltaJoint)
        ((q : Real) * (a + deltaSingle))) := by
  exact le_min hprob (le_min hjoint hsingle)

/-- Literal ordered-disjoint Haar panel endpoint.  The same physical
selected-row panel is bounded both by one joint transfer to the independent
Gaussian product law and by a union of `q` canonical one-pattern transfers.
Thus the finite-Haar outputs are not assumed independent, while the exact
three-way minimum displayed in the Letter is obtained. -/
theorem orderedDisjointHaarHafnianPanelSmallBall_full
    (H : UnitaryHaarProbabilityFamily)
    (M L K q n : Nat) (hL : 1 ≤ L) (hLK : L ≤ K) (hKM : K ≤ M)
    (rows : Fin q → (Fin (2 * n) ↪ Fin L))
    (hrows : Pairwise fun a b ↦
      Disjoint (DisjointGaussianRows.rowRange (rows a))
        (DisjointGaussianRows.rowRange (rows b)))
    (hn : 1 ≤ n) (hKanti : 4 * n ≤ K)
    {t : Real} (ht : 0 ≤ t) :
    (Measure.map
      (ambientHaarHafnianPanel M K q n L
        (hLK.trans hKM) hKM rows) (H.law M)).real
        {w | ∃ j, w j ∈ shiftedComplexDisk 0
          (Real.sqrt t * gramHafnianSigma K n)} ≤
      min 1
        (min
          (1 - (1 - min 1
            (shiftedAnticoncentrationConstant K n * t)) ^ q +
              UniformMatrixHiding.hidingRemainder M L)
          ((q : Real) *
            (min 1 (shiftedAnticoncentrationConstant K n * t) +
              UniformMatrixHiding.hidingRemainder M (2 * n)))) := by
  let mu := Measure.map
    (ambientHaarHafnianPanel M K q n L
      (hLK.trans hKM) hKM rows) (H.law M)
  let event : Set (Fin q → Complex) :=
    {w | ∃ j, w j ∈ shiftedComplexDisk 0
      (Real.sqrt t * gramHafnianSigma K n)}
  letI : IsProbabilityMeasure (H.law M) := H.isProbability M
  letI : IsProbabilityMeasure mu := by
    dsimp [mu]
    exact Measure.isProbabilityMeasure_map
      (measurable_ambientHaarHafnianPanel M K q n L
        (hLK.trans hKM) hKM rows).aemeasurable
  have hjointRaw := orderedDisjointHaarHafnianPanelSmallBall
    H M L K q n hL hLK hKM (by omega) rows hrows hn hKanti ht
  have hlaw := orderedHaarHafnianPanelLaw_eq_ambient
    H M L K q n (hLK.trans hKM) hKM (by omega) rows
  have hjoint : mu.real event ≤
      1 - (1 - min 1 (shiftedAnticoncentrationConstant K n * t)) ^ q +
        UniformMatrixHiding.hidingRemainder M L := by
    change (Measure.map (denormalizedHafnianPanel q n K)
      (UniformMatrixHiding.orderedPatternPanelHaarLaw
        H M L K q (2 * n) rows)).real event ≤ _ at hjointRaw
    rw [hlaw] at hjointRaw
    exact hjointRaw
  have hsingle : mu.real event ≤
      (q : Real) *
        (min 1 (shiftedAnticoncentrationConstant K n * t) +
          UniformMatrixHiding.hidingRemainder M (2 * n)) := by
    exact ambientHaarHafnianPanelSmallBall_union_le
      H M L K q n (hLK.trans hKM) hKM rows hn hKanti ht
  exact disjointPanel_min_of_two q measureReal_le_one hjoint hsingle

/-- Paper-notation specialization of the preceding theorem with photon
number `N = 2n` and exact disjoint-union size `L = qN`. -/
theorem orderedDisjointHaarHafnianPanelSmallBall_full_qN
    (H : UnitaryHaarProbabilityFamily)
    (M K q n : Nat) (hq : 1 ≤ q) (hKM : K ≤ M)
    (hqN : q * (2 * n) ≤ K)
    (rows : Fin q → (Fin (2 * n) ↪ Fin (q * (2 * n))))
    (hrows : Pairwise fun a b ↦
      Disjoint (DisjointGaussianRows.rowRange (rows a))
        (DisjointGaussianRows.rowRange (rows b)))
    (hn : 1 ≤ n) (hKanti : 4 * n ≤ K)
    {t : Real} (ht : 0 ≤ t) :
    (Measure.map
      (ambientHaarHafnianPanel M K q n (q * (2 * n))
        (hqN.trans hKM) hKM rows) (H.law M)).real
        {w | ∃ j, w j ∈ shiftedComplexDisk 0
          (Real.sqrt t * gramHafnianSigma K n)} ≤
      min 1
        (min
          (1 - (1 - min 1
            (shiftedAnticoncentrationConstant K n * t)) ^ q +
              UniformMatrixHiding.hidingRemainder M (q * (2 * n)))
          ((q : Real) *
            (min 1 (shiftedAnticoncentrationConstant K n * t) +
              UniformMatrixHiding.hidingRemainder M (2 * n)))) := by
  exact orderedDisjointHaarHafnianPanelSmallBall_full
    H M (q * (2 * n)) K q n
      (Nat.mul_pos hq (by omega)) hqN hKM rows hrows hn hKanti ht

/-- Physical small-denominator event for a finite panel of scaled hafnian
amplitudes. -/
def gbsPanelSmallDenominatorSet
    (r : Real) (M K q n : Nat) (t : Real) : Set (Fin q → Complex) :=
  {w | ∃ j, w j ∈ scaledAmplitudeSmallDenominatorSet r M K n t}

/-- The physical panel event is exactly the centered hafnian-disk union. -/
theorem gbsPanelSmallDenominatorSet_eq_hafnianDiskUnion
    {r : Real} (hr : 0 < r) {M : Nat} (hM : 0 < M)
    (K q n : Nat) {t : Real} (ht : 0 ≤ t) :
    gbsPanelSmallDenominatorSet r M K q n t =
      {w | ∃ j, w j ∈ shiftedComplexDisk 0
        (Real.sqrt t * gramHafnianSigma K n)} := by
  unfold gbsPanelSmallDenominatorSet
  rw [scaledAmplitudeSmallDenominatorSet_eq_shiftedComplexDisk
    hr hM K n ht]

/-- Literal physical-probability form of the ordered-disjoint panel bound in
the Letter, with `N = 2n` and `L = qN`. -/
theorem orderedDisjointPhysicalPanelSmallDenominator_full_qN
    (H : UnitaryHaarProbabilityFamily)
    {r : Real} (hr : 0 < r)
    (M K q n : Nat) (hq : 1 ≤ q) (hKM : K ≤ M)
    (hqN : q * (2 * n) ≤ K)
    (rows : Fin q → (Fin (2 * n) ↪ Fin (q * (2 * n))))
    (hrows : Pairwise fun a b ↦
      Disjoint (DisjointGaussianRows.rowRange (rows a))
        (DisjointGaussianRows.rowRange (rows b)))
    (hn : 1 ≤ n) (hKanti : 4 * n ≤ K)
    {t : Real} (ht : 0 ≤ t) :
    (Measure.map
      (ambientHaarHafnianPanel M K q n (q * (2 * n))
        (hqN.trans hKM) hKM rows) (H.law M)).real
        (gbsPanelSmallDenominatorSet r M K q n t) ≤
      min 1
        (min
          (1 - (1 - min 1
            (shiftedAnticoncentrationConstant K n * t)) ^ q +
              UniformMatrixHiding.hidingRemainder M (q * (2 * n)))
          ((q : Real) *
            (min 1 (shiftedAnticoncentrationConstant K n * t) +
              UniformMatrixHiding.hidingRemainder M (2 * n)))) := by
  rw [gbsPanelSmallDenominatorSet_eq_hafnianDiskUnion
    hr (by omega) K q n ht]
  exact orderedDisjointHaarHafnianPanelSmallBall_full_qN
    H M K q n hq hKM hqN rows hrows hn hKanti ht

/-! ## Literal ordinary finite-panel endpoint -/

/-- Denormalized Gaussian hafnian-panel law for an arbitrary ordered family
of patterns; overlaps are allowed. -/
def orderedGaussianHafnianPanelLaw
    (L K q n : Nat) (rows : Fin q → (Fin (2 * n) ↪ Fin L)) :
    Measure (Fin q → Complex) :=
  Measure.map (denormalizedHafnianPanel q n K)
    (Measure.map (UniformMatrixHiding.orderedPatternPanel rows)
      (Measure.map
        (UniformMatrixHiding.preselectedPrincipalSubmatrixTuple q L
          (UniformMatrixHiding.orderedPatternSets rows))
        (normalizedGaussianTransposeGramLaw L K)))

/-- Every coordinate of the arbitrary Gaussian panel has the canonical
one-pattern Gram-hafnian law. -/
theorem map_orderedGaussianHafnianPanel_eval
    (L K q n : Nat) (hKpos : 1 ≤ K)
    (rows : Fin q → (Fin (2 * n) ↪ Fin L)) (j : Fin q) :
    Measure.map (fun w : Fin q → Complex ↦ w j)
        (orderedGaussianHafnianPanelLaw L K q n rows) =
      gaussianGramHafnianLaw n K := by
  unfold orderedGaussianHafnianPanelLaw
  rw [Measure.map_map (measurable_pi_apply j)
    (measurable_denormalizedHafnianPanel q n K)]
  rw [UniformMatrixHiding.orderedGaussianPatternPanelLaw rows]
  rw [Measure.map_map
    ((measurable_pi_apply j).comp
      (measurable_denormalizedHafnianPanel q n K))
    (measurable_pi_lambda _ fun i ↦
      DisjointGaussianRows.measurable_orderedNormalizedGram
        (K := K) (rows i))]
  change Measure.map
      (denormalizedHafnianObservable n K ∘
        DisjointGaussianRows.orderedNormalizedGram (K := K) (rows j))
      (standardComplexGaussianRectangularMeasure L K) = _
  rw [← Measure.map_map
    (measurable_denormalizedHafnianObservable n K)
    (DisjointGaussianRows.measurable_orderedNormalizedGram
      (K := K) (rows j))]
  rw [DisjointGaussianRows.map_orderedNormalizedGram (K := K) (rows j)]
  exact map_denormalizedHafnianObservable_normalizedGaussian n K hKpos

/-- Ordinary Gaussian union bound for an arbitrary, possibly overlapping,
finite pattern panel. -/
theorem orderedGaussianHafnianPanelSmallBall_union_le
    (L K q n : Nat) (hKpos : 1 ≤ K)
    (rows : Fin q → (Fin (2 * n) ↪ Fin L))
    (hn : 1 ≤ n) (hKanti : 4 * n ≤ K)
    {t : Real} (ht : 0 ≤ t) :
    (orderedGaussianHafnianPanelLaw L K q n rows).real
        {w | ∃ j, w j ∈ shiftedComplexDisk 0
          (Real.sqrt t * gramHafnianSigma K n)} ≤
      (q : Real) * shiftedAnticoncentrationConstant K n * t := by
  let mu := orderedGaussianHafnianPanelLaw L K q n rows
  let bad := shiftedComplexDisk 0 (Real.sqrt t * gramHafnianSigma K n)
  have hcoord (j : Fin q) :
      mu.real ((fun w : Fin q → Complex ↦ w j) ⁻¹' bad) ≤
        shiftedAnticoncentrationConstant K n * t := by
    rw [← map_measureReal_apply (measurable_pi_apply j)
      (measurableSet_shiftedComplexDisk 0
        (Real.sqrt t * gramHafnianSigma K n))]
    rw [map_orderedGaussianHafnianPanel_eval L K q n hKpos rows j]
    rw [gaussianGramHafnianLaw_shiftedDisk_eq]
    simpa [Real.sq_sqrt ht] using
      (GaussianAnticoncentration.shiftedSmallBall
        n K hn hKanti 0 (Real.sqrt t) (Real.sqrt_nonneg t)).trans
          (min_le_right _ _)
  rw [show {w : Fin q → Complex | ∃ j, w j ∈ bad} =
      ⋃ j, (fun w : Fin q → Complex ↦ w j) ⁻¹' bad by
    ext w
    simp]
  calc
    mu.real (⋃ j, (fun w : Fin q → Complex ↦ w j) ⁻¹' bad) ≤
        ∑ j : Fin q, mu.real
          ((fun w : Fin q → Complex ↦ w j) ⁻¹' bad) :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _j : Fin q, shiftedAnticoncentrationConstant K n * t :=
      Finset.sum_le_sum fun j _ ↦ hcoord j
    _ = (q : Real) * shiftedAnticoncentrationConstant K n * t := by
      simp
      ring

/-- Literal ordinary finite-panel theorem for arbitrary ordered patterns,
combining one joint transfer at union size `L` with `q` one-pattern
transfers.  No disjointness is assumed. -/
theorem orderedHaarHafnianFinitePanelSmallBall
    (H : UnitaryHaarProbabilityFamily)
    (M L K q n : Nat) (hL : 1 ≤ L) (hLK : L ≤ K) (hKM : K ≤ M)
    (hKpos : 1 ≤ K)
    (rows : Fin q → (Fin (2 * n) ↪ Fin L))
    (hn : 1 ≤ n) (hKanti : 4 * n ≤ K)
    {t : Real} (ht : 0 ≤ t) :
    (Measure.map (ambientHaarHafnianPanel M K q n L
      (hLK.trans hKM) hKM rows) (H.law M)).real
        {w | ∃ j, w j ∈ shiftedComplexDisk 0
          (Real.sqrt t * gramHafnianSigma K n)} ≤
      min 1 ((q : Real) * shiftedAnticoncentrationConstant K n * t +
        min (UniformMatrixHiding.hidingRemainder M L)
          ((q : Real) * UniformMatrixHiding.hidingRemainder M (2 * n))) := by
  letI : IsProbabilityMeasure (H.law M) := H.isProbability M
  letI : IsProbabilityMeasure
      (Measure.map (ambientHaarHafnianPanel M K q n L
        (hLK.trans hKM) hKM rows) (H.law M)) :=
    Measure.isProbabilityMeasure_map
      (measurable_ambientHaarHafnianPanel M K q n L
        (hLK.trans hKM) hKM rows).aemeasurable
  let bad : Set (Fin q → Complex) :=
    {w | ∃ j, w j ∈ shiftedComplexDisk 0
      (Real.sqrt t * gramHafnianSigma K n)}
  have hbad : MeasurableSet bad := by
    dsimp [bad]
    rw [show {w : Fin q → Complex | ∃ j, w j ∈ shiftedComplexDisk 0
        (Real.sqrt t * gramHafnianSigma K n)} =
      ⋃ j, (fun w : Fin q → Complex ↦ w j) ⁻¹'
        shiftedComplexDisk 0 (Real.sqrt t * gramHafnianSigma K n) by
      ext w
      simp]
    exact MeasurableSet.iUnion fun j ↦
      (measurable_pi_apply j)
        (measurableSet_shiftedComplexDisk 0
          (Real.sqrt t * gramHafnianSigma K n))
  have htv0 := UniformMatrixHiding.jointPreselectedPatternLaw
    H M L K q hL hLK hKM (UniformMatrixHiding.orderedPatternSets rows)
  have htv1 := htv0.map (UniformMatrixHiding.measurable_orderedPatternPanel rows)
  have htv2 := htv1.map (measurable_denormalizedHafnianPanel q n K)
  have htv : probabilityTotalVariationLE
      (Measure.map (denormalizedHafnianPanel q n K)
        (UniformMatrixHiding.orderedPatternPanelHaarLaw
          H M L K q (2 * n) rows))
      (orderedGaussianHafnianPanelLaw L K q n rows)
      (UniformMatrixHiding.hidingRemainder M L) := by
    simpa [UniformMatrixHiding.orderedPatternPanelHaarLaw,
      orderedGaussianHafnianPanelLaw,
      UniformMatrixHiding.hidingRemainder] using htv2
  have hlaw := orderedHaarHafnianPanelLaw_eq_ambient
    H M L K q n (hLK.trans hKM) hKM hKpos rows
  have hjointRaw := htv.event_le hbad
  have hjoint :
      (Measure.map (ambientHaarHafnianPanel M K q n L
        (hLK.trans hKM) hKM rows) (H.law M)).real bad ≤
        (q : Real) * shiftedAnticoncentrationConstant K n * t +
          UniformMatrixHiding.hidingRemainder M L := by
    rw [hlaw] at hjointRaw
    exact hjointRaw.trans (add_le_add
      (orderedGaussianHafnianPanelSmallBall_union_le
        L K q n hKpos rows hn hKanti ht) le_rfl)
  have hsingleRaw := ambientHaarHafnianPanelSmallBall_union_le
    H M L K q n (hLK.trans hKM) hKM rows hn hKanti ht
  have hsingle :
      (Measure.map (ambientHaarHafnianPanel M K q n L
        (hLK.trans hKM) hKM rows) (H.law M)).real bad ≤
        (q : Real) * shiftedAnticoncentrationConstant K n * t +
          (q : Real) * UniformMatrixHiding.hidingRemainder M (2 * n) := by
    calc
      _ ≤ (q : Real) *
          (min 1 (shiftedAnticoncentrationConstant K n * t) +
            UniformMatrixHiding.hidingRemainder M (2 * n)) := hsingleRaw
      _ ≤ (q : Real) *
          (shiftedAnticoncentrationConstant K n * t +
            UniformMatrixHiding.hidingRemainder M (2 * n)) :=
        mul_le_mul_of_nonneg_left
          (add_le_add (min_le_right _ _) le_rfl) (Nat.cast_nonneg q)
      _ = (q : Real) * shiftedAnticoncentrationConstant K n * t +
          (q : Real) * UniformMatrixHiding.hidingRemainder M (2 * n) := by ring
  change _ ≤ min 1 _
  exact finitePanel_min_hiding_remainder measureReal_le_one hjoint hsingle

/-- Physical-probability form of the ordinary finite-panel display. -/
theorem orderedPhysicalFinitePanelSmallDenominator
    (H : UnitaryHaarProbabilityFamily)
    {r : Real} (hr : 0 < r)
    (M L K q n : Nat) (hL : 1 ≤ L) (hLK : L ≤ K) (hKM : K ≤ M)
    (hKpos : 1 ≤ K)
    (rows : Fin q → (Fin (2 * n) ↪ Fin L))
    (hn : 1 ≤ n) (hKanti : 4 * n ≤ K)
    {t : Real} (ht : 0 ≤ t) :
    (Measure.map (ambientHaarHafnianPanel M K q n L
      (hLK.trans hKM) hKM rows) (H.law M)).real
        (gbsPanelSmallDenominatorSet r M K q n t) ≤
      min 1 ((q : Real) * shiftedAnticoncentrationConstant K n * t +
        min (UniformMatrixHiding.hidingRemainder M L)
          ((q : Real) * UniformMatrixHiding.hidingRemainder M (2 * n))) := by
  rw [gbsPanelSmallDenominatorSet_eq_hafnianDiskUnion
    hr (by omega) K q n ht]
  exact orderedHaarHafnianFinitePanelSmallBall
    H M L K q n hL hLK hKM hKpos rows hn hKanti ht

/-! ## Literal collision-free Haar x uniform-label endpoints -/

/-- Canonical ordered row embedding associated with a collision-free label.
The order is immaterial by Haar row symmetry. -/
def collisionFreeLabelRows {M N : Nat}
    (S : CollisionFreeLabel M N) : Fin N ↪ Fin M :=
  (Finset.equivFinOfCardEq (s := (S : Finset (Fin M))) (by
    simpa [CollisionFreeLabel, collisionFreeLabelSet] using S.property)).symm.asEmbedding

/-- Scaled Gram-hafnian amplitude of one literal collision-free label. -/
def collisionFreeHafnianAmplitude
    (M K n : Nat) (hKM : K ≤ M)
    (U : Matrix.unitaryGroup (Fin M) Complex)
    (S : CollisionFreeLabel M (2 * n)) : Complex :=
  hafnianMatrixObservable n
    (LocalAnticoncentration.scaledRectangularTransposeGram M (2 * n) K
      (LocalAnticoncentration.selectedRowsUnitaryBlock hKM
        (collisionFreeLabelRows S) U))

theorem measurable_collisionFreeHafnianAmplitude
    (M K n : Nat) (hKM : K ≤ M)
    (S : CollisionFreeLabel M (2 * n)) :
    Measurable (fun U ↦ collisionFreeHafnianAmplitude M K n hKM U S) := by
  exact (measurable_hafnianMatrixObservable n).comp
    ((LocalAnticoncentration.measurable_scaledRectangularTransposeGram M (2 * n) K).comp
      (LocalAnticoncentration.measurable_selectedRowsUnitaryBlock hKM
        (collisionFreeLabelRows S)))

/-- Each literal collision-free label has the canonical scaled Haar
Gram-hafnian law. -/
theorem map_collisionFreeHafnianAmplitude_eq_scaledHaar
    (H : UnitaryHaarProbabilityFamily)
    (M K n : Nat) (hNM : 2 * n ≤ M) (hKM : K ≤ M)
    (S : CollisionFreeLabel M (2 * n)) :
    Measure.map (fun U ↦ collisionFreeHafnianAmplitude M K n hKM U S)
        (H.law M) =
      scaledHaarGramHafnianLaw H M n K := by
  rw [← LocalAnticoncentration.selectedRowsScaledGramHafnianLaw_eq
    H hNM hKM (collisionFreeLabelRows S)]
  unfold LocalAnticoncentration.selectedRowsScaledGramHafnianLaw
    LocalAnticoncentration.selectedRowsScaledTransposeGramLaw
    collisionFreeHafnianAmplitude
  rw [Measure.map_map (measurable_hafnianMatrixObservable n)
    (LocalAnticoncentration.measurable_scaledRectangularTransposeGram M (2 * n) K)]
  rw [Measure.map_map
    ((measurable_hafnianMatrixObservable n).comp
      (LocalAnticoncentration.measurable_scaledRectangularTransposeGram M (2 * n) K))
    (LocalAnticoncentration.measurable_selectedRowsUnitaryBlock hKM
      (collisionFreeLabelRows S))]
  apply Measure.map_congr
  exact ae_of_all _ fun _ ↦ rfl

/-- Canonical finite uniform probability law on collision-free labels. -/
def collisionFreeUniformLaw {M N : Nat} (hNM : N ≤ M) :
    Measure (CollisionFreeLabel M N) :=
  let _ : Nonempty (CollisionFreeLabel M N) :=
    collisionFreeLabelSpace_nonempty hNM
  (PMF.uniformOfFintype (CollisionFreeLabel M N)).toMeasure

theorem collisionFreeUniformLaw_isProbability {M N : Nat} (hNM : N ≤ M) :
    IsProbabilityMeasure (collisionFreeUniformLaw hNM) := by
  unfold collisionFreeUniformLaw
  letI : Nonempty (CollisionFreeLabel M N) :=
    collisionFreeLabelSpace_nonempty hNM
  infer_instance

/-- Haar circuit paired independently with a uniform collision-free label. -/
def haarUniformCollisionFreeLaw
    (H : UnitaryHaarProbabilityFamily) {M N : Nat} (hNM : N ≤ M) :
    Measure (CollisionFreeLabel M N × Matrix.unitaryGroup (Fin M) Complex) :=
  (collisionFreeUniformLaw hNM).prod (H.law M)

theorem haarUniformCollisionFreeLaw_isProbability
    (H : UnitaryHaarProbabilityFamily) {M N : Nat} (hNM : N ≤ M) :
    IsProbabilityMeasure (haarUniformCollisionFreeLaw H hNM) := by
  letI : IsProbabilityMeasure (collisionFreeUniformLaw hNM) :=
    collisionFreeUniformLaw_isProbability hNM
  letI : IsProbabilityMeasure (H.law M) := H.isProbability M
  unfold haarUniformCollisionFreeLaw
  infer_instance

/-- A function on a finite discrete first coordinate and a measurable second
coordinate is jointly measurable when every second-coordinate section is. -/
theorem measurable_uncurry_left_finite
    {iota Omega beta : Type*} [MeasurableSpace iota]
    [MeasurableSingletonClass iota] [Fintype iota]
    [MeasurableSpace Omega] [MeasurableSpace beta]
    (f : iota → Omega → beta) (hf : ∀ i, Measurable (f i)) :
    Measurable (Function.uncurry f) := by
  intro s hs
  rw [show Function.uncurry f ⁻¹' s =
      ⋃ i : iota, ({i} : Set iota) ×ˢ (f i ⁻¹' s) by
    ext x
    simp only [Set.mem_preimage, Function.uncurry_apply_pair,
      Set.mem_iUnion, Set.mem_prod, Set.mem_singleton_iff]
    constructor
    · intro hx
      exact ⟨x.1, rfl, hx⟩
    · rintro ⟨i, hi, hx⟩
      change f x.1 x.2 ∈ s
      rw [hi]
      exact hx]
  exact MeasurableSet.iUnion fun i ↦
    (measurableSet_singleton i).prod ((hf i) hs)

/-- Literal amplitude map on Haar x uniform collision-free labels. -/
def haarUniformCollisionFreeAmplitude
    (M K n : Nat) (hKM : K ≤ M) :
    CollisionFreeLabel M (2 * n) ×
        Matrix.unitaryGroup (Fin M) Complex → Complex :=
  fun x ↦ collisionFreeHafnianAmplitude M K n hKM x.2 x.1

theorem measurable_haarUniformCollisionFreeAmplitude
    (M K n : Nat) (hKM : K ≤ M) :
    Measurable (haarUniformCollisionFreeAmplitude M K n hKM) := by
  exact measurable_uncurry_left_finite
    (fun S U ↦ collisionFreeHafnianAmplitude M K n hKM U S)
    (measurable_collisionFreeHafnianAmplitude M K n hKM)

/-- Haar x uniform-label averaging has exactly the canonical one-pattern
amplitude marginal. -/
theorem map_haarUniformCollisionFreeAmplitude_eq_scaledHaar
    (H : UnitaryHaarProbabilityFamily)
    (M K n : Nat) (hNM : 2 * n ≤ M) (hKM : K ≤ M) :
    Measure.map (haarUniformCollisionFreeAmplitude M K n hKM)
        (haarUniformCollisionFreeLaw H hNM) =
      scaledHaarGramHafnianLaw H M n K := by
  letI : IsProbabilityMeasure (collisionFreeUniformLaw hNM) :=
    collisionFreeUniformLaw_isProbability hNM
  letI : IsProbabilityMeasure (H.law M) := H.isProbability M
  ext s hs
  rw [Measure.map_apply
    (measurable_haarUniformCollisionFreeAmplitude M K n hKM) hs]
  unfold haarUniformCollisionFreeLaw
  rw [Measure.prod_apply
    ((measurable_haarUniformCollisionFreeAmplitude M K n hKM) hs)]
  have hsection (S : CollisionFreeLabel M (2 * n)) :
      (H.law M)
          (Prod.mk S ⁻¹'
            (haarUniformCollisionFreeAmplitude M K n hKM ⁻¹' s)) =
        scaledHaarGramHafnianLaw H M n K s := by
    change (H.law M)
        ((fun U ↦ collisionFreeHafnianAmplitude M K n hKM U S) ⁻¹' s) = _
    rw [← Measure.map_apply
      (measurable_collisionFreeHafnianAmplitude M K n hKM S) hs]
    rw [map_collisionFreeHafnianAmplitude_eq_scaledHaar
      H M K n hNM hKM S]
  simp_rw [hsection]
  simp

/-! ## Literal physical dark-label consequences -/

/-- The uncapped one-pattern finite-Haar physical denominator estimate in
the notation used by the Letter. -/
theorem scaledHaarPhysicalSmallDenominator_uncapped
    (H : UnitaryHaarProbabilityFamily)
    {r : Real} (hr : 0 < r)
    (M K n : Nat) (hn : 1 ≤ n) (hKanti : 4 * n ≤ K) (hKM : K ≤ M)
    {t : Real} (ht : 0 ≤ t) :
    (scaledHaarGramHafnianLaw H M n K).real
        (scaledAmplitudeSmallDenominatorSet r M K n t) ≤
      shiftedAnticoncentrationConstant K n * t +
        UniformMatrixHiding.hidingRemainder M (2 * n) := by
  have hM : 0 < M := by omega
  rw [scaledAmplitudeSmallDenominatorSet_eq_shiftedComplexDisk
    hr hM K n ht]
  have hNM : 2 * n ≤ M := by omega
  have hNK : 2 * n ≤ K := by omega
  have hNpos : 1 ≤ 2 * n := by omega
  have htvMatrix := UniformMatrixHiding.matrixLaw.apply
    H hNpos hNK hKM
  have htvHafnian := htvMatrix.map (measurable_hafnianMatrixObservable n)
  have htv : probabilityTotalVariationLE
      (scaledHaarGramHafnianLaw H M n K)
      (gaussianGramHafnianLaw n K)
      (UniformMatrixHiding.hidingRemainder M (2 * n)) := by
    simpa [scaledHaarGramHafnianLaw, gaussianGramHafnianLaw,
      UniformMatrixHiding.hidingRemainder] using htvHafnian
  have htransfer := htv.event_le
    (measurableSet_shiftedComplexDisk 0
      (Real.sqrt t * gramHafnianSigma K n))
  rw [gaussianGramHafnianLaw_shiftedDisk_eq] at htransfer
  have hgaussian := GaussianAnticoncentration.shiftedSmallBall
    n K hn hKanti 0 (Real.sqrt t) (Real.sqrt_nonneg t)
  have hgaussian' :
      gramHafnianShiftedSmallBallProbability K n 0 (Real.sqrt t) ≤
        shiftedAnticoncentrationConstant K n * t := by
    simpa [Real.sq_sqrt ht] using hgaussian.trans (min_le_right _ _)
  exact htransfer.trans (add_le_add hgaussian' le_rfl)

/-- The same tail in the capped error notation `e_t` of the Letter. -/
theorem scaledHaarPhysicalSmallDenominator_le_darkLabelError
    (H : UnitaryHaarProbabilityFamily)
    {r : Real} (hr : 0 < r)
    (M K n : Nat) (hn : 1 ≤ n) (hKanti : 4 * n ≤ K) (hKM : K ≤ M)
    {t : Real} (ht : 0 ≤ t) :
    (scaledHaarGramHafnianLaw H M n K).real
        (scaledAmplitudeSmallDenominatorSet r M K n t) ≤
      darkLabelError M (2 * n) K n t := by
  letI : IsProbabilityMeasure (scaledHaarGramHafnianLaw H M n K) :=
    scaledHaarGramHafnianLaw_isProbability H (by omega) hKM
  unfold darkLabelError
  exact le_min measureReal_le_one
    (scaledHaarPhysicalSmallDenominator_uncapped
      H hr M K n hn hKanti hKM ht)

/-- Literal physical dark event for one collision-free output label. -/
def collisionFreeDarkEvent
    (r : Real) (M K n : Nat) (hKM : K ≤ M) (t : Real)
    (S : CollisionFreeLabel M (2 * n)) :
    Set (Matrix.unitaryGroup (Fin M) Complex) :=
  (fun U ↦ collisionFreeHafnianAmplitude M K n hKM U S) ⁻¹'
    scaledAmplitudeSmallDenominatorSet r M K n t

theorem measurableSet_collisionFreeDarkEvent
    {r : Real} (hr : 0 < r) (M K n : Nat) (hM : 0 < M)
    (hKM : K ≤ M) {t : Real} (ht : 0 ≤ t)
    (S : CollisionFreeLabel M (2 * n)) :
    MeasurableSet (collisionFreeDarkEvent r M K n hKM t S) := by
  unfold collisionFreeDarkEvent
  exact (measurable_collisionFreeHafnianAmplitude M K n hKM S)
    (measurableSet_scaledAmplitudeSmallDenominatorSet hr hM K n ht)

/-- Haar row exchangeability plus the composed one-pattern theorem, stated
directly for every collision-free label. -/
theorem collisionFreeDarkEvent_probability_le
    (H : UnitaryHaarProbabilityFamily)
    {r : Real} (hr : 0 < r)
    (M K n : Nat) (hn : 1 ≤ n) (hKanti : 4 * n ≤ K) (hKM : K ≤ M)
    {t : Real} (ht : 0 ≤ t)
    (S : CollisionFreeLabel M (2 * n)) :
    (H.law M).real (collisionFreeDarkEvent r M K n hKM t S) ≤
      darkLabelError M (2 * n) K n t := by
  have hM : 0 < M := by omega
  have hNM : 2 * n ≤ M := by omega
  unfold collisionFreeDarkEvent
  rw [← map_measureReal_apply
    (measurable_collisionFreeHafnianAmplitude M K n hKM S)
    (measurableSet_scaledAmplitudeSmallDenominatorSet hr hM K n ht)]
  rw [map_collisionFreeHafnianAmplitude_eq_scaledHaar
    H M K n hNM hKM S]
  exact scaledHaarPhysicalSmallDenominator_le_darkLabelError
    H hr M K n hn hKanti hKM ht

/-- Literal expected-dark-fraction display of the Letter, including its
equality with Haar times an independent uniform collision-free label. -/
theorem collisionFreeExpectedDarkFraction
    (H : UnitaryHaarProbabilityFamily)
    {r : Real} (hr : 0 < r)
    (M K n : Nat) (hn : 1 ≤ n) (hKanti : 4 * n ≤ K) (hKM : K ≤ M)
    {t : Real} (ht : 0 ≤ t) :
    let dark := collisionFreeDarkEvent r M K n hKM t
    (∫ U, darkLabelFraction dark U ∂H.law M) =
        (haarUniformCollisionFreeLaw H (by omega)).real
          (haarUniformCollisionFreeAmplitude M K n hKM ⁻¹'
            scaledAmplitudeSmallDenominatorSet r M K n t) ∧
      (∫ U, darkLabelFraction dark U ∂H.law M) ≤
        darkLabelError M (2 * n) K n t := by
  dsimp only
  have hM : 0 < M := by omega
  have hNM : 2 * n ≤ M := by omega
  letI : IsProbabilityMeasure (H.law M) := H.isProbability M
  letI : Nonempty (CollisionFreeLabel M (2 * n)) :=
    collisionFreeLabelSpace_nonempty hNM
  have hdark (S : CollisionFreeLabel M (2 * n)) :
      MeasurableSet (collisionFreeDarkEvent r M K n hKM t S) :=
    measurableSet_collisionFreeDarkEvent hr M K n hM hKM ht S
  have hmarginal (S : CollisionFreeLabel M (2 * n)) :
      (H.law M).real (collisionFreeDarkEvent r M K n hKM t S) =
        (scaledHaarGramHafnianLaw H M n K).real
          (scaledAmplitudeSmallDenominatorSet r M K n t) := by
    unfold collisionFreeDarkEvent
    rw [← map_measureReal_apply
      (measurable_collisionFreeHafnianAmplitude M K n hKM S)
      (measurableSet_scaledAmplitudeSmallDenominatorSet hr hM K n ht)]
    rw [map_collisionFreeHafnianAmplitude_eq_scaledHaar
      H M K n hNM hKM S]
  constructor
  · rw [expectedDarkLabelFraction_eq_uniformMarginal
      (H.law M) (collisionFreeDarkEvent r M K n hKM t) hdark]
    simp_rw [hmarginal]
    unfold uniformFiniteAverage
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : (0 : Real) <
        Fintype.card (CollisionFreeLabel M (2 * n)) := by positivity
    rw [Finset.card_univ]
    rw [mul_div_cancel_left₀ _ hcard.ne']
    rw [← map_measureReal_apply
      (measurable_haarUniformCollisionFreeAmplitude M K n hKM)
      (measurableSet_scaledAmplitudeSmallDenominatorSet hr hM K n ht)]
    rw [map_haarUniformCollisionFreeAmplitude_eq_scaledHaar
      H M K n hNM hKM]
  · exact expectedDarkLabelFraction_le (H.law M)
      (collisionFreeDarkEvent r M K n hKM t) hdark
      (collisionFreeDarkEvent_probability_le
        H hr M K n hn hKanti hKM ht)

/-- Literal circuitwise most-labels-not-dark conclusion. -/
theorem collisionFreeMostLabelsNotDark
    (H : UnitaryHaarProbabilityFamily)
    {r : Real} (hr : 0 < r)
    (M K n : Nat) (hn : 1 ≤ n) (hKanti : 4 * n ≤ K) (hKM : K ≤ M)
    {t : Real} (ht : 0 ≤ t) :
    (H.law M).real {U | Real.sqrt (darkLabelError M (2 * n) K n t) <
        darkLabelFraction (collisionFreeDarkEvent r M K n hKM t) U} ≤
      Real.sqrt (darkLabelError M (2 * n) K n t) := by
  have hM : 0 < M := by omega
  have hNM : 2 * n ≤ M := by omega
  letI : IsProbabilityMeasure (H.law M) := H.isProbability M
  letI : Nonempty (CollisionFreeLabel M (2 * n)) :=
    collisionFreeLabelSpace_nonempty hNM
  apply mostLabelsNotDark (H.law M)
    (collisionFreeDarkEvent r M K n hKM t)
    (measurableSet_collisionFreeDarkEvent hr M K n hM hKM ht)
  · unfold darkLabelError
    have hB : 0 ≤ shiftedAnticoncentrationConstant K n :=
      (GaussianAnticoncentration.shiftedAnticoncentrationConstant_pos
        n K hn hKanti).le
    have hdelta : 0 ≤ UniformMatrixHiding.hidingRemainder M (2 * n) := by
      unfold UniformMatrixHiding.hidingRemainder
      exact le_min zero_le_one (mul_nonneg (by norm_num)
        (ultimateSquaredHidingRate_nonneg M (2 * n)))
    exact le_min zero_le_one (add_nonneg
      (mul_nonneg hB ht) hdelta)
  · exact collisionFreeDarkEvent_probability_le
      H hr M K n hn hKanti hKM ht

/-! ## Literal Haar x uniform-label additive-to-relative transfer -/

/-- Paper-specific additive-to-relative theorem.  The ambient probability
space may include arbitrary estimator randomness; only its `(label,U)`
marginal is required to be uniform-label times Haar. -/
theorem collisionFreeRandomLabelAdditiveToRelative
    {Omega : Type*} [MeasurableSpace Omega]
    {M K n : Nat}
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (labelCircuit : Omega → CollisionFreeLabel M (2 * n) ×
      Matrix.unitaryGroup (Fin M) Complex)
    (hlabelCircuit : Measurable labelCircuit)
    (deltaP : Omega → Real)
    (H : UnitaryHaarProbabilityFamily)
    {r : Real} (hr : 0 < r)
    (hn : 1 ≤ n) (hKanti : 4 * n ≤ K) (hKM : K ≤ M)
    {eta rho gamma : Real}
    (heta : 0 ≤ eta) (hrho : 0 < rho) (hgamma : 0 ≤ gamma)
    (hjoint : Measure.map labelCircuit mu =
      haarUniformCollisionFreeLaw H (by omega))
    (hadd : mu.real
      (additiveFailureEvent deltaP eta
        (gbsGaussianReferenceProbability r M K n)) ≤ gamma) :
    mu.real
        (relativeFailureEvent deltaP
          (fun omega ↦ gbsProbabilityFromScaledAmplitude r M K n
            (haarUniformCollisionFreeAmplitude M K n hKM
              (labelCircuit omega))) rho) ≤
      min 1 (gamma + shiftedAnticoncentrationConstant K n * (eta / rho) +
        UniformMatrixHiding.hidingRemainder M (2 * n)) := by
  have hM : 0 < M := by omega
  have hNM : 2 * n ≤ M := by omega
  have hamplitude : Measurable (fun omega ↦
      haarUniformCollisionFreeAmplitude M K n hKM (labelCircuit omega)) :=
    (measurable_haarUniformCollisionFreeAmplitude M K n hKM).comp
      hlabelCircuit
  have hmarginal : Measure.map
      (fun omega ↦ haarUniformCollisionFreeAmplitude M K n hKM
        (labelCircuit omega)) mu =
      scaledHaarGramHafnianLaw H M n K := by
    change Measure.map
      (haarUniformCollisionFreeAmplitude M K n hKM ∘ labelCircuit) mu = _
    rw [← Measure.map_map
      (measurable_haarUniformCollisionFreeAmplitude M K n hKM)
      hlabelCircuit]
    rw [hjoint, map_haarUniformCollisionFreeAmplitude_eq_scaledHaar
      H M K n hNM hKM]
  have ht : 0 ≤ eta / rho := div_nonneg heta hrho.le
  have hhaar := scaledHaarPhysicalSmallDenominator_uncapped
    H hr M K n hn hKanti hKM ht
  exact randomizedConversion_from_finiteHaarSmallDenominator
    mu (fun omega ↦ haarUniformCollisionFreeAmplitude M K n hKM
      (labelCircuit omega)) hamplitude deltaP H hr hM K n
      heta hrho hgamma hmarginal hadd hhaar

/-- Literal random-label specialization of the Letter's finite error budget. -/
theorem randomLabelFiniteErrorBudget
    {Omega : Type*} [MeasurableSpace Omega]
    {M K n : Nat}
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (labelCircuit : Omega → CollisionFreeLabel M (2 * n) ×
      Matrix.unitaryGroup (Fin M) Complex)
    (hlabelCircuit : Measurable labelCircuit)
    (deltaP : Omega → Real)
    (H : UnitaryHaarProbabilityFamily)
    {r : Real} (hr : 0 < r)
    (hn : 1 ≤ n) (hKanti : 4 * n ≤ K) (hKM : K ≤ M)
    {eta rho gamma deltaH deltaA : Real}
    (heta : 0 ≤ eta) (hrho : 0 < rho) (hgamma : 0 ≤ gamma)
    (hdeltaH : 0 < deltaH)
    (hjoint : Measure.map labelCircuit mu =
      haarUniformCollisionFreeLaw H (by omega))
    (hadd : mu.real
      (additiveFailureEvent deltaP eta
        (gbsGaussianReferenceProbability r M K n)) ≤ gamma)
    (hambient :
      (615172 : Real) * (((2 * n : Nat) : Real) ^ 2) / deltaH ≤ (M : Real))
    (hanti : shiftedAnticoncentrationConstant K n * (eta / rho) ≤ deltaA) :
    mu.real
        (relativeFailureEvent deltaP
          (fun omega ↦ gbsProbabilityFromScaledAmplitude r M K n
            (haarUniformCollisionFreeAmplitude M K n hKM
              (labelCircuit omega))) rho) ≤
      min 1 (gamma + deltaA + deltaH) := by
  have hmain := collisionFreeRandomLabelAdditiveToRelative
    mu labelCircuit hlabelCircuit deltaP H hr hn hKanti hKM
      heta hrho hgamma hjoint hadd
  have hMnat : 0 < M := by omega
  have hMreal : (0 : Real) < (M : Real) := by exact_mod_cast hMnat
  have hambient' :
      (615172 : Real) * (((2 * n : Nat) : Real) ^ 2) ≤
        (M : Real) * deltaH :=
    (div_le_iff₀ hdeltaH).mp hambient
  have hraw :
      615172 * ultimateSquaredHidingRate M (2 * n) ≤ deltaH := by
    unfold ultimateSquaredHidingRate
    calc
      615172 * (((2 * n : Nat) : Real) ^ 2 / (M : Real)) =
          (615172 * (((2 * n : Nat) : Real) ^ 2)) / (M : Real) := by ring
      _ ≤ deltaH := (div_le_iff₀ hMreal).2 (by
        simpa [mul_comm] using hambient')
  have hhide : UniformMatrixHiding.hidingRemainder M (2 * n) ≤ deltaH := by
    unfold UniformMatrixHiding.hidingRemainder
    exact (min_le_right _ _).trans hraw
  exact hmain.trans (min_le_min le_rfl (by linarith))

/-! ## Literal sampler composition on collision-free labels -/

/-- Ordinary hafnians depend only on nondiagonal matrix entries. -/
theorem typeHafnian_congr_offDiagonal
    {α R : Type*} [Fintype α] [LinearOrder α] [CommSemiring R]
    (A B : Matrix α α R)
    (hAB : ∀ i j, i ≠ j → A i j = B i j) :
    typeHafnian A = typeHafnian B := by
  classical
  unfold typeHafnian typeMatchingMonomial
  apply Finset.sum_congr rfl
  intro matching _
  apply Finset.prod_congr rfl
  intro i _
  exact hAB i (matching i) (matching.mate_ne i).symm

/-- Public `Fin (2n)` form: changing arbitrary diagonal entries leaves the
ordinary hafnian unchanged. -/
theorem hafnian_congr_offDiagonal
    {n : ℕ} {R : Type*} [CommSemiring R]
    (A B : Matrix (Fin (2 * n)) (Fin (2 * n)) R)
    (hAB : ∀ i j, i ≠ j → A i j = B i j) :
    hafnian A = hafnian B := by
  rw [← typeHafnian_fin_eq_hafnian A, ← typeHafnian_fin_eq_hafnian B]
  exact typeHafnian_congr_offDiagonal A B hAB

/-- Hafnian homogeneity in the ordinary `Fin (2n)` matrix representation
used by the Letter. -/
theorem hafnian_const_mul
    (n : ℕ) (c : ℂ)
    (A : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ) :
    hafnian (fun i j ↦ c * A i j) = c ^ n * hafnian A := by
  classical
  unfold hafnian matchingMonomial
  calc
    (∑ P : PerfectMatching n,
        ∏ i ∈ P.pairReps, c * A i (P i)) =
        ∑ P : PerfectMatching n,
          c ^ n * ∏ i ∈ P.pairReps, A i (P i) := by
      apply Finset.sum_congr rfl
      intro P hP
      rw [Finset.prod_mul_distrib]
      simp [P.card_pairReps]
    _ = c ^ n * ∑ P : PerfectMatching n,
        ∏ i ∈ P.pairReps, A i (P i) := by
      rw [Finset.mul_sum]

/-- Exact adapter from the adopted optical pattern probability to the scaled
hafnian intensity divided by the finite Gaussian reference variance. -/
theorem gbsProbability_div_reference_eq_scaledHafnian
    {r : ℝ} (hr : 0 < r) {M K : ℕ}
    (hM : 0 < M) (hK : 0 < K) (n : ℕ)
    (A : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ) :
    gbsCollisionFreePatternProbability r K n A /
        gbsGaussianReferenceProbability r M K n =
      Complex.normSq (hafnian (fun i j ↦ (M : ℂ) * A i j)) /
        gramHafnianSigma K n ^ 2 := by
  rw [hafnian_const_mul]
  unfold gbsCollisionFreePatternProbability
    gbsGaussianReferenceProbability scaledGBSOpticalFactor
  have hopt : equalSqueezingOpticalPrefactor r (2 * n) K ≠ 0 :=
    (equalSqueezingOpticalPrefactor_pos hr (2 * n) K).ne'
  have hMR : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hMC : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have hsigma : gramHafnianSigma K n ^ 2 ≠ 0 :=
    pow_ne_zero _ (gramHafnianSigma_pos K n hK).ne'
  rw [Complex.normSq_mul, map_pow, Complex.normSq_natCast]
  field_simp [hopt, hMR, hMC, hsigma]
  ring

theorem gbsGaussianReferenceProbability_pos
    {r : Real} (hr : 0 < r) {M K : Nat} (hM : 0 < M) (hK : 0 < K)
    (n : Nat) :
    0 < gbsGaussianReferenceProbability r M K n := by
  unfold gbsGaussianReferenceProbability
  exact mul_pos (scaledGBSOpticalFactor_pos hr hM K n)
    (pow_pos (gramHafnianSigma_pos K n hK) 2)

/-- Full-discrete sampler TV, specialized to a collision-free label subset
whose ideal masses are the physical selected-row GBS probabilities. -/
theorem collisionFreeSamplerRelative
    {chi : Type*} [Fintype chi]
    (H : UnitaryHaarProbabilityFamily)
    {r : Real} (hr : 0 < r)
    (M K n : Nat) (hn : 1 ≤ n) (hKanti : 4 * n ≤ K) (hKM : K ≤ M)
    (labels : Finset chi) (hlabels : labels.Nonempty)
    (decode : ↑labels ≃ CollisionFreeLabel M (2 * n))
    (p q : Matrix.unitaryGroup (Fin M) Complex → chi → Real)
    (hp : ∀ x, Measurable fun U ↦ p U x)
    (hq : ∀ x, Measurable fun U ↦ q U x)
    {eps zeta rho : Real}
    (heps : 0 < eps) (hzeta : 0 < zeta) (hrho : 0 < rho)
    (htv : ∀ U, finiteDiscreteTotalVariation (p U) (q U) ≤ eps)
    (hpPhysical : ∀ U (x : ↑labels), p U x =
      gbsProbabilityFromScaledAmplitude r M K n
        (collisionFreeHafnianAmplitude M K n hKM U (decode x))) :
    (∫ U, samplerRelativeFailureFraction
      (fun U (x : ↑labels) ↦ p U x)
      (fun U (x : ↑labels) ↦ q U x) rho U ∂H.law M) ≤
      min 1 (zeta + samplerRelativeConstant
        (shiftedAnticoncentrationConstant K n) eps rho
        (Nat.choose M (2 * n))
        (gbsGaussianReferenceProbability r M K n) / zeta +
        UniformMatrixHiding.hidingRemainder M (2 * n)) := by
  have hM : 0 < M := by omega
  have hK : 0 < K := by omega
  have hNM : 2 * n ≤ M := by omega
  have hpRef : 0 < gbsGaussianReferenceProbability r M K n :=
    gbsGaussianReferenceProbability_pos hr hM hK n
  have hcardNat : labels.card = Nat.choose M (2 * n) := by
    calc
      labels.card = Fintype.card ↑labels := (Fintype.card_coe labels).symm
      _ = Fintype.card (CollisionFreeLabel M (2 * n)) :=
        Fintype.card_congr decode
      _ = Nat.choose M (2 * n) := collisionFreeLabelSpace_card M (2 * n)
  let etaS : Real := 2 * eps / (zeta * labels.card)
  let threshold : Real := etaS /
    (rho * gbsGaussianReferenceProbability r M K n)
  have hetaS : 0 < etaS := by
    dsimp [etaS]
    have hcard : (0 : Real) < labels.card := by
      exact_mod_cast hlabels.card_pos
    positivity
  have hthreshold : 0 ≤ threshold := by
    dsimp [threshold]
    positivity
  have hscale : threshold * gbsGaussianReferenceProbability r M K n =
      etaS / rho := by
    dsimp [threshold]
    field_simp
  have hevent (x : ↑labels) :
      {U | p U x ≤ etaS / rho} =
        collisionFreeDarkEvent r M K n hKM threshold (decode x) := by
    ext U
    unfold collisionFreeDarkEvent scaledAmplitudeSmallDenominatorSet
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    rw [hpPhysical U x, hscale]
  letI : IsProbabilityMeasure (H.law M) := H.isProbability M
  letI : Nonempty ↑labels :=
    ⟨⟨hlabels.choose, hlabels.choose_spec⟩⟩
  have hdark :
      (∫ U, samplerDarkFraction
        (fun U (x : ↑labels) ↦ p U x) etaS rho U ∂H.law M) ≤
        shiftedAnticoncentrationConstant K n *
          (etaS / (rho * gbsGaussianReferenceProbability r M K n)) +
          UniformMatrixHiding.hidingRemainder M (2 * n) := by
    unfold samplerDarkFraction
    apply expectedDarkLabelFraction_le (H.law M)
      (fun x : ↑labels ↦ {U | p U x ≤ etaS / rho})
      (fun x ↦ measurableSet_le (hp x) measurable_const)
    intro x
    rw [hevent x]
    exact (collisionFreeDarkEvent_probability_le
      H hr M K n hn hKanti hKM hthreshold (decode x)).trans
        (min_le_right _ _)
  have hbase := samplerTVToRandomLabelRelative_relativeAccuracy
    (H.law M) labels hlabels p q hp hq heps hzeta hrho hpRef htv
    (by simpa [etaS] using hdark)
  simpa [hcardNat] using hbase

/-- Collision free sampler transfer for an arbitrary ambient output type,
using the eventwise consequence of full space total variation. -/
theorem collisionFreeSamplerRelative_eventwise
    {chi : Type*}
    (H : UnitaryHaarProbabilityFamily)
    {r : Real} (hr : 0 < r)
    (M K n : Nat) (hn : 1 ≤ n) (hKanti : 4 * n ≤ K) (hKM : K ≤ M)
    (labels : Finset chi) (hlabels : labels.Nonempty)
    (decode : ↑labels ≃ CollisionFreeLabel M (2 * n))
    (p q : Matrix.unitaryGroup (Fin M) Complex → chi → Real)
    (hp : ∀ x, Measurable fun U ↦ p U x)
    (hq : ∀ x, Measurable fun U ↦ q U x)
    {eps zeta rho : Real}
    (heps : 0 < eps) (hzeta : 0 < zeta) (hrho : 0 < rho)
    (htv : ∀ U, finiteEventTotalVariationLE (p U) (q U) eps)
    (hpPhysical : ∀ U (x : ↑labels), p U x =
      gbsProbabilityFromScaledAmplitude r M K n
        (collisionFreeHafnianAmplitude M K n hKM U (decode x))) :
    (∫ U, samplerRelativeFailureFraction
      (fun U (x : ↑labels) ↦ p U x)
      (fun U (x : ↑labels) ↦ q U x) rho U ∂H.law M) ≤
      min 1 (zeta + samplerRelativeConstant
        (shiftedAnticoncentrationConstant K n) eps rho
        (Nat.choose M (2 * n))
        (gbsGaussianReferenceProbability r M K n) / zeta +
        UniformMatrixHiding.hidingRemainder M (2 * n)) := by
  have hM : 0 < M := by omega
  have hK : 0 < K := by omega
  have hNM : 2 * n ≤ M := by omega
  have hpRef : 0 < gbsGaussianReferenceProbability r M K n :=
    gbsGaussianReferenceProbability_pos hr hM hK n
  have hcardNat : labels.card = Nat.choose M (2 * n) := by
    calc
      labels.card = Fintype.card ↑labels := (Fintype.card_coe labels).symm
      _ = Fintype.card (CollisionFreeLabel M (2 * n)) :=
        Fintype.card_congr decode
      _ = Nat.choose M (2 * n) := collisionFreeLabelSpace_card M (2 * n)
  let etaS : Real := 2 * eps / (zeta * labels.card)
  let threshold : Real := etaS /
    (rho * gbsGaussianReferenceProbability r M K n)
  have hetaS : 0 < etaS := by
    dsimp [etaS]
    have hcard : (0 : Real) < labels.card := by
      exact_mod_cast hlabels.card_pos
    positivity
  have hthreshold : 0 ≤ threshold := by
    dsimp [threshold]
    positivity
  have hscale : threshold * gbsGaussianReferenceProbability r M K n =
      etaS / rho := by
    dsimp [threshold]
    field_simp
  have hevent (x : ↑labels) :
      {U | p U x ≤ etaS / rho} =
        collisionFreeDarkEvent r M K n hKM threshold (decode x) := by
    ext U
    unfold collisionFreeDarkEvent scaledAmplitudeSmallDenominatorSet
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    rw [hpPhysical U x, hscale]
  letI : IsProbabilityMeasure (H.law M) := H.isProbability M
  letI : Nonempty ↑labels :=
    ⟨⟨hlabels.choose, hlabels.choose_spec⟩⟩
  have hdark :
      (∫ U, samplerDarkFraction
        (fun U (x : ↑labels) ↦ p U x) etaS rho U ∂H.law M) ≤
        shiftedAnticoncentrationConstant K n *
          (etaS / (rho * gbsGaussianReferenceProbability r M K n)) +
          UniformMatrixHiding.hidingRemainder M (2 * n) := by
    unfold samplerDarkFraction
    apply expectedDarkLabelFraction_le (H.law M)
      (fun x : ↑labels ↦ {U | p U x ≤ etaS / rho})
      (fun x ↦ measurableSet_le (hp x) measurable_const)
    intro x
    rw [hevent x]
    exact (collisionFreeDarkEvent_probability_le
      H hr M K n hn hKanti hKM hthreshold (decode x)).trans
        (min_le_right _ _)
  have hbase := samplerTVToRandomLabelRelative_eventwise_relativeAccuracy
    (H.law M) labels hlabels p q hp hq heps hzeta hrho hpRef htv
    (by simpa [etaS] using hdark)
  simpa [hcardNat] using hbase

/-- Square-root optimized form of the literal collision-free sampler bound. -/
theorem collisionFreeSamplerRelativeOptimized
    {failure c delta : Real} (hc : 0 < c)
    (hfailure : failure ≤ min 1 (Real.sqrt c + c / Real.sqrt c + delta)) :
    failure ≤ min 1 (2 * Real.sqrt c + delta) :=
  samplerRelativeOptimized hc hfailure

/-! ## Prospective asymptotic regime -/

/-- The three asymptotic conditions displayed in the Letter, packaged as an
adopted prospective regime rather than a complexity-theoretic conclusion.
The first field records the collision-free convention `N=2n`; the positivity
fields make the displayed real divisions physically meaningful. -/
structure ProspectiveAdvantageRegime
    (N n K M : Nat → Nat) (gamma eta rho : Nat → Real) : Prop where
  photons_eq : ∀ j, N j = 2 * n j
  n_pos : ∀ j, 0 < n j
  K_pos : ∀ j, 0 < K j
  M_pos : ∀ j, 0 < M j
  rho_pos : ∀ j, 0 < rho j
  hiding_limit : Filter.Tendsto
    (fun j ↦ ((N j : Nat) : Real) ^ 2 / (M j : Real))
    Filter.atTop (nhds 0)
  coefficient : Asymptotics.IsBigO Filter.atTop
    (fun j ↦ ((n j : Nat) : Real) ^ 2 / (K j : Real))
    (fun j ↦ Real.log (n j : Real))
  estimator : Filter.Tendsto
    (fun j ↦ gamma j + shiftedAnticoncentrationConstant (K j) (n j) *
      (eta j / rho j)) Filter.atTop (nhds 0)

/-! ## Exact sector-scale algebra -/

/-- Public endpoint for the exact cancellation of the optical sector factor
between the physical probability and its Gaussian reference scale. -/
theorem exactSectorScaleIdentity
    (r : Real) (M K n : Nat) (w : Complex) :
    gbsProbabilityFromScaledAmplitude r M K n w *
        LogdetLean.GramHafnian.gramHafnianSigma K n ^ 2 =
      gbsGaussianReferenceProbability r M K n * Complex.normSq w :=
  gbsProbability_reference_scale_identity r M K n w

/-- Exact normalized-probability identity used in the Letter. -/
theorem normalizedSectorProbability
    {r : Real} (hr : 0 < r) {M K : Nat} (hM : 0 < M) (hK : 0 < K)
    (n : Nat) (w : Complex) :
    gbsProbabilityFromScaledAmplitude r M K n w /
        gbsGaussianReferenceProbability r M K n =
      Complex.normSq w /
        LogdetLean.GramHafnian.gramHafnianSigma K n ^ 2 := by
  have hscale : scaledGBSOpticalFactor r M K n ≠ 0 :=
    (scaledGBSOpticalFactor_pos hr hM K n).ne'
  have hsigma : LogdetLean.GramHafnian.gramHafnianSigma K n ≠ 0 :=
    (LogdetLean.GramHafnian.gramHafnianSigma_pos K n hK).ne'
  unfold gbsProbabilityFromScaledAmplitude gbsGaussianReferenceProbability
  field_simp

/-- The paper's normalized physical intensity `Z=p/p_ref`, as an observable
of the scaled hafnian amplitude. -/
def normalizedPhysicalIntensity
    (r : Real) (M K n : Nat) (w : Complex) : Real :=
  gbsProbabilityFromScaledAmplitude r M K n w /
    gbsGaussianReferenceProbability r M K n

/-- Literal normalized one-label finite-Haar tail display. -/
theorem finiteHaarNormalizedPhysicalIntensityTail
    (H : UnitaryHaarProbabilityFamily)
    {r : Real} (hr : 0 < r)
    (M K n : Nat) (hn : 1 ≤ n) (hKanti : 4 * n ≤ K) (hKM : K ≤ M)
    {t : Real} (ht : 0 ≤ t) :
    (scaledHaarGramHafnianLaw H M n K).real
        {w | normalizedPhysicalIntensity r M K n w ≤ t} ≤
      min 1 (shiftedAnticoncentrationConstant K n * t +
        UniformMatrixHiding.hidingRemainder M (2 * n)) := by
  have hM : 0 < M := by omega
  have hK : 0 < K := by omega
  have hpRef : 0 < gbsGaussianReferenceProbability r M K n :=
    gbsGaussianReferenceProbability_pos hr hM hK n
  rw [show {w : Complex | normalizedPhysicalIntensity r M K n w ≤ t} =
      scaledAmplitudeSmallDenominatorSet r M K n t by
    ext w
    unfold normalizedPhysicalIntensity scaledAmplitudeSmallDenominatorSet
    exact (div_le_iff₀ hpRef).trans Iff.rfl]
  exact scaledHaarPhysicalSmallDenominator_le_darkLabelError
    H hr M K n hn hKanti hKM ht

/-- Exact sector-mass algebra conditional on the adopted equal-squeezing
total-`N`-photon formula.  The premise identifies `P_N` with the optical
factor times `sigma^2/N!`; the conclusion proves the two displayed
`D_{M,N} p_ref` forms using only the descending-factorial/binomial identity. -/
theorem sectorReferenceMass
    (r : Real) {M K n : Nat} (hM : 0 < M) (P_N : Real)
    (hTotalPhoton :
      P_N = equalSqueezingOpticalPrefactor r (2 * n) K *
        LogdetLean.GramHafnian.gramHafnianSigma K n ^ 2 /
          ((2 * n).factorial : Real)) :
    (Nat.choose M (2 * n) : Real) *
        gbsGaussianReferenceProbability r M K n =
      (M.descFactorial (2 * n) : Real) / (M : Real) ^ (2 * n) * P_N := by
  have hMreal : (M : Real) ≠ 0 := by positivity
  have hfac : (((2 * n).factorial : Nat) : Real) ≠ 0 := by positivity
  have hdesc :
      ((M.descFactorial (2 * n) : Nat) : Real) =
        (((2 * n).factorial : Nat) : Real) *
          (Nat.choose M (2 * n) : Real) := by
    exact_mod_cast Nat.descFactorial_eq_factorial_mul_choose M (2 * n)
  rw [hTotalPhoton, hdesc]
  unfold gbsGaussianReferenceProbability scaledGBSOpticalFactor
  field_simp

end

end LogdetLean.GramHafnian.ThreePaper.RelativeAccuracy

#print axioms LogdetLean.GramHafnian.ThreePaper.RelativeAccuracy.generalMarkovTradeoff
#print axioms LogdetLean.GramHafnian.ThreePaper.RelativeAccuracy.balancedMarkovTradeoff
#print axioms LogdetLean.GramHafnian.ThreePaper.RelativeAccuracy.samplerRelativeOptimized
#print axioms LogdetLean.GramHafnian.ThreePaper.RelativeAccuracy.finiteHaarTruncatedNegativeMoment
#print axioms LogdetLean.GramHafnian.ThreePaper.RelativeAccuracy.finitePanel_min_hiding_remainder
#print axioms LogdetLean.GramHafnian.ThreePaper.RelativeAccuracy.disjointGaussianPanelSmallBall_exact
#print axioms LogdetLean.GramHafnian.ThreePaper.RelativeAccuracy.disjointGaussianPanelSmallBall_transfer
#print axioms LogdetLean.GramHafnian.ThreePaper.RelativeAccuracy.disjointPanel_min_of_two
#print axioms LogdetLean.GramHafnian.ThreePaper.RelativeAccuracy.orderedHaarHafnianPanelLaw_eq_ambient
#print axioms LogdetLean.GramHafnian.ThreePaper.RelativeAccuracy.ambientHaarHafnianPanelSmallBall_union_le
#print axioms LogdetLean.GramHafnian.ThreePaper.RelativeAccuracy.orderedDisjointHaarHafnianPanelSmallBall
#print axioms LogdetLean.GramHafnian.ThreePaper.RelativeAccuracy.orderedDisjointHaarHafnianPanelSmallBall_full_qN
#print axioms LogdetLean.GramHafnian.ThreePaper.RelativeAccuracy.orderedDisjointPhysicalPanelSmallDenominator_full_qN
#print axioms LogdetLean.GramHafnian.ThreePaper.RelativeAccuracy.orderedPhysicalFinitePanelSmallDenominator
#print axioms LogdetLean.GramHafnian.ThreePaper.RelativeAccuracy.collisionFreeExpectedDarkFraction
#print axioms LogdetLean.GramHafnian.ThreePaper.RelativeAccuracy.collisionFreeMostLabelsNotDark
#print axioms LogdetLean.GramHafnian.ThreePaper.RelativeAccuracy.collisionFreeRandomLabelAdditiveToRelative
#print axioms LogdetLean.GramHafnian.ThreePaper.RelativeAccuracy.randomLabelFiniteErrorBudget
#print axioms LogdetLean.GramHafnian.ThreePaper.RelativeAccuracy.collisionFreeSamplerRelative
#print axioms LogdetLean.GramHafnian.ThreePaper.RelativeAccuracy.finiteHaarNormalizedPhysicalIntensityTail
#print axioms LogdetLean.GramHafnian.ThreePaper.RelativeAccuracy.normalizedSectorProbability
