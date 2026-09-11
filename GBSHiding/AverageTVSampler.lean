import LogdetLean.GramHafnian.ThreePaper.RelativeAccuracyApplicationEndpoints
import Mathlib.Probability.ProbabilityMassFunction.Basic

/-! Average total-variation sampling error on the full discrete outcome space.
The distributions are genuine normalized PMFs. Only their average distance,
not a uniform distance over interferometers, is bounded. -/
open MeasureTheory Set Filter
open LogdetLean.GramHafnian
open LogdetLean.GramHafnian.LocalAnticoncentration
open LogdetLean.GramHafnian.ThreePaper.RelativeAccuracy

namespace GBSHiding
noncomputable section
set_option maxHeartbeats 1600000

def pmfMass {χ : Type*} (p : PMF χ) (x : χ) : ℝ := (p x).toReal

def discreteTotalVariation {χ : Type*} (p q : PMF χ) : ℝ :=
  (∑' x, |pmfMass p x - pmfMass q x|) / 2

theorem pmfMass_summable {χ : Type*} (p : PMF χ) : Summable (pmfMass p) :=
  ENNReal.summable_toReal p.tsum_coe_ne_top

theorem pmfMass_tsum {χ : Type*} (p : PMF χ) : ∑' x, pmfMass p x = 1 := by
  simpa [pmfMass, p.tsum_coe] using (ENNReal.tsum_toReal_eq (fun x ↦ p.apply_ne_top x)).symm

theorem pmfMass_abs_sub_summable {χ : Type*} (p q : PMF χ) :
    Summable (fun x ↦ |pmfMass p x - pmfMass q x|) :=
  ((pmfMass_summable p).sub (pmfMass_summable q)).abs

theorem discreteTotalVariation_nonneg {χ : Type*} (p q : PMF χ) :
    0 ≤ discreteTotalVariation p q := by
  exact div_nonneg (tsum_nonneg (fun x ↦ abs_nonneg _)) (by norm_num)

theorem discreteTotalVariation_le_one {χ : Type*} (p q : PMF χ) :
    discreteTotalVariation p q ≤ 1 := by
  have h := (pmfMass_abs_sub_summable p q).tsum_le_tsum
    (fun x ↦ (abs_sub _ _).trans (by
      simp only [pmfMass, abs_of_nonneg ENNReal.toReal_nonneg, le_refl]))
    ((pmfMass_summable p).add (pmfMass_summable q))
  rw [(pmfMass_summable p).tsum_add (pmfMass_summable q),
    pmfMass_tsum, pmfMass_tsum] at h
  unfold discreteTotalVariation
  linarith

theorem finiteLabel_abs_error_le_two_tv {χ : Type*}
    (labels : Finset χ) (p q : PMF χ) :
    (∑ x ∈ labels, |pmfMass p x - pmfMass q x|) ≤
      2 * discreteTotalVariation p q := by
  have h := (pmfMass_abs_sub_summable p q).sum_le_tsum labels
    (fun x _ ↦ abs_nonneg (pmfMass p x - pmfMass q x))
  unfold discreteTotalVariation
  linarith

theorem discreteTotalVariation_measurable {Ω χ : Type*}
    [MeasurableSpace Ω] [Countable χ] (P Q : Ω → PMF χ)
    (hp : ∀ x, Measurable fun u ↦ pmfMass (P u) x)
    (hq : ∀ x, Measurable fun u ↦ pmfMass (Q u) x) :
    Measurable (fun u ↦ discreteTotalVariation (P u) (Q u)) := by
  apply Measurable.div_const
  exact Measurable.tsum (fun x ↦ ((hp x).sub (hq x)).abs)

theorem discreteTotalVariation_integrable {Ω χ : Type*}
    [MeasurableSpace Ω] [Countable χ] (μ : Measure Ω) [IsFiniteMeasure μ]
    (P Q : Ω → PMF χ)
    (hp : ∀ x, Measurable fun u ↦ pmfMass (P u) x)
    (hq : ∀ x, Measurable fun u ↦ pmfMass (Q u) x) :
    Integrable (fun u ↦ discreteTotalVariation (P u) (Q u)) μ := by
  refine Integrable.of_bound
    (discreteTotalVariation_measurable P Q hp hq).aestronglyMeasurable 1 ?_
  exact ae_of_all _ fun u ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (discreteTotalVariation_nonneg _ _)]
    exact discreteTotalVariation_le_one _ _

theorem darkLabelFraction_integrable {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] [Nonempty ι]
    (μ : Measure Ω) [IsFiniteMeasure μ] (E : ι → Set Ω)
    (hE : ∀ i, MeasurableSet (E i)) : Integrable (darkLabelFraction E) μ := by
  refine Integrable.of_bound (darkLabelFraction_measurable E hE).aestronglyMeasurable 1 ?_
  exact ae_of_all _ fun u ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (darkLabelFraction_nonneg _ _)]
    exact darkLabelFraction_le_one _ _

/-- Equation (4.5): the expectation over an independent uniform finite
label is a finite average, integrated over the circuit law. -/
theorem averageTV_uniformLabel_mean {Ω χ : Type*}
    [MeasurableSpace Ω] [Countable χ]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P Q : Ω → PMF χ)
    (hp : ∀ x, Measurable fun u ↦ pmfMass (P u) x)
    (hq : ∀ x, Measurable fun u ↦ pmfMass (Q u) x)
    (labels : Finset χ) (hl : labels.Nonempty)
    {eps : ℝ} (havg : (∫ u, discreteTotalVariation (P u) (Q u) ∂μ) ≤ eps) :
    (∫ u, eventwiseFiniteLabelMeanAbsError labels
      (pmfMass (P u)) (pmfMass (Q u)) ∂μ) ≤ 2 * eps / labels.card := by
  have hc : (0 : ℝ) < labels.card := by exact_mod_cast hl.card_pos
  have htvint := discreteTotalVariation_integrable μ P Q hp hq
  have hm : Measurable fun u ↦ eventwiseFiniteLabelMeanAbsError labels
      (pmfMass (P u)) (pmfMass (Q u)) := by
    unfold eventwiseFiniteLabelMeanAbsError
    fun_prop
  have hpoint (u : Ω) : eventwiseFiniteLabelMeanAbsError labels
      (pmfMass (P u)) (pmfMass (Q u)) ≤
        2 * discreteTotalVariation (P u) (Q u) / labels.card :=
    div_le_div_of_nonneg_right (finiteLabel_abs_error_le_two_tv labels _ _) hc.le
  have hmeanint : Integrable (fun u ↦ eventwiseFiniteLabelMeanAbsError labels
      (pmfMass (P u)) (pmfMass (Q u))) μ := by
    refine (htvint.const_mul 2 |>.div_const (labels.card : ℝ)).mono
      hm.aestronglyMeasurable (ae_of_all _ fun u ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by
      unfold eventwiseFiniteLabelMeanAbsError; positivity),
      Real.norm_eq_abs, abs_of_nonneg (div_nonneg (mul_nonneg (by norm_num)
        (discreteTotalVariation_nonneg _ _)) hc.le)]
    exact hpoint u
  calc
    _ ≤ ∫ u, 2 * discreteTotalVariation (P u) (Q u) / labels.card ∂μ :=
      integral_mono hmeanint (htvint.const_mul 2 |>.div_const _) hpoint
    _ = 2 * (∫ u, discreteTotalVariation (P u) (Q u) ∂μ) / labels.card := by
      rw [integral_div, integral_const_mul]
    _ ≤ 2 * eps / labels.card := by gcongr

/-- Markov's inequality after averaging over circuits. -/
theorem averageTV_uniformLabel_markov {Ω χ : Type*}
    [MeasurableSpace Ω] [Countable χ]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P Q : Ω → PMF χ)
    (hp : ∀ x, Measurable fun u ↦ pmfMass (P u) x)
    (hq : ∀ x, Measurable fun u ↦ pmfMass (Q u) x)
    (labels : Finset χ) (hl : labels.Nonempty)
    {eps zeta : ℝ} (heps : 0 < eps) (hzeta : 0 < zeta)
    (havg : (∫ u, discreteTotalVariation (P u) (Q u) ∂μ) ≤ eps) :
    (∫ u, samplerAdditiveFailureFraction
      (fun u (x : ↑labels) ↦ pmfMass (P u) x)
      (fun u (x : ↑labels) ↦ pmfMass (Q u) x)
      (2 * eps / (zeta * labels.card)) u ∂μ) ≤ zeta := by
  classical
  letI : Nonempty ↑labels := ⟨⟨hl.choose, hl.choose_spec⟩⟩
  let t := 2 * eps / (zeta * labels.card)
  have hc : (0 : ℝ) < labels.card := by exact_mod_cast hl.card_pos
  have ht : 0 < t := by dsimp [t]; positivity
  have hpoint (u : Ω) : t * samplerAdditiveFailureFraction
      (fun u (x : ↑labels) ↦ pmfMass (P u) x)
      (fun u (x : ↑labels) ↦ pmfMass (Q u) x) t u ≤
      eventwiseFiniteLabelMeanAbsError labels (pmfMass (P u)) (pmfMass (Q u)) := by
    have h := finiteUniformMarkov (fun x : ↑labels ↦ |pmfMass (P u) x - pmfMass (Q u) x|)
      (fun _ ↦ abs_nonneg _) ht le_rfl
    have heq : uniformFiniteAverage (fun x : ↑labels ↦ |pmfMass (P u) x - pmfMass (Q u) x|) =
        eventwiseFiniteLabelMeanAbsError labels (pmfMass (P u)) (pmfMass (Q u)) := by
      unfold uniformFiniteAverage eventwiseFiniteLabelMeanAbsError
      rw [← Finset.sum_attach labels (fun x ↦ |pmfMass (P u) x - pmfMass (Q u) x|),
        Finset.attach_eq_univ, Fintype.card_coe]
    rw [heq] at h
    have h' := (le_div_iff₀ ht).mp h
    simpa [samplerAdditiveFailureFraction, darkLabelFraction, Set.indicator,
      mul_comm] using h'
  have hi := darkLabelFraction_integrable μ
    (fun x : ↑labels ↦ {u | t < |pmfMass (P u) x - pmfMass (Q u) x|})
    (fun x ↦ measurableSet_lt measurable_const ((hp x).sub (hq x)).abs)
  have hmean := averageTV_uniformLabel_mean μ P Q hp hq labels hl havg
  have hmeanint : Integrable (fun u ↦ eventwiseFiniteLabelMeanAbsError labels
      (pmfMass (P u)) (pmfMass (Q u))) μ := by
    unfold eventwiseFiniteLabelMeanAbsError
    apply Integrable.div_const
    apply integrable_finsetSum
    intro x _
    refine Integrable.of_bound (((hp x).sub (hq x)).abs.aestronglyMeasurable) 2 ?_
    exact ae_of_all _ fun u ↦ by
      rw [Real.norm_eq_abs, abs_abs]
      have hp1 : pmfMass (P u) x ≤ 1 := by
        exact ENNReal.toReal_mono ENNReal.one_ne_top ((P u).coe_le_one x)
      have hq1 : pmfMass (Q u) x ≤ 1 := by
        exact ENNReal.toReal_mono ENNReal.one_ne_top ((Q u).coe_le_one x)
      have hp0 : 0 ≤ pmfMass (P u) x := ENNReal.toReal_nonneg
      have hq0 : 0 ≤ pmfMass (Q u) x := ENNReal.toReal_nonneg
      exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hh := (integral_mono (hi.const_mul t) hmeanint hpoint).trans hmean
  rw [integral_const_mul] at hh
  have htcalc : t * zeta = 2 * eps / labels.card := by dsimp [t]; field_simp
  rw [← htcalc] at hh
  exact (mul_le_mul_iff_right₀ ht).mp hh

/-- Averaged total variation and an averaged small-denominator estimate
give the relative-error bound. The latter premise is instantiated with the
proved Route 1 hafnian bound in the physical endpoint below. -/
theorem averageTV_sampler_relative {Ω χ : Type*}
    [MeasurableSpace Ω] [Countable χ]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P Q : Ω → PMF χ)
    (hp : ∀ x, Measurable fun u ↦ pmfMass (P u) x)
    (hq : ∀ x, Measurable fun u ↦ pmfMass (Q u) x)
    (labels : Finset χ) (hl : labels.Nonempty)
    {eps zeta rho darkBound : ℝ}
    (heps : 0 < eps) (hzeta : 0 < zeta) (hrho : 0 < rho)
    (havg : (∫ u, discreteTotalVariation (P u) (Q u) ∂μ) ≤ eps)
    (hdark : (∫ u, samplerDarkFraction
      (fun u (x : ↑labels) ↦ pmfMass (P u) x)
      (2 * eps / (zeta * labels.card)) rho u ∂μ) ≤ darkBound) :
    (∫ u, samplerRelativeFailureFraction
      (fun u (x : ↑labels) ↦ pmfMass (P u) x)
      (fun u (x : ↑labels) ↦ pmfMass (Q u) x) rho u ∂μ) ≤
      min 1 (zeta + darkBound) := by
  letI : Nonempty ↑labels := ⟨⟨hl.choose, hl.choose_spec⟩⟩
  let p := fun u (x : ↑labels) ↦ pmfMass (P u) x
  let q := fun u (x : ↑labels) ↦ pmfMass (Q u) x
  let t := 2 * eps / (zeta * labels.card)
  have hri : Integrable (samplerRelativeFailureFraction p q rho) μ :=
    darkLabelFraction_integrable μ _ (fun x ↦
      measurableSet_lt (measurable_const.mul (hp x)) ((hp x).sub (hq x)).abs)
  have hai : Integrable (samplerAdditiveFailureFraction p q t) μ :=
    darkLabelFraction_integrable μ _ (fun x ↦
      measurableSet_lt measurable_const ((hp x).sub (hq x)).abs)
  have hdi : Integrable (samplerDarkFraction p t rho) μ :=
    darkLabelFraction_integrable μ _ (fun x ↦ measurableSet_le (hp x) measurable_const)
  refine le_min ?_ ?_
  · calc
      _ ≤ ∫ _u, (1 : ℝ) ∂μ :=
        integral_mono hri (integrable_const _) (fun u ↦ darkLabelFraction_le_one _ _)
      _ = 1 := by simp
  · calc
      _ ≤ ∫ u, samplerAdditiveFailureFraction p q t u +
          samplerDarkFraction p t rho u ∂μ :=
        integral_mono hri (hai.add hdi)
          (samplerRelativeFailureFraction_le_additive_add_dark p q hrho)
      _ = (∫ u, samplerAdditiveFailureFraction p q t u ∂μ) +
          ∫ u, samplerDarkFraction p t rho u ∂μ := integral_add hai hdi
      _ ≤ zeta + darkBound := add_le_add
        (averageTV_uniformLabel_markov μ P Q hp hq labels hl heps hzeta havg) hdark

/-- Corollary 4.2, Route 1, with the full outcome distributions and only
their average total variation as sampler input. -/
theorem collisionFreeSamplerRelative_averageTV_pos
    {χ : Type*} [Countable χ] (H : UnitaryHaarProbabilityFamily)
    {r : ℝ} (hr : 0 < r) (M K n : ℕ)
    (hn : 1 ≤ n) (hKanti : 4 * n ≤ K) (hKM : K ≤ M)
    (labels : Finset χ) (hlabels : labels.Nonempty)
    (decode : ↑labels ≃ CollisionFreeLabel M (2 * n))
    (P Q : Matrix.unitaryGroup (Fin M) ℂ → PMF χ)
    (hp : ∀ x, Measurable fun U ↦ pmfMass (P U) x)
    (hq : ∀ x, Measurable fun U ↦ pmfMass (Q U) x)
    {eps zeta rho : ℝ}
    (heps : 0 < eps) (hzeta : 0 < zeta) (hrho : 0 < rho)
    (havg : (∫ U, discreteTotalVariation (P U) (Q U) ∂H.law M) ≤ eps)
    (hpPhysical : ∀ U (x : ↑labels), pmfMass (P U) x =
      gbsProbabilityFromScaledAmplitude r M K n
        (collisionFreeHafnianAmplitude M K n hKM U (decode x))) :
    (∫ U, samplerRelativeFailureFraction
      (fun U (x : ↑labels) ↦ pmfMass (P U) x)
      (fun U (x : ↑labels) ↦ pmfMass (Q U) x) rho U ∂H.law M) ≤
      min 1 (zeta + samplerRelativeConstant
        (shiftedAnticoncentrationConstant K n) eps rho
        (Nat.choose M (2 * n)) (gbsGaussianReferenceProbability r M K n) / zeta +
        ThreePaper.UniformMatrixHiding.hidingRemainder M (2 * n)) := by
  have hM : 0 < M := by omega
  have hK : 0 < K := by omega
  have hpRef := gbsGaussianReferenceProbability_pos hr hM hK n
  have hcardNat : labels.card = Nat.choose M (2 * n) := by
    calc
      labels.card = Fintype.card ↑labels := (Fintype.card_coe labels).symm
      _ = Fintype.card (CollisionFreeLabel M (2 * n)) := Fintype.card_congr decode
      _ = _ := collisionFreeLabelSpace_card M (2 * n)
  let etaS : ℝ := 2 * eps / (zeta * labels.card)
  let threshold := etaS / (rho * gbsGaussianReferenceProbability r M K n)
  have hetaS : 0 < etaS := by
    dsimp [etaS]
    have hc : (0 : ℝ) < labels.card := by exact_mod_cast hlabels.card_pos
    positivity
  have hthreshold : 0 ≤ threshold := by dsimp [threshold]; positivity
  have hscale : threshold * gbsGaussianReferenceProbability r M K n = etaS / rho := by
    dsimp [threshold]
    field_simp
  have hevent (x : ↑labels) : {U | pmfMass (P U) x ≤ etaS / rho} =
      collisionFreeDarkEvent r M K n hKM threshold (decode x) := by
    ext U
    unfold collisionFreeDarkEvent scaledAmplitudeSmallDenominatorSet
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    rw [hpPhysical U x, hscale]
  letI : IsProbabilityMeasure (H.law M) := H.isProbability M
  letI : Nonempty ↑labels := ⟨⟨hlabels.choose, hlabels.choose_spec⟩⟩
  have hdark : (∫ U, samplerDarkFraction
      (fun U (x : ↑labels) ↦ pmfMass (P U) x) etaS rho U ∂H.law M) ≤
      shiftedAnticoncentrationConstant K n * threshold +
        ThreePaper.UniformMatrixHiding.hidingRemainder M (2 * n) := by
    unfold samplerDarkFraction
    apply expectedDarkLabelFraction_le (H.law M)
      (fun x : ↑labels ↦ {U | pmfMass (P U) x ≤ etaS / rho})
      (fun x ↦ measurableSet_le (hp x) measurable_const)
    intro x
    rw [hevent x]
    exact (collisionFreeDarkEvent_probability_le
      H hr M K n hn hKanti hKM hthreshold (decode x)).trans (min_le_right _ _)
  have hh := averageTV_sampler_relative (H.law M) P Q hp hq labels hlabels
    heps hzeta hrho havg hdark
  convert hh using 1
  unfold samplerRelativeConstant threshold etaS
  rw [hcardNat]
  field_simp
  <;> ring

/-- Continuity extends a positive-error bound to zero sampling error. -/
theorem le_at_nonnegative_parameter {f : ℝ → ℝ} {eps F : ℝ}
    (hf : Continuous f) (h : ∀ e, eps < e → F ≤ f e) : F ≤ f eps := by
  have ht : Tendsto (fun j : ℕ ↦ eps + 1 / ((j : ℝ) + 1)) atTop (nhds eps) := by
    simpa using (tendsto_const_nhds (x := eps)).add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  apply ge_of_tendsto' (hf.continuousAt.tendsto.comp ht)
  intro j
  exact h _ (lt_add_of_pos_right _ (by positivity))


/-- Corollary 4.2 includes zero average sampling error. -/
theorem collisionFreeSamplerRelative_averageTV
    {χ : Type*} [Countable χ] (H : UnitaryHaarProbabilityFamily)
    {r : ℝ} (hr : 0 < r) (M K n : ℕ)
    (hn : 1 ≤ n) (hKanti : 4 * n ≤ K) (hKM : K ≤ M)
    (labels : Finset χ) (hlabels : labels.Nonempty)
    (decode : ↑labels ≃ CollisionFreeLabel M (2 * n))
    (P Q : Matrix.unitaryGroup (Fin M) ℂ → PMF χ)
    (hp : ∀ x, Measurable fun U ↦ pmfMass (P U) x)
    (hq : ∀ x, Measurable fun U ↦ pmfMass (Q U) x)
    {eps zeta rho : ℝ}
    (heps : 0 ≤ eps) (hzeta : 0 < zeta) (hrho : 0 < rho)
    (havg : (∫ U, discreteTotalVariation (P U) (Q U) ∂H.law M) ≤ eps)
    (hpPhysical : ∀ U (x : ↑labels), pmfMass (P U) x =
      gbsProbabilityFromScaledAmplitude r M K n
        (collisionFreeHafnianAmplitude M K n hKM U (decode x))) :
    (∫ U, samplerRelativeFailureFraction
      (fun U (x : ↑labels) ↦ pmfMass (P U) x)
      (fun U (x : ↑labels) ↦ pmfMass (Q U) x) rho U ∂H.law M) ≤
      min 1 (zeta + samplerRelativeConstant
        (shiftedAnticoncentrationConstant K n) eps rho
        (Nat.choose M (2 * n)) (gbsGaussianReferenceProbability r M K n) / zeta +
        ThreePaper.UniformMatrixHiding.hidingRemainder M (2 * n)) := by
  apply le_at_nonnegative_parameter
    (f := fun e ↦ min 1 (zeta + samplerRelativeConstant
      (shiftedAnticoncentrationConstant K n) e rho (Nat.choose M (2*n))
      (gbsGaussianReferenceProbability r M K n) / zeta +
      ThreePaper.UniformMatrixHiding.hidingRemainder M (2*n)))
  · unfold samplerRelativeConstant
    fun_prop
  · intro e he
    exact collisionFreeSamplerRelative_averageTV_pos H hr M K n hn hKanti hKM
      labels hlabels decode P Q hp hq (lt_of_le_of_lt heps he) hzeta hrho
      (havg.trans he.le) hpPhysical

/-- Optimized Route 1 sampler bound, including zero error. -/
theorem collisionFreeSamplerRelativeOptimized_averageTV
    {χ : Type*} [Countable χ] (H : UnitaryHaarProbabilityFamily)
    {r : ℝ} (hr : 0 < r) (M K n : ℕ)
    (hn : 1 ≤ n) (hKanti : 4 * n ≤ K) (hKM : K ≤ M)
    (labels : Finset χ) (hlabels : labels.Nonempty)
    (decode : ↑labels ≃ CollisionFreeLabel M (2 * n))
    (P Q : Matrix.unitaryGroup (Fin M) ℂ → PMF χ)
    (hp : ∀ x, Measurable fun U ↦ pmfMass (P U) x)
    (hq : ∀ x, Measurable fun U ↦ pmfMass (Q U) x)
    {eps rho : ℝ}
    (heps : 0 ≤ eps) (hrho : 0 < rho)
    (havg : (∫ U, discreteTotalVariation (P U) (Q U) ∂H.law M) ≤ eps)
    (hpPhysical : ∀ U (x : ↑labels), pmfMass (P U) x =
      gbsProbabilityFromScaledAmplitude r M K n
        (collisionFreeHafnianAmplitude M K n hKM U (decode x))) :
    (∫ U, samplerRelativeFailureFraction
      (fun U (x : ↑labels) ↦ pmfMass (P U) x)
      (fun U (x : ↑labels) ↦ pmfMass (Q U) x) rho U ∂H.law M) ≤
      min 1 (ThreePaper.UniformMatrixHiding.hidingRemainder M (2 * n) +
        2 * Real.sqrt (samplerRelativeConstant
          (shiftedAnticoncentrationConstant K n) eps rho
          (Nat.choose M (2 * n)) (gbsGaussianReferenceProbability r M K n))) := by
  have hM : 0 < M := by omega
  have hpRef := gbsGaussianReferenceProbability_pos hr hM (show 0 < K by omega) n
  have hD : (0 : ℝ) < Nat.choose M (2*n) := by
    exact_mod_cast Nat.choose_pos (show 2*n ≤ M by omega)
  have hB := ThreePaper.GaussianAnticoncentration.shiftedAnticoncentrationConstant_pos
    n K hn hKanti
  apply le_at_nonnegative_parameter
    (f := fun e ↦ min 1 (ThreePaper.UniformMatrixHiding.hidingRemainder M (2*n) +
      2 * Real.sqrt (samplerRelativeConstant (shiftedAnticoncentrationConstant K n)
        e rho (Nat.choose M (2*n)) (gbsGaussianReferenceProbability r M K n))))
  · unfold samplerRelativeConstant
    fun_prop
  · intro e he
    have he0 : 0 < e := lt_of_le_of_lt heps he
    let A := samplerRelativeConstant (shiftedAnticoncentrationConstant K n)
      e rho (Nat.choose M (2*n)) (gbsGaussianReferenceProbability r M K n)
    have hA : 0 < A := by unfold A samplerRelativeConstant; positivity
    have hh := collisionFreeSamplerRelative_averageTV_pos H hr M K n hn hKanti hKM
      labels hlabels decode P Q hp hq he0 (Real.sqrt_pos.mpr hA) hrho
      (havg.trans he.le) hpPhysical
    change _ ≤ min 1 (Real.sqrt A + A / Real.sqrt A + _) at hh
    rw [samplerSqrtChoice_exact hA] at hh
    simpa [A, add_comm] using hh

end
end GBSHiding
