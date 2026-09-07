import LogdetLean.GramHafnian.ThreePaper.GaussianAnticoncentration
import LogdetLean.GramHafnian.ThreePaper.UniformMatrixHiding
import LogdetLean.GramHafnian.ThreePaper.RelativeAccuracyApplicationEndpoints
import LogdetLean.GramHafnian.ThreePaper.TwoMethodComparison
import LogdetLean.GramHafnian.ThreePaper.CoefficientAsymptoticComparison
import LogdetLean.GramHafnian.ThreePaper.FairAbsoluteThresholdComparison
import LogdetLean.GramHafnian.ThreePaper.RouteTwoMatrixComparisonInterface
import LogdetLean.GramHafnian.UltimateHiding.SquaredGBS

/-!
# Physical Review Letters endpoint: interaction of the two Articles

This module takes the two matrix-law endpoint modules as its only scientific
inputs and proves the new Letter result from them.  The additional
`SquaredGBS` import supplies only the common optical-scaling definitions and
elementary conversion lemmas.  This file neither re-proves the Gaussian
small-ball theorem nor reopens the hiding argument.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.ThreePaper.RelativeAccuracy

noncomputable section

open LocalAnticoncentration UltimateHiding
open GaussianAnticoncentration UniformMatrixHiding

/-- Hiding plus anticoncentration gives a finite-Haar shifted hafnian disk
bound for every `1 <= n`, `4 n <= K <= M`. -/
theorem finiteHaarShiftedSmallBall
    (H : UnitaryHaarProbabilityFamily)
    {M n K : ℕ} (hn : 1 ≤ n) (hK : 4 * n ≤ K) (hKM : K ≤ M)
    (z : ℂ) (eps : ℝ) (heps : 0 ≤ eps) :
    (scaledHaarGramHafnianLaw H M n K).real
        (shiftedComplexDisk z (eps * gramHafnianSigma K n)) ≤
      min 1
        (shiftedAnticoncentrationConstant K n * eps ^ 2 +
          615172 * ultimateSquaredHidingRate M (2 * n)) := by
  have hNM : 2 * n ≤ M := by omega
  have hNK : 2 * n ≤ K := by omega
  have hNpos : 1 ≤ 2 * n := by omega
  have htvMatrix := matrixLaw.apply H hNpos hNK hKM
  have htvHafnian := htvMatrix.map (measurable_hafnianMatrixObservable n)
  have htv : probabilityTotalVariationLE
      (scaledHaarGramHafnianLaw H M n K)
      (gaussianGramHafnianLaw n K)
      (min 1 (615172 * ultimateSquaredHidingRate M (2 * n))) := by
    simpa [scaledHaarGramHafnianLaw, gaussianGramHafnianLaw] using htvHafnian
  letI : IsProbabilityMeasure (scaledHaarGramHafnianLaw H M n K) :=
    scaledHaarGramHafnianLaw_isProbability H hNM hKM
  have htransfer := htv.event_le
    (measurableSet_shiftedComplexDisk z (eps * gramHafnianSigma K n))
  rw [gaussianGramHafnianLaw_shiftedDisk_eq] at htransfer
  have hgaussian := shiftedSmallBall_uncapped n K hn hK z eps heps
  apply le_min measureReal_le_one
  calc
    (scaledHaarGramHafnianLaw H M n K).real
        (shiftedComplexDisk z (eps * gramHafnianSigma K n)) ≤
        gramHafnianShiftedSmallBallProbability K n z eps +
          min 1 (615172 * ultimateSquaredHidingRate M (2 * n)) := htransfer
    _ ≤ shiftedAnticoncentrationConstant K n * eps ^ 2 +
          615172 * ultimateSquaredHidingRate M (2 * n) :=
      add_le_add hgaussian (min_le_right _ _)

/-- Zero-center specialization controlling the physical small denominator. -/
theorem gbsSmallDenominator
    (H : UnitaryHaarProbabilityFamily)
    {r : ℝ} (hr : 0 < r)
    {M n K : ℕ} (hn : 1 ≤ n) (hK : 4 * n ≤ K) (hKM : K ≤ M)
    {t : ℝ} (ht : 0 ≤ t) :
    (scaledHaarGramHafnianLaw H M n K).real
        (scaledAmplitudeSmallDenominatorSet r M K n t) ≤
      min 1
        (shiftedAnticoncentrationConstant K n * t +
          615172 * ultimateSquaredHidingRate M (2 * n)) := by
  have hM : 0 < M := by omega
  rw [scaledAmplitudeSmallDenominatorSet_eq_shiftedComplexDisk
    hr hM K n ht]
  have h := finiteHaarShiftedSmallBall H hn hK hKM
    0 (Real.sqrt t) (Real.sqrt_nonneg t)
  simpa [Real.sq_sqrt ht] using h

/-- Main manuscript computational consequence.  A normalized additive estimator
becomes a relative estimator except with the sum of its additive-failure
probability, the Gaussian small-denominator term, and the hiding error. -/
theorem randomizedAdditiveToRelative
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (amplitude : Ω → ℂ) (hamplitude : Measurable amplitude)
    (deltaP : Ω → ℝ)
    (H : UnitaryHaarProbabilityFamily)
    {r : ℝ} (hr : 0 < r) {M n K : ℕ}
    (hn : 1 ≤ n) (hK : 4 * n ≤ K) (hKM : K ≤ M)
    {eta rho gamma : ℝ}
    (heta : 0 ≤ eta) (hrho : 0 < rho) (hgamma : 0 ≤ gamma)
    (hmarginal : Measure.map amplitude μ =
      scaledHaarGramHafnianLaw H M n K)
    (hadd : μ.real
      (additiveFailureEvent deltaP eta
        (gbsGaussianReferenceProbability r M K n)) ≤ gamma) :
    μ.real
        (relativeFailureEvent deltaP
          (fun omega ↦
            gbsProbabilityFromScaledAmplitude r M K n (amplitude omega))
          rho) ≤
      min 1
        (gamma + shiftedAnticoncentrationConstant K n * (eta / rho) +
          615172 * ultimateSquaredHidingRate M (2 * n)) := by
  have hM : 0 < M := by omega
  have ht : 0 ≤ eta / rho := div_nonneg heta hrho.le
  have hhaar := gbsSmallDenominator H hr hn hK hKM ht
  have hhaar' :
      (scaledHaarGramHafnianLaw H M n K).real
          (scaledAmplitudeSmallDenominatorSet r M K n (eta / rho)) ≤
        shiftedAnticoncentrationConstant K n * (eta / rho) +
          615172 * ultimateSquaredHidingRate M (2 * n) :=
    hhaar.trans (min_le_right _ _)
  exact randomizedConversion_from_finiteHaarSmallDenominator
    μ amplitude hamplitude deltaP H hr hM K n
    heta hrho hgamma hmarginal hadd hhaar'

/-- Explicit finite error-budget form of the manuscript result.  The first displayed
budget is exactly the ambient inequality from the paper; the second allocates
at most deltaA to the Gaussian small-denominator term. -/
theorem finiteErrorBudget
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (amplitude : Ω → ℂ) (hamplitude : Measurable amplitude)
    (deltaP : Ω → ℝ)
    (H : UnitaryHaarProbabilityFamily)
    {r : ℝ} (hr : 0 < r) {M n K : ℕ}
    (hn : 1 ≤ n) (hK : 4 * n ≤ K) (hKM : K ≤ M)
    {eta rho gamma deltaH deltaA : ℝ}
    (heta : 0 ≤ eta) (hrho : 0 < rho) (hgamma : 0 ≤ gamma)
    (hdeltaH : 0 < deltaH)
    (hmarginal : Measure.map amplitude μ =
      scaledHaarGramHafnianLaw H M n K)
    (hadd : μ.real
      (additiveFailureEvent deltaP eta
        (gbsGaussianReferenceProbability r M K n)) ≤ gamma)
    (hambient :
      (615172 : ℝ) * (((2 * n : ℕ) : ℝ) ^ 2) / deltaH ≤ (M : ℝ))
    (hanti :
      shiftedAnticoncentrationConstant K n * (eta / rho) ≤ deltaA) :
    μ.real
        (relativeFailureEvent deltaP
          (fun omega ↦
            gbsProbabilityFromScaledAmplitude r M K n (amplitude omega))
          rho) ≤
      min 1 (gamma + deltaA + deltaH) := by
  have hmain := randomizedAdditiveToRelative
    μ amplitude hamplitude deltaP H hr hn hK hKM
    heta hrho hgamma hmarginal hadd
  have hMnat : 0 < M := by omega
  have hMreal : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hMnat
  have hambient' :
      (615172 : ℝ) * (((2 * n : ℕ) : ℝ) ^ 2) ≤
        (M : ℝ) * deltaH :=
    (div_le_iff₀ hdeltaH).mp hambient
  have hhide :
      615172 * ultimateSquaredHidingRate M (2 * n) ≤ deltaH := by
    unfold ultimateSquaredHidingRate
    calc
      615172 * (((2 * n : ℕ) : ℝ) ^ 2 / (M : ℝ)) =
          (615172 * (((2 * n : ℕ) : ℝ) ^ 2)) / (M : ℝ) := by ring
      _ ≤ deltaH := (div_le_iff₀ hMreal).2 (by
        simpa [mul_comm] using hambient')
  have hsum :
      gamma + shiftedAnticoncentrationConstant K n * (eta / rho) +
          615172 * ultimateSquaredHidingRate M (2 * n) ≤
        gamma + deltaA + deltaH := by
    linarith
  exact hmain.trans (min_le_min le_rfl hsum)

/-! ## Random labels, circuitwise prevalence, and finite panels -/

/-- Markov's inequality upgrades an expected dark-label fraction `≤ e` to:
all but a `sqrt e` fraction of circuits have dark-label fraction `≤ sqrt e`.
The zero-error case is excluded from this numerical form and is immediate by
the vanishing-integral lemma. -/
theorem mostCircuitsMostLabels
    {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu]
    (darkFraction : Ω → ℝ)
    (hdark_nonneg : ∀ᵐ ω ∂mu, 0 ≤ darkFraction ω)
    (hdark_int : Integrable darkFraction mu)
    {e : ℝ} (he : 0 < e)
    (hexpect : ∫ ω, darkFraction ω ∂mu ≤ e) :
    mu.real {ω | Real.sqrt e < darkFraction ω} ≤ Real.sqrt e := by
  have hsqrt : 0 < Real.sqrt e := Real.sqrt_pos.2 he
  have hsubset : {ω | Real.sqrt e < darkFraction ω} ⊆
      {ω | Real.sqrt e ≤ darkFraction ω} := by
    intro omega homega
    show Real.sqrt e ≤ darkFraction omega
    exact le_of_lt homega
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    hdark_nonneg hdark_int (Real.sqrt e)
  have hmul : Real.sqrt e *
      mu.real {ω | Real.sqrt e < darkFraction ω} ≤
      ∫ ω, darkFraction ω ∂mu := by
    calc
      Real.sqrt e * mu.real {ω | Real.sqrt e < darkFraction ω} ≤
          Real.sqrt e * mu.real {ω | Real.sqrt e ≤ darkFraction ω} :=
        mul_le_mul_of_nonneg_left (measureReal_mono hsubset) hsqrt.le
      _ ≤ ∫ ω, darkFraction ω ∂mu := hmarkov
  apply le_of_mul_le_mul_left
  calc
    Real.sqrt e * mu.real {ω | Real.sqrt e < darkFraction ω} ≤ e :=
      hmul.trans hexpect
    _ = Real.sqrt e * Real.sqrt e := by
      rw [Real.mul_self_sqrt he.le]
  exact hsqrt

/-- The random-label additive-to-relative endpoint is the existing joint-space
conversion theorem, now exported under the Letter's application name. -/
theorem randomLabelAdditiveToRelative
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (amplitude : Ω → ℂ) (hamplitude : Measurable amplitude)
    (deltaP : Ω → ℝ)
    (H : UnitaryHaarProbabilityFamily)
    {r : ℝ} (hr : 0 < r) {M n K : ℕ}
    (hn : 1 ≤ n) (hK : 4 * n ≤ K) (hKM : K ≤ M)
    {eta rho gamma : ℝ}
    (heta : 0 ≤ eta) (hrho : 0 < rho) (hgamma : 0 ≤ gamma)
    (hmarginal : Measure.map amplitude μ =
      scaledHaarGramHafnianLaw H M n K)
    (hadd : μ.real
      (additiveFailureEvent deltaP eta
        (gbsGaussianReferenceProbability r M K n)) ≤ gamma) :
    μ.real
        (relativeFailureEvent deltaP
          (fun omega ↦
            gbsProbabilityFromScaledAmplitude r M K n (amplitude omega))
          rho) ≤
      min 1
        (gamma + shiftedAnticoncentrationConstant K n * (eta / rho) +
          615172 * ultimateSquaredHidingRate M (2 * n)) :=
  randomizedAdditiveToRelative μ amplitude hamplitude deltaP H hr
    hn hK hKM heta hrho hgamma hmarginal hadd

/-- Total-variation sampler interface in its analytic finite-label form.
If the uniform-label mean absolute probability error is at most
`2 eps / D`, then at most a `zeta` fraction of labels have error larger than
`2 eps / (zeta D)`. -/
theorem samplerTVInterface
    {Ω : Type*} [MeasurableSpace Ω]
    (uniformLabel : Measure Ω) [IsProbabilityMeasure uniformLabel]
    (p q : Ω → ℝ)
    (hpq_int : Integrable (fun s ↦ |p s - q s|) uniformLabel)
    {eps zeta D : ℝ} (heps : 0 < eps) (hzeta : 0 < zeta) (hD : 0 < D)
    (hmean : (∫ s, |p s - q s| ∂uniformLabel) ≤ 2 * eps / D) :
    uniformLabel.real
        {s | 2 * eps / (zeta * D) < |p s - q s|} ≤ zeta := by
  let threshold : ℝ := 2 * eps / (zeta * D)
  have hthreshold : 0 < threshold := by
    dsimp [threshold]
    positivity
  have hsubset : {s | threshold < |p s - q s|} ⊆
      {s | threshold ≤ |p s - q s|} := by
    intro s hs
    show threshold ≤ |p s - q s|
    exact le_of_lt hs
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun s ↦ abs_nonneg (p s - q s))
    hpq_int threshold
  have hmul : threshold *
      uniformLabel.real {s | threshold < |p s - q s|} ≤
      2 * eps / D := by
    calc
      threshold * uniformLabel.real {s | threshold < |p s - q s|} ≤
          threshold * uniformLabel.real {s | threshold ≤ |p s - q s|} :=
        mul_le_mul_of_nonneg_left (measureReal_mono hsubset) hthreshold.le
      _ ≤ ∫ s, |p s - q s| ∂uniformLabel := hmarkov
      _ ≤ 2 * eps / D := hmean
  apply le_of_mul_le_mul_left
  calc
    threshold *
        uniformLabel.real {s | 2 * eps / (zeta * D) < |p s - q s|} =
        threshold *
          uniformLabel.real {s | threshold < |p s - q s|} := by
      rfl
    _ ≤ 2 * eps / D := hmul
    _ = threshold * zeta := by
      dsimp [threshold]
      field_simp
  exact hthreshold

/-- Panel application: one common hiding transfer plus a Gaussian union bound gives the
finite-panel estimate.  The Gaussian bound can be `q B t`; the hiding term is
paid once at the union size `L`. -/
theorem finitePanelEventTransfer
    {α : Type*} [MeasurableSpace α]
    (haar gaussian : Measure α) {delta gaussianBound : ℝ}
    (htv : probabilityTotalVariationLE haar gaussian delta)
    (bad : Set α) (hbad : MeasurableSet bad)
    (hgaussian : gaussian.real bad ≤ gaussianBound) :
    haar.real bad ≤ gaussianBound + delta := by
  exact (htv.event_le hbad).trans
    (by simpa [add_comm] using (add_le_add_right hgaussian delta))

/-- Panel application, disjoint-panel specialization.  Independence enters only through
the explicit Gaussian sharp-union hypothesis; hiding is still paid once. -/
theorem disjointPanelEventTransfer
    {α : Type*} [MeasurableSpace α]
    (haar gaussian : Measure α) {delta sharpGaussianBound : ℝ}
    (htv : probabilityTotalVariationLE haar gaussian delta)
    (bad : Set α) (hbad : MeasurableSet bad)
    (hgaussianIndependent : gaussian.real bad ≤ sharpGaussianBound) :
    haar.real bad ≤ sharpGaussianBound + delta :=
  finitePanelEventTransfer haar gaussian htv bad hbad hgaussianIndependent

end

end LogdetLean.GramHafnian.ThreePaper.RelativeAccuracy

#print axioms LogdetLean.GramHafnian.ThreePaper.RelativeAccuracy.finiteHaarShiftedSmallBall
#print axioms LogdetLean.GramHafnian.ThreePaper.RelativeAccuracy.gbsSmallDenominator
#print axioms LogdetLean.GramHafnian.ThreePaper.RelativeAccuracy.randomizedAdditiveToRelative
#print axioms LogdetLean.GramHafnian.ThreePaper.RelativeAccuracy.finiteErrorBudget
#print axioms LogdetLean.GramHafnian.ThreePaper.RelativeAccuracy.balancedMarkovTradeoff
#print axioms LogdetLean.GramHafnian.ThreePaper.RelativeAccuracy.samplerRelativeOptimized
#print axioms LogdetLean.GramHafnian.ThreePaper.RelativeAccuracy.finiteHaarTruncatedNegativeMoment
#print axioms LogdetLean.GramHafnian.ThreePaper.RelativeAccuracy.finiteHaarTruncatedNormalizedIntensityNegativeMoment
#print axioms LogdetLean.GramHafnian.ThreePaper.RelativeAccuracy.collisionFreeLabelSpace_card
#print axioms LogdetLean.GramHafnian.ThreePaper.RelativeAccuracy.mostLabelsNotDark
#print axioms LogdetLean.GramHafnian.ThreePaper.RelativeAccuracy.circuitwiseConditionalFailure
#print axioms LogdetLean.GramHafnian.ThreePaper.RelativeAccuracy.samplerTVToUniformLabelAdditive
#print axioms LogdetLean.GramHafnian.ThreePaper.RelativeAccuracy.samplerTVToRandomLabelRelative_relativeAccuracy
#print axioms LogdetLean.GramHafnian.ThreePaper.RelativeAccuracy.disjointGaussianPanelSmallBall_exact
#print axioms LogdetLean.GramHafnian.ThreePaper.RelativeAccuracy.disjointGaussianPanelSmallBall_transfer
#print axioms LogdetLean.GramHafnian.ThreePaper.RelativeAccuracy.disjointPanel_min_of_two
#print axioms LogdetLean.GramHafnian.ThreePaper.RelativeAccuracy.orderedHaarHafnianPanelLaw_eq_ambient
#print axioms LogdetLean.GramHafnian.ThreePaper.RelativeAccuracy.ambientHaarHafnianPanelSmallBall_union_le
#print axioms LogdetLean.GramHafnian.ThreePaper.RelativeAccuracy.orderedDisjointHaarHafnianPanelSmallBall_full_qN
#print axioms LogdetLean.GramHafnian.ThreePaper.RelativeAccuracy.orderedDisjointPhysicalPanelSmallDenominator_full_qN
#print axioms LogdetLean.GramHafnian.ThreePaper.RelativeAccuracy.orderedPhysicalFinitePanelSmallDenominator
#print axioms LogdetLean.GramHafnian.ThreePaper.RelativeAccuracy.collisionFreeExpectedDarkFraction
#print axioms LogdetLean.GramHafnian.ThreePaper.RelativeAccuracy.collisionFreeMostLabelsNotDark
#print axioms LogdetLean.GramHafnian.ThreePaper.RelativeAccuracy.randomLabelAdditiveToRelative
#print axioms LogdetLean.GramHafnian.ThreePaper.RelativeAccuracy.collisionFreeRandomLabelAdditiveToRelative
#print axioms LogdetLean.GramHafnian.ThreePaper.RelativeAccuracy.randomLabelFiniteErrorBudget
#print axioms LogdetLean.GramHafnian.ThreePaper.RelativeAccuracy.collisionFreeSamplerRelative
#print axioms LogdetLean.GramHafnian.ThreePaper.RelativeAccuracy.finiteHaarNormalizedPhysicalIntensityTail
#print axioms LogdetLean.GramHafnian.ThreePaper.RelativeAccuracy.sectorReferenceMass
#print axioms LogdetLean.GramHafnian.ThreePaper.RelativeAccuracy.normalizedSectorProbability
