import LogdetLean.GramHafnian.ThreePaper.FairAbsoluteThresholdComparison

/-!
# Named interface for the cited Route 2 matrix comparison

The Shou et al. matrix comparison is a literature input, not a theorem or an
axiom of this package.  This module represents one finite instance of that
input as an explicit hypothesis.  All results below retain that hypothesis in
their theorem signatures and verify only the deductions from it.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.ThreePaper.PRLConsequences

noncomputable section

open CurrentPRL UltimateHiding TwoMethodComparison

/-- The exact finite-instance interface for the cited matrix-law estimate

`dTV(Law((M / sqrt K) U U^T), Law(Gsym_N)) <= C' N / sqrt K`.

The target measure is supplied explicitly.  Constructing a value of this
structure is precisely the external scientific premise; declaring the
structure introduces no constant and no axiom. -/
structure ShouSymmetricMatrixComparisonAt
    (H : UnitaryHaarProbabilityFamily)
    (M N K : ℕ)
    (symmetricMatrixLaw : Measure (Matrix (Fin N) (Fin N) ℂ))
    (Cprime : ℝ) : Prop where
  target_isProbability : IsProbabilityMeasure symmetricMatrixLaw
  matrixLaw : probabilityTotalVariationLE
    (normalizedHaarTransposeGramLaw H M N K)
    symmetricMatrixLaw
    (symmetricHidingEnvelope Cprime K N)

/-- Hafnian pushforward of the normalized Haar transpose Gram law used by
Route 2. -/
def routeTwoHaarHafnianLaw
    (H : UnitaryHaarProbabilityFamily) (M n K : ℕ) : Measure ℂ :=
  Measure.map (hafnianMatrixObservable n)
    (normalizedHaarTransposeGramLaw H M (2 * n) K)

/-- Hafnian pushforward of a supplied independent symmetric matrix law. -/
def independentSymmetricHafnianLaw
    (n : ℕ)
    (symmetricMatrixLaw : Measure (Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ)) :
    Measure ℂ :=
  Measure.map (hafnianMatrixObservable n) symmetricMatrixLaw

/-- Named interface for the direct independent symmetric Gaussian small ball
theorem proved in the companion archive.  Unlike the Shou matrix comparison,
this premise can be instantiated by an axiom-free theorem from that archive. -/
def IndependentSymmetricHafnianSmallBallAt
    (n : ℕ)
    (symmetricMatrixLaw : Measure (Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ)) :
    Prop :=
  ∀ z eps, 0 ≤ eps →
    (independentSymmetricHafnianLaw n symmetricMatrixLaw).real
        (shiftedComplexDisk z
          (eps * Real.sqrt (symmetricHafnianVariance n))) ≤
      min 1 (paperBn n * eps ^ 2)

/-- Data processing of the named Shou premise through the hafnian map. -/
theorem routeTwoHafnianLawTV_of_shou
    {H : UnitaryHaarProbabilityFamily}
    {Cprime : ℝ} {M n K : ℕ}
    {symmetricMatrixLaw :
      Measure (Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ)}
    (hShou : ShouSymmetricMatrixComparisonAt H M (2 * n) K
      symmetricMatrixLaw Cprime) :
    probabilityTotalVariationLE
      (routeTwoHaarHafnianLaw H M n K)
      (independentSymmetricHafnianLaw n symmetricMatrixLaw)
      (symmetricHidingEnvelope Cprime K (2 * n)) := by
  exact hShou.matrixLaw.map (measurable_hafnianMatrixObservable n)

/-- The Route 2 disk transfer in the second line of the End Matter display.
The cited matrix comparison remains an explicit theorem hypothesis. -/
theorem routeTwoShiftedDiskTransfer_of_shou
    {H : UnitaryHaarProbabilityFamily}
    {Cprime : ℝ} {M n K : ℕ}
    {symmetricMatrixLaw :
      Measure (Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ)}
    (hShou : ShouSymmetricMatrixComparisonAt H M (2 * n) K
      symmetricMatrixLaw Cprime)
    (z : ℂ) (radius : ℝ) :
    (routeTwoHaarHafnianLaw H M n K).real
        (shiftedComplexDisk z radius) ≤
      (independentSymmetricHafnianLaw n symmetricMatrixLaw).real
          (shiftedComplexDisk z radius) +
        symmetricHidingEnvelope Cprime K (2 * n) := by
  exact (routeTwoHafnianLawTV_of_shou hShou).event_le
    (measurableSet_shiftedComplexDisk z radius)

/-- Exact Route 2 Haar small ball composition, conditional on the named Shou
matrix comparison and the companion independent symmetric small ball theorem. -/
theorem routeTwoFiniteHaarShiftedSmallBall_of_shou
    {H : UnitaryHaarProbabilityFamily}
    {Cprime : ℝ} {M n K : ℕ}
    {symmetricMatrixLaw :
      Measure (Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ)}
    (hNK : 2 * n ≤ K) (hKM : K ≤ M)
    (hShou : ShouSymmetricMatrixComparisonAt H M (2 * n) K
      symmetricMatrixLaw Cprime)
    (hSmallBall :
      IndependentSymmetricHafnianSmallBallAt n symmetricMatrixLaw)
    (z : ℂ) (eps : ℝ) (heps : 0 ≤ eps) :
    (routeTwoHaarHafnianLaw H M n K).real
        (shiftedComplexDisk z
          (eps * Real.sqrt (symmetricHafnianVariance n))) ≤
      min 1 (paperBn n * eps ^ 2 +
        symmetricHidingEnvelope Cprime K (2 * n)) := by
  letI : IsProbabilityMeasure
      (scaledHaarTransposeGramLaw H M (2 * n) K) :=
    scaledHaarTransposeGramLaw_isProbability H (hNK.trans hKM) hKM
  letI : IsProbabilityMeasure
      (normalizedHaarTransposeGramLaw H M (2 * n) K) := by
    unfold normalizedHaarTransposeGramLaw
    exact Measure.isProbabilityMeasure_map
      (measurable_normalizeTransposeGram (2 * n) K).aemeasurable
  letI : IsProbabilityMeasure (routeTwoHaarHafnianLaw H M n K) := by
    unfold routeTwoHaarHafnianLaw
    exact Measure.isProbabilityMeasure_map
      (measurable_hafnianMatrixObservable n).aemeasurable
  apply le_min measureReal_le_one
  calc
    (routeTwoHaarHafnianLaw H M n K).real
        (shiftedComplexDisk z
          (eps * Real.sqrt (symmetricHafnianVariance n))) ≤
      (independentSymmetricHafnianLaw n symmetricMatrixLaw).real
          (shiftedComplexDisk z
            (eps * Real.sqrt (symmetricHafnianVariance n))) +
        symmetricHidingEnvelope Cprime K (2 * n) :=
      routeTwoShiftedDiskTransfer_of_shou hShou z _
    _ ≤ min 1 (paperBn n * eps ^ 2) +
        symmetricHidingEnvelope Cprime K (2 * n) :=
      add_le_add (hSmallBall z eps heps) le_rfl
    _ ≤ paperBn n * eps ^ 2 +
        symmetricHidingEnvelope Cprime K (2 * n) :=
      add_le_add (min_le_right _ _) le_rfl

/-- The independent symmetric hafnian standard deviation used in the paper. -/
def symmetricHafnianSigma (n : ℕ) : ℝ :=
  Real.sqrt (symmetricHafnianVariance n)

theorem symmetricHafnianSigma_nonneg (n : ℕ) :
    0 ≤ symmetricHafnianSigma n :=
  Real.sqrt_nonneg _

theorem symmetricHafnianSigma_sq (n : ℕ) :
    symmetricHafnianSigma n ^ 2 = symmetricHafnianVariance n := by
  unfold symmetricHafnianSigma symmetricHafnianVariance
  rw [Real.sq_sqrt]
  positivity

/-- Normalized intensity event corresponding exactly to
`p_S <= t p_ref^(2)`. -/
def routeTwoNormalizedSmallDenominatorSet (n : ℕ) (t : ℝ) : Set ℂ :=
  {w | Complex.normSq w ≤ t * symmetricHafnianVariance n}

theorem routeTwoNormalizedSmallDenominatorSet_eq_disk
    (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    routeTwoNormalizedSmallDenominatorSet n t =
      shiftedComplexDisk 0 (Real.sqrt t * symmetricHafnianSigma n) := by
  ext w
  unfold routeTwoNormalizedSmallDenominatorSet shiftedComplexDisk
  simp only [Set.mem_setOf_eq, sub_zero, Complex.normSq_eq_norm_sq]
  have hradius : 0 ≤ Real.sqrt t * symmetricHafnianSigma n :=
    mul_nonneg (Real.sqrt_nonneg _) (symmetricHafnianSigma_nonneg n)
  calc
    ‖w‖ ^ 2 ≤ t * symmetricHafnianVariance n ↔
        ‖w‖ ^ 2 ≤ (Real.sqrt t * symmetricHafnianSigma n) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt ht, symmetricHafnianSigma_sq]
    _ ↔ ‖w‖ ≤ Real.sqrt t * symmetricHafnianSigma n :=
      sq_le_sq₀ (norm_nonneg _) hradius

theorem measurableSet_routeTwoNormalizedSmallDenominatorSet
    (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    MeasurableSet (routeTwoNormalizedSmallDenominatorSet n t) := by
  rw [routeTwoNormalizedSmallDenominatorSet_eq_disk n ht]
  exact measurableSet_shiftedComplexDisk _ _

/-- Physical Route 2 probability written as its reference probability times
the normalized symmetric hafnian intensity. -/
def routeTwoPhysicalProbabilityFromNormalizedHafnian
    (pRefTwo : ℝ) (n : ℕ) (w : ℂ) : ℝ :=
  pRefTwo * Complex.normSq w / symmetricHafnianVariance n

theorem routeTwoPhysicalSmallDenominatorSet_eq_normalized
    {pRefTwo : ℝ} (hpRefTwo : 0 < pRefTwo)
    (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    {w | routeTwoPhysicalProbabilityFromNormalizedHafnian pRefTwo n w ≤
      t * pRefTwo} = routeTwoNormalizedSmallDenominatorSet n t := by
  have hvariance : 0 < symmetricHafnianVariance n := by
    unfold symmetricHafnianVariance
    exact_mod_cast oddPairingNat_pos n
  ext w
  unfold routeTwoPhysicalProbabilityFromNormalizedHafnian
    routeTwoNormalizedSmallDenominatorSet
  simp only [Set.mem_setOf_eq]
  rw [div_le_iff₀ hvariance]
  rw [show t * pRefTwo * symmetricHafnianVariance n =
      pRefTwo * (t * symmetricHafnianVariance n) by ring]
  exact mul_le_mul_iff_of_pos_left hpRefTwo

theorem measurableSet_routeTwoPhysicalSmallDenominator
    {pRefTwo : ℝ} (hpRefTwo : 0 < pRefTwo)
    (n : ℕ) (hn : 1 ≤ n) {t : ℝ} (ht : 0 ≤ t) :
    MeasurableSet
      {w | routeTwoPhysicalProbabilityFromNormalizedHafnian pRefTwo n w ≤
        t * pRefTwo} := by
  rw [routeTwoPhysicalSmallDenominatorSet_eq_normalized hpRefTwo n hn t]
  exact measurableSet_routeTwoNormalizedSmallDenominatorSet n ht

/-- The exact Route 2 small denominator display, conditional on the named
matrix comparison.  The conclusion is written in physical probability units. -/
theorem routeTwoPhysicalSmallDenominator_of_shou
    {H : UnitaryHaarProbabilityFamily}
    {Cprime pRefTwo : ℝ} {M n K : ℕ}
    {symmetricMatrixLaw :
      Measure (Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ)}
    (hn : 1 ≤ n) (hNK : 2 * n ≤ K) (hKM : K ≤ M)
    (hpRefTwo : 0 < pRefTwo)
    (hShou : ShouSymmetricMatrixComparisonAt H M (2 * n) K
      symmetricMatrixLaw Cprime)
    (hSmallBall :
      IndependentSymmetricHafnianSmallBallAt n symmetricMatrixLaw)
    {t : ℝ} (ht : 0 ≤ t) :
    (routeTwoHaarHafnianLaw H M n K).real
        {w | routeTwoPhysicalProbabilityFromNormalizedHafnian pRefTwo n w ≤
          t * pRefTwo} ≤
      min 1 (paperBn n * t +
        symmetricHidingEnvelope Cprime K (2 * n)) := by
  rw [routeTwoPhysicalSmallDenominatorSet_eq_normalized hpRefTwo n hn t]
  rw [routeTwoNormalizedSmallDenominatorSet_eq_disk n ht]
  have h := routeTwoFiniteHaarShiftedSmallBall_of_shou
    hNK hKM hShou hSmallBall 0 (Real.sqrt t) (Real.sqrt_nonneg t)
  simpa [symmetricHafnianSigma, Real.sq_sqrt ht] using h

/-! ## Exact paper wrappers retaining the named premise -/

/-- The Route 2 row of the fair additive to relative display at one common
absolute threshold.  Both the Shou comparison and the symmetric Gaussian
small ball theorem remain explicit hypotheses. -/
theorem routeTwoFairRelativeFailure_of_shou
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (deltaP : Omega → ℝ) (amplitude : Omega → ℂ)
    (hamplitude : Measurable amplitude)
    {H : UnitaryHaarProbabilityFamily}
    {Cprime pRefOne pRefTwo tau rho additiveFailureAtTau : ℝ}
    {M n K : ℕ}
    {symmetricMatrixLaw :
      Measure (Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ)}
    (hn : 1 ≤ n) (hNK : 2 * n ≤ K) (hKM : K ≤ M)
    (hpRefOne : 0 < pRefOne) (hpRefTwo : 0 < pRefTwo)
    (htau : 0 ≤ tau) (hrho : 0 < rho)
    (hreference : pRefOne =
      gramToSymmetricVarianceRatio K n * pRefTwo)
    (hShou : ShouSymmetricMatrixComparisonAt H M (2 * n) K
      symmetricMatrixLaw Cprime)
    (hSmallBall :
      IndependentSymmetricHafnianSmallBallAt n symmetricMatrixLaw)
    (hmarginal : Measure.map amplitude mu =
      routeTwoHaarHafnianLaw H M n K)
    (hadd : mu.real
      (FairAbsoluteThresholdComparison.absoluteAdditiveFailureEvent
        deltaP tau) ≤ additiveFailureAtTau) :
    mu.real
        (relativeFailureEvent deltaP
          (fun omega ↦
            routeTwoPhysicalProbabilityFromNormalizedHafnian
              pRefTwo n (amplitude omega)) rho) ≤
      min 1 (additiveFailureAtTau +
        paperBn n * gramToSymmetricVarianceRatio K n *
          FairAbsoluteThresholdComparison.commonAbsoluteThresholdRatio
            tau rho pRefOne +
        Cprime * ((2 * n : ℕ) : ℝ) / Real.sqrt (K : ℝ)) := by
  have hKpos : 0 < K := by omega
  have hratio : 0 < gramToSymmetricVarianceRatio K n :=
    gramToSymmetricVarianceRatio_pos K n hKpos
  let threshold : ℝ :=
    gramToSymmetricVarianceRatio K n *
      FairAbsoluteThresholdComparison.commonAbsoluteThresholdRatio
        tau rho pRefOne
  have hcommon : 0 ≤
      FairAbsoluteThresholdComparison.commonAbsoluteThresholdRatio
        tau rho pRefOne := by
    unfold FairAbsoluteThresholdComparison.commonAbsoluteThresholdRatio
    positivity
  have hthreshold : 0 ≤ threshold :=
    mul_nonneg hratio.le hcommon
  have hthreshold_eq : threshold = (tau / pRefTwo) / rho := by
    dsimp [threshold]
    symm
    exact FairAbsoluteThresholdComparison.symmetricThreshold_eq_ratio_mul_commonThreshold
      hrho.ne' hpRefTwo.ne' hratio.ne' hreference
  have hthreshold_mul : threshold * pRefTwo = tau / rho := by
    rw [hthreshold_eq]
    field_simp [hpRefTwo.ne', hrho.ne']
  let physicalProbability : Omega → ℝ := fun omega ↦
    routeTwoPhysicalProbabilityFromNormalizedHafnian
      pRefTwo n (amplitude omega)
  have hevent :
      FairAbsoluteThresholdComparison.absoluteSmallDenominatorEvent
          physicalProbability tau rho =
        amplitude ⁻¹'
          {w | routeTwoPhysicalProbabilityFromNormalizedHafnian
            pRefTwo n w ≤ threshold * pRefTwo} := by
    ext omega
    unfold FairAbsoluteThresholdComparison.absoluteSmallDenominatorEvent
      physicalProbability
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    rw [hthreshold_mul]
    constructor
    · intro h
      exact (le_div_iff₀ hrho).2 (by simpa [mul_comm] using h)
    · intro h
      have h' := (le_div_iff₀ hrho).1 h
      simpa [mul_comm] using h'
  have htargetMeasurable : MeasurableSet
      {w | routeTwoPhysicalProbabilityFromNormalizedHafnian
        pRefTwo n w ≤ threshold * pRefTwo} :=
    measurableSet_routeTwoPhysicalSmallDenominator
      hpRefTwo n hn hthreshold
  have hhaar := routeTwoPhysicalSmallDenominator_of_shou
    hn hNK hKM hpRefTwo hShou hSmallBall hthreshold
  have hdenominator : mu.real
      (FairAbsoluteThresholdComparison.absoluteSmallDenominatorEvent
        physicalProbability tau rho) ≤
        paperBn n * gramToSymmetricVarianceRatio K n *
          FairAbsoluteThresholdComparison.commonAbsoluteThresholdRatio
            tau rho pRefOne +
        symmetricHidingEnvelope Cprime K (2 * n) := by
    rw [hevent, ← map_measureReal_apply hamplitude htargetMeasurable,
      hmarginal]
    have huncapped := hhaar.trans (min_le_right _ _)
    simpa [threshold, mul_assoc] using huncapped
  simpa [physicalProbability, symmetricHidingEnvelope] using
    (FairAbsoluteThresholdComparison.relativeFailureProbability_le_routeTwoFairExplicitBound
      mu deltaP physicalProbability hadd hdenominator)

set_option maxHeartbeats 800000 in
/-- The Route 2 row of the sampler relative error display.  Every selected
label is assumed to have the normalized Haar hafnian marginal; the theorem
derives its dark probability from the named Shou premise before applying the
eventwise sampler total variation transfer. -/
theorem routeTwoSamplerRelative_eventwise_of_shou
    {Omega chi : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (labels : Finset chi) (hlabels : labels.Nonempty)
    (amplitude : Omega → chi → ℂ)
    (p q : Omega → chi → ℝ)
    (hamplitude : ∀ x, Measurable fun omega ↦ amplitude omega x)
    (hp : ∀ x, Measurable fun omega ↦ p omega x)
    (hq : ∀ x, Measurable fun omega ↦ q omega x)
    {H : UnitaryHaarProbabilityFamily}
    {Cprime pRefTwo eps zeta rho : ℝ} {M n K : ℕ}
    {symmetricMatrixLaw :
      Measure (Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ)}
    (hn : 1 ≤ n) (hNK : 2 * n ≤ K) (hKM : K ≤ M)
    (hpRefTwo : 0 < pRefTwo) (heps : 0 < eps)
    (hzeta : 0 < zeta) (hrho : 0 < rho)
    (hShou : ShouSymmetricMatrixComparisonAt H M (2 * n) K
      symmetricMatrixLaw Cprime)
    (hSmallBall :
      IndependentSymmetricHafnianSmallBallAt n symmetricMatrixLaw)
    (hpPhysical : ∀ omega x,
      p omega x = routeTwoPhysicalProbabilityFromNormalizedHafnian
        pRefTwo n (amplitude omega x))
    (hmarginal : ∀ x : ↑labels,
      Measure.map (fun omega ↦ amplitude omega x) mu =
        routeTwoHaarHafnianLaw H M n K)
    (htv : ∀ omega, finiteEventTotalVariationLE
      (p omega) (q omega) eps) :
    (∫ omega, samplerRelativeFailureFraction
      (fun omega (x : ↑labels) ↦ p omega x)
      (fun omega (x : ↑labels) ↦ q omega x) rho omega ∂mu) ≤
      min 1 (zeta +
        samplerRelativeConstant (paperBn n) eps rho labels.card pRefTwo /
          zeta +
        Cprime * ((2 * n : ℕ) : ℝ) / Real.sqrt (K : ℝ)) := by
  letI : Nonempty ↑labels := ⟨⟨hlabels.choose, hlabels.choose_spec⟩⟩
  let etaS : ℝ := 2 * eps / (zeta * labels.card)
  have hcard : (0 : ℝ) < labels.card := by
    exact_mod_cast hlabels.card_pos
  have hetaS : 0 < etaS := by
    dsimp [etaS]
    positivity
  let threshold : ℝ := etaS / (rho * pRefTwo)
  have hthreshold : 0 ≤ threshold := by
    dsimp [threshold]
    positivity
  have hthreshold_mul : threshold * pRefTwo = etaS / rho := by
    dsimp [threshold]
    field_simp [hpRefTwo.ne', hrho.ne']
  have htargetMeasurable : MeasurableSet
      {w | routeTwoPhysicalProbabilityFromNormalizedHafnian
        pRefTwo n w ≤ threshold * pRefTwo} :=
    measurableSet_routeTwoPhysicalSmallDenominator
      hpRefTwo n hn hthreshold
  have hhaar := routeTwoPhysicalSmallDenominator_of_shou
    hn hNK hKM hpRefTwo hShou hSmallBall hthreshold
  have honeLabel (x : ↑labels) :
      mu.real {omega | p omega x ≤ etaS / rho} ≤
        paperBn n * threshold +
          symmetricHidingEnvelope Cprime K (2 * n) := by
    have hevent : {omega | p omega x ≤ etaS / rho} =
        (fun omega ↦ amplitude omega x) ⁻¹'
          {w | routeTwoPhysicalProbabilityFromNormalizedHafnian
            pRefTwo n w ≤ threshold * pRefTwo} := by
      ext omega
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, hpPhysical]
      rw [hthreshold_mul]
    rw [hevent, ← map_measureReal_apply
      (hamplitude x) htargetMeasurable, hmarginal x]
    exact hhaar.trans (min_le_right _ _)
  have hdark : (∫ omega, samplerDarkFraction
      (fun omega (x : ↑labels) ↦ p omega x) etaS rho omega ∂mu) ≤
        paperBn n * (etaS / (rho * pRefTwo)) +
          symmetricHidingEnvelope Cprime K (2 * n) := by
    unfold samplerDarkFraction
    apply expectedDarkLabelFraction_le mu
      (fun x : ↑labels ↦ {omega | p omega x ≤ etaS / rho})
      (fun x ↦ measurableSet_le (hp x) measurable_const)
    intro x
    simpa [threshold] using honeLabel x
  have hbase := samplerTVToRandomLabelRelative_eventwise_prl
    mu labels hlabels p q hp hq heps hzeta hrho hpRefTwo htv
    (by simpa [etaS] using hdark)
  simpa [symmetricHidingEnvelope] using hbase

end

end LogdetLean.GramHafnian.ThreePaper.PRLConsequences
