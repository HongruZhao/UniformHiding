import LogdetLean.GramHafnian.ThreePaper.GaussianAnticoncentration
import LogdetLean.GramHafnian.ThreePaper.UniformMatrixHiding

/-!
# Axiom-free common definitions for the manuscript composition

The two Article packages deliberately expose disjoint scientific endpoint
surfaces.  This module supplies only the elementary definitions and proved
measure/event identities needed to compose those endpoints in the Letter.
It contains no external scientific declaration.
-/

open scoped BigOperators
open MeasureTheory ProbabilityTheory Set

namespace LogdetLean.GramHafnian.LocalAnticoncentration

noncomputable section

/-! ## Adopted optical normalization -/

/-- Equal-squeezing factor outside the squared hafnian. -/
def equalSqueezingOpticalPrefactor (r : ℝ) (N K : ℕ) : ℝ :=
  Real.tanh r ^ N / Real.cosh r ^ K

theorem equalSqueezingOpticalPrefactor_pos
    {r : ℝ} (hr : 0 < r) (N K : ℕ) :
    0 < equalSqueezingOpticalPrefactor r N K := by
  have htanh : 0 < Real.tanh r := by
    rw [Real.tanh_eq]
    have hneg : Real.exp (-r) < Real.exp r :=
      Real.exp_lt_exp.mpr (by linarith)
    have hden : 0 < Real.exp r + Real.exp (-r) :=
      add_pos (Real.exp_pos _) (Real.exp_pos _)
    positivity
  unfold equalSqueezingOpticalPrefactor
  exact div_pos (pow_pos htanh N) (pow_pos (Real.cosh_pos r) K)

/-- Adopted equal-squeezing collision-free GBS probability model. -/
def gbsCollisionFreePatternProbability
    (r : ℝ) (K n : ℕ)
    (A : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ) : ℝ :=
  equalSqueezingOpticalPrefactor r (2 * n) K *
    Complex.normSq (LogdetLean.GramHafnian.hafnian A)

/-- The displayed collision-free GBS probability formula.  This is a
definitional endpoint for the adopted optical model. -/
theorem eq1_gbs_collision_free_probability
    (r : ℝ) (K n : ℕ)
    (A : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ) :
    gbsCollisionFreePatternProbability r K n A =
      Real.tanh r ^ (2 * n) / Real.cosh r ^ K *
        Complex.normSq (LogdetLean.GramHafnian.hafnian A) := by
  rfl

/-- Optical factor accompanying the hidden scaled amplitude. -/
def scaledGBSOpticalFactor (r : ℝ) (M K n : ℕ) : ℝ :=
  equalSqueezingOpticalPrefactor r (2 * n) K / (M : ℝ) ^ (2 * n)

theorem scaledGBSOpticalFactor_pos
    {r : ℝ} (hr : 0 < r) {M : ℕ} (hM : 0 < M) (K n : ℕ) :
    0 < scaledGBSOpticalFactor r M K n := by
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  unfold scaledGBSOpticalFactor
  exact div_pos (equalSqueezingOpticalPrefactor_pos hr (2 * n) K)
    (pow_pos hMR (2 * n))

/-- Physical probability as a function of the hidden scaled hafnian. -/
def gbsProbabilityFromScaledAmplitude
    (r : ℝ) (M K n : ℕ) (w : ℂ) : ℝ :=
  scaledGBSOpticalFactor r M K n * Complex.normSq w

/-- Gaussian reference probability used in the Letter. -/
def gbsGaussianReferenceProbability
    (r : ℝ) (M K n : ℕ) : ℝ :=
  scaledGBSOpticalFactor r M K n *
    LogdetLean.GramHafnian.gramHafnianSigma K n ^ 2

/-- The physical probability and Gaussian reference share the same optical
factor. This is an elementary ring identity, not a scientific input. -/
theorem gbsProbability_reference_scale_identity
    (r : ℝ) (M K n : ℕ) (w : ℂ) :
    gbsProbabilityFromScaledAmplitude r M K n w *
        LogdetLean.GramHafnian.gramHafnianSigma K n ^ 2 =
      gbsGaussianReferenceProbability r M K n * Complex.normSq w := by
  unfold gbsProbabilityFromScaledAmplitude
    gbsGaussianReferenceProbability
  ring

/-! ## Hafnian pushforwards of the two matrix laws -/

/-- Hafnian as a measurable observable on a `2n x 2n` matrix. -/
def hafnianMatrixObservable (n : ℕ) :
    Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ → ℂ :=
  hafnian

@[fun_prop]
theorem measurable_hafnianMatrixObservable (n : ℕ) :
    Measurable (hafnianMatrixObservable n) := by
  unfold hafnianMatrixObservable hafnian matchingMonomial
  fun_prop

/-- Haar law of the scaled transpose-Gram hafnian. -/
def scaledHaarGramHafnianLaw
    (H : UnitaryHaarProbabilityFamily) (M n K : ℕ) : Measure ℂ :=
  Measure.map (hafnianMatrixObservable n)
    (scaledHaarTransposeGramLaw H M (2 * n) K)

/-- Gaussian law of the transpose-Gram hafnian. -/
def gaussianGramHafnianLaw (n K : ℕ) : Measure ℂ :=
  Measure.map (hafnianMatrixObservable n)
    (gaussianTransposeGramLaw (2 * n) K)

/-- The closed complex disk used by the law transfer. -/
def shiftedComplexDisk (z : ℂ) (rho : ℝ) : Set ℂ :=
  {w | ‖w - z‖ ≤ rho}

theorem measurableSet_shiftedComplexDisk (z : ℂ) (rho : ℝ) :
    MeasurableSet (shiftedComplexDisk z rho) := by
  unfold shiftedComplexDisk
  exact measurableSet_le ((measurable_id.sub_const z).norm) measurable_const

theorem hafnian_rectangularTransposeGram_eq_gramHafnianObservable
    (n K : ℕ) (G : Matrix (Fin (2 * n)) (Fin K) ℂ) :
    hafnianMatrixObservable n (rectangularTransposeGram G) =
      LogdetLean.GramHafnian.gramHafnianObservable n K G := by
  unfold hafnianMatrixObservable rectangularTransposeGram
    LogdetLean.GramHafnian.gramHafnianObservable
    LogdetLean.GramHafnian.gramHafnian
    LogdetLean.GramHafnian.transposeGram
    LogdetLean.GramHafnian.rowMatrix
  congr

/-- The Gaussian pushforward law is the literal matrix model used by the
anticoncentration Article. -/
theorem gaussianGramHafnianLaw_eq_literal (n K : ℕ) :
    gaussianGramHafnianLaw n K =
      Measure.map
        (LogdetLean.GramHafnian.gramHafnianObservable n K)
        (LogdetLean.GramHafnian.circularGaussianColumnMatrixMeasure n K) := by
  unfold gaussianGramHafnianLaw gaussianTransposeGramLaw
    standardComplexGaussianRectangularMeasure
    LogdetLean.GramHafnian.circularGaussianColumnMatrixMeasure
  rw [Measure.map_map (measurable_rectangularTransposeGram (2 * n) K)
    (measurable_functionToComplexMatrix (2 * n) K)]
  rw [Measure.map_map (measurable_hafnianMatrixObservable n)
    ((measurable_rectangularTransposeGram (2 * n) K).comp
      (measurable_functionToComplexMatrix (2 * n) K))]
  congr 1

/-- Gaussian disk probabilities agree exactly with the small-ball probability
used by the anticoncentration Article. -/
theorem gaussianGramHafnianLaw_shiftedDisk_eq
    (n K : ℕ) (z : ℂ) (eps : ℝ) :
    (gaussianGramHafnianLaw n K).real
        (shiftedComplexDisk z
          (eps * LogdetLean.GramHafnian.gramHafnianSigma K n)) =
      LogdetLean.GramHafnian.gramHafnianShiftedSmallBallProbability
        K n z eps := by
  rw [gaussianGramHafnianLaw_eq_literal]
  rw [MeasureTheory.map_measureReal_apply
    (LogdetLean.GramHafnian.measurable_gramHafnianObservable n K)
    (measurableSet_shiftedComplexDisk z
      (eps * LogdetLean.GramHafnian.gramHafnianSigma K n))]
  rfl

theorem scaledHaarGramHafnianLaw_isProbability
    (H : UnitaryHaarProbabilityFamily) {M n K : ℕ}
    (hNM : 2 * n ≤ M) (hKM : K ≤ M) :
    IsProbabilityMeasure (scaledHaarGramHafnianLaw H M n K) := by
  letI : IsProbabilityMeasure
      (scaledHaarTransposeGramLaw H M (2 * n) K) :=
    scaledHaarTransposeGramLaw_isProbability H hNM hKM
  unfold scaledHaarGramHafnianLaw
  exact Measure.isProbabilityMeasure_map
    (measurable_hafnianMatrixObservable n).aemeasurable

/-! ## Physical small-denominator event -/

def scaledAmplitudeSmallDenominatorSet
    (r : ℝ) (M K n : ℕ) (t : ℝ) : Set ℂ :=
  {w | gbsProbabilityFromScaledAmplitude r M K n w ≤
    t * gbsGaussianReferenceProbability r M K n}

theorem scaledAmplitudeSmallDenominatorSet_eq_shiftedComplexDisk
    {r : ℝ} (hr : 0 < r) {M : ℕ} (hM : 0 < M)
    (K n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    scaledAmplitudeSmallDenominatorSet r M K n t =
      shiftedComplexDisk 0
        (Real.sqrt t * LogdetLean.GramHafnian.gramHafnianSigma K n) := by
  have hscale : 0 < scaledGBSOpticalFactor r M K n :=
    scaledGBSOpticalFactor_pos hr hM K n
  have hsigma : 0 ≤ LogdetLean.GramHafnian.gramHafnianSigma K n :=
    LogdetLean.GramHafnian.gramHafnianSigma_nonneg K n
  ext w
  simp only [scaledAmplitudeSmallDenominatorSet, Set.mem_setOf_eq,
    gbsProbabilityFromScaledAmplitude, gbsGaussianReferenceProbability]
  rw [show t *
      (scaledGBSOpticalFactor r M K n *
        LogdetLean.GramHafnian.gramHafnianSigma K n ^ 2) =
      scaledGBSOpticalFactor r M K n *
        (t * LogdetLean.GramHafnian.gramHafnianSigma K n ^ 2) by ring]
  rw [mul_le_mul_iff_of_pos_left hscale]
  unfold shiftedComplexDisk
  simp only [Set.mem_setOf_eq, sub_zero, Complex.normSq_eq_norm_sq]
  have hradius : 0 ≤
      Real.sqrt t * LogdetLean.GramHafnian.gramHafnianSigma K n :=
    mul_nonneg (Real.sqrt_nonneg _) hsigma
  calc
    ‖w‖ ^ 2 ≤
        t * LogdetLean.GramHafnian.gramHafnianSigma K n ^ 2 ↔
      ‖w‖ ^ 2 ≤
        (Real.sqrt t *
          LogdetLean.GramHafnian.gramHafnianSigma K n) ^ 2 := by
            rw [mul_pow, Real.sq_sqrt ht]
    _ ↔ ‖w‖ ≤
        Real.sqrt t *
          LogdetLean.GramHafnian.gramHafnianSigma K n :=
      sq_le_sq₀ (norm_nonneg _) hradius

theorem measurableSet_scaledAmplitudeSmallDenominatorSet
    {r : ℝ} (hr : 0 < r) {M : ℕ} (hM : 0 < M)
    (K n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    MeasurableSet (scaledAmplitudeSmallDenominatorSet r M K n t) := by
  rw [scaledAmplitudeSmallDenominatorSet_eq_shiftedComplexDisk
    hr hM K n ht]
  exact measurableSet_shiftedComplexDisk _ _

/-! ## Randomized additive-to-relative conversion -/

def additiveFailureEvent {Omega : Type*}
    (deltaP : Omega → ℝ) (eta pRef : ℝ) : Set Omega :=
  {omega | eta * pRef < |deltaP omega|}

def smallDenominatorEvent {Omega : Type*}
    (p : Omega → ℝ) (eta pRef rho : ℝ) : Set Omega :=
  {omega | rho * p omega ≤ eta * pRef}

def relativeFailureEvent {Omega : Type*}
    (deltaP p : Omega → ℝ) (rho : ℝ) : Set Omega :=
  {omega | rho * p omega < |deltaP omega|}

theorem relativeFailureEvent_subset_additive_union_smallDenominator
    {Omega : Type*} (deltaP p : Omega → ℝ)
    (eta pRef rho : ℝ) :
    relativeFailureEvent deltaP p rho ⊆
      additiveFailureEvent deltaP eta pRef ∪
        smallDenominatorEvent p eta pRef rho := by
  intro omega hrel
  by_cases hadd : omega ∈ additiveFailureEvent deltaP eta pRef
  · exact Or.inl hadd
  · right
    change rho * p omega ≤ eta * pRef
    by_contra hden
    have hadd' : |deltaP omega| ≤ eta * pRef := le_of_not_gt hadd
    have hden' : eta * pRef < rho * p omega := lt_of_not_ge hden
    exact (not_lt_of_ge hadd') (hden'.trans hrel)

theorem randomizedAdditiveToRelativeProbability_le_min
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (deltaP p : Omega → ℝ) (eta pRef rho gamma darkBound : ℝ)
    (hadd : mu.real (additiveFailureEvent deltaP eta pRef) ≤ gamma)
    (hdark : mu.real
      (smallDenominatorEvent p eta pRef rho) ≤ darkBound) :
    mu.real (relativeFailureEvent deltaP p rho) ≤
      min 1 (gamma + darkBound) := by
  apply le_min measureReal_le_one
  calc
    mu.real (relativeFailureEvent deltaP p rho) ≤
        mu.real
          (additiveFailureEvent deltaP eta pRef ∪
            smallDenominatorEvent p eta pRef rho) :=
      measureReal_mono
        (relativeFailureEvent_subset_additive_union_smallDenominator
          deltaP p eta pRef rho)
    _ ≤ mu.real (additiveFailureEvent deltaP eta pRef) +
          mu.real (smallDenominatorEvent p eta pRef rho) :=
      measureReal_union_le _ _
    _ ≤ gamma + darkBound := add_le_add hadd hdark

theorem randomizedConversion_relativeAccuracy_bound
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (deltaP p : Omega → ℝ)
    {eta pRef rho gamma B hidingError : ℝ}
    (heta : 0 ≤ eta) (hrho : 0 < rho) (hgamma : 0 ≤ gamma)
    (hadd : mu.real (additiveFailureEvent deltaP eta pRef) ≤ gamma)
    (hdark : mu.real (smallDenominatorEvent p eta pRef rho) ≤
      B * (eta / rho) + hidingError) :
    mu.real (relativeFailureEvent deltaP p rho) ≤
      min 1 (gamma + B * (eta / rho) + hidingError) := by
  have h := randomizedAdditiveToRelativeProbability_le_min
    mu deltaP p eta pRef rho gamma (B * (eta / rho) + hidingError) hadd hdark
  simpa [add_assoc] using h

theorem smallDenominatorEvent_gbs_eq_preimage
    {Omega : Type*} (amplitude : Omega → ℂ)
    {r : ℝ} {M K n : ℕ} {eta rho : ℝ} (hrho : 0 < rho) :
    smallDenominatorEvent
        (fun omega ↦
          gbsProbabilityFromScaledAmplitude r M K n (amplitude omega))
        eta (gbsGaussianReferenceProbability r M K n) rho =
      amplitude ⁻¹'
        scaledAmplitudeSmallDenominatorSet r M K n (eta / rho) := by
  ext omega
  simp only [smallDenominatorEvent, scaledAmplitudeSmallDenominatorSet,
    Set.mem_ofPred_eq, Set.mem_preimage]
  rw [show (eta / rho) * gbsGaussianReferenceProbability r M K n =
      (eta * gbsGaussianReferenceProbability r M K n) / rho by ring]
  rw [le_div_iff₀ hrho]
  ring_nf

theorem smallDenominatorProbability_eq_scaledHaarLaw
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (amplitude : Omega → ℂ)
    (hamplitude : Measurable amplitude)
    (H : UnitaryHaarProbabilityFamily)
    {r : ℝ} (hr : 0 < r) {M : ℕ} (hM : 0 < M) (K n : ℕ)
    {eta rho : ℝ} (heta : 0 ≤ eta) (hrho : 0 < rho)
    (hmarginal : Measure.map amplitude mu =
      scaledHaarGramHafnianLaw H M n K) :
    mu.real
        (smallDenominatorEvent
          (fun omega ↦
            gbsProbabilityFromScaledAmplitude r M K n (amplitude omega))
          eta (gbsGaussianReferenceProbability r M K n) rho) =
      (scaledHaarGramHafnianLaw H M n K).real
        (scaledAmplitudeSmallDenominatorSet r M K n (eta / rho)) := by
  rw [smallDenominatorEvent_gbs_eq_preimage amplitude hrho]
  have ht : 0 ≤ eta / rho := div_nonneg heta hrho.le
  rw [← MeasureTheory.map_measureReal_apply hamplitude
    (measurableSet_scaledAmplitudeSmallDenominatorSet
      hr hM K n ht)]
  rw [hmarginal]

theorem randomizedConversion_from_finiteHaarSmallDenominator
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (amplitude : Omega → ℂ) (hamplitude : Measurable amplitude)
    (deltaP : Omega → ℝ)
    (H : UnitaryHaarProbabilityFamily)
    {r : ℝ} (hr : 0 < r) {M : ℕ} (hM : 0 < M) (K n : ℕ)
    {eta rho gamma B hidingError : ℝ}
    (heta : 0 ≤ eta) (hrho : 0 < rho) (hgamma : 0 ≤ gamma)
    (hmarginal : Measure.map amplitude mu =
      scaledHaarGramHafnianLaw H M n K)
    (hadd : mu.real
      (additiveFailureEvent deltaP eta
        (gbsGaussianReferenceProbability r M K n)) ≤ gamma)
    (hhaar : (scaledHaarGramHafnianLaw H M n K).real
      (scaledAmplitudeSmallDenominatorSet r M K n (eta / rho)) ≤
        B * (eta / rho) + hidingError) :
    mu.real
        (relativeFailureEvent deltaP
          (fun omega ↦
            gbsProbabilityFromScaledAmplitude r M K n (amplitude omega))
          rho) ≤
      min 1 (gamma + B * (eta / rho) + hidingError) := by
  apply randomizedConversion_relativeAccuracy_bound
    mu deltaP
      (fun omega ↦
        gbsProbabilityFromScaledAmplitude r M K n (amplitude omega))
      heta hrho hgamma hadd
  rw [smallDenominatorProbability_eq_scaledHaarLaw
    mu amplitude hamplitude H hr hM K n heta hrho hmarginal]
  exact hhaar

/-! ## Independent uniform pattern selection -/

/-- Arithmetic probability of an independent uniform choice from a finite
pattern type. -/
def uniformFinitePatternProbability
    {Pattern : Type*} [Fintype Pattern] (q : Pattern -> ℝ) : ℝ :=
  (∑ pattern, q pattern) / Fintype.card Pattern

/-- If Haar row symmetry makes every preselected pattern law identical, then
independent uniform pattern selection has exactly the same event probability.
The conclusion is an average, not a union, so no pattern count is lost. -/
theorem uniformFinitePatternProbability_eq_of_rowSymmetry
    {Pattern alpha : Type*} [Fintype Pattern] [Nonempty Pattern]
    [MeasurableSpace alpha]
    (patternLaw : Pattern -> Measure alpha) (referenceLaw : Measure alpha)
    (event : Set alpha)
    (hrow : ∀ pattern, patternLaw pattern = referenceLaw) :
    uniformFinitePatternProbability
        (fun pattern => (patternLaw pattern).real event) =
      referenceLaw.real event := by
  unfold uniformFinitePatternProbability
  simp_rw [hrow]
  simp [Fintype.card_pos]

/-- No union bound is incurred after an independent uniform choice when the
preselected bounds are identical by row symmetry. -/
theorem uniformFinitePatternProbability_le_of_rowSymmetry
    {Pattern alpha : Type*} [Fintype Pattern] [Nonempty Pattern]
    [MeasurableSpace alpha]
    (patternLaw : Pattern -> Measure alpha) (referenceLaw : Measure alpha)
    (event : Set alpha) (bound : ℝ)
    (hrow : ∀ pattern, patternLaw pattern = referenceLaw)
    (hbound : referenceLaw.real event <= bound) :
    uniformFinitePatternProbability
        (fun pattern => (patternLaw pattern).real event) <= bound := by
  rw [uniformFinitePatternProbability_eq_of_rowSymmetry
    patternLaw referenceLaw event hrow]
  exact hbound

end

end LogdetLean.GramHafnian.LocalAnticoncentration
