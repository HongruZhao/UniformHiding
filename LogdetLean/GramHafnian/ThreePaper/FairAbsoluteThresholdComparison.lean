import LogdetLean.GramHafnian.ThreePaper.TwoMethodComparison

/-!
# Fair two-route comparison at one absolute threshold

This module isolates the algebra needed to compare the two PRL routes at the
same physical additive threshold `tau`.  The common Route-1 normalized
threshold is

`tau / (rho * p₁)`.

Because the exact reference scales satisfy `p₁ = R_{K,n} p₂`, Route 2 sees
`R_{K,n} * tau / (rho * p₁)`, not the same dimensionless threshold.  The
definitions below therefore use one additive-failure value at `tau` on both
sides and spell out each coefficient and hiding term; they do not use generic
route-indexed coefficient or hiding ledgers.

The physical convention is `N = 2n`, where `N` is the total photon number and
`n` is the pair count required by `B_{K,n}`, `b_n`, and the hafnian variance.
The Route-1 hiding term is the explicit certified envelope
`615172 * N^2 / M`.  Route 2 can either retain a supplied scalar or use the
purely algebraic envelope `C' * N / sqrt K`.  The assertion that the cited
symmetric-matrix law obeys that envelope is not introduced as a Lean axiom.
-/

open scoped BigOperators

namespace LogdetLean.GramHafnian.ThreePaper.FairAbsoluteThresholdComparison

noncomputable section

open MeasureTheory
open CurrentPRL PRXQUniformHiding UltimateHiding TwoMethodComparison

/-! ## Absolute-threshold additive-to-relative transfer -/

/-- The additive failure event at the physical threshold `tau`. -/
def absoluteAdditiveFailureEvent {Ω : Type*}
    (deltaP : Ω → ℝ) (tau : ℝ) : Set Ω :=
  {ω | tau < |deltaP ω|}

/-- The small-denominator event paired with the same physical threshold. -/
def absoluteSmallDenominatorEvent {Ω : Type*}
    (p : Ω → ℝ) (tau rho : ℝ) : Set Ω :=
  {ω | rho * p ω ≤ tau}

/-- The relative-failure event is contained in the union of the additive
failure event at `tau` and the small-denominator event at `tau/rho`. -/
theorem relativeFailureEvent_subset_absolute_additive_union_denominator
    {Ω : Type*} (deltaP p : Ω → ℝ) (tau rho : ℝ) :
    relativeFailureEvent deltaP p rho ⊆
      absoluteAdditiveFailureEvent deltaP tau ∪
        absoluteSmallDenominatorEvent p tau rho := by
  simpa [absoluteAdditiveFailureEvent, absoluteSmallDenominatorEvent,
    additiveFailureEvent, smallDenominatorEvent] using
    (relativeFailureEvent_subset_additive_union_smallDenominator
      deltaP p tau 1 rho)

/-- Literal manuscript form of the same inclusion, with the positive
relative tolerance used to divide the denominator threshold by `rho`. -/
theorem relativeFailureEvent_subset_absolute_additive_union_dividedDenominator
    {Ω : Type*} (deltaP p : Ω → ℝ) (tau rho : ℝ) (hrho : 0 < rho) :
    relativeFailureEvent deltaP p rho ⊆
      absoluteAdditiveFailureEvent deltaP tau ∪
        {ω | p ω ≤ tau / rho} := by
  intro ω hω
  rcases relativeFailureEvent_subset_absolute_additive_union_denominator
      deltaP p tau rho hω with hadd | hden
  · exact Or.inl hadd
  · change rho * p ω ≤ tau at hden
    exact Or.inr ((le_div_iff₀ hrho).2 (by simpa [mul_comm] using hden))

/-- Probability form of the common-absolute-threshold conversion.  The one
value `additiveFailureAtTau` is the same `gamma(tau)` used by both routes. -/
theorem absoluteAdditiveToRelativeProbability_le
    {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu]
    (deltaP p : Ω → ℝ)
    {tau rho additiveFailureAtTau smallDenominatorBound : ℝ}
    (hadd : mu.real (absoluteAdditiveFailureEvent deltaP tau) ≤
      additiveFailureAtTau)
    (hdenominator : mu.real
      (absoluteSmallDenominatorEvent p tau rho) ≤
        smallDenominatorBound) :
    mu.real (relativeFailureEvent deltaP p rho) ≤
      min 1 (additiveFailureAtTau + smallDenominatorBound) := by
  simpa [absoluteAdditiveFailureEvent, absoluteSmallDenominatorEvent,
    additiveFailureEvent, smallDenominatorEvent] using
    (randomizedAdditiveToRelativeProbability_le_min
      mu deltaP p tau 1 rho additiveFailureAtTau smallDenominatorBound
        (by simpa [absoluteAdditiveFailureEvent, additiveFailureEvent] using
          hadd)
        (by simpa [absoluteSmallDenominatorEvent,
          smallDenominatorEvent] using hdenominator))

/-- The dimensionless threshold associated with one physical additive
tolerance `tau`, relative tolerance `rho`, and Route-1 reference `p₁`. -/
def commonAbsoluteThresholdRatio (tau rho p₁ : ℝ) : ℝ :=
  tau / (rho * p₁)

/-- The paper's polynomial choice `N^{-a}` for the common dimensionless
threshold.  The exponent is real, so this is `Real.rpow`. -/
def polynomialRelativeThreshold (N : ℕ) (a : ℝ) : ℝ :=
  (N : ℝ) ^ (-a)

/-- The uncapped, explicit Route-1 hiding envelope `C_* N^2/M`, with the
kernel-certified constant `C_* = 615172`. -/
def routeOneExplicitHidingTerm (M N : ℕ) : ℝ :=
  (615172 : ℝ) * (N : ℝ) ^ 2 / (M : ℝ)

/-- The existing capped hiding remainder is bounded by the explicit
`615172 N^2/M` envelope. -/
theorem hidingRemainder_le_routeOneExplicitHidingTerm (M N : ℕ) :
    hidingRemainder M N ≤ routeOneExplicitHidingTerm M N := by
  unfold hidingRemainder routeOneExplicitHidingTerm
    ultimateSquaredHidingRate
  calc
    min 1 ((615172 : ℝ) * ((N : ℝ) ^ 2 / (M : ℝ))) ≤
        (615172 : ℝ) * ((N : ℝ) ^ 2 / (M : ℝ)) := min_le_right _ _
    _ = (615172 : ℝ) * (N : ℝ) ^ 2 / (M : ℝ) := by ring

/-- Exact uncapped crossover criterion with the explicit Route-1 hiding
envelope.  This is the named algebraic equivalence used by the final
comparison: Route 2 has the smaller uncapped remainder exactly when its
hiding-cost excess is smaller than its anticoncentration gain. -/
theorem routeTwoUncapped_lt_routeOneUncapped_iff_explicitCrossover
    (M K n : ℕ) (q symmetricHidingError : ℝ) :
    symmetricHidingError - routeOneExplicitHidingTerm M (2 * n) <
        (paperBkn K n -
          paperBn n * gramToSymmetricVarianceRatio K n) * q ↔
      paperBn n * gramToSymmetricVarianceRatio K n * q +
          symmetricHidingError <
        paperBkn K n * q + routeOneExplicitHidingTerm M (2 * n) := by
  constructor <;> intro h <;> nlinarith

/-- The paper's crossover criterion after the literal substitution of the
explicit `C' N / sqrt K` Route-2 envelope.  This is algebra only and does not
assert the cited matrix-law estimate. -/
theorem routeTwoUncapped_lt_routeOneUncapped_iff_explicitCprimeCrossover
    (Cprime q : ℝ) (M K N n : ℕ) :
    symmetricHidingEnvelope Cprime K N -
          routeOneExplicitHidingTerm M (2 * n) <
        (paperBkn K n -
          paperBn n * gramToSymmetricVarianceRatio K n) * q ↔
      paperBn n * gramToSymmetricVarianceRatio K n * q +
          Cprime * (N : ℝ) / Real.sqrt (K : ℝ) <
        paperBkn K n * q + routeOneExplicitHidingTerm M (2 * n) := by
  simpa [symmetricHidingEnvelope] using
    (routeTwoUncapped_lt_routeOneUncapped_iff_explicitCrossover
      M K n q (symmetricHidingEnvelope Cprime K N))

/-- Route 1's fair upper envelope at the common absolute threshold `tau`.
The additive-failure input `additiveFailureAtTau` is shared literally with
Route 2. -/
def routeOneFairAbsoluteThresholdBound
    (additiveFailureAtTau : ℝ) (M K n : ℕ)
    (tau rho p₁ : ℝ) : ℝ :=
  min 1 (additiveFailureAtTau +
    paperBkn K n * commonAbsoluteThresholdRatio tau rho p₁ +
      routeOneExplicitHidingTerm M (2 * n))

/-- Route 2's fair upper envelope at the same absolute threshold `tau`.
The independent-symmetric hiding error is an explicit supplied input. -/
def routeTwoFairAbsoluteThresholdBound
    (additiveFailureAtTau : ℝ) (K n : ℕ)
    (tau rho p₁ symmetricHidingError : ℝ) : ℝ :=
  min 1 (additiveFailureAtTau +
    paperBn n * gramToSymmetricVarianceRatio K n *
      commonAbsoluteThresholdRatio tau rho p₁ +
        symmetricHidingError)

/-- The Route-2 fair envelope with the Letter's explicit
`C' N / sqrt K` hiding term substituted literally. -/
theorem routeTwoFairAbsoluteThresholdBound_explicit
    (additiveFailureAtTau Cprime tau rho p₁ : ℝ)
    (K N n : ℕ) :
    routeTwoFairAbsoluteThresholdBound additiveFailureAtTau K n
        tau rho p₁ (symmetricHidingEnvelope Cprime K N) =
      min 1 (additiveFailureAtTau +
        paperBn n * gramToSymmetricVarianceRatio K n *
          commonAbsoluteThresholdRatio tau rho p₁ +
            Cprime * (N : ℝ) / Real.sqrt (K : ℝ)) := by
  rfl

/-- The best fair upper envelope is the minimum of the two separately capped
bounds evaluated with the same `tau` and the same additive-failure value. -/
def bestFairAbsoluteThresholdBound
    (additiveFailureAtTau : ℝ) (M K n : ℕ)
    (tau rho p₁ symmetricHidingError : ℝ) : ℝ :=
  min (routeOneFairAbsoluteThresholdBound additiveFailureAtTau M K n
      tau rho p₁)
    (routeTwoFairAbsoluteThresholdBound additiveFailureAtTau K n
      tau rho p₁ symmetricHidingError)

/-- A Route-1 small-denominator estimate at the common absolute threshold
implies the displayed fair `E₁` probability bound. -/
theorem relativeFailureProbability_le_routeOneFairBound
    {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu]
    (deltaP p : Ω → ℝ)
    {additiveFailureAtTau tau rho p₁ : ℝ} {M K n : ℕ}
    (hadd : mu.real (absoluteAdditiveFailureEvent deltaP tau) ≤
      additiveFailureAtTau)
    (hdenominator : mu.real
      (absoluteSmallDenominatorEvent p tau rho) ≤
        paperBkn K n * commonAbsoluteThresholdRatio tau rho p₁ +
          routeOneExplicitHidingTerm M (2 * n)) :
    mu.real (relativeFailureEvent deltaP p rho) ≤
      routeOneFairAbsoluteThresholdBound additiveFailureAtTau M K n
        tau rho p₁ := by
  simpa [routeOneFairAbsoluteThresholdBound, add_assoc] using
    (absoluteAdditiveToRelativeProbability_le mu deltaP p hadd hdenominator)

/-- A Route-2 small-denominator estimate at the same absolute threshold
implies the displayed fair `E₂` probability bound.  Its symmetric hiding
term is supplied explicitly. -/
theorem relativeFailureProbability_le_routeTwoFairBound
    {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu]
    (deltaP p : Ω → ℝ)
    {additiveFailureAtTau tau rho p₁ symmetricHidingError : ℝ}
    {K n : ℕ}
    (hadd : mu.real (absoluteAdditiveFailureEvent deltaP tau) ≤
      additiveFailureAtTau)
    (hdenominator : mu.real
      (absoluteSmallDenominatorEvent p tau rho) ≤
        paperBn n * gramToSymmetricVarianceRatio K n *
          commonAbsoluteThresholdRatio tau rho p₁ +
            symmetricHidingError) :
    mu.real (relativeFailureEvent deltaP p rho) ≤
      routeTwoFairAbsoluteThresholdBound additiveFailureAtTau K n
        tau rho p₁ symmetricHidingError := by
  simpa [routeTwoFairAbsoluteThresholdBound, add_assoc] using
    (absoluteAdditiveToRelativeProbability_le mu deltaP p hadd hdenominator)

/-- Probability transfer for the explicit Route-2 envelope.  The displayed
small-denominator estimate is an input; in the paper its matrix-law component
comes from the cited Shou theorem. -/
theorem relativeFailureProbability_le_routeTwoFairExplicitBound
    {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu]
    (deltaP p : Ω → ℝ)
    {additiveFailureAtTau Cprime tau rho p₁ : ℝ}
    {K N n : ℕ}
    (hadd : mu.real (absoluteAdditiveFailureEvent deltaP tau) ≤
      additiveFailureAtTau)
    (hdenominator : mu.real
      (absoluteSmallDenominatorEvent p tau rho) ≤
        paperBn n * gramToSymmetricVarianceRatio K n *
          commonAbsoluteThresholdRatio tau rho p₁ +
            symmetricHidingEnvelope Cprime K N) :
    mu.real (relativeFailureEvent deltaP p rho) ≤
      min 1 (additiveFailureAtTau +
        paperBn n * gramToSymmetricVarianceRatio K n *
          commonAbsoluteThresholdRatio tau rho p₁ +
            Cprime * (N : ℝ) / Real.sqrt (K : ℝ)) := by
  simpa [routeTwoFairAbsoluteThresholdBound,
    symmetricHidingEnvelope, add_assoc] using
    (relativeFailureProbability_le_routeTwoFairBound
      mu deltaP p hadd hdenominator)

/-- If both scientific small-denominator estimates are available, the same
relative-failure probability obeys the minimum of the two fair bounds. -/
theorem relativeFailureProbability_le_bestFairBound
    {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu]
    (deltaP p : Ω → ℝ)
    {additiveFailureAtTau tau rho p₁ symmetricHidingError : ℝ}
    {M K n : ℕ}
    (hadd : mu.real (absoluteAdditiveFailureEvent deltaP tau) ≤
      additiveFailureAtTau)
    (hrouteOneDenominator : mu.real
      (absoluteSmallDenominatorEvent p tau rho) ≤
        paperBkn K n * commonAbsoluteThresholdRatio tau rho p₁ +
          routeOneExplicitHidingTerm M (2 * n))
    (hrouteTwoDenominator : mu.real
      (absoluteSmallDenominatorEvent p tau rho) ≤
        paperBn n * gramToSymmetricVarianceRatio K n *
          commonAbsoluteThresholdRatio tau rho p₁ +
            symmetricHidingError) :
    mu.real (relativeFailureEvent deltaP p rho) ≤
      bestFairAbsoluteThresholdBound additiveFailureAtTau M K n
        tau rho p₁ symmetricHidingError := by
  exact le_min
    (relativeFailureProbability_le_routeOneFairBound
      mu deltaP p hadd hrouteOneDenominator)
    (relativeFailureProbability_le_routeTwoFairBound
      mu deltaP p hadd hrouteTwoDenominator)

/-- Dividing the same absolute threshold by two reference scales related by
`p₁ = R p₂` multiplies Route 2's normalized threshold by `R`. -/
theorem symmetricThreshold_eq_ratio_mul_commonThreshold
    {tau rho p₁ p₂ R : ℝ}
    (hrho : rho ≠ 0) (hp₂ : p₂ ≠ 0) (hR : R ≠ 0)
    (hreference : p₁ = R * p₂) :
    (tau / p₂) / rho =
      R * commonAbsoluteThresholdRatio tau rho p₁ := by
  unfold commonAbsoluteThresholdRatio
  rw [hreference]
  field_simp [hrho, hp₂, hR]

/-- The exact Gram and independent-symmetric physical references instantiate
the abstract reference-scale identity used by the fair comparison. -/
theorem physicalReferences_obey_fair_scale_identity
    (r : ℝ) (M K n : ℕ) (hK : 0 < K) (hn : 1 ≤ n) :
    gbsGaussianReferenceProbability r M K n =
      gramToSymmetricVarianceRatio K n *
        symmetricGaussianReferenceProbability r M K n :=
  gramReferenceProbability_eq_ratio_mul_symmetricReference
    r M K n hK hn

/-- Rewriting the pre-existing Method-1 budget at the absolute tolerance
`tau` and replacing its capped hiding remainder by the explicit envelope
gives the fair Route-1 bound. -/
theorem methodOneBudget_at_same_absolute_threshold_le_fairBound
    (additiveFailureAtTau : ℝ) (M K n : ℕ)
    (tau rho p₁ : ℝ) :
    methodOneRelativeBudget additiveFailureAtTau M K n
        (tau / p₁) rho ≤
      routeOneFairAbsoluteThresholdBound additiveFailureAtTau M K n
        tau rho p₁ := by
  have hratio : (tau / p₁) / rho =
      commonAbsoluteThresholdRatio tau rho p₁ := by
    unfold commonAbsoluteThresholdRatio
    simp only [div_eq_mul_inv]
    ring
  have hhiding :=
    hidingRemainder_le_routeOneExplicitHidingTerm M (2 * n)
  unfold methodOneRelativeBudget methodOneRelativeRemainder
    routeOneFairAbsoluteThresholdBound
  rw [hratio]
  exact min_le_min le_rfl (by linarith)

/-- Rewriting the pre-existing common-scale Method-2 budget at the same
absolute tolerance is an equality. -/
theorem methodTwoCommonBudget_at_same_absolute_threshold_eq_fairBound
    (additiveFailureAtTau : ℝ) (K n : ℕ)
    (tau rho p₁ symmetricHidingError : ℝ) :
    methodTwoCommonRelativeBudget additiveFailureAtTau K n
        (tau / p₁) rho symmetricHidingError =
      routeTwoFairAbsoluteThresholdBound additiveFailureAtTau K n
        tau rho p₁ symmetricHidingError := by
  unfold methodTwoCommonRelativeBudget methodTwoCommonRelativeRemainder
    routeTwoFairAbsoluteThresholdBound commonAbsoluteThresholdRatio
  apply congrArg (fun x : ℝ ↦ min 1 x)
  simp only [div_eq_mul_inv]
  ring

/-- At two exact reference scales `p₁ = R_{K,n} p₂`, Route 2's natural
budget evaluated at the same absolute tolerance equals the fair Route-2
bound. -/
theorem methodTwoNaturalBudget_at_same_absolute_threshold_eq_fairBound
    (additiveFailureAtTau : ℝ) (K n : ℕ)
    (tau rho p₁ p₂ symmetricHidingError : ℝ)
    (hrho : rho ≠ 0) (hp₂ : p₂ ≠ 0)
    (hreference : p₁ = gramToSymmetricVarianceRatio K n * p₂)
    (hratio : gramToSymmetricVarianceRatio K n ≠ 0) :
    min 1 (additiveFailureAtTau +
        methodTwoNaturalRelativeRemainder n
          (tau / p₂) rho symmetricHidingError) =
      routeTwoFairAbsoluteThresholdBound additiveFailureAtTau K n
        tau rho p₁ symmetricHidingError := by
  have hthreshold := symmetricThreshold_eq_ratio_mul_commonThreshold
    (tau := tau) (rho := rho) (p₁ := p₁) (p₂ := p₂)
    (R := gramToSymmetricVarianceRatio K n)
    hrho hp₂ hratio hreference
  unfold methodTwoNaturalRelativeRemainder
    routeTwoFairAbsoluteThresholdBound
  rw [hthreshold]
  apply congrArg (fun x : ℝ ↦ min 1 x)
  ring

/-- Route 1 after the paper specialization
`tau/(rho p₁) = N^{-a}`, with total photon number `N = 2n`. -/
theorem routeOneFairBound_of_polynomialThreshold
    (additiveFailureAtTau : ℝ) (M K n : ℕ)
    (tau rho p₁ a : ℝ)
    (hthreshold : commonAbsoluteThresholdRatio tau rho p₁ =
      polynomialRelativeThreshold (2 * n) a) :
    routeOneFairAbsoluteThresholdBound additiveFailureAtTau M K n
        tau rho p₁ =
      min 1 (additiveFailureAtTau +
        paperBkn K n * polynomialRelativeThreshold (2 * n) a +
          routeOneExplicitHidingTerm M (2 * n)) := by
  unfold routeOneFairAbsoluteThresholdBound
  rw [hthreshold]

/-- Route 2 under the same specialization.  The normalized threshold is
`R_{K,n} N^{-a}` because the common absolute tolerance is fixed at the
Route-1 reference scale. -/
theorem routeTwoFairBound_of_polynomialThreshold
    (additiveFailureAtTau : ℝ) (K n : ℕ)
    (tau rho p₁ symmetricHidingError a : ℝ)
    (hthreshold : commonAbsoluteThresholdRatio tau rho p₁ =
      polynomialRelativeThreshold (2 * n) a) :
    routeTwoFairAbsoluteThresholdBound additiveFailureAtTau K n
        tau rho p₁ symmetricHidingError =
      min 1 (additiveFailureAtTau +
        paperBn n * gramToSymmetricVarianceRatio K n *
          polynomialRelativeThreshold (2 * n) a +
            symmetricHidingError) := by
  unfold routeTwoFairAbsoluteThresholdBound
  rw [hthreshold]

/-- Polynomial-threshold specialization with the explicit
`C' N / sqrt K` Route-2 envelope. -/
theorem routeTwoFairBound_of_polynomialThreshold_explicit
    (additiveFailureAtTau Cprime : ℝ) (K N n : ℕ)
    (tau rho p₁ a : ℝ)
    (hthreshold : commonAbsoluteThresholdRatio tau rho p₁ =
      polynomialRelativeThreshold (2 * n) a) :
    routeTwoFairAbsoluteThresholdBound additiveFailureAtTau K n
        tau rho p₁ (symmetricHidingEnvelope Cprime K N) =
      min 1 (additiveFailureAtTau +
        paperBn n * gramToSymmetricVarianceRatio K n *
          polynomialRelativeThreshold (2 * n) a +
            Cprime * (N : ℝ) / Real.sqrt (K : ℝ)) := by
  simpa [symmetricHidingEnvelope] using
    (routeTwoFairBound_of_polynomialThreshold
      additiveFailureAtTau K n tau rho p₁
        (symmetricHidingEnvelope Cprime K N) a hthreshold)

/-- Both fair bounds use the same additive-failure value at `tau`; under the
power specialization their only differences are the displayed
anticoncentration and hiding terms. -/
theorem bothFairBounds_of_polynomialThreshold
    (additiveFailureAtTau : ℝ) (M K n : ℕ)
    (tau rho p₁ symmetricHidingError a : ℝ)
    (hthreshold : commonAbsoluteThresholdRatio tau rho p₁ =
      polynomialRelativeThreshold (2 * n) a) :
    routeOneFairAbsoluteThresholdBound additiveFailureAtTau M K n
          tau rho p₁ =
        min 1 (additiveFailureAtTau +
          paperBkn K n * polynomialRelativeThreshold (2 * n) a +
            routeOneExplicitHidingTerm M (2 * n)) ∧
      routeTwoFairAbsoluteThresholdBound additiveFailureAtTau K n
          tau rho p₁ symmetricHidingError =
        min 1 (additiveFailureAtTau +
          paperBn n * gramToSymmetricVarianceRatio K n *
            polynomialRelativeThreshold (2 * n) a +
              symmetricHidingError) :=
  ⟨routeOneFairBound_of_polynomialThreshold
      additiveFailureAtTau M K n tau rho p₁ a hthreshold,
    routeTwoFairBound_of_polynomialThreshold
      additiveFailureAtTau K n tau rho p₁ symmetricHidingError a
        hthreshold⟩

/-- If a relative-failure probability is controlled by both fair route
bounds, it is controlled by their fair minimum.  Each scientific route bound
is an explicit premise; this theorem introduces no random-matrix assumption. -/
theorem failure_le_bestFairAbsoluteThresholdBound
    {failure additiveFailureAtTau tau rho p₁ symmetricHidingError : ℝ}
    {M K n : ℕ}
    (hrouteOne : failure ≤
      routeOneFairAbsoluteThresholdBound additiveFailureAtTau M K n
        tau rho p₁)
    (hrouteTwo : failure ≤
      routeTwoFairAbsoluteThresholdBound additiveFailureAtTau K n
        tau rho p₁ symmetricHidingError) :
    failure ≤ bestFairAbsoluteThresholdBound additiveFailureAtTau M K n
      tau rho p₁ symmetricHidingError := by
  exact le_min hrouteOne hrouteTwo

end

end LogdetLean.GramHafnian.ThreePaper.FairAbsoluteThresholdComparison
