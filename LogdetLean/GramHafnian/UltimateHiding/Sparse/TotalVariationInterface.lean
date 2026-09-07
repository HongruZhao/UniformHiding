import LogdetLean.GramHafnian.UltimateHiding.Sparse.InformationWrappers

/-!
# Concrete eventwise total variation interface

The installed Mathlib revision has KL divergence and its data processing
theorem, but no named probability total variation distance or Pinsker theorem.
This file therefore introduces the exact eventwise predicate used by the paper
and proves its deterministic data processing property.  The genuinely missing
Pinsker step is exposed as the named proposition
`eventwisePinskerKLLowerBound` rather than hidden behind a declaration.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.Sparse

/-- Every measurable event differs in probability by at most `epsilon`.  For
probability measures this is the paper's total variation convention. -/
def probabilityTotalVariationLE
    {X : Type*} [MeasurableSpace X]
    (mu nu : Measure X) (epsilon : ℝ) : Prop :=
  ∀ s : Set X, MeasurableSet s → |mu.real s - nu.real s| ≤ epsilon

theorem probabilityTotalVariationLE_mono
    {X : Type*} [MeasurableSpace X] {mu nu : Measure X} {a b : ℝ}
    (hab : a ≤ b) (h : probabilityTotalVariationLE mu nu a) :
    probabilityTotalVariationLE mu nu b := by
  intro s hs
  exact (h s hs).trans hab

/-- Eventwise total variation cannot increase under a measurable statistic. -/
theorem probabilityTotalVariationLE_map
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {mu nu : Measure X} {epsilon : ℝ}
    (statistic : X → Y) (hstatistic : Measurable statistic)
    (h : probabilityTotalVariationLE mu nu epsilon) :
    probabilityTotalVariationLE (mu.map statistic) (nu.map statistic) epsilon := by
  intro s hs
  have hpre := h (statistic ⁻¹' s) (hs.preimage hstatistic)
  simpa [measureReal_def, Measure.map_apply hstatistic hs] using hpre

/-- The event probability difference is the integral of the centered Radon
Nikodym derivative over that event.  Thus this part of a direct Pinsker proof
is already available from Mathlib's Radon Nikodym API. -/
theorem event_difference_eq_setIntegral_rnDeriv_sub_one
    {X : Type*} [MeasurableSpace X]
    (mu nu : Measure X) [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (hmunu : mu ≪ nu) (s : Set X) :
    mu.real s - nu.real s =
      ∫ x in s, ((mu.rnDeriv nu x).toReal - 1) ∂nu := by
  have hrn : IntegrableOn (fun x ↦ (mu.rnDeriv nu x).toReal) s nu :=
    Measure.integrable_toReal_rnDeriv.integrableOn
  have hone : IntegrableOn (fun _ : X ↦ (1 : ℝ)) s nu :=
    integrableOn_const
  rw [integral_sub hrn hone, Measure.setIntegral_toReal_rnDeriv hmunu,
    setIntegral_const]
  simp

/-- Exact remaining Radon Nikodym inequality for a direct Pinsker proof.  It
is the two cell, or binary, convexity estimate; the event representation and
the KL integral identity are already in Mathlib. -/
def rnEventPinskerLowerBound
    {X : Type*} [MeasurableSpace X]
    (mu nu : Measure X) : Prop :=
  ∀ s : Set X, MeasurableSet s →
    2 * |∫ x in s, ((mu.rnDeriv nu x).toReal - 1) ∂nu| ^ 2
      ≤ ∫ x, InformationTheory.klFun (mu.rnDeriv nu x).toReal ∂nu

/-- The exact eventwise inequality still needed to derive concrete Pinsker in
this Mathlib revision.  It is a proposition, not a typeclass or assumption. -/
def eventwisePinskerKLLowerBound
    {X : Type*} [MeasurableSpace X]
    (mu nu : Measure X) : Prop :=
  ∀ s : Set X, MeasurableSet s →
    2 * |mu.real s - nu.real s| ^ 2
      ≤ (InformationTheory.klDiv mu nu).toReal

/-- The named Radon Nikodym binary inequality supplies the eventwise KL lower
bound using only existing Mathlib identities. -/
theorem eventwisePinskerKLLowerBound_of_rn
    {X : Type*} [MeasurableSpace X]
    (mu nu : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hmunu : mu ≪ nu) (hrn : rnEventPinskerLowerBound mu nu) :
    eventwisePinskerKLLowerBound mu nu := by
  intro s hs
  rw [event_difference_eq_setIntegral_rnDeriv_sub_one mu nu hmunu s,
    InformationTheory.toReal_klDiv_eq_integral_klFun hmunu]
  exact hrn s hs

/-- The named missing eventwise KL lower bound implies the concrete Pinsker
statement with the eventwise total variation predicate. -/
theorem probabilityTotalVariationLE_of_eventwisePinskerKLLowerBound
    {X : Type*} [MeasurableSpace X]
    (mu nu : Measure X)
    (hpin : eventwisePinskerKLLowerBound mu nu) :
    probabilityTotalVariationLE mu nu
      (Real.sqrt ((InformationTheory.klDiv mu nu).toReal / 2)) := by
  intro s hs
  have hnonneg : 0 ≤ |mu.real s - nu.real s| := abs_nonneg _
  exact pinsker_squared_to_sqrt hnonneg (hpin s hs)

end LogdetLean.GramHafnian.UltimateHiding.Sparse
