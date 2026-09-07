import LogdetLean.WishartLeadingKolmogorov
import LogdetLean.KolmogorovCLTBridge
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Sequential general-correlation central limit theorem

The finite-dimensional Berry--Esseen theorem is meaningful only when
`Admissible m p`, whereas a sequence indexed by all natural numbers also has
finitely many initial, non-admissible indices.  This module removes that
minor logical nuisance exactly as `NullWeakCLT.lean` does in the identity
case: outside the admissible range the law is defined to be standard
Gaussian.  Eventual admissibility therefore recovers the actual statistic
and the fallback has no effect on any limit.

The only model-specific input here is
`kolmogorovDistance_ZRmpStatistic_le_finalRateEnvelope`.  Everything after
that finite inequality is an elementary squeeze argument.
-/

namespace LogdetLean

open Filter MeasureTheory ProbabilityTheory

noncomputable section

/-- A version of the generic Kolmogorov squeeze lemma in which the finite
upper bound is required only eventually.  This is the natural formulation
for triangular arrays whose dimension restrictions hold eventually. -/
theorem tendsto_kolmogorovDistance_of_eventually_bound
    {ι : Type*} {l : Filter ι} (μ : ι → Measure ℝ) (ν : Measure ℝ)
    (rate : ι → ℝ)
    (hbound : ∀ᶠ i in l, kolmogorovDistance (μ i) ν ≤ rate i)
    (hrate : Tendsto rate l (nhds 0)) :
    Tendsto (fun i ↦ kolmogorovDistance (μ i) ν) l (nhds 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun i ↦
      kolmogorovDistance_nonneg (μ i) ν
  · exact hbound
  · exact hrate

/-- Eventual Berry--Esseen bounds also imply pointwise convergence of the
CDFs. -/
theorem tendsto_cdf_of_eventually_kolmogorov_bound
    {ι : Type*} {l : Filter ι} (μ : ι → Measure ℝ) (ν : Measure ℝ)
    (rate : ι → ℝ)
    (hbound : ∀ᶠ i in l, kolmogorovDistance (μ i) ν ≤ rate i)
    (hrate : Tendsto rate l (nhds 0)) (x : ℝ) :
    Tendsto (fun i ↦ cdf (μ i) x) l (nhds (cdf ν x)) := by
  exact tendsto_cdf_of_tendsto_kolmogorovDistance μ ν
    (tendsto_kolmogorovDistance_of_eventually_bound
      μ ν rate hbound hrate) x

/-- Totalized law of the actual general-`R` statistic.  On admissible
dimensions this is exactly the Gaussian-data pushforward studied in the
papers; outside that range it is standard Gaussian. -/
def actualZRmpMeasureOrGaussian {p : ℕ} (m : ℕ)
    (R : CorrelationMatrix p) : Measure ℝ := by
  classical
  exact if Admissible m p then
      Measure.map (ZRmpStatistic m R) (standardGaussianDataMeasure m p)
    else gaussianReal 0 1

theorem actualZRmpMeasureOrGaussian_isProbability {p : ℕ} (m : ℕ)
    (R : CorrelationMatrix p) :
    IsProbabilityMeasure (actualZRmpMeasureOrGaussian m R) := by
  classical
  unfold actualZRmpMeasureOrGaussian
  by_cases h : Admissible m p
  · rw [if_pos h]
    exact Measure.isProbabilityMeasure_map
      (measurable_ZRmpStatistic R).aemeasurable
  · rw [if_neg h]
    infer_instance

/-- Probability-measure wrapper for the totalized actual law. -/
def actualZRmpProbabilityMeasureOrGaussian {p : ℕ} (m : ℕ)
    (R : CorrelationMatrix p) : ProbabilityMeasure ℝ :=
  ⟨actualZRmpMeasureOrGaussian m R,
    actualZRmpMeasureOrGaussian_isProbability m R⟩

@[simp]
theorem actualZRmpMeasureOrGaussian_eq_actual {m p : ℕ}
    (h : Admissible m p) (R : CorrelationMatrix p) :
    actualZRmpMeasureOrGaussian m R =
      Measure.map (ZRmpStatistic m R)
        (standardGaussianDataMeasure m p) := by
  simp [actualZRmpMeasureOrGaussian, h]

@[simp]
theorem actualZRmpMeasureOrGaussian_eq_gaussian {m p : ℕ}
    (h : ¬ Admissible m p) (R : CorrelationMatrix p) :
    actualZRmpMeasureOrGaussian m R = gaussianReal 0 1 := by
  simp [actualZRmpMeasureOrGaussian, h]

/-- Along an eventually admissible array, the totalized law is eventually
literally the pushforward law of the actual statistic. -/
theorem eventually_actualZRmpMeasureOrGaussian_eq_actual
    (m : ℕ → ℕ) (R : (p : ℕ) → CorrelationMatrix p)
    (hadm : ∀ᶠ p in atTop, Admissible (m p) p) :
    ∀ᶠ p in atTop,
      actualZRmpMeasureOrGaussian (m p) (R p) =
        Measure.map (ZRmpStatistic (m p) (R p))
          (standardGaussianDataMeasure (m p) p) := by
  filter_upwards [hadm] with p hp
  exact actualZRmpMeasureOrGaussian_eq_actual hp (R p)

/-- Finite Berry--Esseen bound written for the totalized law. -/
theorem kolmogorovDistance_actualZRmpMeasureOrGaussian_le
    {m p : ℕ} (h : Admissible m p) (R : CorrelationMatrix p) :
    kolmogorovDistance (actualZRmpMeasureOrGaussian m R)
        (gaussianReal 0 1) ≤ generalRFinalRateEnvelope m R := by
  rw [actualZRmpMeasureOrGaussian_eq_actual h R]
  exact kolmogorovDistance_ZRmpStatistic_le_finalRateEnvelope h R

/-- Sequential Kolmogorov CLT for arbitrary arrays of correlation matrices.
The sole dimension assumption is eventual admissibility
`2 ≤ p ≤ m(p)`. -/
theorem tendsto_kolmogorovDistance_actualZRmpMeasureOrGaussian_zero
    (m : ℕ → ℕ) (R : (p : ℕ) → CorrelationMatrix p)
    (hadm : ∀ᶠ p in atTop, Admissible (m p) p) :
    Tendsto (fun p ↦
      kolmogorovDistance
        (actualZRmpMeasureOrGaussian (m p) (R p))
        (gaussianReal 0 1)) atTop (nhds 0) := by
  apply tendsto_kolmogorovDistance_of_eventually_bound
      (fun p ↦ actualZRmpMeasureOrGaussian (m p) (R p))
      (gaussianReal 0 1)
      (fun p ↦ generalRFinalRateEnvelope (m p) (R p))
  · filter_upwards [hadm] with p hp
    exact kolmogorovDistance_actualZRmpMeasureOrGaussian_le hp (R p)
  · exact tendsto_generalRFinalRateEnvelope_zero m R hadm

/-- Pointwise-CDF form of the sequential general-`R` CLT. -/
theorem tendsto_cdf_actualZRmpMeasureOrGaussian
    (m : ℕ → ℕ) (R : (p : ℕ) → CorrelationMatrix p)
    (hadm : ∀ᶠ p in atTop, Admissible (m p) p) (x : ℝ) :
    Tendsto (fun p ↦
      cdf (actualZRmpMeasureOrGaussian (m p) (R p)) x)
      atTop (nhds (cdf (gaussianReal 0 1) x)) := by
  exact tendsto_cdf_of_tendsto_kolmogorovDistance
    (fun p ↦ actualZRmpMeasureOrGaussian (m p) (R p))
    (gaussianReal 0 1)
    (tendsto_kolmogorovDistance_actualZRmpMeasureOrGaussian_zero
      m R hadm) x

/-- The same CDF CLT stated directly for the actual Gaussian-data
pushforward.  The totalized theorem above explains why its finitely many
non-admissible initial indices are harmless. -/
theorem tendsto_cdf_ZRmpStatistic
    (m : ℕ → ℕ) (R : (p : ℕ) → CorrelationMatrix p)
    (hadm : ∀ᶠ p in atTop, Admissible (m p) p) (x : ℝ) :
    Tendsto (fun p ↦
      cdf
        (Measure.map (ZRmpStatistic (m p) (R p))
          (standardGaussianDataMeasure (m p) p)) x)
      atTop (nhds (cdf (gaussianReal 0 1) x)) := by
  exact tendsto_cdf_of_tendsto_kolmogorovDistance
    (fun p ↦ Measure.map (ZRmpStatistic (m p) (R p))
      (standardGaussianDataMeasure (m p) p))
    (gaussianReal 0 1)
    (tendsto_kolmogorovDistance_ZRmpStatistic_zero m R hadm) x

end

end LogdetLean
