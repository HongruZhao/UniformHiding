import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Information theoretic wrappers for sparse hiding

Mathlib supplies the KL data processing inequality.  At this revision it does
not supply Pinsker's inequality under a named total variation distance, so the
Pinsker conversion below is deliberately stated as an algebraic implication
from its standard squared premise.
-/

open MeasureTheory
open scoped ENNReal

namespace LogdetLean.GramHafnian.UltimateHiding.Sparse

/-- KL divergence cannot increase under the measurable Gram map, or under any
other measurable deterministic statistic. -/
theorem klDiv_statistic_le
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (mu nu : Measure X) [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (statistic : X → Y) (hstatistic : Measurable statistic) :
    InformationTheory.klDiv (mu.map statistic) (nu.map statistic)
      ≤ InformationTheory.klDiv mu nu :=
  InformationTheory.klDiv_map_le mu nu hstatistic

/-- The real algebraic content of Pinsker: its squared premise implies the
usual square root estimate. -/
theorem pinsker_squared_to_sqrt
    {tv divergence : ℝ} (htv : 0 ≤ tv)
    (hpinsker : 2 * tv ^ 2 ≤ divergence) :
    tv ≤ Real.sqrt (divergence / 2) := by
  have hsq : tv ^ 2 ≤ divergence / 2 := by linarith
  have hsqrt := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg htv] at hsqrt
  exact hsqrt

/-- Pinsker followed by an externally established finite KL upper bound. -/
theorem pinsker_with_kl_upper_bound
    {tv divergence bound : ℝ}
    (htv : 0 ≤ tv)
    (hpinsker : 2 * tv ^ 2 ≤ divergence)
    (hKL : divergence ≤ bound) :
    tv ≤ Real.sqrt (bound / 2) := by
  have hfirst := pinsker_squared_to_sqrt htv hpinsker
  have hhalf : divergence / 2 ≤ bound / 2 := by linarith
  exact hfirst.trans (Real.sqrt_le_sqrt hhalf)

/-- Substitution of the finite sparse scalar KL estimate into Pinsker. -/
theorem pinsker_finite_sparse_kl
    {tv divergence p q s M : ℝ}
    (htv : 0 ≤ tv)
    (hpinsker : 2 * tv ^ 2 ≤ divergence)
    (hKL : divergence ≤ p * q * s ^ 2 / (2 * M ^ 2)) :
    tv ≤ Real.sqrt (p * q * s ^ 2 / (4 * M ^ 2)) := by
  have h := pinsker_with_kl_upper_bound htv hpinsker hKL
  convert h using 1
  ring_nf

/-- Closed form of the square root produced by Pinsker in the sparse block
calculation. -/
theorem sqrt_finite_sparse_bound
    {p q s M : ℝ} (hpq : 0 ≤ p * q) (hs : 0 ≤ s) (hM : 0 < M) :
    Real.sqrt (p * q * s ^ 2 / (4 * M ^ 2)) =
      s * Real.sqrt (p * q) / (2 * M) := by
  have hnum : 0 ≤ p * q * s ^ 2 := mul_nonneg hpq (sq_nonneg s)
  rw [Real.sqrt_div hnum]
  rw [Real.sqrt_mul hpq, Real.sqrt_sq_eq_abs, abs_of_nonneg hs]
  have hsqrtDen : Real.sqrt (4 * M ^ 2) = 2 * M := by
    have htwoM : 0 ≤ 2 * M := by positivity
    calc
      Real.sqrt (4 * M ^ 2) = Real.sqrt ((2 * M) ^ 2) := by ring_nf
      _ = 2 * M := by rw [Real.sqrt_sq_eq_abs, abs_of_nonneg htwoM]
  rw [hsqrtDen]
  ring

/-- Publication facing Pinsker conversion with the explicit finite block
constant. -/
theorem pinsker_finite_sparse_rate
    {tv divergence p q s M : ℝ}
    (htv : 0 ≤ tv) (hp : 0 ≤ p) (hq : 0 ≤ q) (hs : 0 ≤ s) (hM : 0 < M)
    (hpinsker : 2 * tv ^ 2 ≤ divergence)
    (hKL : divergence ≤ p * q * s ^ 2 / (2 * M ^ 2)) :
    tv ≤ s * Real.sqrt (p * q) / (2 * M) := by
  have h := pinsker_finite_sparse_kl htv hpinsker hKL
  rw [sqrt_finite_sparse_bound (mul_nonneg hp hq) hs hM] at h
  exact h

end LogdetLean.GramHafnian.UltimateHiding.Sparse
