import LogdetLean.GramHafnian.SymmetricGaussianLimit.Parameters
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Small-ball bounds pass to weak limits

This module isolates the Portmanteau step used when a finite-dimensional
Gaussian transpose-Gram law converges to an independent complex-symmetric
Gaussian law.  The statement is deliberately generic: any quadratic raw
radius bound with a convergent coefficient passes to the weak limit.
-/

open Filter MeasureTheory Metric Set

namespace LogdetLean.GramHafnian.SymmetricGaussianLimit

noncomputable section

/-- Open-ball form of the transfer. -/
theorem openBall_measure_le_of_weakLimit
    (muSeq : ℕ → ProbabilityMeasure ℂ) (mu : ProbabilityMeasure ℂ)
    (rawCoeffSeq : ℕ → ℝ) (rawCoeff : ℝ)
    (hmu : Tendsto muSeq atTop (nhds mu))
    (hcoeff : Tendsto rawCoeffSeq atTop (nhds rawCoeff))
    (z : ℂ)
    (hfinite : ∀ᶠ k : ℕ in atTop, ∀ r : ℝ, 0 < r →
      (muSeq k : Measure ℂ) (Metric.closedBall z r) ≤
        ENNReal.ofReal (rawCoeffSeq k * r ^ 2))
    (r : ℝ) (hr : 0 < r) :
    (mu : Measure ℂ) (Metric.ball z r) ≤
      ENNReal.ofReal (rawCoeff * r ^ 2) := by
  have hopen :
      (mu : Measure ℂ) (Metric.ball z r) ≤
        atTop.liminf (fun k ↦
          (muSeq k : Measure ℂ) (Metric.ball z r)) :=
    ProbabilityMeasure.le_liminf_measure_open_of_tendsto
      hmu Metric.isOpen_ball
  have hpointwise : ∀ᶠ k : ℕ in atTop,
      (muSeq k : Measure ℂ) (Metric.ball z r) ≤
        ENNReal.ofReal (rawCoeffSeq k * r ^ 2) := by
    filter_upwards [hfinite] with k hk
    exact (measure_mono Metric.ball_subset_closedBall).trans (hk r hr)
  have hliminf :
      atTop.liminf (fun k ↦
          (muSeq k : Measure ℂ) (Metric.ball z r)) ≤
        atTop.liminf (fun k ↦
          ENNReal.ofReal (rawCoeffSeq k * r ^ 2)) :=
    Filter.liminf_le_liminf hpointwise
  have hrhs : Tendsto
      (fun k : ℕ ↦ ENNReal.ofReal (rawCoeffSeq k * r ^ 2))
      atTop (nhds (ENNReal.ofReal (rawCoeff * r ^ 2))) :=
    ENNReal.tendsto_ofReal (hcoeff.mul_const (r ^ 2))
  exact hopen.trans (hliminf.trans_eq hrhs.liminf_eq)

/-- Closed-ball form.  The proof first uses Portmanteau on every slightly
larger open ball and then decreases the radius to the requested one. -/
theorem closedBall_measure_le_of_weakLimit
    (muSeq : ℕ → ProbabilityMeasure ℂ) (mu : ProbabilityMeasure ℂ)
    (rawCoeffSeq : ℕ → ℝ) (rawCoeff : ℝ)
    (hmu : Tendsto muSeq atTop (nhds mu))
    (hcoeff : Tendsto rawCoeffSeq atTop (nhds rawCoeff))
    (z : ℂ)
    (hfinite : ∀ᶠ k : ℕ in atTop, ∀ r : ℝ, 0 < r →
      (muSeq k : Measure ℂ) (Metric.closedBall z r) ≤
        ENNReal.ofReal (rawCoeffSeq k * r ^ 2))
    (r : ℝ) (hr : 0 ≤ r) :
    (mu : Measure ℂ) (Metric.closedBall z r) ≤
      ENNReal.ofReal (rawCoeff * r ^ 2) := by
  let rSeq : ℕ → ℝ := fun m ↦ r + 1 / ((m : ℝ) + 1)
  have hrSeq_gt (m : ℕ) : r < rSeq m := by
    dsimp [rSeq]
    have hm : 0 < (m : ℝ) + 1 := by positivity
    linarith [one_div_pos.mpr hm]
  have hrSeq_pos (m : ℕ) : 0 < rSeq m :=
    lt_of_le_of_lt hr (hrSeq_gt m)
  have h_each (m : ℕ) :
      (mu : Measure ℂ) (Metric.closedBall z r) ≤
        ENNReal.ofReal (rawCoeff * (rSeq m) ^ 2) := by
    exact (measure_mono (Metric.closedBall_subset_ball (hrSeq_gt m))).trans
      (openBall_measure_le_of_weakLimit muSeq mu rawCoeffSeq rawCoeff
        hmu hcoeff z hfinite (rSeq m) (hrSeq_pos m))
  have hrSeq_tendsto : Tendsto rSeq atTop (nhds r) := by
    simpa [rSeq, Nat.cast_add, Nat.cast_one] using
      tendsto_const_nhds.add
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun m : ℕ ↦ (1 : ℝ) / (m + 1)) atTop (nhds 0))
  have hrhs : Tendsto
      (fun m : ℕ ↦ ENNReal.ofReal (rawCoeff * (rSeq m) ^ 2))
      atTop (nhds (ENNReal.ofReal (rawCoeff * r ^ 2))) :=
    ENNReal.tendsto_ofReal (tendsto_const_nhds.mul (hrSeq_tendsto.pow 2))
  exact ge_of_tendsto' hrhs h_each

/-- Normalized form used by the Gaussian transpose-Gram limit.  Both the
finite reference scale and the finite quadratic coefficient may vary. -/
theorem normalized_closedBall_measure_le_of_weakLimit
    (muSeq : ℕ → ProbabilityMeasure ℂ) (mu : ProbabilityMeasure ℂ)
    (scaleSeq : ℕ → ℝ) (scale : ℝ)
    (coeffSeq : ℕ → ℝ) (coeff : ℝ)
    (hmu : Tendsto muSeq atTop (nhds mu))
    (hscale : Tendsto scaleSeq atTop (nhds scale))
    (hscale_pos : 0 < scale)
    (hscaleSeq_pos : ∀ᶠ k : ℕ in atTop, 0 < scaleSeq k)
    (hcoeff : Tendsto coeffSeq atTop (nhds coeff))
    (z : ℂ)
    (hfinite : ∀ᶠ k : ℕ in atTop, ∀ eps : ℝ, 0 < eps →
      (muSeq k : Measure ℂ)
          (Metric.closedBall z (eps * scaleSeq k)) ≤
        ENNReal.ofReal (coeffSeq k * eps ^ 2))
    (eps : ℝ) (heps : 0 ≤ eps) :
    (mu : Measure ℂ) (Metric.closedBall z (eps * scale)) ≤
      ENNReal.ofReal (coeff * eps ^ 2) := by
  let rawCoeffSeq : ℕ → ℝ :=
    fun k ↦ coeffSeq k / (scaleSeq k) ^ 2
  let rawCoeff : ℝ := coeff / scale ^ 2
  have hrawCoeff : Tendsto rawCoeffSeq atTop (nhds rawCoeff) := by
    dsimp [rawCoeffSeq, rawCoeff]
    exact hcoeff.div (hscale.pow 2) (pow_ne_zero _ hscale_pos.ne')
  have hrawFinite : ∀ᶠ k : ℕ in atTop, ∀ r : ℝ, 0 < r →
      (muSeq k : Measure ℂ) (Metric.closedBall z r) ≤
        ENNReal.ofReal (rawCoeffSeq k * r ^ 2) := by
    filter_upwards [hscaleSeq_pos, hfinite] with k hskpos hk
    intro r hr
    have hsk : scaleSeq k ≠ 0 := hskpos.ne'
    have h := hk (r / scaleSeq k) (div_pos hr hskpos)
    convert h using 1
    · field_simp
    · congr 1
      dsimp [rawCoeffSeq]
      field_simp
  have hraw := closedBall_measure_le_of_weakLimit
    muSeq mu rawCoeffSeq rawCoeff hmu hrawCoeff z hrawFinite
    (eps * scale) (mul_nonneg heps hscale_pos.le)
  convert hraw using 1
  congr 1
  dsimp [rawCoeff]
  field_simp

end

end LogdetLean.GramHafnian.SymmetricGaussianLimit
