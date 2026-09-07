import LogdetLean.GramHafnian.ThreePaper.AC2NegativeMoments
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
# matrix-law endpoint: Gaussian Gram-hafnian anticoncentration

This is the public import surface for the anticoncentration Article.  It has
no hiding assumption and imports no uniformly-hiding theorem.  The principal
endpoint is the finite, uniformly shifted, probability-capped disk bound.
-/

namespace LogdetLean.GramHafnian.ThreePaper.GaussianAnticoncentration

noncomputable section

open MeasureTheory Set

/-- The Article's main theorem: for every `n >= 1`, `k >= 4 n`, every
complex center, and every nonnegative normalized radius, the Gaussian
transpose-Gram hafnian has quadratic small-ball decay. -/
theorem shiftedSmallBall
    (n k : ℕ) (hn : 1 ≤ n) (hk : 4 * n ≤ k)
    (z : ℂ) (eps : ℝ) (heps : 0 ≤ eps) :
    gramHafnianShiftedSmallBallProbability k n z eps ≤
      min 1 (shiftedAnticoncentrationConstant k n * eps ^ 2) :=
  gaussianGramHafnianShiftedAnticoncentration_min
    n k hn hk z eps heps

/-- Robustness extension: an arbitrary random matrix may be added to the
Gaussian factor before the transpose-Gram map, provided the complete shift
matrix is independent of the complete Gaussian matrix. -/
theorem independentMatrixShiftSmallBall
    (n k : ℕ) (hn : 1 ≤ n) (hk : 4 * n ≤ k)
    (nu : Measure (ComplexColumnMatrix n k)) [IsProbabilityMeasure nu]
    (w : ℂ) (eps : ℝ) (heps : 0 < eps) :
    ((circularGaussianColumnMatrixMeasure n k).prod nu).real
        {p | ‖gramHafnianObservable n k
          (fun i => p.1 i + p.2 i) - w‖ ≤
            eps * gramHafnianSigma k n} ≤
      min 1 (Real.exp 1 * shiftedAnticoncentrationConstant k n * eps ^ 2) :=
  independentFactorShift_normalizedSmallBall hn hk nu w eps heps

/-- The exact uncapped form used by the manuscript composition theorem. -/
theorem shiftedSmallBall_uncapped
    (n k : ℕ) (hn : 1 ≤ n) (hk : 4 * n ≤ k)
    (z : ℂ) (eps : ℝ) (heps : 0 ≤ eps) :
    gramHafnianShiftedSmallBallProbability k n z eps ≤
      shiftedAnticoncentrationConstant k n * eps ^ 2 :=
  gaussianGramHafnianShiftedAnticoncentration
    n k hn hk z eps heps

/-- Exact Gamma-product identity for the finite coefficient. -/
theorem exactCoefficient
    (n k : ℕ) (hn : 1 ≤ n) (hk : 4 * n ≤ k) :
    shiftedAnticoncentrationConstant k n =
      LocalAnticoncentration.paperBn n *
        ((k : ℝ) / ((k : ℝ) - 1)) *
        ((2 : ℝ) ^ (n - 1) / (4 : ℝ) ^ (n - 1)) *
        (Real.Gamma ((k : ℝ) / 2 + (n : ℝ)) /
          Real.Gamma ((k : ℝ) / 2 + 1)) *
        (Real.Gamma (((k : ℝ) - 4 * (n : ℝ) + 1) / 4) /
          Real.Gamma (((k : ℝ) - 3) / 4)) := by
  simpa [LocalAnticoncentration.paperBn, LocalAnticoncentration.gammaAnticoncentrationConstant] using
    LocalAnticoncentration.shiftedAnticoncentrationConstant_eq_gamma k n hn hk

/-! ## Finite-precision consequences -/

/-- The lower-tail probability of the normalized shifted intensity
`Q_z = |H-z|^2 / sigma^2`, written through the exact small-ball observable.
This definition avoids introducing a second copy of the Gaussian experiment. -/
def normalizedIntensityLowerTailProbability
    (k n : ℕ) (z : ℂ) (t : ℝ) : ℝ :=
  gramHafnianShiftedSmallBallProbability k n z (Real.sqrt t)

/-- AC1: the quadratic amplitude small-ball estimate is a linear lower-tail
estimate for normalized intensity. -/
theorem normalizedIntensityLowerTail
    (n k : ℕ) (hn : 1 ≤ n) (hk : 4 * n ≤ k)
    (z : ℂ) (t : ℝ) (ht : 0 ≤ t) :
    normalizedIntensityLowerTailProbability k n z t ≤
      min 1 (shiftedAnticoncentrationConstant k n * t) := by
  simpa [normalizedIntensityLowerTailProbability, Real.sq_sqrt ht] using
    shiftedSmallBall n k hn hk z (Real.sqrt t) (Real.sqrt_nonneg t)

/-- AC3: the normalized denominator-resolution tail at `b` binary digits. -/
theorem normalizedDenominatorResolution
    (n k : ℕ) (hn : 1 ≤ n) (hk : 4 * n ≤ k)
    (z : ℂ) (b : ℕ) :
    normalizedIntensityLowerTailProbability k n z (((2 : ℝ) ^ b)⁻¹) ≤
      min 1
        (shiftedAnticoncentrationConstant k n * ((2 : ℝ) ^ b)⁻¹) := by
  apply normalizedIntensityLowerTail n k hn hk z
  positivity

/-- The purely numerical bit-budget implication used to read AC3: if
`B * 2^{-b} <= delta`, then the lower-tail failure probability is at most
`delta`. -/
theorem normalizedDenominatorResolution_of_budget
    (n k : ℕ) (hn : 1 ≤ n) (hk : 4 * n ≤ k)
    (z : ℂ) (b : ℕ) {delta : ℝ}
    (hbudget :
      shiftedAnticoncentrationConstant k n * ((2 : ℝ) ^ b)⁻¹ ≤ delta) :
    normalizedIntensityLowerTailProbability k n z (((2 : ℝ) ^ b)⁻¹) ≤
      delta := by
  exact (normalizedDenominatorResolution n k hn hk z b).trans
    ((min_le_right _ _).trans hbudget)

end

end LogdetLean.GramHafnian.ThreePaper.GaussianAnticoncentration

#print axioms LogdetLean.GramHafnian.ThreePaper.GaussianAnticoncentration.shiftedSmallBall
#print axioms LogdetLean.GramHafnian.ThreePaper.GaussianAnticoncentration.independentMatrixShiftSmallBall
#print axioms LogdetLean.GramHafnian.ThreePaper.GaussianAnticoncentration.exactCoefficient
#print axioms LogdetLean.GramHafnian.ThreePaper.GaussianAnticoncentration.PaperEndpoints.result_thm_main_finite
#print axioms LogdetLean.GramHafnian.ThreePaper.GaussianAnticoncentration.PaperEndpoints.result_cor_exact_local_power_of_inverse
#print axioms LogdetLean.GramHafnian.ThreePaper.GaussianAnticoncentration.PaperEndpoints.result_lemma_radial_angular_factorization_of_inverse
#print axioms LogdetLean.GramHafnian.ThreePaper.GaussianAnticoncentration.negativeRpowMoment_le_of_powerLowerTail
#print axioms LogdetLean.GramHafnian.ThreePaper.GaussianAnticoncentration.normalizedShiftedIntensity_negativeMoment
#print axioms LogdetLean.GramHafnian.ThreePaper.GaussianAnticoncentration.normalizedShiftedIntensity_relativeErrorMoment
#print axioms LogdetLean.GramHafnian.ThreePaper.GaussianAnticoncentration.normalizedShiftedIntensity_negativeMoment_eq_top
#print axioms LogdetLean.GramHafnian.ThreePaper.GaussianAnticoncentration.gaussianGBSPatternWeight_eq_reference_mul_normalizedIntensity
#print axioms LogdetLean.GramHafnian.ThreePaper.GaussianAnticoncentration.additiveToRelative_of_lowerTail
#print axioms LogdetLean.GramHafnian.ThreePaper.GaussianAnticoncentration.normalizedDenominatorResolutionReal_of_logBudget
