import LogdetLean.GeneralRDecomposition
import LogdetLean.GeneralRLeadingVarianceAlgebra
import LogdetLean.GeneralRResidualCovariance

/-!
# The actual standardized general-correlation statistic

This module gives one public name to the random variable studied in both
papers and transfers its law to the exact common-space decomposition
`(M_R-E_R)/s_R`.
-/

namespace LogdetLean

noncomputable section

open MeasureTheory ProbabilityTheory

/-- The sample-correlation log determinant, centered by the exact
deterministic center and divided by the proxy scale `s_R`. -/
def ZRmpStatistic {p : ℕ} (m : ℕ) (R : CorrelationMatrix p)
    (z : GaussianData m p) : ℝ :=
  (Real.log (GeneralRDecomposition.sampleCorrelation R z).det -
      GeneralRDecomposition.logDetCenter m R) /
    generalRProxyScale m R

theorem measurable_ZRmpStatistic {m p : ℕ} (R : CorrelationMatrix p) :
    Measurable (ZRmpStatistic m R) := by
  unfold ZRmpStatistic
  exact ((GeneralRDecomposition.measurable_log_det_sampleCorrelation R).sub
    measurable_const).div_const _

/-- The actual statistic has exactly the law of the proved common-space
decomposition.  This uses equality almost surely, not an informal Slutsky
replacement. -/
theorem map_ZRmpStatistic_eq_map_centeredDecomposition
    {m p : ℕ} (hp : p ≤ m) (R : CorrelationMatrix p) :
    Measure.map (ZRmpStatistic m R)
        (standardGaussianDataMeasure m p) =
      Measure.map
        (fun z ↦
          (GeneralRDecomposition.M_R m R z -
            GeneralRDecomposition.E_R m R z) /
              generalRProxyScale m R)
        (standardGaussianDataMeasure m p) := by
  apply Measure.map_congr
  filter_upwards
      [GeneralRDecomposition.ae_centered_log_det_eq_M_R_sub_E_R hp R]
      with z hz
  unfold ZRmpStatistic
  rw [hz]

/-- The complete nonlinear-remainder transfer for the actual statistic.  The
only term left to bound is the leading variable `M_R/s_R`. -/
theorem kolmogorovDistance_ZRmpStatistic_le_leading_add_cubeRoot
    {m p : ℕ} (h : Admissible m p) (R : CorrelationMatrix p) :
    kolmogorovDistance
        (Measure.map (ZRmpStatistic m R)
          (standardGaussianDataMeasure m p))
        (gaussianReal 0 1) ≤
      kolmogorovDistance
          (Measure.map
            (fun z ↦ GeneralRDecomposition.M_R m R z /
              generalRProxyScale m R)
            (standardGaussianDataMeasure m p))
          (gaussianReal 0 1) +
        generalRNonlinearCubeRootRate m R +
          generalRNonlinearCubeRootRate m R /
            Real.sqrt (2 * Real.pi) := by
  rw [map_ZRmpStatistic_eq_map_centeredDecomposition h.2 R]
  exact
    GeneralRDecomposition.kolmogorovDistance_centeredDecomposition_proxyScale_le
      h R

end

end LogdetLean
