import LogdetLean.GramHafnian.ShiftedAnticoncentration.Experimental.GaussianPolar.PiCircularDensity

/-!
# The literal circular law as a radial density on complex Euclidean space
-/

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal NNReal Real

namespace LogdetLean.GramHafnian

noncomputable section

/-- The additive Haar measure obtained by transporting product complex volume
to the paper's Euclidean realization. -/
def circularEuclideanVolume (k : ℕ) : Measure (CircularEuclideanSpace k) :=
  Measure.map (WithLp.toLp 2) (volume : Measure (Fin k → ℂ))

instance circularEuclideanVolume_isAddHaarMeasure (k : ℕ) :
    (circularEuclideanVolume k).IsAddHaarMeasure := by
  unfold circularEuclideanVolume
  rw [← PiLp.coe_symm_continuousLinearEquiv (p := 2) (𝕜 := ℝ)
    (β := fun _ : Fin k ↦ ℂ)]
  infer_instance

/-- Radial density of the paper-normalized circular column. -/
def circularGaussianEuclideanDensity (k : ℕ)
    (x : CircularEuclideanSpace k) : ℝ≥0∞ :=
  ENNReal.ofReal ((Real.pi⁻¹) ^ k * Real.exp (-‖x‖ ^ 2))

@[fun_prop]
theorem measurable_circularGaussianEuclideanDensity (k : ℕ) :
    Measurable (circularGaussianEuclideanDensity k) := by
  unfold circularGaussianEuclideanDensity
  fun_prop

private theorem rawVectorDensity_eq_radial (k : ℕ) (x : Fin k → ℂ) :
    circularGaussianRawVectorDensity k x =
      circularGaussianEuclideanDensity k (WithLp.toLp 2 x) := by
  unfold circularGaussianRawVectorDensity localAnticoncentrationCircularGaussianDensity
    circularGaussianEuclideanDensity
  rw [← ENNReal.ofReal_prod_of_nonneg]
  · congr 1
    rw [Finset.prod_mul_distrib, Finset.prod_const]
    simp only [Finset.card_univ, Fintype.card_fin]
    rw [← Real.exp_sum]
    congr 1
    rw [EuclideanSpace.norm_sq_eq]
    simp only [norm_neg, Finset.sum_neg_distrib]
  · intro i hi
    positivity

/-- Exact radial density statement on `CircularEuclideanSpace k`. -/
theorem circularGaussianEuclidean_eq_withDensity (k : ℕ) :
    ((Measure.pi fun _ : Fin k ↦ circularGaussian).map (WithLp.toLp 2)) =
      (circularEuclideanVolume k).withDensity
        (circularGaussianEuclideanDensity k) := by
  rw [pi_circularGaussian_eq_withDensity_rawVector]
  let e : (Fin k → ℂ) ≃ᵐ CircularEuclideanSpace k :=
    MeasurableEquiv.toLp 2 (Fin k → ℂ)
  rw [show (WithLp.toLp 2 : (Fin k → ℂ) → CircularEuclideanSpace k) = e by rfl]
  rw [map_measurableEquiv_withDensity_localAnticoncentration e
    (volume : Measure (Fin k → ℂ))
    (circularGaussianRawVectorDensity k)
    (measurable_circularGaussianRawVectorDensity k)]
  unfold circularEuclideanVolume
  congr 1
  funext x
  change circularGaussianRawVectorDensity k (WithLp.ofLp x) =
    circularGaussianEuclideanDensity k x
  simpa using rawVectorDensity_eq_radial k (WithLp.ofLp x)

end

end LogdetLean.GramHafnian
