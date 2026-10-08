import A2.OrbitMeasureRadialRegularity

open MeasureTheory MeasureTheory.Measure Set Function
open scoped BigOperators ENNReal

noncomputable section

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

theorem measurableSet_regularTakagiSquaredRadii (N : ℕ) :
    MeasurableSet (regularTakagiSquaredRadii N) :=
  (isOpen_regularTakagiSquaredRadii N).measurableSet

theorem exists_vanishing_strictPair_of_not_injective {N : ℕ}
    (lambda : Fin N → ℝ) (h : ¬ Injective lambda) :
    ∃ p ∈ H6DensityTransform.strictPairs N, |lambda p.1 - lambda p.2| = 0 := by
  obtain ⟨i, j, he, hij⟩ := Function.not_injective_iff.mp h
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact ⟨(i, j), by simp [H6DensityTransform.strictPairs, hlt], by simp [he]⟩
  · exact ⟨(j, i), by simp [H6DensityTransform.strictPairs, hgt], by simp [he]⟩

theorem vandermondeAbs_eq_zero_of_not_injective {N : ℕ}
    (lambda : Fin N → ℝ) (h : ¬ Injective lambda) :
    H6DensityTransform.vandermondeAbs N lambda = 0 := by
  obtain ⟨p, hp, hz⟩ := exists_vanishing_strictPair_of_not_injective lambda h
  exact Finset.prod_eq_zero hp hz

theorem takagiFlatEigenvalueDensity_eq_zero_of_not_injective {N : ℕ}
    (lambda : Fin N → ℝ) (h : ¬ Injective lambda) :
    takagiFlatEigenvalueDensity N lambda = 0 := by
  simp [takagiFlatEigenvalueDensity, vandermondeAbs_eq_zero_of_not_injective lambda h]

/-- The collision restriction is exact for any underlying measure, since
the literal Vandermonde product already vanishes on every collision. -/
theorem takagi_radial_withDensity_eq_regularRestriction {N : ℕ}
    (mu : Measure (Fin N → ℝ)) :
    (mu.restrict (H6CoordinateAlgebra.openPositiveOrthant N)).withDensity (takagiFlatEigenvalueDensity N) =
      (mu.restrict (regularTakagiSquaredRadii N)).withDensity
        (takagiFlatEigenvalueDensity N) := by
  have horth : MeasurableSet (H6CoordinateAlgebra.openPositiveOrthant N) := by
    unfold H6CoordinateAlgebra.openPositiveOrthant
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter fun i : Fin N =>
      measurableSet_Ioi.preimage (measurable_pi_apply i)
  rw [← withDensity_indicator horth,
    ← withDensity_indicator (measurableSet_regularTakagiSquaredRadii N)]
  apply withDensity_congr_ae
  filter_upwards [] with lambda
  by_cases hp : lambda ∈ H6CoordinateAlgebra.openPositiveOrthant N
  · by_cases hi : Injective lambda
    · have hr : lambda ∈ regularTakagiSquaredRadii N := ⟨hp, hi⟩
      simp only [Set.indicator_of_mem hp, Set.indicator_of_mem hr]
    · have hr : lambda ∉ regularTakagiSquaredRadii N := fun h => hi h.2
      simp [hp, hr, takagiFlatEigenvalueDensity_eq_zero_of_not_injective lambda hi]
  · have hr : lambda ∉ regularTakagiSquaredRadii N := fun h => hp h.1
    simp [hp, hr]

theorem takagiFlatEigenvalueRadialMeasure_eq_regularRestriction (N : ℕ) :
    takagiFlatEigenvalueRadialMeasure N =
      (volume.restrict (regularTakagiSquaredRadii N)).withDensity
        (fun lambda => ENNReal.ofReal (H6DensityTransform.vandermondeAbs N lambda)) := by
  exact takagi_radial_withDensity_eq_regularRestriction volume

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
