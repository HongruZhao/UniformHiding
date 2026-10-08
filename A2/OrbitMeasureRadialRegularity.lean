import A2.TakagiOrbit

open MeasureTheory MeasureTheory.Measure Set Function
open scoped BigOperators ENNReal

noncomputable section

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

set_option maxHeartbeats 600000

/-- The positive, distinct squared-radius domain of the regular orbit. -/
def regularTakagiSquaredRadii (N : ℕ) : Set (Fin N → ℝ) :=
  {lambda | IsRegularTakagiSpectrum lambda}

theorem continuous_vandermondeAbs (N : ℕ) : Continuous (H6DensityTransform.vandermondeAbs N) := by
  unfold H6DensityTransform.vandermondeAbs
  fun_prop

theorem vandermondeAbs_nonneg {N : ℕ} (lambda : Fin N → ℝ) :
    0 ≤ H6DensityTransform.vandermondeAbs N lambda :=
  Finset.prod_nonneg fun _ _ ↦ abs_nonneg _

theorem vandermondeAbs_ne_zero_iff_injective {N : ℕ} (lambda : Fin N → ℝ) :
    H6DensityTransform.vandermondeAbs N lambda ≠ 0 ↔ Injective lambda := by
  classical
  unfold H6DensityTransform.vandermondeAbs
  rw [Finset.prod_ne_zero_iff]
  constructor
  · intro h i j hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hp : (i, j) ∈ H6DensityTransform.strictPairs N := by simp [H6DensityTransform.strictPairs, hlt]
      exact (h (i, j) hp) (by simp [hij])
    · have hp : (j, i) ∈ H6DensityTransform.strictPairs N := by simp [H6DensityTransform.strictPairs, hgt]
      exact (h (j, i) hp) (by simp [hij])
  · intro h p hp
    have hlt : p.1 < p.2 := (Finset.mem_filter.mp hp).2
    exact abs_ne_zero.mpr (sub_ne_zero.mpr (fun he ↦ hlt.ne (h he)))

theorem vandermondeAbs_pos_iff_injective {N : ℕ} (lambda : Fin N → ℝ) :
    0 < H6DensityTransform.vandermondeAbs N lambda ↔ Injective lambda := by
  rw [← vandermondeAbs_ne_zero_iff_injective]
  exact ⟨ne_of_gt, fun h ↦ lt_of_le_of_ne (vandermondeAbs_nonneg lambda) h.symm⟩

theorem isOpen_regularTakagiSquaredRadii (N : ℕ) : IsOpen (regularTakagiSquaredRadii N) := by
  have horth : IsOpen (H6CoordinateAlgebra.openPositiveOrthant N) := by
    unfold H6CoordinateAlgebra.openPositiveOrthant
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun (i : Fin N) ↦ (isOpen_Ioi : IsOpen (Ioi (0 : ℝ))).preimage
      (show Continuous (fun lambda : Fin N → ℝ ↦ lambda i) from continuous_apply i)
  have he : regularTakagiSquaredRadii N = H6CoordinateAlgebra.openPositiveOrthant N ∩
      {lambda | 0 < H6DensityTransform.vandermondeAbs N lambda} := by
    ext lambda
    simp only [regularTakagiSquaredRadii, IsRegularTakagiSpectrum, mem_ofPred_eq,
      mem_inter_iff, H6CoordinateAlgebra.openPositiveOrthant, vandermondeAbs_pos_iff_injective]
  rw [he]
  exact horth.inter (isOpen_Ioi.preimage (continuous_vandermondeAbs N))

theorem a2_measurable_takagiFlatEigenvalueDensity (N : ℕ) :
    Measurable (takagiFlatEigenvalueDensity N) :=
  (continuous_vandermondeAbs N).measurable.ennreal_ofReal

/-- The Vandermonde density gives every repeated-radius point zero mass.
Consequently regularity does not change the actual flat radial measure. -/
theorem ae_mem_regularTakagiSquaredRadii_radialMeasure (N : ℕ) :
    ∀ᵐ lambda ∂takagiFlatEigenvalueRadialMeasure N,
      lambda ∈ regularTakagiSquaredRadii N := by
  unfold takagiFlatEigenvalueRadialMeasure
  rw [ae_withDensity_iff (a2_measurable_takagiFlatEigenvalueDensity N)]
  have horth : MeasurableSet (H6CoordinateAlgebra.openPositiveOrthant N) := by
    unfold H6CoordinateAlgebra.openPositiveOrthant
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter fun (i : Fin N) ↦ (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ))).preimage
      (show Measurable (fun lambda : Fin N → ℝ ↦ lambda i) from measurable_pi_apply i)
  filter_upwards [ae_restrict_mem horth] with lambda hlambda hdensity
  refine ⟨hlambda, (vandermondeAbs_ne_zero_iff_injective lambda).mp ?_⟩
  intro hz
  apply hdensity
  simp [takagiFlatEigenvalueDensity, hz]

theorem regular_radial_withDensity_eq_flat (N : ℕ) :
    (volume.restrict (regularTakagiSquaredRadii N)).withDensity
      (takagiFlatEigenvalueDensity N) = takagiFlatEigenvalueRadialMeasure N := by
  have hreg := (isOpen_regularTakagiSquaredRadii N).measurableSet
  have hsub : regularTakagiSquaredRadii N ⊆ H6CoordinateAlgebra.openPositiveOrthant N := fun _ h ↦ h.1
  have he := restrict_eq_self_of_ae_mem (ae_mem_regularTakagiSquaredRadii_radialMeasure N)
  rw [takagiFlatEigenvalueRadialMeasure, restrict_withDensity hreg,
    restrict_restrict hreg, inter_eq_left.mpr hsub] at he
  exact he

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
