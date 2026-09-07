import LogdetLean.GramHafnian.LocalAnticoncentration.MixtureDensity
import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-!
# Exact density of a finite circular Gaussian column

This experimental module packages the literal paper-normalized circular law
as one radial density on a finite complex coordinate space.  It is an
unconditional bridge from the existing scalar density theorem to the polar
coordinate machinery in Mathlib.
-/

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal NNReal Real

namespace LogdetLean.GramHafnian

noncomputable section

/-- Product density of `k` iid paper-normalized circular coordinates. -/
def circularGaussianRawVectorDensity (k : ℕ) (x : Fin k → ℂ) : ℝ≥0∞ :=
  ∏ i, localAnticoncentrationCircularGaussianDensity (x i)

@[fun_prop]
theorem measurable_circularGaussianRawVectorDensity (k : ℕ) :
    Measurable (circularGaussianRawVectorDensity k) := by
  unfold circularGaussianRawVectorDensity
  apply Finset.measurable_prod
  intro i hi
  exact measurable_localAnticoncentrationCircularGaussianDensity.comp
    (measurable_pi_apply i)

/-- Mapping measures by a measurable equivalence is injective. -/
private theorem map_measurableEquiv_injective
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) : Function.Injective (Measure.map e) := by
  intro μ ν h
  have h' := congrArg (Measure.map e.symm) h
  simpa [Measure.map_map, e.symm_apply_apply] using h'

/-- The finite iid circular law has the product of the scalar
`π⁻¹ exp (-|z|²)` densities with respect to product complex volume. -/
theorem pi_circularGaussian_eq_withDensity_rawVector (k : ℕ) :
    (Measure.pi fun _ : Fin k ↦ circularGaussian) =
      (volume : Measure (Fin k → ℂ)).withDensity
        (circularGaussianRawVectorDensity k) := by
  induction k with
  | zero =>
      rw [Measure.pi_of_empty, volume_pi, Measure.pi_of_empty]
      change Measure.dirac (fun a : Fin 0 ↦ isEmptyElim a) =
        (Measure.dirac (fun a : Fin 0 ↦ isEmptyElim a)).withDensity
          (circularGaussianRawVectorDensity 0)
      rw [dirac_withDensity'
        (measurable_circularGaussianRawVectorDensity 0)]
      simp [circularGaussianRawVectorDensity]
  | succ k ih =>
      let e : (Fin (k + 1) → ℂ) ≃ᵐ (ℂ × (Fin k → ℂ)) :=
        MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) ↦ ℂ) 0
      apply map_measurableEquiv_injective e
      have hpi :=
        (measurePreserving_piFinSuccAbove
          (fun _ : Fin (k + 1) ↦ circularGaussian) 0).map_eq
      have hvol :=
        (volume_preserving_piFinSuccAbove
          (fun _ : Fin (k + 1) ↦ ℂ) 0).map_eq
      rw [hpi]
      change circularGaussian.prod
          (Measure.pi fun _ : Fin k ↦ circularGaussian) = _
      rw [ih, circularGaussian_eq_withDensity_localAnticoncentration,
        prod_withDensity measurable_localAnticoncentrationCircularGaussianDensity
          (measurable_circularGaussianRawVectorDensity k)]
      rw [map_measurableEquiv_withDensity_localAnticoncentration e
          (volume : Measure (Fin (k + 1) → ℂ))
          (circularGaussianRawVectorDensity (k + 1))
          (measurable_circularGaussianRawVectorDensity (k + 1)),
        hvol]
      congr 1
      funext z
      change localAnticoncentrationCircularGaussianDensity z.1 *
          circularGaussianRawVectorDensity k z.2 =
        circularGaussianRawVectorDensity (k + 1) (e.symm z)
      unfold circularGaussianRawVectorDensity
      rw [Fin.prod_univ_succAbove _ 0]
      rfl

end

end LogdetLean.GramHafnian
