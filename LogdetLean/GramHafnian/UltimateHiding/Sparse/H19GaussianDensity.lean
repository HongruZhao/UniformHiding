import LogdetLean.GramHafnian.UltimateHiding.Sparse.CircularGaussianDensityBasic
import LogdetLean.GramHafnian.UltimateHiding.Sparse.FinitePiWithDensity
import LogdetLean.GramHafnian.UltimateHiding.Sparse.H19JiangRawDensity

/-!
# Explicit density of the rectangular complex Gaussian reference law

This module lifts the scalar density `pi⁻¹ exp (-|z|²)` through the two
finite coordinate products defining a rectangular matrix of independent
standard circular complex Gaussians.
-/

open MeasureTheory
open scoped BigOperators ENNReal

namespace LogdetLean.GramHafnian.UltimateHiding.Sparse

noncomputable section

open CurrentPRL

/-- The ordinary real density of a `K × N` matrix of independent standard
circular complex Gaussians. -/
def standardComplexGaussianRectangularDensityReal (K N : ℕ)
    (Z : Matrix (Fin K) (Fin N) ℂ) : ℝ :=
  (Real.pi ^ (K * N))⁻¹ *
    Real.exp (-∑ i : Fin K, ∑ j : Fin N, ‖Z i j‖ ^ 2)

/-- The same rectangular Gaussian density in the `ENNReal` form expected by
`Measure.withDensity`. -/
def standardComplexGaussianRectangularPDF (K N : ℕ)
    (Z : Matrix (Fin K) (Fin N) ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (standardComplexGaussianRectangularDensityReal K N Z)

theorem standardComplexGaussianRectangularDensityReal_pos
    (K N : ℕ) (Z : Matrix (Fin K) (Fin N) ℂ) :
    0 < standardComplexGaussianRectangularDensityReal K N Z := by
  unfold standardComplexGaussianRectangularDensityReal
  exact mul_pos (inv_pos.mpr (pow_pos Real.pi_pos _)) (Real.exp_pos _)

theorem measurable_standardComplexGaussianRectangularPDF (K N : ℕ) :
    Measurable (standardComplexGaussianRectangularPDF K N) := by
  unfold standardComplexGaussianRectangularPDF
    standardComplexGaussianRectangularDensityReal
  fun_prop

/-- The closed-form matrix density is exactly the product of the scalar
`CN(0,1)` densities over all entries. -/
theorem prod_currentPRLCircularGaussianDensity_eq_rectangularPDF
    (K N : ℕ) (Z : Matrix (Fin K) (Fin N) ℂ) :
    (∏ i : Fin K, ∏ j : Fin N,
      currentPRLCircularGaussianDensity (Z i j)) =
      standardComplexGaussianRectangularPDF K N Z := by
  unfold currentPRLCircularGaussianDensity
    standardComplexGaussianRectangularPDF
  have hnonneg (i : Fin K) (j : Fin N) :
      0 ≤ Real.pi⁻¹ * Real.exp (-‖Z i j‖ ^ 2) := by positivity
  simp_rw [← ENNReal.ofReal_prod_of_nonneg
    (fun j _ ↦ hnonneg _ j)]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ ↦
    Finset.prod_nonneg fun j _ ↦ hnonneg i j)]
  apply congrArg ENNReal.ofReal
  unfold standardComplexGaussianRectangularDensityReal
  simp only [Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, ← Real.exp_sum,
    Finset.sum_neg_distrib]
  rw [← pow_mul, inv_pow]
  rw [Nat.mul_comm N K]

/-- The finite circular-Gaussian vector has the product of the scalar
`CN(0,1)` densities with respect to coordinatewise complex volume. -/
theorem circularGaussianVector_eq_withDensity_H19 (N : ℕ) :
    circularGaussianVector N =
      (Measure.pi fun _ : Fin N ↦ (volume : Measure ℂ)).withDensity
        (fun z ↦ ∏ j : Fin N,
          currentPRLCircularGaussianDensity (z j)) := by
  have hsf : ∀ _ : Fin N,
      SigmaFinite ((volume : Measure ℂ).withDensity
        currentPRLCircularGaussianDensity) := fun _ ↦ by
    rw [← circularGaussian_eq_withDensity_currentPRL]
    infer_instance
  unfold circularGaussianVector
  rw [show (fun _ : Fin N ↦ circularGaussian) =
      (fun _ : Fin N ↦
        (volume : Measure ℂ).withDensity
          currentPRLCircularGaussianDensity) by
    funext j
    exact circularGaussian_eq_withDensity_currentPRL]
  exact @piFin_withDensity N ℂ _
    (fun _ : Fin N ↦ (volume : Measure ℂ))
    (fun _ ↦ inferInstance)
    (fun _ : Fin N ↦ currentPRLCircularGaussianDensity)
    hsf
    (fun _ ↦ measurable_currentPRLCircularGaussianDensity)

/-- The project-standard `K × N` complex Gaussian matrix law has the
explicit density `pi^(-K*N) exp (-sum |Z_ij|²)` with respect to the same
coordinatewise complex volume used by Jiang's Haar-corner density. -/
theorem standardComplexGaussianRectangularMeasure_eq_withDensity_H19
    (K N : ℕ) :
    standardComplexGaussianRectangularMeasure K N =
      (complexRectangularLebesgueVolume K N).withDensity
        (standardComplexGaussianRectangularPDF K N) := by
  let rowVolume : Measure (Fin N → ℂ) :=
    Measure.pi fun _ : Fin N ↦ (volume : Measure ℂ)
  let rowDensity : (Fin N → ℂ) → ℝ≥0∞ :=
    fun z ↦ ∏ j : Fin N, currentPRLCircularGaussianDensity (z j)
  have hrow : circularGaussianVector N =
      rowVolume.withDensity rowDensity := by
    simpa [rowVolume, rowDensity] using
      circularGaussianVector_eq_withDensity_H19 N
  have hrowSigma : ∀ _ : Fin K,
      SigmaFinite (rowVolume.withDensity rowDensity) := fun _ ↦ by
    rw [← hrow]
    infer_instance
  have houter := @piFin_withDensity K (Fin N → ℂ) _
    (fun _ : Fin K ↦ rowVolume)
    (fun _ ↦ inferInstance)
    (fun _ : Fin K ↦ rowDensity)
    hrowSigma
    (fun _ ↦ by
      dsimp [rowDensity]
      simpa using Finset.measurable_fun_prod Finset.univ
        (fun j _ ↦ measurable_currentPRLCircularGaussianDensity.comp
          (measurable_pi_apply j)))
  unfold standardComplexGaussianRectangularMeasure
  change Measure.map id
      (Measure.pi fun _ : Fin K ↦ circularGaussianVector N) = _
  rw [Measure.map_id]
  rw [show (fun _ : Fin K ↦ circularGaussianVector N) =
      (fun _ : Fin K ↦ rowVolume.withDensity rowDensity) by
    funext i
    exact hrow]
  rw [houter]
  unfold complexRectangularLebesgueVolume rowVolume rowDensity
  congr 1
  funext Z
  exact prod_currentPRLCircularGaussianDensity_eq_rectangularPDF K N Z

/-- The same density theorem under the semantic block-law name used by the
sparse H19 comparison. -/
theorem standardGaussianBlockLaw_eq_withDensity_H19 (K N : ℕ) :
    standardGaussianBlockLaw K N =
      (complexRectangularLebesgueVolume K N).withDensity
        (standardComplexGaussianRectangularPDF K N) :=
  standardComplexGaussianRectangularMeasure_eq_withDensity_H19 K N

end

end LogdetLean.GramHafnian.UltimateHiding.Sparse
