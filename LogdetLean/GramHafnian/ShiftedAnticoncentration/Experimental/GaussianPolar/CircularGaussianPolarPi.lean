import LogdetLean.GramHafnian.ShiftedAnticoncentration.Experimental.GaussianPolar.GaussianPolar

/-!
# Finite families of circular-Gaussian polar samples

This file transports the exact one-column polar reconstruction law through a
finite product.  It is the literal independent-column interface needed by the
past-cofactor radial factorization.
-/

open MeasureTheory ProbabilityTheory Set Metric Function
open scoped ENNReal NNReal Real Pointwise

namespace LogdetLean.GramHafnian

noncomputable section

/-- Raw-coordinate reconstruction of a circular-Gaussian column from its unit
direction and positive radius. -/
def circularGaussianPolarRawReconstruct (k : ℕ) :
    sphere (0 : CircularEuclideanSpace k) 1 × Ioi (0 : ℝ) →
      (Fin k → ℂ) :=
  fun z ↦ WithLp.ofLp (circularGaussianPolarReconstruct k z)

@[fun_prop]
theorem measurable_circularGaussianPolarRawReconstruct (k : ℕ) :
    Measurable (circularGaussianPolarRawReconstruct k) := by
  unfold circularGaussianPolarRawReconstruct
  fun_prop

/-- Pointwise form of polar reconstruction in the raw complex coordinates. -/
theorem circularGaussianPolarRawReconstruct_apply
    (k : ℕ)
    (u : sphere (0 : CircularEuclideanSpace k) 1)
    (r : Ioi (0 : ℝ)) (p : Fin k) :
    circularGaussianPolarRawReconstruct k (u, r) p =
      (r.1 : ℂ) * WithLp.ofLp u.1 p := by
  simp [circularGaussianPolarRawReconstruct,
    circularGaussianPolarReconstruct,
    homeomorphUnitSphereProd_symm_apply_coe]

/-- Forgetting the Euclidean wrapper after polar reconstruction gives the
literal law of `k` iid circular complex coordinates. -/
theorem map_circularGaussianPolarRawReconstruct
    {k : ℕ} (hk : 0 < k) :
    Measure.map (circularGaussianPolarRawReconstruct k)
        ((circularGaussianSphereProbability k).prod
          (circularGaussianPositiveRadiusMeasure k)) =
      circularGaussianVector k := by
  unfold circularGaussianPolarRawReconstruct
  change Measure.map
      ((WithLp.ofLp : CircularEuclideanSpace k → (Fin k → ℂ)) ∘
        circularGaussianPolarReconstruct k)
        ((circularGaussianSphereProbability k).prod
          (circularGaussianPositiveRadiusMeasure k)) =
      circularGaussianVector k
  rw [← Measure.map_map
    (by fun_prop : Measurable (WithLp.ofLp :
      CircularEuclideanSpace k → (Fin k → ℂ)))
    (measurable_circularGaussianPolarReconstruct k)]
  rw [map_circularGaussianPolarReconstruct hk]
  unfold circularGaussianVector
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  convert Measure.map_id
  funext x
  simp

/-- Coordinatewise reconstruction of a finite family of independent polar
samples. -/
def circularGaussianPolarFamilyReconstruct (k : ℕ) {ι : Type*} :
    (ι → sphere (0 : CircularEuclideanSpace k) 1 × Ioi (0 : ℝ)) →
      (ι → Fin k → ℂ) :=
  fun z i ↦ circularGaussianPolarRawReconstruct k (z i)

@[fun_prop]
theorem measurable_circularGaussianPolarFamilyReconstruct
    (k : ℕ) {ι : Type*} [Fintype ι] :
    Measurable (circularGaussianPolarFamilyReconstruct k (ι := ι)) := by
  unfold circularGaussianPolarFamilyReconstruct
  fun_prop

/-- Exact finite-column reconstruction law.  Independent normalized polar
samples reconstruct a family of iid literal circular-Gaussian columns. -/
theorem map_pi_circularGaussianPolarFamilyReconstruct
    {k : ℕ} (hk : 0 < k) {ι : Type*} [Fintype ι] :
    Measure.map (circularGaussianPolarFamilyReconstruct k (ι := ι))
        (Measure.pi fun _ : ι ↦
          (circularGaussianSphereProbability k).prod
            (circularGaussianPositiveRadiusMeasure k)) =
      Measure.pi (fun _ : ι ↦ circularGaussianVector k) := by
  let μ : Measure
      (sphere (0 : CircularEuclideanSpace k) 1 × Ioi (0 : ℝ)) :=
    (circularGaussianSphereProbability k).prod
      (circularGaussianPositiveRadiusMeasure k)
  have hcol : MeasurePreserving
      (circularGaussianPolarRawReconstruct k) μ
      (circularGaussianVector k) := ⟨
    measurable_circularGaussianPolarRawReconstruct k,
    map_circularGaussianPolarRawReconstruct hk⟩
  exact (measurePreserving_pi
    (fun _ : ι ↦ μ)
    (fun _ : ι ↦ circularGaussianVector k)
    (fun _ ↦ hcol)).map_eq

end

end LogdetLean.GramHafnian
