import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H7LineIdentifications
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ConcreteCubicWitnessCore

/-!
# CONDITIONAL exact H7 assembly from three residual identities

This file is deliberately named `Conditional`.  Its theorem does not claim
H7: the remaining rank-one scalar derivative, central scalar derivative, and
mixed projective mean are explicit parameters.  It records that all other
fields of `ConcreteCubicDifferentialWitness` follow from the assumption-free
Frechet, symmetry, centered-line, and compactness layers.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- **CONDITIONAL.** Exact witness assembly from the three residual scalar
identities.  Each premise is strictly smaller than the witness conclusion
and exposes its literal line or projective-integral content. -/
noncomputable def h7Witness_of_three_residual_identities_CONDITIONAL
    {N K : ℕ} (hN : 1 ≤ N) (_hboundary : 2 * N + 8 ≤ K)
    (A : ConcreteMatrixState N)
    (_hsymm : (unscaleCOECorner K A).IsSymm)
    (hsupport : coeCornerSupport (unscaleCOECorner K A))
    (hrankOne : ∀ v : ComplexUnitSphere N,
      iteratedDeriv 3
        (fun t : ℝ ↦ h16CoordinateLikelihoodCore K A
          (t • concreteMatrixRealCoordinates (complexRankOneProjection v))) 0 =
        concreteRankOneDensityScoreThree N K v A)
    (hcentral :
      iteratedDeriv 3
        (fun t : ℝ ↦ h16CoordinateLikelihoodCore K A
          (t • concreteMatrixRealCoordinates
            (1 : ConcreteMatrixState N))) 0 =
        concreteCentralDensityScoreThree N K A)
    (hmixed :
      (∫ v : ComplexUnitSphere N,
        (h7CoordinateDifferential K A).form
          (concreteMatrixRealCoordinates (1 : ConcreteMatrixState N))
          (concreteMatrixRealCoordinates
            (concreteCenteredOrbitalDirection N v))
          (concreteMatrixRealCoordinates
            (concreteCenteredOrbitalDirection N v))
          ∂(complexUnitSphereProbabilityMeasure N)) =
        concreteMixedScalarQuadraticDensity N K A) :
    ConcreteCubicDifferentialWitness N K A := by
  let T := h7CoordinateDifferential K A
  refine {
    differential := T
    rankOne_diagonal := ?_
    centered_diagonal := ?_
    central_diagonal := ?_
    centered_integrable := ?_
    mixed_integrable := ?_
    mixed_mean := ?_ }
  · intro v
    rw [show T = h7CoordinateDifferential K A by rfl,
      h7CoordinateDifferential_diagonal_eq_iteratedDeriv A hsupport]
    exact hrankOne v
  · intro v
    simpa only [T] using
      h7CoordinateDifferential_centered_diagonal hN A hsupport v
  · rw [show T = h7CoordinateDifferential K A by rfl,
      h7CoordinateDifferential_diagonal_eq_iteratedDeriv A hsupport]
    exact hcentral
  · have hfun :
        (fun v : ComplexUnitSphere N ↦
          concreteCenteredDensityScore 3 N K v A) =
        (fun v : ComplexUnitSphere N ↦
          let q := concreteMatrixRealCoordinates
            (concreteCenteredOrbitalDirection N v)
          T.form q q q) := by
      funext v
      exact (by
        simpa only [T] using
          (h7CoordinateDifferential_centered_diagonal
            hN A hsupport v).symm)
    rw [hfun]
    exact integrable_symmetricTrilinear_centeredDiagonal hN T
  · exact integrable_symmetricTrilinear_mixed hN T
  · simpa only [T] using hmixed

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
