import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CubicDifferentialBasics
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ConcreteCentralCubicDefinitions
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ConcreteMixedCubicDefinitions
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ConcreteCOEStatistics
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# Exact cubic differential witness data

This narrow core contains only the data record consumed by the exact H7
assembler.  It has no moment bound or historical H7 declaration.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- Exact supported-state third-density differential data. -/
structure ConcreteCubicDifferentialWitness
    (N K : ℕ) (A : ConcreteMatrixState N) where
  differential : SymmetricRealTrilinearForm (ConcreteMatrixRealCoordinates N)
  rankOne_diagonal : ∀ v : ComplexUnitSphere N,
    differential.form (concreteMatrixRealCoordinates (complexRankOneProjection v))
        (concreteMatrixRealCoordinates (complexRankOneProjection v))
        (concreteMatrixRealCoordinates (complexRankOneProjection v)) =
      concreteRankOneDensityScoreThree N K v A
  centered_diagonal : ∀ v : ComplexUnitSphere N,
    differential.form
        (concreteMatrixRealCoordinates (concreteCenteredOrbitalDirection N v))
        (concreteMatrixRealCoordinates (concreteCenteredOrbitalDirection N v))
        (concreteMatrixRealCoordinates (concreteCenteredOrbitalDirection N v)) =
      concreteCenteredDensityScore 3 N K v A
  central_diagonal :
    differential.form
        (concreteMatrixRealCoordinates (1 : ConcreteMatrixState N))
        (concreteMatrixRealCoordinates (1 : ConcreteMatrixState N))
        (concreteMatrixRealCoordinates (1 : ConcreteMatrixState N)) =
      concreteCentralDensityScoreThree N K A
  centered_integrable :
    Integrable (fun v : ComplexUnitSphere N ↦
      concreteCenteredDensityScore 3 N K v A)
      (complexUnitSphereProbabilityMeasure N)
  mixed_integrable :
    Integrable (fun v : ComplexUnitSphere N ↦
      differential.form
        (concreteMatrixRealCoordinates (1 : ConcreteMatrixState N))
        (concreteMatrixRealCoordinates (concreteCenteredOrbitalDirection N v))
        (concreteMatrixRealCoordinates (concreteCenteredOrbitalDirection N v)))
      (complexUnitSphereProbabilityMeasure N)
  mixed_mean :
    (∫ v : ComplexUnitSphere N,
      differential.form
        (concreteMatrixRealCoordinates (1 : ConcreteMatrixState N))
        (concreteMatrixRealCoordinates (concreteCenteredOrbitalDirection N v))
        (concreteMatrixRealCoordinates (concreteCenteredOrbitalDirection N v))
        ∂(complexUnitSphereProbabilityMeasure N)) =
      concreteMixedScalarQuadraticDensity N K A

end


end LogdetLean.GramHafnian.UltimateHiding.DenseScore
