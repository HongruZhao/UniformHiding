import LogdetLean.GramHafnian.UltimateHiding.Sparse.HaarBlockKL

/-!
# Base definitions for the H19 Haar-block source calculation

This module separates the reusable definitions from the external source
statements.  The split lets the generic matrix-beta moment package be proved
from a Jacobi determinant factorization without creating an import cycle.

There are no axioms in this module.
-/

open MeasureTheory
open scoped BigOperators

namespace LogdetLean.GramHafnian.UltimateHiding.Sparse

noncomputable section

open CurrentPRL

/-- The log determinant of the positive matrix-beta complement associated to
a scaled rectangular block.  It is a total real-valued function; positivity
on the Haar support is supplied by the determinant-law source statement. -/
def scaledBlockLogDetComplement {N K : ℕ} (M : ℕ)
    (Z : Matrix (Fin N) (Fin K) ℂ) : ℝ :=
  Real.log
    (Matrix.det
      (1 - ((((M : ℝ)⁻¹ : ℝ) : ℂ)) • (Z * Z.conjTranspose))).re

/-- The Gaussian quadratic energy appearing in the block likelihood. -/
def scaledBlockEnergy {N K : ℕ}
    (Z : Matrix (Fin N) (Fin K) ℂ) : ℝ :=
  (Matrix.trace (Z * Z.conjTranspose)).re

/-- The logarithm of Jiang's factorial normalizer, already expanded into its
finite product factors. -/
def jiangScaledBlockLogNormalizer (M N K : ℕ) : ℝ :=
  ∑ i : Fin N × Fin K,
    Real.log (1 - rectangularNormalizedIndex K N M i)

/-- The explicit log Radon--Nikodym derivative of the scaled Haar corner
against the standard complex Gaussian block on the Haar support. -/
def jiangScaledBlockLogLikelihood {N K : ℕ} (M : ℕ)
    (Z : Matrix (Fin N) (Fin K) ℂ) : ℝ :=
  jiangScaledBlockLogNormalizer M N K +
    ((M : ℝ) - K - N) * scaledBlockLogDetComplement M Z +
    scaledBlockEnergy Z

/-- The generic `q × a` Haar realization of a complex matrix-beta-I law
with complementary shape parameter `b`. -/
def complexMatrixBetaIHaarBlockLaw (q a b : ℕ) :
    Measure (Matrix (Fin q) (Fin a) ℂ) :=
  sqrtScaledHaarBlockLaw canonicalUnitaryHaarProbabilityFamily
    (a + b) q a

/-- The reflected reciprocal sum obtained from the scalar-beta log moments. -/
def complexMatrixBetaIReciprocalSum (q a b : ℕ) : ℝ :=
  ∑ i : Fin q × Fin a,
    ((a + b : ℝ)⁻¹ /
      (1 - rectangularNormalizedIndex a q (a + b) i))

/-- A generic package for the two sufficient statistics used by a
matrix-beta likelihood calculation.  It is independent of H19's KL endpoint. -/
structure ComplexMatrixBetaILogDetEnergyMomentPackage
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (logDet energy : Ω → ℝ)
    (logDetMean energyMean : ℝ) : Prop where
  logDet_integrable : Integrable logDet μ
  integral_logDet : ∫ x, logDet x ∂μ = logDetMean
  energy_integrable : Integrable energy μ
  integral_energy : ∫ x, energy x ∂μ = energyMean

end

end LogdetLean.GramHafnian.UltimateHiding.Sparse
