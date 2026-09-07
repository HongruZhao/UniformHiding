import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H7WitnessIntegrability
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CenteredFlowGeometry

/-!
# Literal line identifications for H7

This file separates the tautological coordinate and centered-line reductions
from the genuinely nontrivial rank-one, central, and mixed calculations.  It
does not use the external H7 declaration and introduces no assumptions.

The file was written after a host-wide file-table saturation stopped further
Lean processes.  Its declarations therefore remain UNVERIFIED until the next
single-module build; `STATUS.md` records that boundary explicitly.
-/

open Function
open scoped Matrix

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- Reconstructing a real scalar multiple of matrix coordinates gives the
same real scalar multiple of the original matrix. -/
@[simp]
theorem concreteMatrixOfRealCoordinates_smul_coordinates
    {N : ℕ} (t : ℝ) (H : ConcreteMatrixState N) :
    concreteMatrixOfRealCoordinates
        (t • concreteMatrixRealCoordinates H) = t • H := by
  apply concreteMatrixRealCoordinates_injective_internal
  rw [concreteMatrixRealCoordinates_ofCoordinates,
    concreteMatrixRealCoordinates_smul]

/-- A coordinate line is literally the corresponding matrix line. -/
theorem h16CoordinateLikelihoodCore_matrix_line
    {N K : ℕ} (A H : ConcreteMatrixState N) (t : ℝ) :
    h16CoordinateLikelihoodCore K A
        (t • concreteMatrixRealCoordinates H) =
      h16GeneralCOELikelihoodCore N K (t • H) A := by
  simp [h16CoordinateLikelihoodCore]

/-- Absorbing real time into the direction and evaluating the inverse flow at
time `-1` is exactly the inverse flow at time `-t`. -/
theorem transposeCongruenceFlow_real_smul_neg_one
    {N : ℕ} (H C : ConcreteMatrixState N) (t : ℝ) :
    transposeCongruenceFlow (t • H) (-1 : ℝ) C =
      transposeCongruenceFlow H (-t) C := by
  unfold transposeCongruenceFlow
  apply congrArg (fun g ↦ transposeCongruence g C)
  congr 1
  simp [smul_smul]

/-- The arbitrary-direction determinant in the traceless projective
direction is the determinant used by the literal centered likelihood. -/
theorem h16GeneralCOEInverseDeterminant_centered_line
    {N K : ℕ} (v : ComplexUnitSphere N) (A : ConcreteMatrixState N)
    (t : ℝ) :
    h16GeneralCOEInverseDeterminant K
        (t • concreteCenteredOrbitalDirection N v) A =
      concreteCOECenteredInverseDeterminant K v t A := by
  simp only [h16GeneralCOEInverseDeterminant,
    concreteCOECenteredInverseDeterminant]
  rw [transposeCongruenceFlow_real_smul_neg_one]

/-- The Jacobian part of the general density is one on a centered projective
direction, so the two literal likelihoods agree pointwise. -/
theorem h16GeneralCOELikelihoodCore_centered_line
    {N K : ℕ} (hN : 1 ≤ N) (v : ComplexUnitSphere N)
    (A : ConcreteMatrixState N) (t : ℝ) :
    h16GeneralCOELikelihoodCore N K
        (t • concreteCenteredOrbitalDirection N v) A =
      concreteCenteredLikelihoodCore K v t A := by
  let Q := concreteCenteredOrbitalDirection N v
  have hQtrace : Matrix.trace Q = 0 := by
    simpa only [Q] using
      trace_concreteCenteredOrbitalDirection_eq_zero hN v
  have htrace : (Matrix.trace (t • Q)).re = 0 := by
    change (Matrix.trace (((t : ℂ)) • Q)).re = 0
    rw [Matrix.trace_smul, hQtrace]
    simp
  have hinverse : h16GeneralCOEInverseDeterminant K (t • Q) A =
      concreteCOECenteredInverseDeterminant K v t A := by
    simpa only [Q] using
      h16GeneralCOEInverseDeterminant_centered_line v A t
  unfold h16GeneralCOELikelihoodCore concreteCenteredLikelihoodCore
  split_ifs with hbase
  · rfl
  · rw [show (Matrix.trace
        (t • concreteCenteredOrbitalDirection N v)).re = 0 by
          simpa only [Q] using htrace,
      show h16GeneralCOEInverseDeterminant K
          (t • concreteCenteredOrbitalDirection N v) A =
          concreteCOECenteredInverseDeterminant K v t A by
        simpa only [Q] using hinverse]
    simp

/-- The real-coordinate restriction in the centered direction is exactly the
project's literal centered likelihood function. -/
theorem h16CoordinateLikelihoodCore_centered_line
    {N K : ℕ} (hN : 1 ≤ N) (v : ComplexUnitSphere N)
    (A : ConcreteMatrixState N) :
    (fun t : ℝ ↦ h16CoordinateLikelihoodCore K A
        (t • concreteMatrixRealCoordinates
          (concreteCenteredOrbitalDirection N v))) =
      (fun t : ℝ ↦ concreteCenteredLikelihoodCore K v t A) := by
  funext t
  rw [h16CoordinateLikelihoodCore_matrix_line]
  exact h16GeneralCOELikelihoodCore_centered_line hN v A t

/-- Consequently the bundled Frechet differential has the exact centered
diagonal demanded by `ConcreteCubicDifferentialWitness`; no explicit
five-trace expansion is needed for this field. -/
theorem h7CoordinateDifferential_centered_diagonal
    {N K : ℕ} (hN : 1 ≤ N) (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A))
    (v : ComplexUnitSphere N) :
    (h7CoordinateDifferential K A).form
        (concreteMatrixRealCoordinates
          (concreteCenteredOrbitalDirection N v))
        (concreteMatrixRealCoordinates
          (concreteCenteredOrbitalDirection N v))
        (concreteMatrixRealCoordinates
          (concreteCenteredOrbitalDirection N v)) =
      concreteCenteredDensityScore 3 N K v A := by
  rw [h7CoordinateDifferential_diagonal_eq_iteratedDeriv A hsupport]
  unfold concreteCenteredDensityScore
  rw [h16CoordinateLikelihoodCore_centered_line hN v A]

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
