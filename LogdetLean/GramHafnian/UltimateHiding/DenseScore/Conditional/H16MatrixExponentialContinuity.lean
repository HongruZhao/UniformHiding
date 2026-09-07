import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# Exact matrix-exponential continuity input isolated by H16

Mathlib deliberately does not choose a canonical normed-ring structure on a
finite matrix space.  Consequently its generic Banach-algebra continuity
theorem does not elaborate directly against the coordinatewise matrix
topology used by the probability model.  This file names only that finite-
dimensional topology bridge.  It introduces no axiom and asserts no theorem.
-/

open NormedSpace

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

/-- Continuity of one finite matrix-exponential curve in the coordinatewise
matrix topology.  This is a deterministic finite-dimensional statement, not
a density, integration, event, H5, or H16 conclusion. -/
abbrev H16MatrixExponentialCurveContinuous (N : ℕ)
    (A : Matrix (Fin N) (Fin N) ℂ) : Prop :=
  Continuous (fun t : ℝ ↦ exp (((t : ℂ)) • A))

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
