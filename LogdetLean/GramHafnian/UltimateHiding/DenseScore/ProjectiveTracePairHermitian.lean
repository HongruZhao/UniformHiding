import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ProjectiveSecondMoment
import Mathlib.Tactic

/-!
# Hermitian reality of the projective trace pairing

This axiom-free helper records the elementary fact that
`Tr(P_v A)` is real when `A` is Hermitian.  It is kept below the cubic and H14
branches so both can reuse the proved matrix identity without importing one
another.
-/

open scoped BigOperators ComplexConjugate

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

private theorem complexRankOneProjection_isHermitian_shared
    {N : ℕ} (v : ComplexUnitSphere N) :
    (complexRankOneProjection v).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  simp [Matrix.conjTranspose_apply, complexRankOneProjection]
  ring

/-- A projective quadratic form of a Hermitian matrix is real. -/
theorem complexProjectiveTracePair_im_eq_zero_of_isHermitian
    {N : ℕ} (v : ComplexUnitSphere N) (A : ConcreteMatrixState N)
    (hA : A.IsHermitian) :
    (complexProjectiveTracePair v A).im = 0 := by
  rw [complexProjectiveTracePair_eq_trace]
  apply Complex.conj_eq_iff_im.mp
  calc
    star (Matrix.trace (complexRankOneProjection v * A)) =
        Matrix.trace ((complexRankOneProjection v * A).conjTranspose) := by
          rw [Matrix.trace_conjTranspose]
    _ = Matrix.trace (A * complexRankOneProjection v) := by
          rw [Matrix.conjTranspose_mul, hA,
            complexRankOneProjection_isHermitian_shared]
    _ = Matrix.trace (complexRankOneProjection v * A) :=
          Matrix.trace_mul_comm _ _

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
