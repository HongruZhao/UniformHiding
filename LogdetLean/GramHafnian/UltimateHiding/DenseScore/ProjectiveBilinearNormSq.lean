import LogdetLean.GramHafnian.UltimateHiding.Dense.OneColumnConcrete
import LogdetLean.GramHafnian.UltimateHiding.Dense.RadialConcrete

/-!
# Shared projective bilinear coordinate polynomial

This axiom-free definition is used by both the second-score contraction and
the cubic-score identification.  Isolating it here prevents either proof
branch from importing the other.
-/

open scoped BigOperators ComplexConjugate

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- Coordinate form of `|v^* T conjugate(v)|^2`. -/
def complexProjectiveBilinearNormSq {N : ℕ}
    (v : ComplexUnitSphere N) (T : ConcreteMatrixState N) : ℂ :=
  ∑ b, ∑ c, ∑ a, ∑ d,
    complexRankOneProjection v a b * T b c *
      complexRankOneProjection v d c * star (T a d)

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
