import A2.Definitions
open scoped ENNReal
open MeasureTheory
noncomputable section

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore
open LogdetLean.GramHafnian.UltimateHiding.Dense
def IsPermutationInvariantSpectralTest {N : ℕ} {γ : Type}
    (F : (Fin N → ℝ) → γ) : Prop :=
  ∀ (sigma : Equiv.Perm (Fin N)) (lambda : Fin N → ℝ),
    F (lambda ∘ sigma) = F lambda

/-- The structure of the raw, invariant Takagi--Weyl integration formula.

The target type is any ordinary (`Type 0`) measurable space.  The equality is
the pushforward form of the Weyl formula and is deliberately restricted to
permutation-invariant tests, so it does not identify a canonical ordered
selector with the full unordered orthant. -/
structure TakagiWeylSymmetricIntegrationLaw (N : ℕ) where
  orbitConstant : NNReal
  orbitConstant_pos : 0 < orbitConstant
  measurable_spectrum : Measurable (canonicalGapSquaredSpectrum N)
  symmetric_flat_radial_law :
    ∀ {γ : Type} [MeasurableSpace γ]
      (F : (Fin N → ℝ) → γ),
      Measurable F →
      IsPermutationInvariantSpectralTest F →
      Measure.map (F ∘ canonicalGapSquaredSpectrum N)
          (complexSymmetricMatrixVolume N) =
        (orbitConstant : ℝ≥0∞) •
          Measure.map F (takagiFlatEigenvalueRadialMeasure N)

theorem TakagiWeylSymmetricIntegrationLaw.orbitConstant_ne_zero
    {N : ℕ} (h : TakagiWeylSymmetricIntegrationLaw N) :
    h.orbitConstant ≠ 0 :=
  ne_of_gt h.orbitConstant_pos

abbrev Target :=
  ∀
    (N : ℕ) (_hN : 1 ≤ N),
    TakagiWeylSymmetricIntegrationLaw N

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
