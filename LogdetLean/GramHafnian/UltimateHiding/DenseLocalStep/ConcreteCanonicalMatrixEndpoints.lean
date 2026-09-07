import LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep.CombinedSharperCanonicalScoreCertificate
import LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep.COEBaseFullRangeCertificate

/-!
# Matrix-only canonical hiding endpoint

This release-local module factors the uniformly-hiding matrix theorem out of
the historical aggregate `ConcreteCanonicalPaperEndpoints`.  The historical
aggregate also imported GBS small-ball consequences and thereby pulled the
anticoncentration development into the physical source closure of the hiding
Article.  No theorem statement or proof object is changed here; only the
downstream, unused GBS imports are removed from this standalone package.
-/

namespace LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding
open LogdetLean.GramHafnian.UltimateHiding.DenseScore

/-- Explicit absolute coefficient in the closed full-range matrix theorem. -/
def concreteCanonicalHidingSquaredConstant : ℝ :=
  4 * exactVarianceCentralScoreOneConstant +
    5 * exactVarianceCentralScoreTwoConstant +
    2 * exactVarianceOrbitalScoreTwoConstant +
    2 * combinedSharperCanonicalOrbitalThirdConstant + 106

/-- Fully evaluated value of the combined-sharper absolute constant. -/
theorem concreteCanonicalHidingSquaredConstant_eq :
    concreteCanonicalHidingSquaredConstant = 615172 := by
  unfold concreteCanonicalHidingSquaredConstant
  rw [combinedSharperCanonicalOrbitalThirdConstant_eq]
  norm_num [exactVarianceCentralScoreOneConstant,
    exactVarianceCentralScoreTwoConstant, exactVarianceOrbitalScoreTwoConstant]

/-- Closed finite all-rank transpose-Gram hiding at rate
`min {1, C N^2/M}`. -/
theorem uniformProductMatrixHidingSquaredAt_concreteCanonical :
    UniformProductMatrixHidingSquaredAt
      concreteCanonicalHidingSquaredConstant := by
  simpa only [concreteCanonicalHidingSquaredConstant] using
    uniformProductMatrixHidingSquaredAt_of_canonicalCOEBaseScoreCertificate
      uniformCanonicalScaledCOESharedBetaScoreCertificate_combinedSharper

/-- Existential headline form of the closed full-range matrix theorem. -/
theorem uniformProductMatrixHidingSquared_concreteCanonical :
    UniformProductMatrixHidingSquared :=
  ⟨concreteCanonicalHidingSquaredConstant,
    uniformProductMatrixHidingSquaredAt_concreteCanonical⟩

end

end LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep
