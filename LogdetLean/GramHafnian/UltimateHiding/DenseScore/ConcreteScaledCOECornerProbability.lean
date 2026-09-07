import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ConcreteCenteredLikelihood

/-!
# Probability normalization of the concrete scaled COE corner law

This foundational fact is kept below the score-moment hierarchy so that
measure-theoretic arguments such as Fubini do not acquire dependencies on
downstream trace-moment bounds.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.CurrentPRL

/-- The canonical square COE law is a probability measure. -/
theorem canonicalScaledCOECornerLaw_isProbability
    {N K : ℕ} (hNK : N ≤ K) :
    IsProbabilityMeasure
      (concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K) := by
  letI : IsProbabilityMeasure
      (scaledHaarTransposeGramLaw
        canonicalUnitaryHaarProbabilityFamily K N K) :=
    scaledHaarTransposeGramLaw_isProbability _ hNK le_rfl
  unfold concreteScaledCOECornerLaw concreteHaarAmbientLaw
    normalizedHaarTransposeGramLaw
  exact Measure.isProbabilityMeasure_map
    (measurable_normalizeTransposeGram N K).aemeasurable

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
