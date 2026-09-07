import LogdetLean.GramHafnian.UltimateHiding.Normalized

/-!
# Normalized form of squared-rate product matrix hiding
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding

noncomputable section

open CurrentPRL

theorem normalizedProductMatrixHidingSquared_of_unnormalized
    {C : ℝ} (hhide : UniformProductMatrixHidingSquaredAt C)
    (H : UnitaryHaarProbabilityFamily) {M N K : ℕ}
    (hN : 1 <= N) (hNK : N <= K) (hKM : K <= M) :
    probabilityTotalVariationLE
      (normalizedHaarTransposeGramLaw H M N K)
      (normalizedGaussianTransposeGramLaw N K)
      (min 1 (C * ultimateSquaredHidingRate M N)) := by
  unfold normalizedHaarTransposeGramLaw normalizedGaussianTransposeGramLaw
  exact (hhide.apply H hN hNK hKM).map
    (measurable_normalizeTransposeGram N K)

end


end LogdetLean.GramHafnian.UltimateHiding
