import A3.GaussianBetaJacobiLaw
import A3.GSVJacobiMeasureBridge

open MeasureTheory
noncomputable section

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

/-- Edelman--Sutton Proposition 1.2 on the literal Gaussian-pair carrier,
with the original squared-GSV statistic and unordered beta-Jacobi law. -/
theorem A3_edelmanSutton_proposition_1_2 : A3OriginalTarget := by
  intro n a b beta hn hbeta
  refine ⟨measurable_edelmanSuttonSquaredGSVCoordinates n a b beta, ?_⟩
  intro gamma inst F hF hperm
  rcases hbeta with rfl | rfl
  · rw [A3Research.map_real_squaredGSV_symmetric_statistic F hF hperm]
    exact A3Research.realGaussianGramPair_symmetric_betaJacobiLaw n a b hn F hF hperm
  · rw [A3Research.map_complex_squaredGSV_symmetric_statistic F hF]
    exact A3Research.complexGaussianGramPair_symmetric_betaJacobiLaw n a b hn F hF hperm

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
