import LogdetLean.GramHafnian.UltimateHiding.Dense.TargetConvergence
import LogdetLean.GramHafnian.UltimateHiding.Dense.TelescopingFrom

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.Dense

noncomputable section

open LocalAnticoncentration

/-- Concrete dense telescope with both the correct start-indexed local premise
and the Gaussian target convergence discharged. -/
theorem probabilityTVLE_dense_telescope_from_to_gaussianTransposeGram
    (H : UnitaryHaarProbabilityFamily) (C : ℝ) {N K start : ℕ}
    (hC : 0 <= C) (hN : 0 < N) (hK : 0 < K) (hNK : N <= K)
    (hstart : K + N <= start)
    (hstep : ∀ m, start <= m →
      ProbabilityTVLE
        (denseHaarAmbientLaw H N K m)
        (denseHaarAmbientLaw H N K (m + 1))
        (denseTelescopingRate C N m)) :
    ProbabilityTVLE
      (denseHaarAmbientLaw H N K start)
      (denseGaussianTransposeGramTarget N K)
      (C * (N : ℝ) ^ 2 / (start : ℝ)) := by
  exact probabilityTVLE_dense_telescope_from
    (denseHaarAmbientLaw H N K)
    (denseGaussianTransposeGramTarget N K)
    C N start hC (by omega) hstep
    (jiang_denseHaarAmbient_targetConvergence H hN hK hNK hstart)

/-- Correct start-indexed dense telescope without a `K+N <= start`
restriction.  This is the paper-facing wrapper needed uniformly through
`K = start`. -/
theorem probabilityTVLE_dense_telescope_from_to_gaussianTransposeGram_unrestricted
    (H : UnitaryHaarProbabilityFamily) (C : ℝ) {N K start : ℕ}
    (hC : 0 <= C) (hN : 0 < N) (hK : 0 < K) (hNK : N <= K)
    (hstart : 1 <= start)
    (hstep : ∀ m, start <= m →
      ProbabilityTVLE
        (denseHaarAmbientLaw H N K m)
        (denseHaarAmbientLaw H N K (m + 1))
        (denseTelescopingRate C N m)) :
    ProbabilityTVLE
      (denseHaarAmbientLaw H N K start)
      (denseGaussianTransposeGramTarget N K)
      (C * (N : ℝ) ^ 2 / (start : ℝ)) := by
  exact probabilityTVLE_dense_telescope_from
    (denseHaarAmbientLaw H N K)
    (denseGaussianTransposeGramTarget N K)
    C N start hC hstart hstep
    (jiang_denseHaarAmbient_targetConvergence_unrestricted H hN hK hNK)

end

end LogdetLean.GramHafnian.UltimateHiding.Dense
