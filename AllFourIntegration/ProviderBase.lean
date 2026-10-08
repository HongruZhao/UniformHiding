import Mathlib
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ClassicalCOEExternal
import LogdetLean.GramHafnian.UltimateHiding.HaarGaussianMatrixLaws
import LogdetLean.GramHafnian.GramMomentFubini
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H6_BetaJacobiCore
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H6_DensityTransform

/- The original transparent Gaussian, Haar, symmetric-coordinate and beta
definitions are shared by the proved providers and consumer. No theorem
axiom is imported by this thin base. -/
namespace AllFourIntegration
instance complexMatrixBorelSpace (N K : ℕ) :
    BorelSpace (Matrix (Fin N) (Fin K) ℂ) := by
  exact inferInstanceAs (BorelSpace (Fin N → Fin K → ℂ))
end AllFourIntegration
