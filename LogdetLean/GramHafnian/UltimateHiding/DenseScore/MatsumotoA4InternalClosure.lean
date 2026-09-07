import LogdetLean.GramHafnian.UltimateHiding.DenseScore.MatsumotoDeterminantLaplace
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.MatsumotoA4IntegrabilityClosure
import Mathlib.Tactic

/-!
# Internal half-Gaussian realization for the Matsumoto A4 consumer

This module combines the proved determinant Laplace transform with the
proved inverse-trace-four integrability transport.  Consequently the A4
specialization no longer takes a Gaussian-to-Wishart pushforward certificate
or a separate integrability premise from its caller.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.Wishart

/-- The H12/H14 Matsumoto identity-scale trace-four moment obtained from the
approved A4 theorem and the now-internal half-Gaussian Gram realization. -/
theorem h12h14_matsumotoIdentityTraceFourMoment_of_A4_internal
    {d k : Nat} (hd : 0 < d) (hgap : d + 7 < k) :
    H12H14MatsumotoIdentityTraceFourMoment d k
      (halfGaussianMatsumotoGamma d k)
      (matsumotoA4TraceFourValue d k) :=
  h12h14_matsumotoIdentityTraceFourMoment_of_A4_of_pushforward
    hd hgap (halfGaussianMatsumotoWishartPushforward_internal (by omega))

/-- Direct project-side A4 trace-four moment, with both the pushforward and
paper-side integrability premises discharged internally. -/
theorem h12h14_projectTraceFourMoment_of_A4_internal
    {N K : Nat} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    Integrable (h12h14ProjectScaledInverseTraceFour N K)
        (standardRealGaussianMatrixMeasure (K - N) N) ∧
      (∫ R : Matrix (Fin (K - N)) (Fin N) Real,
        h12h14ProjectScaledInverseTraceFour N K R
          ∂standardRealGaussianMatrixMeasure (K - N) N) =
        matsumotoA4TraceFourValue N (K - N) := by
  have hmoment :=
    h12h14_matsumotoIdentityTraceFourMoment_of_A4_internal
      (d := N) (k := K - N) (by omega) (by omega)
  have hmoment' :
      H12H14MatsumotoIdentityTraceFourMoment N (K - N)
        (h12h14MatsumotoGamma N (h12h14MatsumotoBeta (K - N)))
        (matsumotoA4TraceFourValue N (K - N)) := by
    simpa [halfGaussianMatsumotoGamma, halfGaussianMatsumotoBeta,
      h12h14MatsumotoGamma, h12h14MatsumotoBeta] using hmoment
  exact h12h14_projectTraceFourMoment_of_matsumotoIdentity hgap hmoment'

/-- Direct A4-to-projective-cancellation package at the existing H12/H14
adapter boundary.  This does not change either frozen endpoint type. -/
theorem h12h14_matsumotoTraceFour_projectiveCancellationBridge_of_A4_internal
    {N K : Nat} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    (Integrable (h12h14ProjectScaledInverseTraceFour N K)
        (standardRealGaussianMatrixMeasure (K - N) N) ∧
      (∫ R : Matrix (Fin (K - N)) (Fin N) Real,
        h12h14ProjectScaledInverseTraceFour N K R
          ∂standardRealGaussianMatrixMeasure (K - N) N) =
        matsumotoA4TraceFourValue N (K - N)) ∧
      ∀ R : Matrix (Fin (K - N)) (Fin N) Real,
        H12H14ProjectiveTraceZeroFourthPackage
          (h12h14ComplexProjectScaledInverseMatrix N K R) := by
  have hmoment :=
    h12h14_matsumotoIdentityTraceFourMoment_of_A4_internal
      (d := N) (k := K - N) (by omega) (by omega)
  have hmoment' :
      H12H14MatsumotoIdentityTraceFourMoment N (K - N)
        (h12h14MatsumotoGamma N (h12h14MatsumotoBeta (K - N)))
        (matsumotoA4TraceFourValue N (K - N)) := by
    simpa [halfGaussianMatsumotoGamma, halfGaussianMatsumotoBeta,
      h12h14MatsumotoGamma, h12h14MatsumotoBeta] using hmoment
  exact h12h14_matsumotoTraceFour_projectiveCancellationBridge
    hN hgap hmoment'

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
