import LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep.CorrelatedTaylorTV
import LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep.OneStepBridge

/-!
# Same-beta scalar--orbital one-step bridge

The central coefficient and the traceless orbital coefficient in one Haar
column are functions of one beta variable `q`.  This module keeps that
correlation pointwise.  In particular, the orbital path at zero is required
to equal the central path made with the same `q`; it is not an independently
averaged copy of the central law.

All probability, score, and coupling statements remain explicit theorem
hypotheses.  The proof below contains only Taylor integration, moment-budget
comparison, the already proved concrete bad-event estimate, and the TV
triangle inequality.
-/

open MeasureTheory Set

namespace LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep

noncomputable section

/-- Correlation-correct event-path endpoint for one dense Haar column.

The hypothesis `horbitalZero_sameBeta` is the crucial interface: at each
sampled `q`, the zero-orbital endpoint is the central move at that exact same
`q`.  Consequently `goodLaw` is the shared-beta mixture
`E_q[e^{c(q)X_I} K_{b(q)} mu]`, rather than the independent mixture
`E_q K_{b(q)} E_{q'}e^{c(q')X_I} mu`.
-/
theorem probabilityTVLE_denseOneStep_of_correlated_eventPaths
    {State : Type*} [MeasurableSpace State]
    (mu scalarLaw goodLaw nu : Measure State)
    {Cmean CscalarTwo CbTwo CbThree : ℝ}
    {CscoreOne CscoreTwo CorbitalTwo CorbitalThree : ℝ}
    {m N : ℕ}
    (hN : 1 ≤ N) (hNm : N ≤ m)
    (hthreshold : 24 * (N : ℝ) ^ 2 ≤ (m : ℝ))
    (hmom : OneColumnLogMomentBoundsAt
      Cmean CscalarTwo CbTwo CbThree m N)
    (hscoreOne : 0 ≤ CscoreOne) (hscoreTwo : 0 ≤ CscoreTwo)
    (horbitalTwo : 0 ≤ CorbitalTwo)
    (horbitalThree : 0 ≤ CorbitalThree)
    (scalarEventPath : Set State → ℝ → ℝ)
    (orbitalEventPath : ℝ → Set State → ℝ → ℝ)
    (orbitalAmplitude : ℝ → ℝ)
    (hscalarMu : ∀ A, MeasurableSet A → scalarEventPath A 0 = mu.real A)
    (hscalarLaw : ∀ A, MeasurableSet A →
      ∫ q, scalarEventPath A (Dense.oneColumnCenteredScalarLog m N q)
        ∂(Dense.oneColumnBetaLaw m N) = scalarLaw.real A)
    (hscalarSmooth : ∀ A, MeasurableSet A → ContDiff ℝ 2 (scalarEventPath A))
    (hscalarFirst : ∀ A, MeasurableSet A →
      |iteratedDeriv 1 (scalarEventPath A) 0| ≤ CscoreOne * (N : ℝ))
    (hscalarSecond : ∀ A, MeasurableSet A → ∀ q,
      ∀ y ∈ uIcc 0 (Dense.oneColumnCenteredScalarLog m N q),
        |iteratedDeriv 2 (scalarEventPath A) y| ≤
          CscoreTwo * (N : ℝ) ^ 2)
    (hscalarPathIntegrable : ∀ A, MeasurableSet A →
      Integrable
        (fun q ↦ scalarEventPath A (Dense.oneColumnCenteredScalarLog m N q))
        (Dense.oneColumnBetaLaw m N))
    (horbitalZero_sameBeta : ∀ q A, MeasurableSet A →
      orbitalEventPath q A 0 =
        scalarEventPath A (Dense.oneColumnCenteredScalarLog m N q))
    (horbitalLaw : ∀ A, MeasurableSet A →
      ∫ q, orbitalEventPath q A (orbitalAmplitude q)
        ∂(Dense.oneColumnBetaLaw m N) = goodLaw.real A)
    (horbitalSmooth : ∀ q A, MeasurableSet A →
      ContDiff ℝ 3 (orbitalEventPath q A))
    (horbitalFirst : ∀ q A, MeasurableSet A →
      iteratedDeriv 1 (orbitalEventPath q A) 0 = 0)
    (horbitalSecond : ∀ q A, MeasurableSet A →
      |iteratedDeriv 2 (orbitalEventPath q A) 0| ≤ CorbitalTwo)
    (horbitalThird : ∀ q A, MeasurableSet A →
      ∀ y ∈ uIcc 0 (orbitalAmplitude q),
        |iteratedDeriv 3 (orbitalEventPath q A) y| ≤
          CorbitalThree * (N : ℝ))
    (horbitalZeroIntegrable : ∀ A, MeasurableSet A →
      Integrable (fun q ↦ orbitalEventPath q A 0)
        (Dense.oneColumnBetaLaw m N))
    (horbitalMoveIntegrable : ∀ A, MeasurableSet A →
      Integrable (fun q ↦ orbitalEventPath q A (orbitalAmplitude q))
        (Dense.oneColumnBetaLaw m N))
    (horbitalAmplitude_sq_integrable :
      Integrable (fun q ↦ orbitalAmplitude q ^ 2)
        (Dense.oneColumnBetaLaw m N))
    (horbitalAmplitude_cube_integrable :
      Integrable (fun q ↦ |orbitalAmplitude q| ^ 3)
        (Dense.oneColumnBetaLaw m N))
    (horbitalSecondMoment_le :
      (∫ q, orbitalAmplitude q ^ 2 ∂(Dense.oneColumnBetaLaw m N)) ≤
        ∫ q, Dense.oneColumnRankOneLog q ^ 2
          ∂(Dense.oneColumnBetaLaw m N))
    (horbitalThirdMoment_le :
      (∫ q, |orbitalAmplitude q| ^ 3 ∂(Dense.oneColumnBetaLaw m N)) ≤
        ∫ q, |Dense.oneColumnRankOneLog q| ^ 3
          ∂(Dense.oneColumnBetaLaw m N))
    (hbadTV : Dense.ProbabilityTVLE goodLaw nu
      (Dense.oneColumnLogBadProbability m N 1)) :
    Dense.ProbabilityTVLE mu nu
      (Dense.denseTelescopingRate
        (CscoreOne * Cmean + CscoreTwo * CscalarTwo +
          (CorbitalTwo * CbTwo / 2 + CorbitalThree * CbThree / 6) + 72)
        N m) := by
  letI : IsProbabilityMeasure (Dense.oneColumnBetaLaw m N) :=
    Dense.oneColumnBetaLaw_isProbability hN hNm
  have hscalarTV : Dense.ProbabilityTVLE mu scalarLaw
      (oneColumnScalarTaylorBudget CscoreOne CscoreTwo m N) := by
    have hraw := probabilityTVLE_of_random_scalar_eventPath
      mu scalarLaw (Dense.oneColumnBetaLaw m N)
      (Dense.oneColumnCenteredScalarLog m N) scalarEventPath
      (CscoreOne * (N : ℝ)) (CscoreTwo * (N : ℝ) ^ 2)
      (mul_nonneg hscoreOne (Nat.cast_nonneg N))
      (mul_nonneg hscoreTwo (sq_nonneg _))
      hscalarMu hscalarLaw hscalarSmooth hscalarFirst hscalarSecond
      hscalarPathIntegrable hmom.centeredScalar_integrable
      hmom.centeredScalar_sq_integrable
    simpa [oneColumnScalarTaylorBudget] using hraw
  have horbitalBase : ∀ A, MeasurableSet A →
      ∫ q, orbitalEventPath q A 0 ∂(Dense.oneColumnBetaLaw m N) =
        scalarLaw.real A := by
    intro A hA
    calc
      ∫ q, orbitalEventPath q A 0 ∂(Dense.oneColumnBetaLaw m N) =
          ∫ q, scalarEventPath A (Dense.oneColumnCenteredScalarLog m N q)
            ∂(Dense.oneColumnBetaLaw m N) := by
              apply integral_congr_ae
              filter_upwards [] with q
              exact horbitalZero_sameBeta q A hA
      _ = scalarLaw.real A := hscalarLaw A hA
  have horbitalRaw := probabilityTVLE_of_correlated_centered_eventPath
    scalarLaw goodLaw (Dense.oneColumnBetaLaw m N) orbitalAmplitude
      orbitalEventPath CorbitalTwo (CorbitalThree * (N : ℝ))
      horbitalTwo (mul_nonneg horbitalThree (Nat.cast_nonneg N))
      horbitalBase horbitalLaw horbitalSmooth horbitalFirst horbitalSecond
      horbitalThird horbitalZeroIntegrable horbitalMoveIntegrable
      horbitalAmplitude_sq_integrable horbitalAmplitude_cube_integrable
  have horbitalBudgetLe :
      CorbitalTwo *
            (∫ q, orbitalAmplitude q ^ 2
              ∂(Dense.oneColumnBetaLaw m N)) / 2 +
          (CorbitalThree * (N : ℝ)) *
            (∫ q, |orbitalAmplitude q| ^ 3
              ∂(Dense.oneColumnBetaLaw m N)) / 6 ≤
        oneColumnOrbitalTaylorBudget CorbitalTwo CorbitalThree m N := by
    unfold oneColumnOrbitalTaylorBudget
    exact add_le_add
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left horbitalSecondMoment_le horbitalTwo)
        (by norm_num))
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left horbitalThirdMoment_le
          (mul_nonneg horbitalThree (Nat.cast_nonneg N)))
        (by norm_num))
  have horbitalTV : Dense.ProbabilityTVLE scalarLaw goodLaw
      (oneColumnOrbitalTaylorBudget CorbitalTwo CorbitalThree m N) :=
    horbitalRaw.mono horbitalBudgetLe
  exact probabilityTVLE_denseOneStep_of_betaLogScores
    mu scalarLaw goodLaw nu hN hNm hthreshold hmom
      hscoreOne hscoreTwo horbitalTwo horbitalThree
      hscalarTV horbitalTV hbadTV

end

end LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep
