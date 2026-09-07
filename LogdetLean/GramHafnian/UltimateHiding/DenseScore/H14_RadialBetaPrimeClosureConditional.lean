import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H14_SeparatedFactorIntegralBounds
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H14_ProjectiveCancellationAlgebra
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.BetaPrimeTraceTwoCounterexample
import Mathlib.Tactic

/-!
# CONDITIONAL radial beta-prime closure for H14 projective cancellation

The fixed-matrix projective contraction has already been proved in
`H14_SeparatedFactorIntegralBounds`.  This file performs the next, purely
radial, step on the literal four-trace beta-prime law.

The terms involving only `Tr Y` squared and `Tr (Y^2)` are closed
unconditionally from the proved source-level PSD trace inequality and the
proved cubic trace-two mean.  The sole remaining hypothesis is isolated as
`H14BetaPrimeNormalizedFourthRemainderExpectationContract`: it asks only for
the normalized expectation of `(Tr Y)^4` and `(Tr (Y^2))^2`.  It contains no
projective variable, score, H6 transport, or H3--H18 endpoint.

In particular, the false raw `O(N^2)` bound on `E Tr(Y^2)` is not used:
projective cancellation first supplies the inverse powers of `N`, and the
correct cubic estimate is applied only afterwards.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

set_option maxHeartbeats 1200000

/-- The part of the fixed-matrix projective envelope controlled by the
proved second-entry/Wick ledger. -/
def h14BetaPrimeProjectiveLowerEnvelope (N K : ℕ)
    (u : Fin 4 → ℝ) : ℝ :=
  4096 *
    ((betaPrimeYTraceOne N K u ^ 2 + |betaPrimeYTraceTwo N K u|) /
      (N : ℝ) ^ 2)

/-- The only fourth-order radial remainder not controlled by the checked
second-entry tensor. -/
def h14BetaPrimeNormalizedFourthRemainder (N K : ℕ)
    (u : Fin 4 → ℝ) : ℝ :=
  betaPrimeYTraceOne N K u ^ 4 /
      ((N : ℝ) ^ 4 * concreteCOEExponent N K ^ 2) +
    betaPrimeYTraceTwo N K u ^ 2 /
      ((N : ℝ) ^ 2 * concreteCOEExponent N K ^ 2)

/-- The complete radial pullback of the proved fixed-matrix envelope. -/
def h14BetaPrimeProjectiveCancellationEnvelope (N K : ℕ)
    (u : Fin 4 → ℝ) : ℝ :=
  h14BetaPrimeProjectiveLowerEnvelope N K u +
    4096 * h14BetaPrimeNormalizedFourthRemainder N K u

/-- A convenient power-of-two envelope for the already closed lower-order
radial contribution.  The proof below actually gives `163840`. -/
def h14BetaPrimeProjectiveLowerMomentConstant : ℝ := 262144

/-- The first scaled trace is exactly the concrete first trace after the
four-trace map.  This is definitional matrix algebra and uses no law
transport. -/
theorem h14_betaPrimeYTraceOne_comp_concreteTraceFour_internal
    (N K : ℕ) (A : ConcreteMatrixState N) :
    betaPrimeYTraceOne N K (concreteCOETracePowerVector 4 N K A) =
      concreteCOETraceOne N K A := by
  unfold betaPrimeYTraceOne concreteCOETracePowerVector concreteCOETraceOne
    concreteCOEY concreteRealTrace
  simp [pow_succ, Complex.mul_re]

/-- The second scaled trace is exactly the concrete second trace after the
four-trace map. -/
theorem h14_betaPrimeYTraceTwo_comp_concreteTraceFour_internal
    (N K : ℕ) (A : ConcreteMatrixState N) :
    betaPrimeYTraceTwo N K (concreteCOETracePowerVector 4 N K A) =
      concreteCOETraceTwo N K A := by
  unfold betaPrimeYTraceTwo concreteCOETracePowerVector concreteCOETraceTwo
    concreteCOEY concreteRealTrace
  simp [pow_succ, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul,
    smul_smul, Complex.mul_re]

/-- The new radial envelope is the literal pullback of the already proved
fixed-matrix projective envelope. -/
theorem h14_betaPrimeProjectiveCancellationEnvelope_comp_traceFour_internal
    (N K : ℕ) (A : ConcreteMatrixState N) :
    h14BetaPrimeProjectiveCancellationEnvelope N K
        (concreteCOETracePowerVector 4 N K A) =
      h14ProjectiveCancellationEnvelope N K A := by
  unfold h14BetaPrimeProjectiveCancellationEnvelope
    h14BetaPrimeProjectiveLowerEnvelope
    h14BetaPrimeNormalizedFourthRemainder
    h14ProjectiveCancellationEnvelope
  rw [h14_betaPrimeYTraceOne_comp_concreteTraceFour_internal,
    h14_betaPrimeYTraceTwo_comp_concreteTraceFour_internal]
  ring

private theorem measurable_betaPrimeYTraceOne_h14_radial (N K : ℕ) :
    Measurable (betaPrimeYTraceOne N K) := by
  unfold betaPrimeYTraceOne
  fun_prop

private theorem measurable_betaPrimeYTraceTwo_h14_radial (N K : ℕ) :
    Measurable (betaPrimeYTraceTwo N K) := by
  unfold betaPrimeYTraceTwo
  fun_prop

/-- Axiom-free square integrability in `L^1` of the first exposed trace,
obtained by pushing forward the already checked Gaussian-source theorem. -/
theorem integrable_betaPrimeYTraceOne_sq_h14_radial_internal
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K) :
    Integrable (fun u ↦ betaPrimeYTraceOne N K u ^ 2)
      (betaPrimeTraceFourLaw N K) := by
  unfold betaPrimeTraceFourLaw
  apply (integrable_map_measure
    ((measurable_betaPrimeYTraceOne_h14_radial N K).pow_const 2).aestronglyMeasurable
    (measurable_realBetaPrimeTracePowerVector_internal 4 N K).aemeasurable).2
  change Integrable
    (fun source : U08.BetaPrimeGaussianSource N K ↦
      betaPrimeYTraceOne N K
        (realBetaPrimeTracePowerVector 4 N K source) ^ 2)
    (realBetaPrimeGaussianSourceLaw N K)
  exact U08.integrable_betaPrimeTraceOneSource_sq_internal hgap

/-- Axiom-free integrability of the second exposed trace, again by the
literal Gaussian pushforward. -/
theorem integrable_betaPrimeYTraceTwo_h14_radial_internal
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K) :
    Integrable (betaPrimeYTraceTwo N K) (betaPrimeTraceFourLaw N K) := by
  unfold betaPrimeTraceFourLaw
  apply (integrable_map_measure
    (measurable_betaPrimeYTraceTwo_h14_radial N K).aestronglyMeasurable
    (measurable_realBetaPrimeTracePowerVector_internal 4 N K).aemeasurable).2
  change Integrable
    (fun source : U08.BetaPrimeGaussianSource N K ↦
      betaPrimeYTraceTwo N K
        (realBetaPrimeTracePowerVector 4 N K source))
    (realBetaPrimeGaussianSourceLaw N K)
  exact U08.integrable_betaPrimeTraceTwoSource_internal hgap

/-- The entire lower-order projective radial envelope is integrable at the
sharp qualitative threshold. -/
theorem integrable_h14BetaPrimeProjectiveLowerEnvelope_internal
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K) :
    Integrable (h14BetaPrimeProjectiveLowerEnvelope N K)
      (betaPrimeTraceFourLaw N K) := by
  have hOne := integrable_betaPrimeYTraceOne_sq_h14_radial_internal hgap
  have hTwo := integrable_betaPrimeYTraceTwo_h14_radial_internal hgap
  have hsum := hOne.add hTwo.abs
  have hscaled := hsum.const_mul (4096 / (N : ℝ) ^ 2)
  have heq : h14BetaPrimeProjectiveLowerEnvelope N K =
      fun u ↦ (4096 / (N : ℝ) ^ 2) *
        (betaPrimeYTraceOne N K u ^ 2 + |betaPrimeYTraceTwo N K u|) := by
    funext u
    unfold h14BetaPrimeProjectiveLowerEnvelope
    ring
  rw [heq]
  exact hscaled

/-- On the literal beta-prime law, PSD gives both nonnegativity of the
second trace and `Tr(Y)^2 ≤ N Tr(Y^2)`.  Unlike the older support route,
this proof stays entirely on the explicit Gaussian source and therefore
uses no H6 distributional axiom. -/
theorem betaPrimeYTraceTwo_nonneg_and_traceOne_sq_le_dimension_mul_ae_internal
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    ∀ᵐ u ∂(betaPrimeTraceFourLaw N K),
      0 ≤ betaPrimeYTraceTwo N K u ∧
        betaPrimeYTraceOne N K u ^ 2 ≤
          (N : ℝ) * betaPrimeYTraceTwo N K u := by
  have hc : 0 ≤ concreteCOEExponent N K := by
    have hgapR : ((2 * N + 8 : ℕ) : ℝ) ≤ (K : ℝ) := by
      exact_mod_cast hgap
    push_cast at hgapR
    unfold concreteCOEExponent
    linarith
  have hmap : AEMeasurable (realBetaPrimeTracePowerVector 4 N K)
      (realBetaPrimeGaussianSourceLaw N K) :=
    (measurable_realBetaPrimeTracePowerVector_internal 4 N K).aemeasurable
  have hp : MeasurableSet {u : Fin 4 → ℝ |
      0 ≤ betaPrimeYTraceTwo N K u ∧
        betaPrimeYTraceOne N K u ^ 2 ≤
          (N : ℝ) * betaPrimeYTraceTwo N K u} := by
    exact (measurableSet_le measurable_const
      (measurable_betaPrimeYTraceTwo_h14_radial N K)).inter
      (measurableSet_le
        ((measurable_betaPrimeYTraceOne_h14_radial N K).pow_const 2)
        (measurable_const.mul
          (measurable_betaPrimeYTraceTwo_h14_radial N K)))
  unfold betaPrimeTraceFourLaw
  apply (ae_map_iff hmap hp).2
  filter_upwards [] with source
  have htrace :=
    U08.betaPrimeTraceOneSource_sq_le_dimension_mul_traceTwoSource hc source
  have hNpos : 0 < (N : ℝ) := by
    exact_mod_cast (show 0 < N by omega)
  change 0 ≤ U08.betaPrimeTraceTwoSource N K source ∧
    U08.betaPrimeTraceOneSource N K source ^ 2 ≤
      (N : ℝ) * U08.betaPrimeTraceTwoSource N K source
  constructor
  · nlinarith [sq_nonneg (U08.betaPrimeTraceOneSource N K source)]
  · exact htrace

/-- After the fixed-matrix projective cancellation, the correct cubic
trace-two mean controls the lower radial envelope at order `N^2`. -/
theorem integral_h14BetaPrimeProjectiveLowerEnvelope_le_internal
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (hdense : 16 * N ≤ K) :
    (∫ u, h14BetaPrimeProjectiveLowerEnvelope N K u
      ∂(betaPrimeTraceFourLaw N K)) ≤
      h14BetaPrimeProjectiveLowerMomentConstant * (N : ℝ) ^ 2 := by
  let mu := betaPrimeTraceFourLaw N K
  let n : ℝ := N
  have hn : 0 < n := by
    dsimp only [n]
    exact_mod_cast (show 0 < N by omega)
  have hn0 : n ≠ 0 := ne_of_gt hn
  have hlower : Integrable (h14BetaPrimeProjectiveLowerEnvelope N K) mu := by
    simpa only [mu] using
      integrable_h14BetaPrimeProjectiveLowerEnvelope_internal hgap
  have htwo : Integrable (betaPrimeYTraceTwo N K) mu := by
    simpa only [mu] using
      integrable_betaPrimeYTraceTwo_h14_radial_internal hgap
  have hmajor : Integrable
      (fun u ↦ (8192 / n) * betaPrimeYTraceTwo N K u) mu :=
    htwo.const_mul (8192 / n)
  have hpoint : ∀ᵐ u ∂mu,
      h14BetaPrimeProjectiveLowerEnvelope N K u ≤
        (8192 / n) * betaPrimeYTraceTwo N K u := by
    filter_upwards
      [betaPrimeYTraceTwo_nonneg_and_traceOne_sq_le_dimension_mul_ae_internal
        hN hgap] with u hu
    have hnOne : n + 1 ≤ 2 * n := by
      dsimp only [n]
      exact_mod_cast (show N + 1 ≤ 2 * N by omega)
    have hmul := mul_le_mul_of_nonneg_right hnOne hu.1
    have hsum : betaPrimeYTraceOne N K u ^ 2 +
        betaPrimeYTraceTwo N K u ≤
          2 * n * betaPrimeYTraceTwo N K u := by
      dsimp only [n] at hmul
      nlinarith [hu.2]
    unfold h14BetaPrimeProjectiveLowerEnvelope
    rw [show |betaPrimeYTraceTwo N K u| = betaPrimeYTraceTwo N K u by
      exact abs_of_nonneg hu.1]
    calc
      4096 * ((betaPrimeYTraceOne N K u ^ 2 +
          betaPrimeYTraceTwo N K u) / (N : ℝ) ^ 2) =
          (4096 / n ^ 2) *
            (betaPrimeYTraceOne N K u ^ 2 +
              betaPrimeYTraceTwo N K u) := by
            dsimp only [n]
            ring
      _ ≤ (4096 / n ^ 2) *
          (2 * n * betaPrimeYTraceTwo N K u) := by
        exact mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = (8192 / n) * betaPrimeYTraceTwo N K u := by
        field_simp [hn0]
        <;> ring
  have hmono :
      (∫ u, h14BetaPrimeProjectiveLowerEnvelope N K u ∂mu) ≤
        ∫ u, (8192 / n) * betaPrimeYTraceTwo N K u ∂mu := by
    exact integral_mono_ae hlower hmajor hpoint
  rw [integral_const_mul] at hmono
  have hmeanAbs :=
    h14_betaPrimeYTraceTwoFormalMeanU08_abs_le_twenty_cube_internal
      hN hdense
  have hmeanAbs' :
      |∫ u, betaPrimeYTraceTwo N K u ∂mu| ≤ 20 * n ^ 3 := by
    simpa only [U08.betaPrimeYTraceTwoFormalMeanU08, mu, n] using hmeanAbs
  have hmean :
      (∫ u, betaPrimeYTraceTwo N K u ∂mu) ≤ 20 * n ^ 3 :=
    (le_abs_self _).trans hmeanAbs'
  have hcoef : 0 ≤ 8192 / n := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hmean hcoef
  have heq : (8192 / n) * (20 * n ^ 3) = 163840 * n ^ 2 := by
    field_simp [hn0]
    <;> ring
  calc
    (∫ u, h14BetaPrimeProjectiveLowerEnvelope N K u ∂mu) ≤
        (8192 / n) *
          (∫ u, betaPrimeYTraceTwo N K u ∂mu) := hmono
    _ ≤ (8192 / n) * (20 * n ^ 3) := hscaled
    _ = 163840 * n ^ 2 := heq
    _ ≤ h14BetaPrimeProjectiveLowerMomentConstant * (N : ℝ) ^ 2 := by
      dsimp only [h14BetaPrimeProjectiveLowerMomentConstant, n]
      exact mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg (N : ℝ))

/-- **CONDITIONAL, non-endpoint, radial-only contract.**  This is the
smallest remaining expectation input after the second-entry/Wick ledger and
the fixed-matrix projective contraction have been discharged.  It is exactly
the qualitative integrability and dense bound for the two normalized
fourth-order trace monomials. -/
structure H14BetaPrimeNormalizedFourthRemainderExpectationContract
    (N K : ℕ) : Prop where
  integrable :
    Integrable (h14BetaPrimeNormalizedFourthRemainder N K)
      (betaPrimeTraceFourLaw N K)
  integral_le_dense :
    16 * N ≤ K →
      (∫ u, h14BetaPrimeNormalizedFourthRemainder N K u
        ∂(betaPrimeTraceFourLaw N K)) ≤
        denseClassicalMomentConstant * (N : ℝ) ^ 2

/-- Conditional radial closure.  Everything except the explicit normalized
fourth-remainder expectation contract is kernel-proved in this file.  This
theorem contains neither H6 transport nor a score/projective endpoint. -/
theorem h14_betaPrimeProjectiveCancellationEnvelope_momentPackage_conditional
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (Hfourth :
      H14BetaPrimeNormalizedFourthRemainderExpectationContract N K) :
    Integrable (h14BetaPrimeProjectiveCancellationEnvelope N K)
        (betaPrimeTraceFourLaw N K) ∧
      (16 * N ≤ K →
        (∫ u, h14BetaPrimeProjectiveCancellationEnvelope N K u
          ∂(betaPrimeTraceFourLaw N K)) ≤
          centeredLogScoreFourthMomentConstant * (N : ℝ) ^ 2) := by
  have hlower := integrable_h14BetaPrimeProjectiveLowerEnvelope_internal hgap
  have hfourthScaled := Hfourth.integrable.const_mul (4096 : ℝ)
  have hfull :
      Integrable (h14BetaPrimeProjectiveCancellationEnvelope N K)
        (betaPrimeTraceFourLaw N K) := by
    change Integrable (fun u ↦
      h14BetaPrimeProjectiveLowerEnvelope N K u +
        4096 * h14BetaPrimeNormalizedFourthRemainder N K u)
      (betaPrimeTraceFourLaw N K)
    exact hlower.add hfourthScaled
  refine ⟨hfull, ?_⟩
  intro hdense
  have hlowerBound := integral_h14BetaPrimeProjectiveLowerEnvelope_le_internal
    hN hgap hdense
  have hfourthBound := Hfourth.integral_le_dense hdense
  have hscaled := mul_le_mul_of_nonneg_left hfourthBound
    (show (0 : ℝ) ≤ 4096 by norm_num)
  change
    (∫ u, h14BetaPrimeProjectiveLowerEnvelope N K u +
        4096 * h14BetaPrimeNormalizedFourthRemainder N K u
      ∂(betaPrimeTraceFourLaw N K)) ≤
      centeredLogScoreFourthMomentConstant * (N : ℝ) ^ 2
  rw [integral_add hlower hfourthScaled, integral_const_mul]
  calc
    (∫ u, h14BetaPrimeProjectiveLowerEnvelope N K u
        ∂(betaPrimeTraceFourLaw N K)) +
        4096 *
          (∫ u, h14BetaPrimeNormalizedFourthRemainder N K u
            ∂(betaPrimeTraceFourLaw N K)) ≤
      h14BetaPrimeProjectiveLowerMomentConstant * (N : ℝ) ^ 2 +
        4096 * (denseClassicalMomentConstant * (N : ℝ) ^ 2) := by
          exact add_le_add hlowerBound hscaled
    _ = (h14BetaPrimeProjectiveLowerMomentConstant +
          4096 * denseClassicalMomentConstant) * (N : ℝ) ^ 2 := by ring
    _ ≤ centeredLogScoreFourthMomentConstant * (N : ℝ) ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg (N : ℝ))
      norm_num [h14BetaPrimeProjectiveLowerMomentConstant,
        denseClassicalMomentConstant, centeredLogScoreFourthMomentConstant]

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
