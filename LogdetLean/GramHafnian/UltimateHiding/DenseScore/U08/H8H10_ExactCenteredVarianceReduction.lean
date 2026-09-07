import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.H8H10CenteredL2FourthMomentTransport
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.H14_FiniteGaussianFourthWickFormulaClosure
import Mathlib.Tactic

/-!
# Exact H8/H10 centered-variance reduction

This file completes the previously unfinished direct pushforward reduction.
The qualitative `L²` statements, the finite 105-pairing Wick formula, and the
raw fourth-moment bounds are all internal.  For arbitrary dimension, the only
remaining quantitative obligations are the two displayed centered-variance
inequalities below.

The existing H14 raw bounds are also propagated as far as they can go.  They
give `2^16 N^8` and `2^16 N^6`; the literal H8/H10 endpoints require orders
`N^6` and `N^4` after squaring their `L²` bounds.  Hence a raw-moment argument
loses exactly one factor `N^2`.  It nevertheless closes both literal endpoint
packages through dimension `N ≤ 2^32`, because the endpoint constant is
`2^40`.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08

noncomputable section

/-- The exact remaining H8 scalar obligation after all source transport and
finite Wick contractions have been checked. -/
def H8SharpCenteredVarianceContract (N K : ℕ) : Prop :=
  16 * N ≤ K →
    h8DenominatorCenteredVariance N K ≤
      (denseClassicalMomentConstant * (N : ℝ) ^ 3) ^ 2

/-- The exact remaining H10 scalar obligation after all source transport and
finite Wick contractions have been checked. -/
def H10SharpCenteredVarianceContract (N K : ℕ) : Prop :=
  16 * N ≤ K →
    h10DenominatorCenteredVariance N K ≤
      (denseClassicalMomentConstant * (N : ℝ) ^ 2) ^ 2

/-- The two sharp scalar inequalities, and nothing else, complete the exact
H8/H10 transport record. -/
theorem h8H10ExactFourthMomentTransport_of_sharpCenteredVariance
    {N K : ℕ}
    (h8 : H8SharpCenteredVarianceContract N K)
    (h10 : H10SharpCenteredVarianceContract N K) :
    H8H10ExactFourthMomentTransport N K := by
  refine
    { finiteGaussianFourthWick := h14FiniteGaussianFourthWickFormula_internal N K
      traceOneSquare_centeredVariance_le := ?_
      traceTwo_centeredVariance_le := ?_ }
  · exact h8
  · exact h10

/-- The qualitative half of H8 is fully proved for every dimension in the
literal moment range. -/
theorem betaPrimeYTraceOneSquare_centered_memLp_two_proved_allDimensions
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K) :
    MemLp
      (fun u => betaPrimeYTraceOne N K u ^ 2 -
        ∫ z, betaPrimeYTraceOne N K z ^ 2 ∂betaPrimeTraceFourLaw N K)
      2 (betaPrimeTraceFourLaw N K) :=
  (betaPrimeYTraceOneSquare_centered_memLp_two_and_lpNorm_eq_sqrt_internal
    hgap (h14FiniteGaussianFourthWickFormula_internal N K)).1

/-- The qualitative half of H10 is fully proved for every dimension in the
literal moment range. -/
theorem betaPrimeYTraceTwo_centered_memLp_two_proved_allDimensions
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K) :
    MemLp
      (fun u => betaPrimeYTraceTwo N K u -
        ∫ z, betaPrimeYTraceTwo N K z ∂betaPrimeTraceFourLaw N K)
      2 (betaPrimeTraceFourLaw N K) :=
  (betaPrimeYTraceTwo_centered_memLp_two_and_lpNorm_eq_sqrt_internal
    hgap (h14FiniteGaussianFourthWickFormula_internal N K)).1

/-- Exact individual H8 endpoint reduction: only the H8 centered-variance
inequality is required; no H10 hypothesis is smuggled into the result. -/
theorem betaPrimeYTraceOneSquare_centered_two_momentPackage_of_sharpVariance
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (h8 : H8SharpCenteredVarianceContract N K) :
    MemLp
        (fun u => betaPrimeYTraceOne N K u ^ 2 -
          ∫ z, betaPrimeYTraceOne N K z ^ 2 ∂betaPrimeTraceFourLaw N K)
        2 (betaPrimeTraceFourLaw N K) ∧
      (16 * N ≤ K →
        lpNorm
            (fun u => betaPrimeYTraceOne N K u ^ 2 -
              ∫ z, betaPrimeYTraceOne N K z ^ 2 ∂betaPrimeTraceFourLaw N K)
            2 (betaPrimeTraceFourLaw N K) ≤
          denseClassicalMomentConstant * (N : ℝ) ^ 3) := by
  have hCore :=
    betaPrimeYTraceOneSquare_centered_memLp_two_and_lpNorm_eq_sqrt_internal
      hgap (h14FiniteGaussianFourthWickFormula_internal N K)
  refine ⟨hCore.1, ?_⟩
  intro hdense
  rw [hCore.2]
  apply Real.sqrt_le_iff.mpr
  refine ⟨?_, h8 hdense⟩
  exact mul_nonneg (by norm_num [denseClassicalMomentConstant])
    (pow_nonneg (by positivity) 3)

/-- Exact individual H10 endpoint reduction: only the H10 centered-variance
inequality is required. -/
theorem betaPrimeYTraceTwo_centered_two_momentPackage_of_sharpVariance
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (h10 : H10SharpCenteredVarianceContract N K) :
    MemLp
        (fun u => betaPrimeYTraceTwo N K u -
          ∫ z, betaPrimeYTraceTwo N K z ∂betaPrimeTraceFourLaw N K)
        2 (betaPrimeTraceFourLaw N K) ∧
      (16 * N ≤ K →
        lpNorm
            (fun u => betaPrimeYTraceTwo N K u -
              ∫ z, betaPrimeYTraceTwo N K z ∂betaPrimeTraceFourLaw N K)
            2 (betaPrimeTraceFourLaw N K) ≤
          denseClassicalMomentConstant * (N : ℝ) ^ 2) := by
  have hCore :=
    betaPrimeYTraceTwo_centered_memLp_two_and_lpNorm_eq_sqrt_internal
      hgap (h14FiniteGaussianFourthWickFormula_internal N K)
  refine ⟨hCore.1, ?_⟩
  intro hdense
  rw [hCore.2]
  apply Real.sqrt_le_iff.mpr
  refine ⟨?_, h10 hdense⟩
  exact mul_nonneg (by norm_num [denseClassicalMomentConstant])
    (pow_nonneg (by positivity) 2)

/-! ## What the internal H14 raw estimates prove -/

theorem h8DenominatorCenteredVariance_le_fourthRaw_internal (N K : ℕ) :
    h8DenominatorCenteredVariance N K ≤
      h8DenominatorFourthRawMoment N K := by
  unfold h8DenominatorCenteredVariance
  nlinarith [sq_nonneg (h8DenominatorSecondRawMoment N K)]

theorem h10DenominatorCenteredVariance_le_secondRaw_internal (N K : ℕ) :
    h10DenominatorCenteredVariance N K ≤
      h10DenominatorSecondRawMoment N K := by
  unfold h10DenominatorCenteredVariance
  nlinarith [sq_nonneg (h10DenominatorFirstRawMoment N K)]

/-- Strongest H8 variance estimate obtainable by discarding the centering
cancellation and applying the checked H14 raw fourth-moment bound. -/
theorem h8DenominatorCenteredVariance_le_h14Raw_internal
    {N K : ℕ} (hdense : 16 * N ≤ K) :
    h8DenominatorCenteredVariance N K ≤
      (2 : ℝ) ^ 16 * (N : ℝ) ^ 8 := by
  calc
    h8DenominatorCenteredVariance N K ≤
        h8DenominatorFourthRawMoment N K :=
      h8DenominatorCenteredVariance_le_fourthRaw_internal N K
    _ ≤ (2 : ℝ) ^ 16 * (N : ℝ) ^ 8 := by
      simpa [h8DenominatorFourthRawMoment] using
        (h14DenominatorFourthTracePolynomialBounds_internal N K).1 hdense

/-- Strongest H10 variance estimate obtainable by discarding the centering
cancellation and applying the checked H14 raw second-moment bound. -/
theorem h10DenominatorCenteredVariance_le_h14Raw_internal
    {N K : ℕ} (hdense : 16 * N ≤ K) :
    h10DenominatorCenteredVariance N K ≤
      (2 : ℝ) ^ 16 * (N : ℝ) ^ 6 := by
  calc
    h10DenominatorCenteredVariance N K ≤
        h10DenominatorSecondRawMoment N K :=
      h10DenominatorCenteredVariance_le_secondRaw_internal N K
    _ ≤ (2 : ℝ) ^ 16 * (N : ℝ) ^ 6 := by
      simpa [h10DenominatorSecondRawMoment] using
        (h14DenominatorFourthTracePolynomialBounds_internal N K).2 hdense

theorem h8_h14Raw_exponent_gap_identity (n : ℝ) :
    (2 : ℝ) ^ 16 * n ^ 8 = ((2 : ℝ) ^ 16 * n ^ 6) * n ^ 2 := by
  ring

theorem h10_h14Raw_exponent_gap_identity (n : ℝ) :
    (2 : ℝ) ^ 16 * n ^ 6 = ((2 : ℝ) ^ 16 * n ^ 4) * n ^ 2 := by
  ring

/-! ## A fully proved finite-dimension closure from the generous constant -/

/-- `2^32`, the largest dimension for which the raw H14 estimates alone are
absorbed by the squared endpoint constant `2^80`. -/
def h8H10RawMomentDimensionCeiling : ℕ := 4294967296

theorem natCast_sq_le_two_pow_sixtyFour_of_le_ceiling
    {N : ℕ} (hNdim : N ≤ h8H10RawMomentDimensionCeiling) :
    (N : ℝ) ^ 2 ≤ (2 : ℝ) ^ 64 := by
  have hcast : (N : ℝ) ≤ (4294967296 : ℝ) := by
    exact_mod_cast hNdim
  have hpow : (N : ℝ) ^ 2 ≤ (4294967296 : ℝ) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hcast 2
  norm_num at hpow ⊢
  exact hpow

theorem h8SharpCenteredVariance_of_dimensionSquare_le_internal
    {N K : ℕ} (hNdim : (N : ℝ) ^ 2 ≤ (2 : ℝ) ^ 64) :
    H8SharpCenteredVarianceContract N K := by
  intro hdense
  calc
    h8DenominatorCenteredVariance N K ≤
        (2 : ℝ) ^ 16 * (N : ℝ) ^ 8 :=
      h8DenominatorCenteredVariance_le_h14Raw_internal hdense
    _ = ((2 : ℝ) ^ 16 * (N : ℝ) ^ 6) * (N : ℝ) ^ 2 := by ring
    _ ≤ ((2 : ℝ) ^ 16 * (N : ℝ) ^ 6) * (2 : ℝ) ^ 64 := by
      gcongr
    _ = (denseClassicalMomentConstant * (N : ℝ) ^ 3) ^ 2 := by
      norm_num [denseClassicalMomentConstant]
      ring

theorem h10SharpCenteredVariance_of_dimensionSquare_le_internal
    {N K : ℕ} (hNdim : (N : ℝ) ^ 2 ≤ (2 : ℝ) ^ 64) :
    H10SharpCenteredVarianceContract N K := by
  intro hdense
  calc
    h10DenominatorCenteredVariance N K ≤
        (2 : ℝ) ^ 16 * (N : ℝ) ^ 6 :=
      h10DenominatorCenteredVariance_le_h14Raw_internal hdense
    _ = ((2 : ℝ) ^ 16 * (N : ℝ) ^ 4) * (N : ℝ) ^ 2 := by ring
    _ ≤ ((2 : ℝ) ^ 16 * (N : ℝ) ^ 4) * (2 : ℝ) ^ 64 := by
      gcongr
    _ = (denseClassicalMomentConstant * (N : ℝ) ^ 2) ^ 2 := by
      norm_num [denseClassicalMomentConstant]
      ring

theorem h8H10ExactFourthMomentTransport_upTo_twoPow32_internal
    {N K : ℕ} (hNdim : N ≤ h8H10RawMomentDimensionCeiling) :
    H8H10ExactFourthMomentTransport N K := by
  have hsquare := natCast_sq_le_two_pow_sixtyFour_of_le_ceiling hNdim
  exact h8H10ExactFourthMomentTransport_of_sharpCenteredVariance
    (h8SharpCenteredVariance_of_dimensionSquare_le_internal hsquare)
    (h10SharpCenteredVariance_of_dimensionSquare_le_internal hsquare)

/-- Literal H8 moment package, kernel-checked through `N ≤ 2^32`. -/
theorem betaPrimeYTraceOneSquare_centered_two_momentPackage_proved_upTo_twoPow32
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (hNdim : N ≤ h8H10RawMomentDimensionCeiling) :
    MemLp
        (fun u => betaPrimeYTraceOne N K u ^ 2 -
          ∫ z, betaPrimeYTraceOne N K z ^ 2 ∂betaPrimeTraceFourLaw N K)
        2 (betaPrimeTraceFourLaw N K) ∧
      (16 * N ≤ K →
        lpNorm
            (fun u => betaPrimeYTraceOne N K u ^ 2 -
              ∫ z, betaPrimeYTraceOne N K z ^ 2 ∂betaPrimeTraceFourLaw N K)
            2 (betaPrimeTraceFourLaw N K) ≤
          denseClassicalMomentConstant * (N : ℝ) ^ 3) :=
  betaPrimeYTraceOneSquare_centered_two_momentPackage_of_exactTransport
    hN hgap (h8H10ExactFourthMomentTransport_upTo_twoPow32_internal hNdim)

/-- Literal H10 moment package, kernel-checked through `N ≤ 2^32`. -/
theorem betaPrimeYTraceTwo_centered_two_momentPackage_proved_upTo_twoPow32
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (hNdim : N ≤ h8H10RawMomentDimensionCeiling) :
    MemLp
        (fun u => betaPrimeYTraceTwo N K u -
          ∫ z, betaPrimeYTraceTwo N K z ∂betaPrimeTraceFourLaw N K)
        2 (betaPrimeTraceFourLaw N K) ∧
      (16 * N ≤ K →
        lpNorm
            (fun u => betaPrimeYTraceTwo N K u -
              ∫ z, betaPrimeYTraceTwo N K z ∂betaPrimeTraceFourLaw N K)
            2 (betaPrimeTraceFourLaw N K) ≤
          denseClassicalMomentConstant * (N : ℝ) ^ 2) :=
  betaPrimeYTraceTwo_centered_two_momentPackage_of_exactTransport
    hN hgap (h8H10ExactFourthMomentTransport_upTo_twoPow32_internal hNdim)

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08
