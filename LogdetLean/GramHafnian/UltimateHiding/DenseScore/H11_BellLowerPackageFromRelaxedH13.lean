import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H11_BellLowerMomentAssembly
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H11_COEBlockLiteralSign
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H12_ExactMomentEndpointA4
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H14_StrongTwoSquareProductBound
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H13_RelaxedProjectiveEnvelopeTransport
import Mathlib.Tactic

/-!
# H11 Bell-normalization consumer for the relaxed H13 package

The completed H13 calculation uses `16` times the H14 projective envelope.
Its strong product constant still fits the deliberately large public H11
budget.  This file records that numerical splice without depending on the
active H13 endpoint module.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

/-- The sharp H12/H14 packages and a relaxed-strong H13 package still fit the
aggregate lower-Bell budget required by H11. -/
theorem h11BellFourLowerMomentPackage_of_relaxedH13
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (hOneThree :
      MemLp (fun p ↦ concreteCenteredEll 1 N K p *
        concreteCenteredEll 3 N K p) 1
          (concreteCenteredScoreProductLaw N K) ∧
        (16 * N ≤ K →
          lpNorm (fun p ↦ concreteCenteredEll 1 N K p *
            concreteCenteredEll 3 N K p) 1
              (concreteCenteredScoreProductLaw N K) ≤
            h13RelaxedProjectiveEnvelopeStrongConstant * (N : ℝ) ^ 2)) :
    H11BellFourLowerMomentPackage N K := by
  have hOne :=
    centeredLogScore_oneFourth_momentPackage_strong_proved_A1A2A3A4
      hN hgap
  have hTwo := centeredLogScore_twoSquare_momentPackage_strong_A1A2A3
    hN hgap
  let H : H11BellLowerSharpMonomialPackage N K
      ((2 : ℝ) ^ 28)
      h14StrongProjectiveEnvelopeConstant
      h13RelaxedProjectiveEnvelopeStrongConstant :=
    { oneFourth_memLp := hOne.1
      twoSquare_memLp := hTwo.1
      oneThree_memLp := hOneThree.1
      oneFourth_lpNorm_le := hOne.2
      twoSquare_lpNorm_le := hTwo.2
      oneThree_lpNorm_le := hOneThree.2 }
  apply h11BellFourLowerMomentPackage_of_sharpMonomials hN H
  norm_num [h13RelaxedProjectiveEnvelopeStrongConstant,
    h14StrongProjectiveEnvelopeConstant,
    h14BetaPrimeProjectiveLowerMomentConstant,
    denseClassicalMomentConstant, centeredLogScoreFourthMomentConstant]

/-- Final H11 normalization reducer from the foundations-only support sign
and the relaxed-strong H13 package. -/
theorem centeredLogScore_four_momentPackage_of_relaxedH13
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (hOneThree :
      MemLp (fun p ↦ concreteCenteredEll 1 N K p *
        concreteCenteredEll 3 N K p) 1
          (concreteCenteredScoreProductLaw N K) ∧
        (16 * N ≤ K →
          lpNorm (fun p ↦ concreteCenteredEll 1 N K p *
            concreteCenteredEll 3 N K p) 1
              (concreteCenteredScoreProductLaw N K) ≤
            h13RelaxedProjectiveEnvelopeStrongConstant * (N : ℝ) ^ 2)) :
    MemLp (concreteCenteredEll 4 N K) 1
        (concreteCenteredScoreProductLaw N K) ∧
      (16 * N ≤ K →
        lpNorm (concreteCenteredEll 4 N K) 1
            (concreteCenteredScoreProductLaw N K) ≤
          centeredLogScoreFourthMomentConstant * (N : ℝ) ^ 2) :=
  centeredLogScore_four_momentPackage_of_BellNormalization_nonpos
    hN hgap
      (h11FourthLogScoreNonpositiveOnSupport_proved hN hgap)
      (h11BellFourLowerMomentPackage_of_relaxedH13 hN hgap hOneThree)

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
