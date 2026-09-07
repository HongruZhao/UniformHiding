import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ExactVarianceLowOrderScoreBounds
import LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep.COEBaseDenseCertificate
import LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep.ThirdDerivativePropagation
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.UltraNGeTwoCubicNormalizationBound
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CombinedSharperFourthScoreBound
import Mathlib.Tactic

/-!
# Combined-sharper canonical score certificate

This certificate combines the exact low-order and cubic bounds with the
combined sharp H13/fourth-score assembly.  The constants are `5`, `44`,
`573`, `3934`, and `302906`; inverse-dimension propagation therefore gives
orbital-third constant `306840`.
-/

open MeasureTheory Set

namespace LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding
open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.UltimateHiding.DenseScore
open LogdetLean.GramHafnian.CurrentPRL

/-- Orbital-third constant obtained by propagating the cubic-origin estimate
with the combined-sharper fourth derivative. -/
def combinedSharperCanonicalOrbitalThirdConstant : ℝ :=
  ultraNGeTwoAveragedCenteredCubicNormalizationConstant +
    combinedSharperFullFourthDensityScoreConstant

theorem combinedSharperCanonicalOrbitalThirdConstant_eq :
    combinedSharperCanonicalOrbitalThirdConstant = 306840 := by
  rw [combinedSharperCanonicalOrbitalThirdConstant,
    ultraNGeTwoAveragedCenteredCubicNormalizationConstant_eq,
    combinedSharperFullFourthDensityScoreConstant_eq]
  norm_num

/-- Third derivative throughout the inverse-dimension orbital window. -/
theorem abs_iteratedDeriv_three_concreteSharedBetaOrbitalEventPath_le_combinedSharper
    {m N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K)
    (q : ℝ) (event : Set (ConcreteMatrixState N))
    (hevent : MeasurableSet event)
    (y : ℝ) (hy : y ∈ uIcc 0 (concreteGoodOrbitalAmplitude N 1 q)) :
    |iteratedDeriv 3
        (concreteSharedBetaOrbitalEventPath m N
          (concreteScaledCOECornerLaw
            canonicalUnitaryHaarProbabilityFamily N K)
          q event) y| ≤
      combinedSharperCanonicalOrbitalThirdConstant * (N : ℝ) := by
  let path := concreteSharedBetaOrbitalEventPath m N
    (concreteScaledCOECornerLaw
      canonicalUnitaryHaarProbabilityFamily N K) q event
  have hsmooth : ContDiff ℝ 4 path :=
    concreteSharedBetaOrbitalEventPath_contDiff_four
      hN hdense q event hevent
  have hzero : |iteratedDeriv 3 path 0| ≤
      ultraNGeTwoAveragedCenteredCubicNormalizationConstant * (N : ℝ) :=
    abs_iteratedDeriv_three_concreteSharedBetaOrbitalEventPath_zero_le_ultraNGeTwo
      hN hdense q event hevent
  have hfour : ∀ z ∈ uIcc 0 y,
      |iteratedDeriv 4 path z| ≤
        combinedSharperFullFourthDensityScoreConstant * (N : ℝ) ^ 2 := by
    intro z hz
    exact
      abs_iteratedDeriv_four_concreteSharedBetaOrbitalEventPath_le_combinedSharper
        hN hdense q event hevent z
  have hs : |y| ≤ 1 / (N : ℝ) := by
    have hamp :=
      abs_concreteGoodOrbitalAmplitude_one_le_inverse_dimension hN q
    have hyamp : |y| ≤ |concreteGoodOrbitalAmplitude N 1 q| := by
      simpa only [sub_zero] using abs_sub_left_of_mem_uIcc hy
    exact hyamp.trans hamp
  have hfourNonneg : 0 ≤ combinedSharperFullFourthDensityScoreConstant := by
    rw [combinedSharperFullFourthDensityScoreConstant_eq]
    norm_num
  simpa only [combinedSharperCanonicalOrbitalThirdConstant] using
    abs_iteratedDeriv_three_le_at_inverse_dimension_of_fourth
      hN hfourNonneg hsmooth hzero hfour hs

/-- Canonical square scaled-COE score certificate with the combined-sharper
constant ledger. -/
theorem uniformCanonicalScaledCOESharedBetaScoreCertificate_combinedSharper :
    UniformCanonicalScaledCOESharedBetaScoreCertificateAt
      exactVarianceCentralScoreOneConstant
      exactVarianceCentralScoreTwoConstant
      exactVarianceOrbitalScoreTwoConstant
      combinedSharperCanonicalOrbitalThirdConstant := by
  intro N K m hN hNK hKm hlarge hdense
  refine {
    scoreOne_nonneg := ?_
    scoreTwo_nonneg := ?_
    orbitalTwo_nonneg := ?_
    orbitalThree_nonneg := ?_
    scalarSmooth := ?_
    scalarFirst := ?_
    scalarSecond := ?_
    orbitalSmooth := ?_
    orbitalFirst := ?_
    orbitalSecond := ?_
    orbitalThird := ?_ }
  · norm_num [exactVarianceCentralScoreOneConstant]
  · norm_num [exactVarianceCentralScoreTwoConstant]
  · norm_num [exactVarianceOrbitalScoreTwoConstant]
  · rw [combinedSharperCanonicalOrbitalThirdConstant_eq]
    norm_num
  · intro A hA
    exact concreteBaseCentralEventPath_smooth hN hdense A hA
  · intro A hA
    exact abs_iteratedDeriv_one_concreteBaseCentralEventPath_le_exactVariance
      hN hdense A hA
  · intro A hA q y hy
    exact abs_iteratedDeriv_two_concreteBaseCentralEventPath_le_exactVariance
      hN hdense A hA y
  · intro q A hA
    exact (concreteSharedBetaOrbitalEventPath_contDiff_four
      hN hdense q A hA).of_le (by norm_num)
  · intro q A hA
    exact iteratedDeriv_one_concreteSharedBetaOrbitalEventPath_eq_zero
      hN hdense q A hA
  · intro q A hA
    exact abs_iteratedDeriv_two_concreteSharedBetaOrbitalEventPath_le_exactVariance
      hN hdense q A hA
  · intro q A hA y hy
    exact
      abs_iteratedDeriv_three_concreteSharedBetaOrbitalEventPath_le_combinedSharper
        hN hdense q A hA y hy

end

end LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep
