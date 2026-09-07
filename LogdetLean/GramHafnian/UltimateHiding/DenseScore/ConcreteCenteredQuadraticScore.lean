import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CenteredCOERawExternal
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ConcreteCentralScore
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ConcreteTraceMomentTransfer
import Mathlib.Tactic

/-!
# Concrete centered quadratic COE score

This file closes `(R30)--(R31)` for the actual scaled square-COE law.  The
zero mean is derived from total mass in `CenteredCOERawExternal`; the norm
estimate uses only the three individually centered beta-prime trace moments.
No quadratic-score bound is an external input.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.LocalAnticoncentration

/-- Explicit dimension-free constant for the averaged centered quadratic
density score. -/
def concreteOrbitalScoreTwoConstant : ℝ :=
  28 * denseClassicalMomentConstant

/-- The literal averaged centered quadratic density belongs to `L²`. -/
theorem concreteCenteredQuadraticDensity_memLp_two
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    MemLp (concreteCenteredQuadraticDensity N K) 2
      (concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K) := by
  have hgap : 2 * N + 8 ≤ K := by omega
  let mu := concreteScaledCOECornerLaw
    canonicalUnitaryHaarProbabilityFamily N K
  let tOne := concreteCOETraceOne N K
  let tTwo := concreteCOETraceTwo N K
  let meanOne := ∫ A, tOne A ∂mu
  let meanSquare := ∫ A, tOne A ^ 2 ∂mu
  let meanTwo := ∫ A, tTwo A ∂mu
  have H := concreteCOE_centeredQuadraticTraceInputs_of_bracket_zero
    hN hdense (integral_concreteCenteredQuadraticTraceBracket_eq_zero_dense
      hN hdense)
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hc : concreteCOEExponent N K ≠ 0 := by
    unfold concreteCOEExponent
    have hdenseR : (16 : ℝ) * (N : ℝ) ≤ (K : ℝ) := by
      exact_mod_cast hdense
    have hNone : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    nlinarith
  let eTwo : ConcreteMatrixState N → ℝ := fun A ↦ tTwo A - meanTwo
  let eSquare : ConcreteMatrixState N → ℝ := fun A ↦ tOne A ^ 2 - meanSquare
  let eOne : ConcreteMatrixState N → ℝ := fun A ↦ tOne A - meanOne
  let a := quadraticTraceCoeffTwo (N : ℝ) (concreteCOEExponent N K)
  let b := quadraticTraceCoeffSquare (N : ℝ) (concreteCOEExponent N K)
  let d := quadraticTraceCoeffOne (N : ℝ)
  have hmean : a * meanTwo + b * meanSquare + d * meanOne = 0 := by
    simpa only [a, b, d, meanOne, meanSquare, meanTwo, tOne, tTwo, mu] using
      H.mean_identity hNr hc
  have hpoint : concreteCenteredQuadraticDensity N K =
      (4 / ((N : ℝ) * ((N : ℝ) + 1))) •
        (a • eTwo + b • eSquare + d • eOne) := by
    funext A
    change (4 / ((N : ℝ) * ((N : ℝ) + 1))) *
        centeredQuadraticTraceBracket (N : ℝ) (concreteCOEExponent N K)
          (tOne A) (tTwo A) =
      (4 / ((N : ℝ) * ((N : ℝ) + 1))) *
        (a * eTwo A + b * eSquare A + d * eOne A)
    congr 1
    exact centeredQuadraticTraceBracket_eq_centered_components hNr hc hmean
  rw [hpoint]
  have hTwo : MemLp eTwo 2 mu := by
    simpa only [eTwo, meanTwo, tTwo, mu] using H.centered_two_memLp
  have hSquare : MemLp eSquare 2 mu := by
    simpa only [eSquare, meanSquare, tOne, mu] using H.centered_square_memLp
  have hOne : MemLp eOne 2 mu := by
    simpa only [eOne, meanOne, tOne, mu] using H.centered_one_memLp
  exact (((hTwo.const_smul a).add (hSquare.const_smul b)).add
    (hOne.const_smul d)).const_smul
      (4 / ((N : ℝ) * ((N : ℝ) + 1)))

/-- Concrete, internally assembled `L²` estimate for `(R30)`. -/
theorem concreteCenteredQuadraticDensity_lpNorm_two_le
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (concreteCenteredQuadraticDensity N K) 2
      (concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K) ≤
      concreteOrbitalScoreTwoConstant := by
  have hgap : 2 * N + 8 ≤ K := by omega
  have hNone : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hc : (N : ℝ) ≤ concreteCOEExponent N K := by
    unfold concreteCOEExponent
    have hdenseR : (16 : ℝ) * (N : ℝ) ≤ (K : ℝ) := by
      exact_mod_cast hdense
    linarith
  have H := concreteCOE_centeredQuadraticTraceInputs_of_bracket_zero
    hN hdense (integral_concreteCenteredQuadraticTraceBracket_eq_zero_dense
      hN hdense)
  have hraw := H.normalized_bracket_lpNorm_two_le hNone hc
    (by norm_num [denseClassicalMomentConstant] : 0 ≤ denseClassicalMomentConstant)
    (by norm_num [denseClassicalMomentConstant] : 0 ≤ denseClassicalMomentConstant)
    (by norm_num [denseClassicalMomentConstant] : 0 ≤ denseClassicalMomentConstant)
  change lpNorm (fun ω ↦
      4 / ((N : ℝ) * ((N : ℝ) + 1)) *
        centeredQuadraticTraceBracket (N : ℝ) (concreteCOEExponent N K)
          (concreteCOETraceOne N K ω) (concreteCOETraceTwo N K ω)) 2
      (concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K) ≤
    28 * denseClassicalMomentConstant
  calc
    _ ≤ 4 * (2 * denseClassicalMomentConstant +
        2 * denseClassicalMomentConstant +
        3 * denseClassicalMomentConstant) := hraw
    _ = 28 * denseClassicalMomentConstant := by ring

/-- The eventwise quadratic score is also controlled in `L¹`, with the same
constant, by probability-space monotonicity. -/
theorem concreteCenteredQuadraticDensity_lpNorm_one_le
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (concreteCenteredQuadraticDensity N K) 1
      (concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K) ≤
      concreteOrbitalScoreTwoConstant := by
  let mu := concreteScaledCOECornerLaw
    canonicalUnitaryHaarProbabilityFamily N K
  letI : IsProbabilityMeasure mu :=
    canonicalScaledCOECornerLaw_isProbability (by omega)
  have hmem : MemLp (concreteCenteredQuadraticDensity N K) 2 mu := by
    simpa only [mu] using
      concreteCenteredQuadraticDensity_memLp_two hN hdense
  exact (lpNorm_one_le_lpNorm_two_of_memLp hmem).trans <| by
    simpa only [mu] using
      concreteCenteredQuadraticDensity_lpNorm_two_le hN hdense

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
