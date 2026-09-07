import LogdetLean.GramHafnian.UltimateHiding.DenseScore.MatrixInverseMeasurability
import Mathlib.Tactic

/-!
# H6 conditional spectral reduction

This file contains no axiom and does not use the project declaration
`coeTakagiMuirhead_traceVector_betaPrime_external`.  It isolates the two
genuinely spectral source theorems needed by the human Takagi--Muirhead
argument and proves that they imply the exact H6 endpoint.

The result in this file is **CONDITIONAL**, because values of the two
contract structures are explicit theorem parameters.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian
open LogdetLean.GramHafnian.Wishart
open LogdetLean.GramHafnian.LocalAnticoncentration

/-- Trace powers of the unscaled COE matrix.  Taking `K = 1` in the
already-defined total trace map makes `unscaleCOECorner` the identity. -/
def unscaledCOETracePowerVector (r N : ℕ)
    (C : ConcreteMatrixState N) : Fin r → ℝ :=
  concreteCOETracePowerVector r N 1 C

theorem measurable_unscaledCOETracePowerVector (r N : ℕ) :
    Measurable (unscaledCOETracePowerVector r N) := by
  exact measurable_concreteCOETracePowerVector_internal r N 1

/-- Power sums of a real spectral vector. -/
def spectralPowerSumVector (r N : ℕ) (x : Fin N → ℝ) : Fin r → ℝ :=
  fun j ↦ ∑ i : Fin N, (x i) ^ (j.1 + 1)

theorem measurable_spectralPowerSumVector (r N : ℕ) :
    Measurable (spectralPowerSumVector r N) := by
  refine measurable_pi_lambda _ fun j ↦ ?_
  simp only [spectralPowerSumVector]
  fun_prop

/-- The scaled trace statistic is literally the unscaled statistic after
the explicit unscaling map. -/
theorem concreteCOETracePowerVector_eq_unscaled_comp
    (r N K : ℕ) :
    concreteCOETracePowerVector r N K =
      unscaledCOETracePowerVector r N ∘ unscaleCOECorner K := by
  funext A j
  simp [concreteCOETracePowerVector, unscaledCOETracePowerVector,
    concreteCOEZ, unscaleCOECorner]

/-- **CONDITIONAL contract.**  A Takagi-coordinate theorem for the
Friedman--Mello determinant-density model.  It supplies a measurable real
spectrum, its trace-power factorization almost everywhere, and its complete
spectral pushforward law.  No equality with the Wishart source is included. -/
structure COETakagiDensityContract
    (N K : ℕ) (ν : Measure (Fin N → ℝ)) where
  spectrum : ConcreteMatrixState N → (Fin N → ℝ)
  measurable_spectrum : Measurable spectrum
  trace_factorization : ∀ r : ℕ,
    unscaledCOETracePowerVector r N =ᵐ[
      coeCornerDeterminantDensityProbabilityMeasure N K]
      spectralPowerSumVector r N ∘ spectrum
  spectral_law :
    Measure.map spectrum
        (coeCornerDeterminantDensityProbabilityMeasure N K) = ν

/-- The concrete product Gaussian source type used by the beta-prime model. -/
abbrev RealBetaPrimeGaussianSource (N K : ℕ) :=
  Matrix (Fin (N + 1)) (Fin N) ℝ ×
    Matrix (Fin (K - N)) (Fin N) ℝ

/-- **CONDITIONAL contract.**  Muirhead's real matrix beta type-II spectral
law for the literal independent Gaussian/Wishart source.  It is separate
from the Takagi contract and does not mention a COE matrix. -/
structure WishartMuirheadDensityContract
    (N K : ℕ) (ν : Measure (Fin N → ℝ)) where
  spectrum : RealBetaPrimeGaussianSource N K → (Fin N → ℝ)
  measurable_spectrum : Measurable spectrum
  trace_factorization : ∀ r : ℕ,
    realBetaPrimeTracePowerVector r N K =ᵐ[
      realBetaPrimeGaussianSourceLaw N K]
      spectralPowerSumVector r N ∘ spectrum
  spectral_law :
    Measure.map spectrum (realBetaPrimeGaussianSourceLaw N K) = ν

/-- **CONDITIONAL H6.**  The exact original H6 endpoint follows from:

1. H5 stated as an explicit theorem parameter (not the project H5 axiom),
2. a Takagi spectral-density contract for the H5 model, and
3. an independent Muirhead beta-II spectral-density contract for the
   Gaussian/Wishart model.

The conclusion is verbatim the original declaration, including all implicit
quantifiers and the `r = 0` case. -/
theorem coeTakagiMuirhead_traceVector_betaPrime_conditional
    {r N K : ℕ} (_hN : 1 ≤ N) (_h2NK : 2 * N ≤ K)
    {ν : Measure (Fin N → ℝ)}
    (hH5 :
      concreteUnscaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K =
        coeCornerDeterminantDensityProbabilityMeasure N K)
    (hTakagi : COETakagiDensityContract N K ν)
    (hMuirhead : WishartMuirheadDensityContract N K ν) :
    Measure.map (concreteCOETracePowerVector r N K)
        (concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K) =
      Measure.map (realBetaPrimeTracePowerVector r N K)
        (realBetaPrimeGaussianSourceLaw N K) := by
  have hleft :
      Measure.map (concreteCOETracePowerVector r N K)
          (concreteScaledCOECornerLaw
            canonicalUnitaryHaarProbabilityFamily N K) =
        Measure.map (spectralPowerSumVector r N) ν := by
    rw [concreteCOETracePowerVector_eq_unscaled_comp]
    rw [← Measure.map_map (measurable_unscaledCOETracePowerVector r N)
      (measurable_unscaleCOECorner N K)]
    change Measure.map (unscaledCOETracePowerVector r N)
        (concreteUnscaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K) = _
    rw [hH5]
    calc
      Measure.map (unscaledCOETracePowerVector r N)
          (coeCornerDeterminantDensityProbabilityMeasure N K) =
          Measure.map (spectralPowerSumVector r N ∘ hTakagi.spectrum)
            (coeCornerDeterminantDensityProbabilityMeasure N K) := by
              exact Measure.map_congr (hTakagi.trace_factorization r)
      _ = Measure.map (spectralPowerSumVector r N)
          (Measure.map hTakagi.spectrum
            (coeCornerDeterminantDensityProbabilityMeasure N K)) := by
              rw [Measure.map_map (measurable_spectralPowerSumVector r N)
                hTakagi.measurable_spectrum]
      _ = Measure.map (spectralPowerSumVector r N) ν := by
              rw [hTakagi.spectral_law]
  have hright :
      Measure.map (realBetaPrimeTracePowerVector r N K)
          (realBetaPrimeGaussianSourceLaw N K) =
        Measure.map (spectralPowerSumVector r N) ν := by
    calc
      Measure.map (realBetaPrimeTracePowerVector r N K)
          (realBetaPrimeGaussianSourceLaw N K) =
          Measure.map (spectralPowerSumVector r N ∘ hMuirhead.spectrum)
            (realBetaPrimeGaussianSourceLaw N K) := by
              exact Measure.map_congr (hMuirhead.trace_factorization r)
      _ = Measure.map (spectralPowerSumVector r N)
          (Measure.map hMuirhead.spectrum
            (realBetaPrimeGaussianSourceLaw N K)) := by
              rw [Measure.map_map (measurable_spectralPowerSumVector r N)
                hMuirhead.measurable_spectrum]
      _ = Measure.map (spectralPowerSumVector r N) ν := by
              rw [hMuirhead.spectral_law]
  exact hleft.trans hright.symm

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
