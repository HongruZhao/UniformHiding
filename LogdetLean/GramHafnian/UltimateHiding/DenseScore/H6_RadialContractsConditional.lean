import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H6_Conditional
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H6_VectorChangeOfVariables
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H6_TakagiForward
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H6_WishartSimilarity

/-!
# H6 source-native radial contracts (CONDITIONAL)

This file narrows the remaining scientific boundary to two independent radial
integration statements.  The Takagi density appearing below is literally

`|Delta(lambda)| * ∏ i (1-lambda_i)^((K-2N-1)/2)`.

In particular, the contract contains **no extra power of `lambda_i`**.  The
coordinate change and its Jacobian are the proved theorems
`map_coeEigenvalueRadialMeasure_eq_betaPrime` and
`map_normalizedCOEEigenvalueRadialMeasure_eq_normalizedBetaPrime`, not
hypotheses.  Canonical normalization is used on each side, so no equality of
separately computed Selberg constants is assumed.

All declarations in this file are conditional theorem schemas.  No external
H5 or H6 axiom is used.
-/

open scoped ENNReal
open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian
open LogdetLean.GramHafnian.Wishart
open LogdetLean.GramHafnian.CurrentPRL
open H6CoordinateAlgebra H6VectorChangeOfVariables

/-- **CONDITIONAL Takagi--Weyl contract.**  The squared Takagi values of the
H5 determinant-density model have the explicit unnormalized Jacobi radial
measure, up to the single normalization coefficient `normalizer`.  The trace
factorization uses `lambda/(1-lambda)` because H6 concerns `Z`, not `C Cᴴ`.

The displayed radial measure fixes the exact Jacobian at issue: Vandermonde
power one, with no coordinate power `∏ lambda_i^a`. -/
structure COETakagiWeylRadialContract
    (N K : ℕ) where
  spectrum : ConcreteMatrixState N → (Fin N → ℝ)
  measurable_spectrum : Measurable spectrum
  unitary : ConcreteMatrixState N → Matrix.unitaryGroup (Fin N) ℂ
  support : ∀ᵐ C ∂coeCornerDeterminantDensityProbabilityMeasure N K,
    spectrum C ∈ openUnitCube N
  representation : ∀ᵐ C ∂coeCornerDeterminantDensityProbabilityMeasure N K,
    C = h6TakagiForward (unitary C) (spectrum C)
  radial_law :
    Measure.map spectrum
        (coeCornerDeterminantDensityProbabilityMeasure N K) =
      normalizedCOEEigenvalueRadialMeasure N K

/-- The trace factorization is a theorem from the explicit Takagi
representation, not part of the conditional Jacobian input. -/
theorem COETakagiWeylRadialContract.trace_factorization
    {N K : ℕ}
    (h : COETakagiWeylRadialContract N K) (r : ℕ) :
    unscaledCOETracePowerVector r N =ᵐ[
      coeCornerDeterminantDensityProbabilityMeasure N K]
      spectralPowerSumVector r N ∘ betaPrimeForwardVector N ∘ h.spectrum := by
  filter_upwards [h.support, h.representation] with C hsupport hrepresentation
  calc
    unscaledCOETracePowerVector r N C =
        unscaledCOETracePowerVector r N
          (h6TakagiForward (h.unitary C) (h.spectrum C)) :=
      congrArg (unscaledCOETracePowerVector r N) hrepresentation
    _ = (spectralPowerSumVector r N ∘ betaPrimeForwardVector N ∘
          h.spectrum) C := by
      change concreteCOETracePowerVector r N 1
          (h6TakagiForward (h.unitary C) (h.spectrum C)) =
        fun j ↦ ∑ i : Fin N,
          betaPrimeForward (h.spectrum C i) ^ (j.1 + 1)
      exact concreteCOETracePowerVector_h6TakagiForward
        (r := r) (h.unitary C) (h.spectrum C) (fun i ↦ hsupport i)

/-- **CONDITIONAL Muirhead contract.**  The generalized eigenvalues of the
literal independent Gaussian/Wishart source have the explicit real beta-II
radial measure, with the same normalization coefficient.  This contract does
not mention COE matrices or the H6 trace-vector conclusion. -/
structure WishartMuirheadBetaIIRadialContract
    (N K : ℕ) where
  spectrum : RealBetaPrimeGaussianSource N K → (Fin N → ℝ)
  measurable_spectrum : Measurable spectrum
  conjugator : RealBetaPrimeGaussianSource N K → Matrix (Fin N) (Fin N) ℝ
  conjugator_unit : ∀ᵐ p ∂realBetaPrimeGaussianSourceLaw N K,
    IsUnit (conjugator p).det
  diagonalization : ∀ᵐ p ∂realBetaPrimeGaussianSourceLaw N K,
    realMatrixBetaPrimeOfGaussianSource p =
      (conjugator p)⁻¹ * Matrix.diagonal (spectrum p) * conjugator p
  radial_law :
    Measure.map spectrum (realBetaPrimeGaussianSourceLaw N K) =
      normalizedBetaPrimeEigenvalueRadialMeasure N K

/-- As on the Takagi side, the complete trace-power factorization is derived
from an almost-sure matrix diagonalization rather than assumed as a family of
trace-vector equalities. -/
theorem WishartMuirheadBetaIIRadialContract.trace_factorization
    {N K : ℕ}
    (h : WishartMuirheadBetaIIRadialContract N K) (r : ℕ) :
    realBetaPrimeTracePowerVector r N K =ᵐ[
      realBetaPrimeGaussianSourceLaw N K]
      spectralPowerSumVector r N ∘ h.spectrum := by
  filter_upwards [h.conjugator_unit, h.diagonalization] with p hunit hdiag
  funext j
  unfold realBetaPrimeTracePowerVector spectralPowerSumVector
  have hpow := congrArg
    (fun M : Matrix (Fin N) (Fin N) ℝ ↦ Matrix.trace (M ^ (j.1 + 1))) hdiag
  calc
    Matrix.trace ((realMatrixBetaPrimeOfGaussianSource p) ^ (j.1 + 1)) =
        Matrix.trace
          (((h.conjugator p)⁻¹ * Matrix.diagonal (h.spectrum p) *
            h.conjugator p) ^ (j.1 + 1)) := hpow
    _ = Matrix.trace ((Matrix.diagonal (h.spectrum p)) ^ (j.1 + 1)) :=
      trace_inverse_conjugate_pow (h.conjugator p)
        (Matrix.diagonal (h.spectrum p)) (j.1 + 1) hunit
    _ = ∑ i : Fin N, (h.spectrum p i) ^ (j.1 + 1) := by
      rw [Matrix.diagonal_pow, Matrix.trace_diagonal]
      rfl

/-- **CONDITIONAL H6 with source-native premises.**  The conclusion is the
verbatim original H6 endpoint.  Its assumptions are:

1. the exact H5 proposition as a theorem parameter;
2. the Takagi--Weyl radial formula with no extra `lambda_i` power; and
3. the independent real Muirhead beta-II radial formula.

The finite-dimensional density/Jacobian transformation joining (2) and (3)
is proved, not assumed. -/
theorem coeTakagiMuirhead_traceVector_betaPrime_radial_conditional
    {r N K : ℕ} (hN : 1 ≤ N) (_h2NK : 2 * N ≤ K)
    (hH5 :
      concreteUnscaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K =
        coeCornerDeterminantDensityProbabilityMeasure N K)
    (hTakagi : COETakagiWeylRadialContract N K)
    (hMuirhead : WishartMuirheadBetaIIRadialContract N K) :
    Measure.map (concreteCOETracePowerVector r N K)
        (concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K) =
      Measure.map (realBetaPrimeTracePowerVector r N K)
        (realBetaPrimeGaussianSourceLaw N K) := by
  have hforward : Measurable (betaPrimeForwardVector N) :=
    measurable_betaPrimeForwardVector N
  have hpowers : Measurable (spectralPowerSumVector r N) :=
    measurable_spectralPowerSumVector r N
  have hradial :
      Measure.map (betaPrimeForwardVector N)
          (Measure.map hTakagi.spectrum
            (coeCornerDeterminantDensityProbabilityMeasure N K)) =
        Measure.map hMuirhead.spectrum
          (realBetaPrimeGaussianSourceLaw N K) := by
    rw [hTakagi.radial_law,
      map_normalizedCOEEigenvalueRadialMeasure_eq_normalizedBetaPrime hN,
      hMuirhead.radial_law]
  have hleft :
      Measure.map (concreteCOETracePowerVector r N K)
          (concreteScaledCOECornerLaw
            canonicalUnitaryHaarProbabilityFamily N K) =
        Measure.map (spectralPowerSumVector r N)
          (Measure.map (betaPrimeForwardVector N)
            (Measure.map hTakagi.spectrum
              (coeCornerDeterminantDensityProbabilityMeasure N K))) := by
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
          Measure.map
            (spectralPowerSumVector r N ∘ betaPrimeForwardVector N ∘
              hTakagi.spectrum)
            (coeCornerDeterminantDensityProbabilityMeasure N K) := by
              exact Measure.map_congr (hTakagi.trace_factorization r)
      _ = Measure.map (spectralPowerSumVector r N ∘ betaPrimeForwardVector N)
          (Measure.map hTakagi.spectrum
            (coeCornerDeterminantDensityProbabilityMeasure N K)) := by
              rw [Measure.map_map (hpowers.comp hforward)
                hTakagi.measurable_spectrum]
              rfl
      _ = Measure.map (spectralPowerSumVector r N)
          (Measure.map (betaPrimeForwardVector N)
            (Measure.map hTakagi.spectrum
              (coeCornerDeterminantDensityProbabilityMeasure N K))) := by
              rw [Measure.map_map hpowers hforward]
  have hright :
      Measure.map (realBetaPrimeTracePowerVector r N K)
          (realBetaPrimeGaussianSourceLaw N K) =
        Measure.map (spectralPowerSumVector r N)
          (Measure.map hMuirhead.spectrum
            (realBetaPrimeGaussianSourceLaw N K)) := by
    calc
      Measure.map (realBetaPrimeTracePowerVector r N K)
          (realBetaPrimeGaussianSourceLaw N K) =
          Measure.map (spectralPowerSumVector r N ∘ hMuirhead.spectrum)
            (realBetaPrimeGaussianSourceLaw N K) := by
              exact Measure.map_congr (hMuirhead.trace_factorization r)
      _ = Measure.map (spectralPowerSumVector r N)
          (Measure.map hMuirhead.spectrum
            (realBetaPrimeGaussianSourceLaw N K)) := by
              rw [Measure.map_map hpowers hMuirhead.measurable_spectrum]
  calc
    Measure.map (concreteCOETracePowerVector r N K)
        (concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K) =
        Measure.map (spectralPowerSumVector r N)
          (Measure.map (betaPrimeForwardVector N)
            (Measure.map hTakagi.spectrum
              (coeCornerDeterminantDensityProbabilityMeasure N K))) := hleft
    _ = Measure.map (spectralPowerSumVector r N)
          (Measure.map hMuirhead.spectrum
            (realBetaPrimeGaussianSourceLaw N K)) := by rw [hradial]
    _ = Measure.map (realBetaPrimeTracePowerVector r N K)
          (realBetaPrimeGaussianSourceLaw N K) := hright.symm

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
