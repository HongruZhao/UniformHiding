import LogdetLean.GramHafnian.UltimateHiding.DenseScore.MatrixInverseMeasurability
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.BetaPrimeMeanInternal
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Narrow classical fixed-degree moment boundary

Mathlib does not presently contain the fixed negative-Wishart moment and
Gaussian `L^p` Poincare estimates needed for the finite COE score proof.
This file records only individually named trace monomials of the literal
beta-prime trace-vector law from `ClassicalCOEExternal`.  It contains no
averaged score, `D₂`, `D₃`, `Q₄`, event derivative, total-variation, or
hiding assertion.

The hypotheses `2N+8 ≤ K` give eight degrees of denominator-Wishart margin
for the finiteness assertions.  Every displayed dimension-uniform norm bound
uses the stronger paper-facing dense hypothesis `16N ≤ K`.  The deliberately
generous constant `2^40` is exposed rather than hidden behind an existential.

Classical source category: Muirhead, *Aspects of Multivariate Statistical
Theory* (1982), Chapter 3, Sections 3.2--3.3 (Wishart and matrix beta-prime
moments), combined with the real Gaussian `L^p` Poincare inequality applied
to the explicit trace polynomials.  These are classical inputs, not claims
of the new hiding theorem.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

/-- Four-coordinate beta-prime trace law.  Coordinate `j` is
`Tr (B₀⁻¹A₀)^(j+1)`. -/
def betaPrimeTraceFourLaw (N K : ℕ) : Measure (Fin 4 → ℝ) :=
  Measure.map (realBetaPrimeTracePowerVector 4 N K)
    (realBetaPrimeGaussianSourceLaw N K)

/-- The explicit universal constant used at the classical moment boundary. -/
def denseClassicalMomentConstant : ℝ := 1099511627776

/-- `Tr Y`, with `Y=cZ`. -/
def betaPrimeYTraceOne (N K : ℕ) (u : Fin 4 → ℝ) : ℝ :=
  concreteCOEExponent N K * u ⟨0, by norm_num⟩

/-- `Tr Y²`. -/
def betaPrimeYTraceTwo (N K : ℕ) (u : Fin 4 → ℝ) : ℝ :=
  concreteCOEExponent N K ^ 2 * u ⟨1, by norm_num⟩

/-- `Tr Y³`. -/
def betaPrimeYTraceThree (N K : ℕ) (u : Fin 4 → ℝ) : ℝ :=
  concreteCOEExponent N K ^ 3 * u ⟨2, by norm_num⟩

/-- `Tr Y⁴`. -/
def betaPrimeYTraceFour (N K : ℕ) (u : Fin 4 → ℝ) : ℝ :=
  concreteCOEExponent N K ^ 4 * u ⟨3, by norm_num⟩

/-- Measurability of the concrete rational trace map, now proved internally
from the determinant--adjugate formula for the total matrix inverse. -/
theorem measurable_concreteCOETracePowerVector_external (r N K : ℕ) :
    Measurable (concreteCOETracePowerVector r N K) :=
  measurable_concreteCOETracePowerVector_internal r N K

/-- The corresponding real beta-prime trace map is likewise internal. -/
theorem measurable_realBetaPrimeTracePowerVector_external (r N K : ℕ) :
    Measurable (realBetaPrimeTracePowerVector r N K) :=
  measurable_realBetaPrimeTracePowerVector_internal r N K

/-! ## Probability and first moment -/

/-- A finite matrix of independent standard real Gaussians has a probability
law.  This is proved from Mathlib's finite-product probability instance; it is
not part of the external moment boundary. -/
theorem standardRealGaussianMatrixMeasure_isProbability
    (rows cols : ℕ) :
    IsProbabilityMeasure (standardRealGaussianMatrixMeasure rows cols) := by
  unfold standardRealGaussianMatrixMeasure
  apply Measure.pi.instIsProbabilityMeasure

/-- The independent pair of Gaussian matrices defining the beta-prime source
has a probability law. -/
theorem realBetaPrimeGaussianSourceLaw_isProbability
    (N K : ℕ) : IsProbabilityMeasure (realBetaPrimeGaussianSourceLaw N K) := by
  unfold realBetaPrimeGaussianSourceLaw
  letI : IsProbabilityMeasure
      (standardRealGaussianMatrixMeasure (N + 1) N) :=
    standardRealGaussianMatrixMeasure_isProbability _ _
  letI : IsProbabilityMeasure
      (standardRealGaussianMatrixMeasure (K - N) N) :=
    standardRealGaussianMatrixMeasure_isProbability _ _
  infer_instance

/-- Product standard-Gaussian probability, pushed to the four traces.  The
only non-library input needed here is measurability of the total-inverse trace
map, exposed above. -/
theorem betaPrimeTraceFourLaw_isProbability
    (N K : ℕ) : IsProbabilityMeasure (betaPrimeTraceFourLaw N K) := by
  letI : IsProbabilityMeasure (realBetaPrimeGaussianSourceLaw N K) :=
    realBetaPrimeGaussianSourceLaw_isProbability _ _
  exact Measure.isProbabilityMeasure_map
    (measurable_realBetaPrimeTracePowerVector_external 4 N K).aemeasurable

/-- Monotonicity of real `L^p` norms on a probability space. -/
private theorem lpNorm_le_lpNorm_of_exponent_le
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {p q : ENNReal} {f : Omega → ℝ}
    (hf : MemLp f q mu) (hpq : p ≤ q) :
    lpNorm f p mu ≤ lpNorm f q mu := by
  rw [← toReal_eLpNorm (hf.mono_exponent hpq).aestronglyMeasurable,
    ← toReal_eLpNorm hf.aestronglyMeasurable]
  exact ENNReal.toReal_mono hf.eLpNorm_ne_top
    (eLpNorm_le_eLpNorm_of_exponent_le hpq hf.aestronglyMeasurable)

/-- Square integrability recovered from integrability of the pointwise
square. -/
private theorem memLp_two_of_sq_memLp_one
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {f : Omega → ℝ}
    (hf : AEStronglyMeasurable f mu)
    (hsq : MemLp (fun x ↦ f x ^ 2) 1 mu) : MemLp f 2 mu := by
  apply (memLp_two_iff_integrable_sq hf).2
  exact memLp_one_iff_integrable.mp hsq

/-- The square of the real `L^2` norm is the `L^1` norm of the pointwise
square. -/
private theorem lpNorm_two_sq_eq_lpNorm_sq_one
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {f : Omega → ℝ}
    (hf : MemLp f 2 mu) :
    lpNorm f 2 mu ^ 2 = lpNorm (fun x ↦ f x ^ 2) 1 mu := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (p := (2 : ENNReal)) (by norm_num)
      (by norm_num) hf.aestronglyMeasurable]
  rw [lpNorm_one_eq_integral_norm]
  · norm_num
    have hnonneg : 0 ≤ ∫ x, f x ^ 2 ∂mu :=
      integral_nonneg fun _ ↦ sq_nonneg _
    rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hnonneg]
  · exact AEStronglyMeasurable.pow hf.aestronglyMeasurable 2

/-- Exact first beta-prime trace mean, equivalent to `E(cZ)=(N+1)I`.
This is now proved internally from the finite-dimensional Stein--Haff identity,
the standard/half-Gaussian scaling bridge, Gaussian covariance, and Fubini. -/
theorem betaPrimeYTraceOne_integral_external
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 2 ≤ K) :
    (∫ u, betaPrimeYTraceOne N K u ∂(betaPrimeTraceFourLaw N K)) =
      (N : ℝ) * ((N : ℝ) + 1) := by
  letI : IsProbabilityMeasure (realBetaPrimeGaussianSourceLaw N K) :=
    realBetaPrimeGaussianSourceLaw_isProbability _ _
  have hbeta : Measurable (betaPrimeYTraceOne N K) := by
    unfold betaPrimeYTraceOne
    exact measurable_const.mul (measurable_pi_apply _)
  unfold betaPrimeTraceFourLaw
  rw [integral_map
    (measurable_realBetaPrimeTracePowerVector_internal 4 N K).aemeasurable
    hbeta.aestronglyMeasurable]
  simp only [betaPrimeYTraceOne, realBetaPrimeTracePowerVector,
    Nat.zero_add, pow_one]
  rw [integral_const_mul,
    integral_realMatrixBetaPrime_trace_source (N := N) (K := K) (by omega)]
  have hKN : N ≤ K := by omega
  have hden : (((K - N : ℕ) : ℝ) - (N : ℝ) - 1) =
      concreteCOEExponent N K := by
    rw [Nat.cast_sub hKN]
    simp only [concreteCOEExponent]
    ring
  rw [hden]
  have hc : concreteCOEExponent N K ≠ 0 := by
    unfold concreteCOEExponent
    have hreal : 2 * (N : ℝ) + 2 ≤ (K : ℝ) := by
      exact_mod_cast hgap
    linarith
  field_simp [hc]

/-! ## Literal uncentered trace monomials -/

/-! Each primitive moment source is exposed once as a package containing its
threshold finiteness statement and its conditional dense-regime estimate.
The former `MemLp` and `lpNorm` APIs remain as kernel-proved projections. -/

def derivedRawTraceOneConstant : ℝ :=
  2 * denseClassicalMomentConstant

/-- Common coefficient for the internally recovered square and mixed raw
trace products. -/
def derivedRawTraceProductConstant : ℝ :=
  4 * denseClassicalMomentConstant ^ 2

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
