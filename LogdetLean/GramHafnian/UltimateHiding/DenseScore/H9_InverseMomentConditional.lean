import LogdetLean.GramHafnian.UltimateHiding.DenseScore.BetaPrimeMeanInternal
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# H9 denominator-only inverse-Wishart contract

This module isolates the smallest inverse-Wishart input left after the
finite Gaussian numerator contractions in H9.  It does not assume a
beta-prime trace moment, a COE moment, or the H9 conclusion.

For `B` with iid standard real Gaussian entries, put

`D(B) = (K - 2N - 1) (BᵀB)⁻¹`.

The already formalized first inverse-Wishart moment gives
`E[Tr D] = N`.  The higher-order denominator boundary consists only of

* the centered trace `Tr D - N` in `L⁴`, and
* `Tr(D²)` in `L²`.

The threshold `2N + 8 ≤ K` is exactly
`K - N > N + 7`, the order-four inverse-Wishart threshold.  The two
dimension-uniform estimates are requested only in the paper's dense regime
`16N ≤ K`.  No inhabitant of the contract is postulated here: a conditional
H9 theorem must receive it as an explicit theorem parameter.
-/

open MeasureTheory
open ProbabilityTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.Wishart

/-- The Gaussian denominator matrix in the beta-prime representation. -/
abbrev H9InverseWishartSample (N K : ℕ) :=
  Matrix (Fin (K - N)) (Fin N) ℝ

/-- Law of the denominator Gaussian matrix `B`. -/
def h9InverseWishartDenominatorLaw (N K : ℕ) :
    Measure (H9InverseWishartSample N K) :=
  standardRealGaussianMatrixMeasure (K - N) N

/-- The scaled inverse Wishart matrix
`D=(K-2N-1)(BᵀB)⁻¹` occurring after conditioning on the denominator. -/
def h9ScaledInverseWishart (N K : ℕ) (B : H9InverseWishartSample N K) :
    Matrix (Fin N) (Fin N) ℝ :=
  concreteCOEExponent N K • (realWishartGram B)⁻¹

/-- The deterministic regularization sequence `epsilon_j = 1/(j+1)` used to
avoid differentiating through the singular set of the denominator Gram
matrix. -/
def h9RegularizationEpsilon (j : ℕ) : ℝ :=
  (((j + 1 : ℕ) : ℝ))⁻¹

@[simp] theorem h9RegularizationEpsilon_pos (j : ℕ) :
    0 < h9RegularizationEpsilon j := by
  unfold h9RegularizationEpsilon
  exact inv_pos.mpr (by exact_mod_cast (Nat.zero_lt_succ j))

/-- Reviewer-safe regularization
`D_j = (K-2N-1) (B.transpose * B + epsilon_j I)⁻¹`.

All Gaussian Poincare or hypercontractive estimates in H9 are to be applied
to `D_j`, before passing to the total-inverse observable `D` almost
everywhere. -/
def h9RegularizedScaledInverseWishart (N K j : ℕ)
    (B : H9InverseWishartSample N K) :
    Matrix (Fin N) (Fin N) ℝ :=
  concreteCOEExponent N K •
    (realWishartGram B + h9RegularizationEpsilon j •
      (1 : Matrix (Fin N) (Fin N) ℝ))⁻¹

/-- Denominator fluctuation in the conditional mean of the numerator trace. -/
def h9CenteredInverseTrace (N K : ℕ) (B : H9InverseWishartSample N K) : ℝ :=
  Matrix.trace (h9ScaledInverseWishart N K B) - (N : ℝ)

/-- The quadratic spectral observable in the conditional Gaussian fourth
moment `48 n Tr(D⁴) + 12 n² (Tr(D²))²`. -/
def h9InverseTraceSquare (N K : ℕ) (B : H9InverseWishartSample N K) : ℝ :=
  Matrix.trace
    (h9ScaledInverseWishart N K B * h9ScaledInverseWishart N K B)

/-- Centered trace of the regularized inverse-Wishart matrix. -/
def h9RegularizedCenteredInverseTrace (N K j : ℕ)
    (B : H9InverseWishartSample N K) : ℝ :=
  Matrix.trace (h9RegularizedScaledInverseWishart N K j B) - (N : ℝ)

/-- `Tr(D_j^2)`, the regularized conditional-variance observable. -/
def h9RegularizedInverseTraceSquare (N K j : ℕ)
    (B : H9InverseWishartSample N K) : ℝ :=
  Matrix.trace
    (h9RegularizedScaledInverseWishart N K j B *
      h9RegularizedScaledInverseWishart N K j B)

/-- Explicit denominator constant used in the human proof (`2^12`). -/
def h9InverseWishartMomentConstant : ℝ := 4096

@[simp] theorem h9InverseWishartMomentConstant_eq_two_pow :
    h9InverseWishartMomentConstant = (2 : ℝ) ^ 12 := by
  norm_num [h9InverseWishartMomentConstant]

theorem h9InverseWishart_denominator_gap
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K) :
    N + 1 < K - N := by
  omega

theorem h9InverseWishart_exponent_pos
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K) :
    0 < concreteCOEExponent N K := by
  unfold concreteCOEExponent
  have hreal : 2 * (N : ℝ) + 8 ≤ (K : ℝ) := by
    exact_mod_cast hgap
  linarith

theorem h9InverseWishartDenominatorLaw_isProbability (N K : ℕ) :
    IsProbabilityMeasure (h9InverseWishartDenominatorLaw N K) := by
  unfold h9InverseWishartDenominatorLaw
  exact standardRealGaussianMatrixMeasure_isProbability_internal _ _

theorem measurable_h9ScaledInverseWishart (N K : ℕ) :
    Measurable (h9ScaledInverseWishart N K) := by
  have hGram : Measurable
      (fun B : H9InverseWishartSample N K ↦ realWishartGram B) := by
    unfold realWishartGram
    refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    fun_prop
  have hInv : Measurable
      (fun B : H9InverseWishartSample N K ↦ (realWishartGram B)⁻¹) :=
    (measurable_realMatrix_inv N).comp hGram
  unfold h9ScaledInverseWishart
  refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
  exact measurable_const.mul
    ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hInv))

theorem measurable_h9CenteredInverseTrace (N K : ℕ) :
    Measurable (h9CenteredInverseTrace N K) := by
  have hD : Measurable (h9ScaledInverseWishart N K) :=
    measurable_h9ScaledInverseWishart N K
  unfold h9CenteredInverseTrace Matrix.trace
  exact (Finset.measurable_sum _ fun i _ ↦
    (measurable_pi_apply i).comp
      ((measurable_pi_apply i).comp hD)).sub measurable_const

theorem measurable_h9InverseTraceSquare (N K : ℕ) :
    Measurable (h9InverseTraceSquare N K) := by
  have hD : Measurable (h9ScaledInverseWishart N K) :=
    measurable_h9ScaledInverseWishart N K
  unfold h9InverseTraceSquare Matrix.trace
  simp only [Matrix.diag_apply, Matrix.mul_apply]
  exact Finset.measurable_sum _ fun i _ ↦
    Finset.measurable_sum _ fun j _ ↦
      ((measurable_pi_apply j).comp
        ((measurable_pi_apply i).comp hD)).mul
      ((measurable_pi_apply i).comp
        ((measurable_pi_apply j).comp hD))

theorem h9ScaledInverseWishart_posSemidef
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K)
    (B : H9InverseWishartSample N K) :
    (h9ScaledInverseWishart N K B).PosSemidef := by
  unfold h9ScaledInverseWishart
  exact (realWishartGram_inv_posSemidef B).smul
    (le_of_lt (h9InverseWishart_exponent_pos hgap))

theorem h9InverseTraceSquare_nonneg
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K)
    (B : H9InverseWishartSample N K) :
    0 ≤ h9InverseTraceSquare N K B := by
  have hD := h9ScaledInverseWishart_posSemidef hgap B
  simpa [h9InverseTraceSquare, pow_two] using (hD.pow 2).trace_nonneg

theorem integrable_h9ScaledInverseTrace
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K) :
    Integrable
      (fun B : H9InverseWishartSample N K ↦
        Matrix.trace (h9ScaledInverseWishart N K B))
      (h9InverseWishartDenominatorLaw N K) := by
  have hinv := integrable_trace_nonsingInv_realWishartGram_standardGaussian
    (h9InverseWishart_denominator_gap hgap)
  have hscaled := hinv.const_mul (concreteCOEExponent N K)
  simpa [h9InverseWishartDenominatorLaw, h9ScaledInverseWishart,
    Matrix.trace_smul] using hscaled

/-- The scaled inverse-Wishart trace has exact mean `N`; this uses only the
already kernel-checked first inverse-Wishart moment. -/
theorem integral_h9ScaledInverseTrace
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K) :
    (∫ B : H9InverseWishartSample N K,
        Matrix.trace (h9ScaledInverseWishart N K B)
        ∂h9InverseWishartDenominatorLaw N K) = (N : ℝ) := by
  have hKN : N ≤ K := by omega
  have hmean := standardGaussian_inverseWishart_trace_mean
    (h9InverseWishart_denominator_gap hgap)
  have hden : (((K - N : ℕ) : ℝ) - (N : ℝ) - 1) =
      concreteCOEExponent N K := by
    rw [Nat.cast_sub hKN]
    simp only [concreteCOEExponent]
    ring
  have hc : concreteCOEExponent N K ≠ 0 :=
    (h9InverseWishart_exponent_pos hgap).ne'
  unfold h9InverseWishartDenominatorLaw h9ScaledInverseWishart
  simp only [Matrix.trace_smul, smul_eq_mul]
  rw [integral_const_mul, hmean, hden]
  field_simp [hc]

theorem integrable_h9CenteredInverseTrace
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K) :
    Integrable (h9CenteredInverseTrace N K)
      (h9InverseWishartDenominatorLaw N K) := by
  letI : IsProbabilityMeasure (h9InverseWishartDenominatorLaw N K) :=
    h9InverseWishartDenominatorLaw_isProbability N K
  exact (integrable_h9ScaledInverseTrace hgap).sub (integrable_const _)

/-- The denominator fluctuation is centered exactly. -/
theorem integral_h9CenteredInverseTrace
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K) :
    (∫ B : H9InverseWishartSample N K,
        h9CenteredInverseTrace N K B
        ∂h9InverseWishartDenominatorLaw N K) = 0 := by
  letI : IsProbabilityMeasure (h9InverseWishartDenominatorLaw N K) :=
    h9InverseWishartDenominatorLaw_isProbability N K
  unfold h9CenteredInverseTrace
  rw [integral_sub (integrable_h9ScaledInverseTrace hgap) (integrable_const _),
    integral_h9ScaledInverseTrace hgap]
  simp only [integral_const, measureReal_def,
    IsProbabilityMeasure.measure_univ, ENNReal.toReal_one, one_smul, sub_self]

/--
**CONDITIONAL denominator contract for H9.**

This is intentionally a `Prop`-valued structure with no constructor theorem
in this module.  Its fields are precisely the two higher inverse-Wishart
facts consumed after the finite Gaussian contraction.  In particular, it
does not mention the beta-prime trace law or any H9 conclusion.
-/
structure H9InverseWishartDenominatorPackage (N K : ℕ) : Prop where
  centeredTrace_memLp_four :
    MemLp (h9CenteredInverseTrace N K) 4
      (h9InverseWishartDenominatorLaw N K)
  traceSquare_memLp_two :
    MemLp (h9InverseTraceSquare N K) 2
      (h9InverseWishartDenominatorLaw N K)
  dense_bounds : 16 * N ≤ K →
    lpNorm (h9CenteredInverseTrace N K) 4
        (h9InverseWishartDenominatorLaw N K) ≤
      h9InverseWishartMomentConstant ∧
    lpNorm (h9InverseTraceSquare N K) 2
        (h9InverseWishartDenominatorLaw N K) ≤
      h9InverseWishartMomentConstant * (N : ℝ)

/--
**CONDITIONAL deterministic/null-set adapter for the `B_epsilon` repair.**

This package contains no moment estimate.  It records the almost-everywhere
full-rank fact, convergence of the regularized inverse, and the two spectral
dominations used by dominated convergence.  It is deliberately separate from
`H9InverseWishartDenominatorPackage`, which remains the only scientific
inverse-moment input.
-/
structure H9InverseWishartRegularizationAdapter (N K : ℕ) : Prop where
  fullRank_ae :
    ∀ᵐ B ∂h9InverseWishartDenominatorLaw N K,
      Matrix.det (realWishartGram B) ≠ 0
  scaledInverse_tendsto_ae :
    ∀ᵐ B ∂h9InverseWishartDenominatorLaw N K,
      Filter.Tendsto
        (fun j : ℕ ↦ h9RegularizedScaledInverseWishart N K j B)
        Filter.atTop (nhds (h9ScaledInverseWishart N K B))
  traceSquare_domination_ae :
    ∀ᵐ B ∂h9InverseWishartDenominatorLaw N K, ∀ j : ℕ,
      0 ≤ h9RegularizedInverseTraceSquare N K j B ∧
        h9RegularizedInverseTraceSquare N K j B ≤
          h9InverseTraceSquare N K B
  centeredTrace_domination_ae :
    ∀ᵐ B ∂h9InverseWishartDenominatorLaw N K, ∀ j : ℕ,
      |h9RegularizedCenteredInverseTrace N K j B| ≤
        |h9CenteredInverseTrace N K B| + 2 * (N : ℝ)

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
