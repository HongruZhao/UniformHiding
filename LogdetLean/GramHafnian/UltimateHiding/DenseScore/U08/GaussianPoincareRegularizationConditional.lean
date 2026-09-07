import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.GaussianPoincareRegularization
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.DenseInverseWishartTraceConditional

/-!
# CONDITIONAL regularized Gaussian-Poincare inputs

These are fixed, non-endpoint contracts for the reviewer-approved route.
Every inverse is evaluated at `B_ε=B₀+εI`, so the Gaussian functions are
smooth.  Uniform estimates and almost-everywhere convergence imply the
unregularized innovation estimates by the axiom-free Fatou closure.
-/

open MeasureTheory Filter
open scoped MatrixOrder Topology

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08

noncomputable section

open LogdetLean.GramHafnian.Wishart

/-- Concrete ridge sequence `ε_m=1/(m+1)`. -/
def wishartRidge (m : ℕ) : ℝ := ((m : ℝ) + 1)⁻¹

theorem wishartRidge_pos (m : ℕ) : 0 < wishartRidge m := by
  simp only [wishartRidge]
  positivity

theorem wishartRidge_tendsto_zero :
    Tendsto wishartRidge atTop (𝓝 0) := by
  change Tendsto (fun m : ℕ ↦ ((m : ℝ) + 1)⁻¹) atTop (𝓝 0)
  simpa only [one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-- The reviewer-requested pointwise inverse domination along the concrete
ridge sequence. -/
theorem regularizedWishartGram_ridge_inv_le
    {k p : ℕ} (m : ℕ) (H : Matrix (Fin k) (Fin p) ℝ)
    (hdet : (realWishartGram H).det ≠ 0) :
    (regularizedWishartGram (wishartRidge m) H)⁻¹ ≤
      (realWishartGram H)⁻¹ :=
  regularizedWishartGram_inv_le H (wishartRidge_pos m).le hdet

/-- `C₀,ε = c(B₀+εI)⁻¹`. -/
def regularizedScaledInverseWishartDenominator
    (m N K : ℕ) (source : BetaPrimeGaussianSource N K) :
    Matrix (Fin N) (Fin N) ℝ :=
  concreteCOEExponent N K •
    (regularizedWishartGram (wishartRidge m) source.2)⁻¹

/-- Regularized first trace `Tε=tr(CεA₀)`. -/
def regularizedTraceOneSource
    (m N K : ℕ) (source : BetaPrimeGaussianSource N K) : ℝ :=
  Matrix.trace (regularizedScaledInverseWishartDenominator m N K source *
    realWishartGram source.1)

/-- Regularized conditional mean of `Tε`. -/
def regularizedTraceOneConditionalMeanSource
    (m N K : ℕ) (source : BetaPrimeGaussianSource N K) : ℝ :=
  ((N + 1 : ℕ) : ℝ) *
    Matrix.trace (regularizedScaledInverseWishartDenominator m N K source)

/-- Smooth regularized first-trace numerator innovation. -/
def regularizedTraceOneInnovationSource
    (m N K : ℕ) (source : BetaPrimeGaussianSource N K) : ℝ :=
  regularizedTraceOneSource m N K source -
    regularizedTraceOneConditionalMeanSource m N K source

/-- Regularized second trace `Sε=tr(CεA₀CεA₀)`. -/
def regularizedTraceTwoSource
    (m N K : ℕ) (source : BetaPrimeGaussianSource N K) : ℝ :=
  let C := regularizedScaledInverseWishartDenominator m N K source
  let A := realWishartGram source.1
  Matrix.trace (C * A * C * A)

/-- Wick conditional mean of the regularized second trace. -/
def regularizedTraceTwoConditionalMeanSource
    (m N K : ℕ) (source : BetaPrimeGaussianSource N K) : ℝ :=
  let C := regularizedScaledInverseWishartDenominator m N K source
  ((N + 1 : ℕ) : ℝ) * ((N + 2 : ℕ) : ℝ) * Matrix.trace (C ^ 2) +
    ((N + 1 : ℕ) : ℝ) * Matrix.trace C ^ 2

/-- Smooth regularized second-trace numerator innovation. -/
def regularizedTraceTwoInnovationSource
    (m N K : ℕ) (source : BetaPrimeGaussianSource N K) : ℝ :=
  regularizedTraceTwoSource m N K source -
    regularizedTraceTwoConditionalMeanSource m N K source

/-! ## Axiom-free removal of the ridge on the full-rank event -/

@[simp]
theorem betaPrimeTraceOneSource_eq_scaledInverseWishart_trace
    (N K : ℕ) (source : BetaPrimeGaussianSource N K) :
    betaPrimeTraceOneSource N K source =
      Matrix.trace (scaledInverseWishartDenominator N K source *
        realWishartGram source.1) := by
  simp [betaPrimeTraceOneSource, betaPrimeYTraceOne,
    realBetaPrimeTracePowerVector, realMatrixBetaPrimeOfGaussianSource,
    scaledInverseWishartDenominator, Matrix.smul_mul, Matrix.trace_smul]

@[simp]
theorem betaPrimeTraceTwoSource_eq_scaledInverseWishart_trace
    (N K : ℕ) (source : BetaPrimeGaussianSource N K) :
    betaPrimeTraceTwoSource N K source =
      Matrix.trace (scaledInverseWishartDenominator N K source *
        realWishartGram source.1 *
        scaledInverseWishartDenominator N K source *
        realWishartGram source.1) := by
  simp [betaPrimeTraceTwoSource, betaPrimeYTraceTwo,
    realBetaPrimeTracePowerVector, realMatrixBetaPrimeOfGaussianSource,
    scaledInverseWishartDenominator, pow_two, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.trace_smul, smul_smul, Matrix.mul_assoc] <;>
    ring

theorem tendsto_regularizedScaledInverseWishartDenominator
    {N K : ℕ} (source : BetaPrimeGaussianSource N K)
    (hdet : (realWishartGram source.2).det ≠ 0) :
    Tendsto
      (fun m ↦ regularizedScaledInverseWishartDenominator m N K source)
      atTop (𝓝 (scaledInverseWishartDenominator N K source)) := by
  have hinv := tendsto_regularizedWishartGram_inv source.2 hdet
    wishartRidge_tendsto_zero
  have hscale : Continuous
      (fun M : Matrix (Fin N) (Fin N) ℝ ↦
        concreteCOEExponent N K • M) := by
    fun_prop
  simpa only [regularizedScaledInverseWishartDenominator,
    scaledInverseWishartDenominator, Function.comp_def] using
      hscale.continuousAt.tendsto.comp hinv

theorem tendsto_regularizedTraceOneInnovationSource
    {N K : ℕ} (source : BetaPrimeGaussianSource N K)
    (hdet : (realWishartGram source.2).det ≠ 0) :
    Tendsto (fun m ↦ regularizedTraceOneInnovationSource m N K source)
      atTop (𝓝 (traceOneInnovationSource N K source)) := by
  have hC := tendsto_regularizedScaledInverseWishartDenominator source hdet
  let A := realWishartGram source.1
  have hvalueMap : Continuous
      (fun C : Matrix (Fin N) (Fin N) ℝ ↦ Matrix.trace (C * A)) := by
    fun_prop
  have hmeanMap : Continuous
      (fun C : Matrix (Fin N) (Fin N) ℝ ↦
        ((N + 1 : ℕ) : ℝ) * Matrix.trace C) := by
    fun_prop
  have hvalue := hvalueMap.continuousAt.tendsto.comp hC
  have hmean := hmeanMap.continuousAt.tendsto.comp hC
  simpa [regularizedTraceOneInnovationSource, regularizedTraceOneSource,
    regularizedTraceOneConditionalMeanSource, traceOneInnovationSource,
    traceOneConditionalMeanSource, denominatorTraceOneSource, A] using
      hvalue.sub hmean

theorem tendsto_regularizedTraceTwoInnovationSource
    {N K : ℕ} (source : BetaPrimeGaussianSource N K)
    (hdet : (realWishartGram source.2).det ≠ 0) :
    Tendsto (fun m ↦ regularizedTraceTwoInnovationSource m N K source)
      atTop (𝓝 (traceTwoInnovationSource N K source)) := by
  have hC := tendsto_regularizedScaledInverseWishartDenominator source hdet
  let A := realWishartGram source.1
  have hvalueMap : Continuous
      (fun C : Matrix (Fin N) (Fin N) ℝ ↦
        Matrix.trace (C * A * C * A)) := by
    fun_prop
  have hmeanMap : Continuous
      (fun C : Matrix (Fin N) (Fin N) ℝ ↦
        ((N + 1 : ℕ) : ℝ) * ((N + 2 : ℕ) : ℝ) *
            Matrix.trace (C ^ 2) +
          ((N + 1 : ℕ) : ℝ) * Matrix.trace C ^ 2) := by
    fun_prop
  have hvalue := hvalueMap.continuousAt.tendsto.comp hC
  have hmean := hmeanMap.continuousAt.tendsto.comp hC
  simpa [regularizedTraceTwoInnovationSource, regularizedTraceTwoSource,
    regularizedTraceTwoConditionalMeanSource, traceTwoInnovationSource,
    traceTwoConditionalMeanSource, denominatorTraceOneSource,
    denominatorTraceTwoSource, A] using hvalue.sub hmean

theorem ae_tendsto_regularizedTraceOneInnovationSource
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K) :
    ∀ᵐ source ∂(realBetaPrimeGaussianSourceLaw N K),
      Tendsto (fun m ↦ regularizedTraceOneInnovationSource m N K source)
        atTop (𝓝 (traceOneInnovationSource N K source)) := by
  have hfull := ae_isUnit_det_betaPrimeDenominatorWishartGram
    (N := N) (K := K) (by omega)
  filter_upwards [hfull] with source hsource
  exact tendsto_regularizedTraceOneInnovationSource source
    (isUnit_iff_ne_zero.mp hsource)

theorem ae_tendsto_regularizedTraceTwoInnovationSource
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K) :
    ∀ᵐ source ∂(realBetaPrimeGaussianSourceLaw N K),
      Tendsto (fun m ↦ regularizedTraceTwoInnovationSource m N K source)
        atTop (𝓝 (traceTwoInnovationSource N K source)) := by
  have hfull := ae_isUnit_det_betaPrimeDenominatorWishartGram
    (N := N) (K := K) (by omega)
  filter_upwards [hfull] with source hsource
  exact tendsto_regularizedTraceTwoInnovationSource source
    (isUnit_iff_ne_zero.mp hsource)

/-- **CONDITIONAL regularized H8 numerator input.**  The qualitative uniform
bound is supplied by order-four inverse moments; the displayed dense bound is
the regularized Gaussian-chaos estimate. -/
structure H8RegularizedGaussianPoincareInputs (N K : ℕ) : Prop where
  memLp_four : ∀ m, MemLp (regularizedTraceOneInnovationSource m N K) 4
    (realBetaPrimeGaussianSourceLaw N K)
  qualitative_uniform : ∃ C : ℝ, 0 ≤ C ∧ ∀ m,
    lpNorm (regularizedTraceOneInnovationSource m N K) 4
      (realBetaPrimeGaussianSourceLaw N K) ≤ C
  dense_uniform : 16 * N ≤ K → ∀ m,
    lpNorm (regularizedTraceOneInnovationSource m N K) 4
      (realBetaPrimeGaussianSourceLaw N K) ≤ (2 : ℝ) ^ 10 * (N : ℝ)

/-- Global form of the regularized H8 Gaussian-Poincare contract. -/
abbrev H8RegularizedGaussianPoincareContract : Prop :=
  ∀ {N K : ℕ}, 1 ≤ N → 2 * N + 8 ≤ K →
    H8RegularizedGaussianPoincareInputs N K

/-- Fatou removes the ridge and discharges the H8 numerator contract. -/
theorem H8GaussianInnovationInputs.of_regularized
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K)
    (H : H8RegularizedGaussianPoincareInputs N K) :
    H8GaussianInnovationInputs N K := by
  obtain ⟨C, hC, huniform⟩ := H.qualitative_uniform
  have hqual := memLp_and_lpNorm_le_of_ae_tendsto_uniform hC H.memLp_four
    huniform (ae_tendsto_regularizedTraceOneInnovationSource hgap)
  refine
    { memLp_four := hqual.1
      lpNorm_four_le := ?_ }
  intro hdense
  exact (memLp_and_lpNorm_le_of_ae_tendsto_uniform
    (by positivity : 0 ≤ (2 : ℝ) ^ 10 * (N : ℝ)) H.memLp_four
    (H.dense_uniform hdense)
    (ae_tendsto_regularizedTraceOneInnovationSource hgap)).2

/-- **CONDITIONAL regularized H10 numerator input.** -/
structure H10RegularizedGaussianPoincareInputs (N K : ℕ) : Prop where
  conditional_mean_integral_eq :
    (∫ source, betaPrimeTraceTwoSource N K source
      ∂(realBetaPrimeGaussianSourceLaw N K)) =
      ∫ source, traceTwoConditionalMeanSource N K source
        ∂(realBetaPrimeGaussianSourceLaw N K)
  memLp_two : ∀ m, MemLp (regularizedTraceTwoInnovationSource m N K) 2
    (realBetaPrimeGaussianSourceLaw N K)
  qualitative_uniform : ∃ C : ℝ, 0 ≤ C ∧ ∀ m,
    lpNorm (regularizedTraceTwoInnovationSource m N K) 2
      (realBetaPrimeGaussianSourceLaw N K) ≤ C
  dense_uniform : 16 * N ≤ K → ∀ m,
    lpNorm (regularizedTraceTwoInnovationSource m N K) 2
      (realBetaPrimeGaussianSourceLaw N K) ≤
        (2 : ℝ) ^ 23 * (N : ℝ) ^ 2

/-- Global form of the regularized H10 Gaussian-Poincare contract. -/
abbrev H10RegularizedGaussianPoincareContract : Prop :=
  ∀ {N K : ℕ}, 1 ≤ N → 2 * N + 8 ≤ K →
    H10RegularizedGaussianPoincareInputs N K

/-- Fatou removes the ridge and discharges the H10 numerator contract. -/
theorem H10GaussianInnovationInputs.of_regularized
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K)
    (H : H10RegularizedGaussianPoincareInputs N K) :
    H10GaussianInnovationInputs N K := by
  obtain ⟨C, hC, huniform⟩ := H.qualitative_uniform
  have hqual := memLp_and_lpNorm_le_of_ae_tendsto_uniform hC H.memLp_two
    huniform (ae_tendsto_regularizedTraceTwoInnovationSource hgap)
  refine
    { conditional_mean_integral_eq := H.conditional_mean_integral_eq
      memLp_two := hqual.1
      lpNorm_two_le := ?_ }
  intro hdense
  exact (memLp_and_lpNorm_le_of_ae_tendsto_uniform
    (by positivity : 0 ≤ (2 : ℝ) ^ 23 * (N : ℝ) ^ 2) H.memLp_two
    (H.dense_uniform hdense)
    (ae_tendsto_regularizedTraceTwoInnovationSource hgap)).2

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08
