import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ClassicalMomentBoundsExternal

/-!
# H9: reduction to two source-level fourth-moment estimates

This module does not use
`betaPrimeYTraceOne_centered_three_momentPackage_external`, or any other
external moment declaration.  It splits the centered first trace at the
literal independent Gaussian source into

* the numerator-Wishart fluctuation conditional on the denominator; and
* the centered inverse-trace fluctuation of the denominator Wishart matrix.

Two genuinely lower-level `L^4` packages, each assigned half of the exposed
`2^40 N` budget, imply the exact original H9 proposition.  The remaining
scientific work is precisely to establish those two source packages.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.Wishart

/-- The literal independent Gaussian source used in the beta-prime model. -/
abbrev H9BetaPrimeGaussianSource (N K : ℕ) :=
  Matrix (Fin (N + 1)) (Fin N) ℝ ×
    Matrix (Fin (K - N)) (Fin N) ℝ

/-- Trace of the inverse denominator Wishart matrix. -/
def h9SourceInverseTrace (N K : ℕ)
    (p : H9BetaPrimeGaussianSource N K) : ℝ :=
  Matrix.trace ((realWishartGram p.2)⁻¹)

/-- Conditional numerator fluctuation in `Tr(c B₀⁻¹ A₀)`. -/
def h9SourceNumeratorFluctuation (N K : ℕ)
    (p : H9BetaPrimeGaussianSource N K) : ℝ :=
  concreteCOEExponent N K *
    (Matrix.trace (realMatrixBetaPrimeOfGaussianSource p) -
      ((N + 1 : ℕ) : ℝ) * h9SourceInverseTrace N K p)

/-- Denominator inverse-trace fluctuation in `Tr(c B₀⁻¹ A₀)`. -/
def h9SourceDenominatorFluctuation (N K : ℕ)
    (p : H9BetaPrimeGaussianSource N K) : ℝ :=
  ((N + 1 : ℕ) : ℝ) *
    (concreteCOEExponent N K * h9SourceInverseTrace N K p - (N : ℝ))

/-- The deterministic center, equal to the exact first-trace expectation. -/
def h9BetaPrimeTraceOneFixedCenter (N K : ℕ) (u : Fin 4 → ℝ) : ℝ :=
  betaPrimeYTraceOne N K u - (N : ℝ) * ((N : ℝ) + 1)

/-- The fixed-center observable is measurable before any moment input. -/
theorem measurable_h9BetaPrimeTraceOneFixedCenter (N K : ℕ) :
    Measurable (h9BetaPrimeTraceOneFixedCenter N K) := by
  unfold h9BetaPrimeTraceOneFixedCenter betaPrimeYTraceOne
  fun_prop

/-- Exact pointwise numerator/denominator decomposition before any estimate. -/
theorem h9BetaPrimeTraceOneFixedCenter_comp_source (N K : ℕ) :
    h9BetaPrimeTraceOneFixedCenter N K ∘
        realBetaPrimeTracePowerVector 4 N K =
      h9SourceNumeratorFluctuation N K +
        h9SourceDenominatorFluctuation N K := by
  funext p
  simp only [Function.comp_apply, h9BetaPrimeTraceOneFixedCenter,
    betaPrimeYTraceOne, realBetaPrimeTracePowerVector, Nat.zero_add, pow_one,
    h9SourceNumeratorFluctuation, h9SourceDenominatorFluctuation,
    h9SourceInverseTrace, realMatrixBetaPrimeOfGaussianSource, Pi.add_apply]
  push_cast
  ring

/-- Real `L^p` norms are preserved by the defining beta-prime pushforward. -/
theorem h9_lpNorm_source_map
    {N K : ℕ} {p : ENNReal} {g : (Fin 4 → ℝ) → ℝ}
    (hg : AEStronglyMeasurable g (betaPrimeTraceFourLaw N K)) :
    lpNorm g p (betaPrimeTraceFourLaw N K) =
      lpNorm (g ∘ realBetaPrimeTracePowerVector 4 N K) p
        (realBetaPrimeGaussianSourceLaw N K) := by
  let μ := realBetaPrimeGaussianSourceLaw N K
  let f := realBetaPrimeTracePowerVector 4 N K
  have hmap : Measure.map f μ = betaPrimeTraceFourLaw N K := by
    rfl
  have hgf : AEStronglyMeasurable g (Measure.map f μ) := by
    simpa only [hmap] using hg
  have hf : AEMeasurable f μ :=
    (measurable_realBetaPrimeTracePowerVector_external 4 N K).aemeasurable
  rw [← hmap, ← toReal_eLpNorm hgf,
    ← toReal_eLpNorm (hgf.comp_aemeasurable hf)]
  exact congrArg ENNReal.toReal (eLpNorm_map_measure hgf hf)

/-- Monotonicity of real `L^p` norms on a probability space. -/
theorem h9_lpNorm_le_of_exponent_le
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {p q : ENNReal} {f : Ω → ℝ}
    (hf : MemLp f q μ) (hpq : p ≤ q) :
    lpNorm f p μ ≤ lpNorm f q μ := by
  rw [← toReal_eLpNorm (hf.mono_exponent hpq).aestronglyMeasurable,
    ← toReal_eLpNorm hf.aestronglyMeasurable]
  exact ENNReal.toReal_mono hf.eLpNorm_ne_top
    (eLpNorm_le_eLpNorm_of_exponent_le hpq hf.aestronglyMeasurable)

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
