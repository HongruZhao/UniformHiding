import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.BetaPrimeTransportConditional
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.InverseWishartEntryProductIntegrability

/-!
# CONDITIONAL source inputs for U08

These contracts are deliberately below H8 and H10.  They split the literal
Gaussian beta-prime source into a numerator innovation and a denominator-only
drift.  No field is an H8/H10 conclusion, and no declaration is an axiom.

The qualitative inverse-entry integrability needed to justify all products
through degree four is proved in `InverseWishartEntryProductIntegrability`.
What remains conditional here is the Gaussian Poincare/log-Sobolev estimate
and the dense inverse-Wishart trace fluctuation bounds.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08

noncomputable section

open LogdetLean.GramHafnian.Wishart

/-- Literal sample space underlying the beta-prime trace law. -/
abbrev BetaPrimeGaussianSource (N K : ℕ) :=
  Matrix (Fin (N + 1)) (Fin N) ℝ ×
    Matrix (Fin (K - N)) (Fin N) ℝ

/-- The scaled inverse-Wishart denominator `C₀ = c B₀⁻¹`. -/
def scaledInverseWishartDenominator (N K : ℕ)
    (source : BetaPrimeGaussianSource N K) :
    Matrix (Fin N) (Fin N) ℝ :=
  concreteCOEExponent N K • (realWishartGram source.2)⁻¹

/-- `tr C₀` as a function of the literal Gaussian source. -/
def denominatorTraceOneSource (N K : ℕ)
    (source : BetaPrimeGaussianSource N K) : ℝ :=
  Matrix.trace (scaledInverseWishartDenominator N K source)

/-- `tr(C₀²)` as a function of the literal Gaussian source. -/
def denominatorTraceTwoSource (N K : ℕ)
    (source : BetaPrimeGaussianSource N K) : ℝ :=
  Matrix.trace ((scaledInverseWishartDenominator N K source) ^ 2)

/-- Pullback of the exposed first beta-prime trace to its Gaussian source. -/
def betaPrimeTraceOneSource (N K : ℕ)
    (source : BetaPrimeGaussianSource N K) : ℝ :=
  betaPrimeYTraceOne N K (realBetaPrimeTracePowerVector 4 N K source)

/-- Pullback of the exposed second beta-prime trace to its Gaussian source. -/
def betaPrimeTraceTwoSource (N K : ℕ)
    (source : BetaPrimeGaussianSource N K) : ℝ :=
  betaPrimeYTraceTwo N K (realBetaPrimeTracePowerVector 4 N K source)

/-- Exact conditional mean `E[T | C₀] = (N+1) tr C₀`. -/
def traceOneConditionalMeanSource (N K : ℕ)
    (source : BetaPrimeGaussianSource N K) : ℝ :=
  ((N + 1 : ℕ) : ℝ) * denominatorTraceOneSource N K source

/-- Exact Wick conditional mean
`E[S | C₀] = n(n+1) tr(C₀²) + n (tr C₀)²`, `n=N+1`. -/
def traceTwoConditionalMeanSource (N K : ℕ)
    (source : BetaPrimeGaussianSource N K) : ℝ :=
  ((N + 1 : ℕ) : ℝ) * ((N + 2 : ℕ) : ℝ) *
      denominatorTraceTwoSource N K source +
    ((N + 1 : ℕ) : ℝ) * denominatorTraceOneSource N K source ^ 2

/-- Numerator Gaussian chaos in the first trace. -/
def traceOneInnovationSource (N K : ℕ)
    (source : BetaPrimeGaussianSource N K) : ℝ :=
  betaPrimeTraceOneSource N K source -
    traceOneConditionalMeanSource N K source

/-- Denominator drift in the first trace, centered at its exact total mean. -/
def traceOneDenominatorDriftSource (N K : ℕ)
    (source : BetaPrimeGaussianSource N K) : ℝ :=
  traceOneConditionalMeanSource N K source -
    (N : ℝ) * ((N : ℝ) + 1)

/-- Numerator Gaussian chaos in the second trace. -/
def traceTwoInnovationSource (N K : ℕ)
    (source : BetaPrimeGaussianSource N K) : ℝ :=
  betaPrimeTraceTwoSource N K source -
    traceTwoConditionalMeanSource N K source

/-- Denominator-only conditional-mean drift in the second trace. -/
def traceTwoDenominatorDriftSource (N K : ℕ)
    (source : BetaPrimeGaussianSource N K) : ℝ :=
  traceTwoConditionalMeanSource N K source -
    ∫ z, traceTwoConditionalMeanSource N K z
      ∂(realBetaPrimeGaussianSourceLaw N K)

/-- **CONDITIONAL H8 source inputs.**  The two fields are the separate
`2^10 N` numerator-chaos and `2^13 N` denominator-drift estimates from the
human proof. -/
structure H8SourceMomentInputs (N K : ℕ) : Prop where
  innovation_memLp_four :
    MemLp (traceOneInnovationSource N K) 4
      (realBetaPrimeGaussianSourceLaw N K)
  denominator_drift_memLp_four :
    MemLp (traceOneDenominatorDriftSource N K) 4
      (realBetaPrimeGaussianSourceLaw N K)
  innovation_lpNorm_four_le : 16 * N ≤ K →
    lpNorm (traceOneInnovationSource N K) 4
        (realBetaPrimeGaussianSourceLaw N K) ≤
      (2 : ℝ) ^ 10 * (N : ℝ)
  denominator_drift_lpNorm_four_le : 16 * N ≤ K →
    lpNorm (traceOneDenominatorDriftSource N K) 4
        (realBetaPrimeGaussianSourceLaw N K) ≤
      (2 : ℝ) ^ 13 * (N : ℝ)

/-- Global H8 source contract at the exact qualitative threshold. -/
abbrev H8SourceMomentContract : Prop :=
  ∀ {N K : ℕ}, 1 ≤ N → 2 * N + 8 ≤ K → H8SourceMomentInputs N K

/-- **CONDITIONAL H10 source inputs.**  Conditional centering is kept as a
separate Wick identity; the two bounds are the exact `2^23 N²` innovation
and `2^28 N²` denominator estimates from the human proof. -/
structure H10SourceMomentInputs (N K : ℕ) : Prop where
  conditional_mean_integral_eq :
    (∫ source, betaPrimeTraceTwoSource N K source
        ∂(realBetaPrimeGaussianSourceLaw N K)) =
      ∫ source, traceTwoConditionalMeanSource N K source
        ∂(realBetaPrimeGaussianSourceLaw N K)
  innovation_memLp_two :
    MemLp (traceTwoInnovationSource N K) 2
      (realBetaPrimeGaussianSourceLaw N K)
  denominator_drift_memLp_two :
    MemLp (traceTwoDenominatorDriftSource N K) 2
      (realBetaPrimeGaussianSourceLaw N K)
  innovation_lpNorm_two_le : 16 * N ≤ K →
    lpNorm (traceTwoInnovationSource N K) 2
        (realBetaPrimeGaussianSourceLaw N K) ≤
      (2 : ℝ) ^ 23 * (N : ℝ) ^ 2
  denominator_drift_lpNorm_two_le : 16 * N ≤ K →
    lpNorm (traceTwoDenominatorDriftSource N K) 2
        (realBetaPrimeGaussianSourceLaw N K) ≤
      (2 : ℝ) ^ 28 * (N : ℝ) ^ 2

/-- Global H10 source contract at the exact qualitative threshold. -/
abbrev H10SourceMomentContract : Prop :=
  ∀ {N K : ℕ}, 1 ≤ N → 2 * N + 8 ≤ K → H10SourceMomentInputs N K

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08
