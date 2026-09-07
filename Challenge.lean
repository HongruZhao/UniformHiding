import LogdetLean.GramHafnian.ShiftedAnticoncentration.Definitions
import LogdetLean.GramHafnian.SymmetricGaussianHafnian.FullMatrix
import LogdetLean.GramHafnian.LocalAnticoncentration.CoefficientPaperEndpoints

/-!
# Public specifications for the two headline results

These proposition-valued specifications have no assumed theorem or proof
placeholder. The observables and measures below are actual Gaussian models.
`ComplexGramHafnians.lean` supplies the proofs. See `docs/PAPER_COMPARISON.md`.
-/

open MeasureTheory Filter
open scoped BigOperators Nat ENNReal Topology
open LogdetLean.GramHafnian
open LogdetLean.GramHafnian.LocalAnticoncentration
open LogdetLean.GramHafnian.SymmetricGaussianHafnian

namespace ComplexGramHafnians
noncomputable section

/-- Theorem 2.1: normalization, shifted disk bound, and the finite coefficient. -/
structure Theorem21 (n k : ℕ) : Prop where
  rmsPositive : 0 < gramHafnianSigma k n
  exactSecondMoment :
    (∫ X, Complex.normSq (gramHafnianObservable n k X)
      ∂circularGaussianColumnMatrixMeasure n k) =
      (((2 * n - 1)‼ : ℕ) : ℝ) *
        ∏ q ∈ Finset.range n, ((k + 2 * q : ℕ) : ℝ)
  rmsSquared : gramHafnianSigma k n ^ 2 =
    (((2 * n - 1)‼ : ℕ) : ℝ) *
      ∏ q ∈ Finset.range n, ((k + 2 * q : ℕ) : ℝ)
  shiftedSmallBall : ∀ z : ℂ, ∀ epsilon : ℝ, 0 ≤ epsilon →
    (circularGaussianColumnMatrixMeasure n k).real
      {X | ‖gramHafnianObservable n k X - z‖ ≤
        epsilon * gramHafnianSigma k n} ≤
      min 1 (paperBkn k n * epsilon ^ 2)
  limitingCoefficientFormula : paperBn n =
    2 * Real.Gamma ((n : ℝ) + 1 / 2) /
      (Real.sqrt Real.pi * Real.Gamma (n : ℝ))
  coefficientProduct : paperBkn k n =
    paperBn n * ((k : ℝ) / ((k : ℝ) - 1)) *
      ∏ r ∈ Finset.Icc 2 n,
        (((k : ℝ) + 2 * (r : ℝ) - 2) /
          ((k : ℝ) - 4 * (r : ℝ) + 1))
  coefficientBound : paperBkn k n ≤ paperBn n * Real.exp
    ((3 * (n : ℝ) ^ 2 - 2) / (k : ℝ) +
      9 * (n : ℝ) ^ 3 /
        ((k : ℝ) * ((k : ℝ) - 4 * (n : ℝ) + 1)))
  coefficientLimit : Tendsto (fun j : ℕ ↦ paperBkn j n)
    atTop (nhds (paperBn n))
  logarithmicRemainder : 8 * n ≤ k → ∃ theta : ℝ,
    paperBkn k n = paperBn n *
      Real.exp (3 * (n : ℝ) ^ 2 / (k : ℝ) + theta) ∧
    |theta| ≤ 2 / (k : ℝ) + 94 * (n : ℝ) ^ 3 / (k : ℝ) ^ 2

/-- Theorem 2.3: the independent complex symmetric Gaussian ensemble.
The full matrix law has variance-one off-diagonal and variance-two diagonal
entries. Ordinary hafnians are invariant under diagonal changes. -/
structure Theorem23 (n : ℕ) : Prop where
  rmsPositive : 0 < sigma n
  exactSecondMoment :
    (∫ p, Complex.normSq (fullSymmetricHafnian p)
      ∂complexSymmetricGaussianFullMatrixLaw n) =
      (((2 * n - 1)‼ : ℕ) : ℝ)
  rmsSquared : sigma n ^ 2 = (((2 * n - 1)‼ : ℕ) : ℝ)
  shiftedSmallBall : ∀ z : ℂ, ∀ epsilon : ℝ, 0 ≤ epsilon →
    (complexSymmetricGaussianFullMatrixLaw n).real
      {p | ‖fullSymmetricHafnian p - z‖ ≤ epsilon * sigma n} ≤
      min 1 (paperBn n * epsilon ^ 2)
  coefficientFormula : paperBn n =
    2 * Real.Gamma ((n : ℝ) + 1 / 2) /
      (Real.sqrt Real.pi * Real.Gamma (n : ℝ))
  coefficientLimit : Tendsto (fun k : ℕ ↦ paperBkn k n)
    atTop (nhds (paperBn n))
  elementaryCoefficient : paperBn n ≤ 2 * Real.sqrt ((n : ℝ) / Real.pi)

end
end ComplexGramHafnians
