import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.BetaPrimeMomentInputsConditional
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.InverseWishartSecondEntryMomentConditional

/-!
# Low-level fourth-radial producer contracts

These definitions are shared by the Gaussian fourth-Wick producer and the
denominator-only inverse-Wishart proof.  Keeping them in this lower module
prevents the denominator Stein recursion from importing the full radial H14
closure (and, transitively, unrelated positive-trace endpoint machinery).
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08

noncomputable section

open LogdetLean.GramHafnian.Wishart

/-- The raw fourth-Wick polynomial for `T = tr(C GᵀG)`. -/
def h14TraceOneFourthWickPolynomial {p : ℕ} (rows : ℕ)
    (C : Matrix (Fin p) (Fin p) ℝ) : ℝ :=
  (rows : ℝ) ^ 4 * Matrix.trace C ^ 4 +
    12 * (rows : ℝ) ^ 3 * Matrix.trace C ^ 2 * Matrix.trace (C ^ 2) +
    12 * (rows : ℝ) ^ 2 * Matrix.trace (C ^ 2) ^ 2 +
    32 * (rows : ℝ) ^ 2 * Matrix.trace C * Matrix.trace (C ^ 3) +
    48 * (rows : ℝ) * Matrix.trace (C ^ 4)

/-- The raw second-Wick polynomial for `S = tr(C GᵀG C GᵀG)`. -/
def h14TraceTwoSquareWickPolynomial {p : ℕ} (rows : ℕ)
    (C : Matrix (Fin p) (Fin p) ℝ) : ℝ :=
  (rows : ℝ) ^ 2 * Matrix.trace C ^ 4 +
    (2 * (rows : ℝ) ^ 3 + 2 * (rows : ℝ) ^ 2 + 8 * (rows : ℝ)) *
      Matrix.trace C ^ 2 * Matrix.trace (C ^ 2) +
    ((rows : ℝ) ^ 4 + 2 * (rows : ℝ) ^ 3 +
        5 * (rows : ℝ) ^ 2 + 4 * (rows : ℝ)) *
      Matrix.trace (C ^ 2) ^ 2 +
    16 * (rows : ℝ) * ((rows : ℝ) + 1) *
      Matrix.trace C * Matrix.trace (C ^ 3) +
    (8 * (rows : ℝ) ^ 3 + 20 * (rows : ℝ) ^ 2 + 20 * (rows : ℝ)) *
      Matrix.trace (C ^ 4)

/-- The two finite Gaussian fourth-Wick contractions. -/
structure H14FiniteGaussianFourthWickFormula (N K : ℕ) : Prop where
  traceOne_fourth_fiber_eq :
    ∀ H : Matrix (Fin (K - N)) (Fin N) ℝ,
      (∫ G : Matrix (Fin (N + 1)) (Fin N) ℝ,
          betaPrimeTraceOneSource N K (G, H) ^ 4
          ∂standardRealGaussianMatrixMeasure (N + 1) N) =
        h14TraceOneFourthWickPolynomial (N + 1)
          (scaledInverseWishartMatrix N K H)
  traceTwo_square_fiber_eq :
    ∀ H : Matrix (Fin (K - N)) (Fin N) ℝ,
      (∫ G : Matrix (Fin (N + 1)) (Fin N) ℝ,
          betaPrimeTraceTwoSource N K (G, H) ^ 2
          ∂standardRealGaussianMatrixMeasure (N + 1) N) =
        h14TraceTwoSquareWickPolynomial (N + 1)
          (scaledInverseWishartMatrix N K H)

/-- Denominator-only quantitative fourth-trace polynomial contract. -/
structure H14DenominatorFourthTracePolynomialBounds (N K : ℕ) : Prop where
  traceOne_polynomial_integral_le : 16 * N ≤ K →
    (∫ H : Matrix (Fin (K - N)) (Fin N) ℝ,
        h14TraceOneFourthWickPolynomial (N + 1)
          (scaledInverseWishartMatrix N K H)
        ∂standardRealGaussianMatrixMeasure (K - N) N) ≤
      (2 : ℝ) ^ 16 * (N : ℝ) ^ 8
  traceTwo_polynomial_integral_le : 16 * N ≤ K →
    (∫ H : Matrix (Fin (K - N)) (Fin N) ℝ,
        h14TraceTwoSquareWickPolynomial (N + 1)
          (scaledInverseWishartMatrix N K H)
        ∂standardRealGaussianMatrixMeasure (K - N) N) ≤
      (2 : ℝ) ^ 16 * (N : ℝ) ^ 6

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08
