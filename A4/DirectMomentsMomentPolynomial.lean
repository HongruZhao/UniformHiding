import A4.DirectMomentsDeterminantRecursion
import Mathlib.Algebra.Polynomial.Roots

open MeasureTheory Matrix
open scoped BigOperators

noncomputable section

namespace MatsumotoPaper

/-- The all-degree directional moment polynomial in the real shape parameter,
constructed from the already proved determinant recursion. -/
def directionalMomentPolynomial {d : ℕ} (theta sigma : RealMatrix d) : ℕ → Polynomial ℝ
  | 0 => 1
  | n + 1 =>
    -(∑ k ∈ Finset.range (n + 1),
      (Polynomial.X * Polynomial.C (n.choose k : ℝ) +
        Polynomial.C (n.choose (k + 1) : ℝ)) *
      Polynomial.C (iteratedDeriv (k + 1)
        (fun t : ℝ ↦ (directionDetPolynomial theta sigma).eval t) 0) *
      directionalMomentPolynomial theta sigma (n - k))
termination_by n => n
decreasing_by omega

/-- The exact scalar moment in degree `n` has degree at most `n` in the shape.
The determinant derivatives are real coefficients and do not depend on the shape. -/
theorem natDegree_directionalMomentPolynomial_le {d : ℕ}
    (theta sigma : RealMatrix d) (n : ℕ) :
    (directionalMomentPolynomial theta sigma n).natDegree ≤ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [directionalMomentPolynomial]
    | succ n =>
      rw [directionalMomentPolynomial, Polynomial.natDegree_neg]
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro k hk
      have hlinear :
          (Polynomial.X * Polynomial.C (n.choose k : ℝ) +
            Polynomial.C (n.choose (k + 1) : ℝ)).natDegree ≤ 1 := by
        apply Polynomial.natDegree_add_le_of_degree_le
        · simpa using Polynomial.natDegree_mul_C_le Polynomial.X (n.choose k : ℝ)
        · simp
      have hscalar :
          ((Polynomial.X * Polynomial.C (n.choose k : ℝ) +
            Polynomial.C (n.choose (k + 1) : ℝ)) *
            Polynomial.C (iteratedDeriv (k + 1)
              (fun t : ℝ ↦ (directionDetPolynomial theta sigma).eval t) 0)).natDegree ≤ 1 :=
        (Polynomial.natDegree_mul_C_le _ _).trans hlinear
      have h := Polynomial.natDegree_mul_le_of_le hscalar (ih (n - k) (by omega))
      exact h.trans (by omega)

/-- `n+1` distinct shape values determine any proposed degree-`n` moment
polynomial. This is an algebraic interpolation theorem, with the comparison
identities kept explicit. -/
theorem directionalMomentPolynomial_eq_of_samples {d n : ℕ}
    (theta sigma : RealMatrix d) (candidate : Polynomial ℝ)
    (sample : Fin (n + 1) → ℝ) (hinj : Function.Injective sample)
    (hdegree : candidate.natDegree ≤ n)
    (hsample : ∀ i,
      (directionalMomentPolynomial theta sigma n).eval (sample i) =
        candidate.eval (sample i)) :
    directionalMomentPolynomial theta sigma n = candidate := by
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq _ _ hinj hsample
  simpa using Nat.lt_succ_of_le
    (max_le (natDegree_directionalMomentPolynomial_le theta sigma n) hdegree)

/-- Every direct directional moment is the evaluation of one real polynomial
in the shape, in every degree. The only probabilistic hypothesis is the
original exact `W_d` Laplace characterization. -/
theorem W_d.integral_traceObservable_pow_eq_eval_momentPolynomial
    {d : ℕ} {beta : ℝ} {sigma : SymPosDef d} (W : W_d d beta sigma)
    (theta : Sym d) (n : ℕ) :
    (∫ w, traceObservable theta w ^ n ∂W.toMeasure) =
      (directionalMomentPolynomial theta.1 sigma.1 n).eval beta := by
  letI : IsProbabilityMeasure W.toMeasure := W.probability
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [directionalMomentPolynomial]
    | succ n =>
      rw [W.directional_moment_recurrence theta n, directionalMomentPolynomial]
      simp only [Polynomial.eval_neg, Polynomial.eval_finsetSum, Polynomial.eval_mul,
        Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      rw [ih (n - k) (by omega)]

end MatsumotoPaper
