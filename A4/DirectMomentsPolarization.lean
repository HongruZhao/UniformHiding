import A4.DirectMomentsMomentPolynomial
import Mathlib.Algebra.MvPolynomial.Coeff
import Mathlib.Algebra.MvPolynomial.Funext

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace MatsumotoPaper

/-- The finite polynomial of a degree-`n` moment of a linear combination.
Its variables index observables and its coefficients are genuine mixed
moments; no measure on a polynomial space is introduced. -/
def observableMomentPolynomial {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {n m : ℕ} (x : Fin m → Ω → ℝ) : MvPolynomial (Fin m) ℝ :=
  ∑ c : Fin n → Fin m,
    MvPolynomial.C (∫ ω, ∏ i : Fin n, x (c i) ω ∂μ) *
      ∏ i : Fin n, MvPolynomial.X (c i)

theorem eval_observableMomentPolynomial {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {n m : ℕ} (x : Fin m → Ω → ℝ)
    (hint : ∀ c : Fin n → Fin m, Integrable (fun ω ↦ ∏ i, x (c i) ω) μ)
    (t : Fin m → ℝ) :
    MvPolynomial.eval t (observableMomentPolynomial (n := n) μ x) =
      ∫ ω, (∑ j : Fin m, t j * x j ω) ^ n ∂μ := by
  classical
  have heval : MvPolynomial.eval t (observableMomentPolynomial (n := n) μ x) =
      ∑ c : Fin n → Fin m, (∏ i : Fin n, t (c i)) *
        (∫ ω, ∏ i : Fin n, x (c i) ω ∂μ) := by
    simp only [observableMomentPolynomial, map_sum, map_mul, map_prod,
      MvPolynomial.eval_C, MvPolynomial.eval_X]
    apply Finset.sum_congr rfl
    intro c _
    ring
  rw [heval]
  calc
    _ = ∫ ω, ∑ c : Fin n → Fin m,
        (∏ i : Fin n, t (c i)) * (∏ i : Fin n, x (c i) ω) ∂μ := by
      rw [integral_finsetSum]
      · simp only [integral_const_mul]
      · intro c _
        exact (hint c).const_mul _
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω ↦ by
        change (∑ c : Fin n → Fin m,
          (∏ i : Fin n, t (c i)) * ∏ i : Fin n, x (c i) ω) =
          (∑ j : Fin m, t j * x j ω) ^ n
        rw [Fintype.sum_pow]
        simp_rw [Finset.prod_mul_distrib]

theorem coeff_observableMomentPolynomial {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {n m : ℕ} (x : Fin m → Ω → ℝ)
    (hint : ∀ c : Fin n → Fin m, Integrable (fun ω ↦ ∏ i, x (c i) ω) μ)
    (e : Fin m →₀ ℕ) :
    MvPolynomial.coeff e (observableMomentPolynomial (n := n) μ x) =
      ∫ ω, MvPolynomial.coeff e
        ((∑ j : Fin m, x j ω • MvPolynomial.X j : MvPolynomial (Fin m) ℝ) ^ n) ∂μ := by
  classical
  have hexp (ω : Ω) :
      (∑ j : Fin m, x j ω • MvPolynomial.X j : MvPolynomial (Fin m) ℝ) ^ n =
      ∑ c : Fin n → Fin m,
        MvPolynomial.C (∏ i : Fin n, x (c i) ω) *
          ∏ i : Fin n, MvPolynomial.X (c i) := by
    rw [Fintype.sum_pow]
    apply Finset.sum_congr rfl
    intro c _
    simp only [MvPolynomial.smul_eq_C_mul, Finset.prod_mul_distrib, map_prod]
  simp only [observableMomentPolynomial, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_C_mul]
  simp_rw [hexp, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro c _
    simp_rw [mul_comm (∏ i : Fin n, x (c i) _), integral_const_mul]
    ring
  · intro c _
    simpa only [mul_comm] using
      (hint c).const_mul (MvPolynomial.coeff e (∏ i : Fin n, MvPolynomial.X (c i)))

/-- The square-free top-degree exponent. -/
def allOnesExponent (n : ℕ) : Fin n →₀ ℕ :=
  Finsupp.onFinset Finset.univ (fun _ ↦ 1) (by simp)

@[simp] theorem allOnesExponent_apply {n : ℕ} (i : Fin n) :
    allOnesExponent n i = 1 := rfl

theorem allOnesExponent_sum (n : ℕ) :
    (allOnesExponent n).sum (fun _ m ↦ m) = n := by
  rw [Finsupp.sum_of_support_subset _ (Finset.subset_univ _) _ (by simp)]
  simp

theorem allOnesExponent_multinomial (n : ℕ) :
    (allOnesExponent n).multinomial = n.factorial := by
  rw [Finsupp.multinomial_eq_of_support_subset (Finset.subset_univ _)]
  simp [Nat.multinomial]

/-- Extracting the coefficient of `X₀⋯Xₙ₋₁` recovers `n!` times the mixed
moment. This is all-degree polarization through the multinomial coefficient. -/
theorem coeff_allOnes_observableMomentPolynomial {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {n : ℕ} (x : Fin n → Ω → ℝ)
    (hint : ∀ c : Fin n → Fin n, Integrable (fun ω ↦ ∏ i, x (c i) ω) μ) :
    MvPolynomial.coeff (allOnesExponent n) (observableMomentPolynomial (n := n) μ x) =
      (n.factorial : ℝ) * (∫ ω, ∏ i : Fin n, x i ω ∂μ) := by
  rw [coeff_observableMomentPolynomial μ x hint]
  simp_rw [MvPolynomial.coeff_linearCombination_X_pow_of_fintype,
    allOnesExponent_sum, if_true, allOnesExponent_multinomial]
  have hp (ω : Ω) :
      (allOnesExponent n).prod (fun r m ↦ x r ω ^ m) = ∏ i : Fin n, x i ω := by
    rw [Finsupp.prod_of_support_subset _ (Finset.subset_univ _) _ (by simp)]
    simp
  simp_rw [hp]
  exact integral_const_mul _ _

/-- Equality of all degree-`n` moments of linear combinations implies equality
of every mixed degree-`n` moment. The integrability and equality hypotheses are
ordinary explicit hypotheses, with no distribution-specific assumption. -/
theorem mixed_moment_eq_of_linear_combination_moments
    {Ω Ψ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ψ]
    (μ : Measure Ω) (ν : Measure Ψ) {n : ℕ}
    (x : Fin n → Ω → ℝ) (y : Fin n → Ψ → ℝ)
    (hx : ∀ c : Fin n → Fin n, Integrable (fun ω ↦ ∏ i, x (c i) ω) μ)
    (hy : ∀ c : Fin n → Fin n, Integrable (fun ω ↦ ∏ i, y (c i) ω) ν)
    (h : ∀ t : Fin n → ℝ,
      (∫ ω, (∑ j : Fin n, t j * x j ω) ^ n ∂μ) =
        ∫ ω, (∑ j : Fin n, t j * y j ω) ^ n ∂ν) :
    (∫ ω, ∏ i : Fin n, x i ω ∂μ) = ∫ ω, ∏ i : Fin n, y i ω ∂ν := by
  have hpoly : observableMomentPolynomial (n := n) μ x =
      observableMomentPolynomial (n := n) ν y := by
    apply MvPolynomial.funext
    intro t
    rw [eval_observableMomentPolynomial μ x hx,
      eval_observableMomentPolynomial ν y hy]
    exact h t
  have hc := congrArg (MvPolynomial.coeff (allOnesExponent n)) hpoly
  rw [coeff_allOnes_observableMomentPolynomial μ x hx,
    coeff_allOnes_observableMomentPolynomial ν y hy] at hc
  exact mul_left_cancel₀ (by positivity : (n.factorial : ℝ) ≠ 0) hc

end MatsumotoPaper
