import LogdetLean.WishartSequentialKernel
import LogdetLean.WishartComplexTransform
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Tactic

/-!
# Real-axis identification of the actual Wishart transform

`WishartSequentialKernel` derives the real moment-generating transform of the
paper's row-based statistic `M_R` directly from the standard Gaussian product
measure.  `WishartComplexTransform` records the branch-safe finite complex
Gamma product used in Zhao, arXiv:2608.00565v1, Lemma 5.4 and equation (5.20).
This file proves that the two products agree on their common real domain.

The statement is deliberately an equality of transforms, not an equality of
chosen logarithms.  Consequently no principal-log or hidden `2 * pi * I`
assumption enters the certificate.
-/

namespace LogdetLean

noncomputable section

open Complex MeasureTheory
open ProbabilityTheory Set
open scoped BigOperators

/-- Positivity of one real diagonal factor on its natural Mellin--Laplace
domain.  This small certificate is also what turns the exact integral formula
into an exponential-integrability theorem: a nonintegrable Bochner integral
would be zero, whereas the displayed transform is strictly positive. -/
theorem wishartDiagonalStageTransform_pos
    {m n : ℕ} (hnm : n < m) {t c : ℝ}
    (ht : 0 < (((m - n : ℕ) : ℝ) / 2) + t)
    (hrate : 0 < (1 / 2 : ℝ) + c) :
    0 < wishartDiagonalStageTransform m n t c := by
  have hshape : 0 < (((m - n : ℕ) : ℝ) / 2) := by
    have : 0 < m - n := Nat.sub_pos_of_lt hnm
    positivity
  unfold wishartDiagonalStageTransform
  exact mul_pos
    (div_pos (Real.Gamma_pos_of_pos ht)
      (Real.Gamma_pos_of_pos hshape))
    (div_pos (Real.rpow_pos_of_pos (by norm_num) _)
      (Real.rpow_pos_of_pos hrate _))

/-- The diagonal product obtained from the Gaussian integral is exactly the
branch-safe complex Gamma product after embedding a permitted real argument
into `ℂ`.

This is the real-axis compatibility step in the proof of Zhao,
arXiv:2608.00565v1, Lemma 5.4.  The individual factor identity is proved from
the ordinary Gamma integral in `WishartComplexTransform`; this theorem only
assembles the finite product. -/
theorem ofReal_wishartDiagonalProduct_eq_complexWishartCorrelationTransform
    {m p : ℕ} (hm : 0 < m) (hp : p ≤ m)
    (R : CorrelationMatrix p) {t : ℝ}
    (ht : ∀ n < p, 0 < (((m - n : ℕ) : ℝ) / 2) + t)
    (hrate : ∀ n < p,
      0 < (1 / 2 : ℝ) + wishartSpectralTiltCoefficient m R t n) :
    ((∏ n ∈ Finset.range p,
        wishartDiagonalStageTransform m n t
          (wishartSpectralTiltCoefficient m R t n) : ℝ) : ℂ) =
      complexWishartCorrelationTransform R m (t : ℂ) := by
  rw [← Fin.prod_univ_eq_prod_range]
  unfold complexWishartCorrelationTransform
  push_cast
  apply Finset.prod_congr rfl
  intro i _hi
  rw [wishartSpectralTiltCoefficient_fin]
  apply ofReal_wishartDiagonalStageTransform_eq_complex hm
    (lt_of_lt_of_le i.2 hp) (ht i i.2)
  have hrate_i := hrate i i.2
  rw [wishartSpectralTiltCoefficient_fin] at hrate_i
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hm_ne : (m : ℝ) ≠ 0 := ne_of_gt hmR
  have hfactor :
      (m : ℝ) / 2 + (1 + R.deviationEigenvalues i) * t =
        (m : ℝ) *
          ((1 / 2 : ℝ) +
            t * (1 + R.deviationEigenvalues i) / (m : ℝ)) := by
    field_simp [hm_ne]
  rw [hfactor]
  positivity

/-- Exact real MGF of the actual row-based `M_R`, rewritten as the restriction
of the branch-safe complex Wishart product. -/
theorem ofReal_integral_exp_mul_M_R_eq_complexWishartCorrelationTransform
    {m p : ℕ} (hm : 0 < m) (hp : p ≤ m)
    (R : CorrelationMatrix p) {t : ℝ}
    (ht : ∀ n < p, 0 < (((m - n : ℕ) : ℝ) / 2) + t)
    (hrate : ∀ n < p,
      0 < (1 / 2 : ℝ) + wishartSpectralTiltCoefficient m R t n) :
    ((∫ z, Real.exp (t * GeneralRDecomposition.M_R m R z)
        ∂standardGaussianDataMeasure m p : ℝ) : ℂ) =
      Complex.exp
          ((-t * GeneralRDecomposition.W0LogDetMean m p +
            t * (p : ℝ) : ℝ) : ℂ) *
        complexWishartCorrelationTransform R m (t : ℂ) := by
  rw [integral_exp_mul_M_R_eq_diagonal hm hp R ht hrate]
  push_cast
  have hprod :=
    ofReal_wishartDiagonalProduct_eq_complexWishartCorrelationTransform
      hm hp R ht hrate
  push_cast at hprod
  rw [hprod]

/-- Every real parameter in the natural transform domain gives genuine
exponential integrability of the actual `M_R` statistic. -/
theorem integrable_exp_mul_M_R
    {m p : ℕ} (hm : 0 < m) (hp : p ≤ m)
    (R : CorrelationMatrix p) {t : ℝ}
    (ht : ∀ n < p, 0 < (((m - n : ℕ) : ℝ) / 2) + t)
    (hrate : ∀ n < p,
      0 < (1 / 2 : ℝ) + wishartSpectralTiltCoefficient m R t n) :
    Integrable
      (fun z ↦ Real.exp (t * GeneralRDecomposition.M_R m R z))
      (standardGaussianDataMeasure m p) := by
  by_contra hnot
  have hzero :
      (∫ z, Real.exp (t * GeneralRDecomposition.M_R m R z)
          ∂standardGaussianDataMeasure m p) = 0 :=
    integral_undef hnot
  rw [integral_exp_mul_M_R_eq_diagonal hm hp R ht hrate] at hzero
  have hprod :
      0 < ∏ n ∈ Finset.range p,
        wishartDiagonalStageTransform m n t
          (wishartSpectralTiltCoefficient m R t n) := by
    exact Finset.prod_pos fun n hn ↦
      wishartDiagonalStageTransform_pos
        (lt_of_lt_of_le (Finset.mem_range.mp hn) hp)
        (ht n (Finset.mem_range.mp hn))
        (hrate n (Finset.mem_range.mp hn))
  have hpositive :
      0 < Real.exp (-t * GeneralRDecomposition.W0LogDetMean m p +
          t * (p : ℝ)) *
        ∏ n ∈ Finset.range p,
          wishartDiagonalStageTransform m n t
            (wishartSpectralTiltCoefficient m R t n) :=
    mul_pos (Real.exp_pos _) hprod
  linarith

end

end LogdetLean
