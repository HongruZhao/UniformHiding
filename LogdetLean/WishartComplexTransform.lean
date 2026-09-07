import LogdetLean.WishartMellinLaplace
import LogdetLean.WishartPopulationCorrection
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Tactic

/-!
# Branch-safe complex product for the diagonal Wishart transform

The pinned Mathlib release has no primitive Wishart law or multivariate
matrix-Gamma integral.  `WishartMellinLaplace` therefore proves the real
transform from independent Bartlett Beta--Gamma factors.  This file records
the corresponding finite complex product without taking a logarithm of the
Gamma function (whose branch is not available in Mathlib).

The crucial identity is multiplicative and branch safe:

`T_R(z) = T_I(z) * exp (D_A(z))`.

It is exactly Zhao, arXiv:2608.00565v1, equation (5.20), with `D_A` written
as the compatible difference-of-logs branch proved in
`WishartPopulationCorrection`.  Passing from this identity to an additive
`K_R=K_I+D_A` requires only a chosen analytic logarithm of the nonvanishing
identity transform; no unrecorded `2*pi*I` term is introduced here.
-/

namespace LogdetLean

noncomputable section

open Complex Set
open scoped BigOperators

/-- Branch-safe exponent in one diagonal matrix-Gamma factor.  The form
`alpha^alpha m^z /(alpha+r z)^(alpha+z)` is chosen because the common terms
cancel literally when comparing `r` with `1`. -/
def complexWishartDiagonalStageExponent
    (m r : ℝ) (z : ℂ) : ℂ :=
  let alpha := m / 2
  ((alpha * Real.log alpha : ℝ) : ℂ) +
    z * (Real.log m : ℂ) -
    ((alpha : ℂ) + z) *
      Complex.log ((alpha : ℂ) + (r : ℂ) * z)

/-- One factor of the complex diagonal Wishart transform. -/
def complexWishartDiagonalStageTransform
    (m : ℕ) (n : ℕ) (r : ℝ) (z : ℂ) : ℂ :=
  Complex.Gamma (((((m - n : ℕ) : ℝ) / 2 : ℝ) : ℂ) + z) /
      Complex.Gamma ((((m - n : ℕ) : ℝ) / 2 : ℝ) * 1) *
    Complex.exp (complexWishartDiagonalStageExponent (m : ℝ) r z)

/-- The finite transform with eigenvalues `r_i=1+lambda_i(A)`. -/
def complexWishartCorrelationTransform {p : ℕ}
    (R : CorrelationMatrix p) (m : ℕ) (z : ℂ) : ℂ :=
  ∏ i : Fin p, complexWishartDiagonalStageTransform m i.1
    (1 + R.deviationEigenvalues i) z

/-- Identity-correlation version of the same finite transform. -/
def complexWishartIdentityTransform (m p : ℕ) (z : ℂ) : ℂ :=
  ∏ i : Fin p, complexWishartDiagonalStageTransform m i.1 1 z

/-- Exact exponent split for one eigenvalue. -/
theorem complexWishartDiagonalStageExponent_eq_identity_add
    (m r : ℝ) (z : ℂ) :
    complexWishartDiagonalStageExponent m r z =
      complexWishartDiagonalStageExponent m 1 z +
        wishartScalarLogTerm (m / 2) r z := by
  unfold complexWishartDiagonalStageExponent wishartScalarLogTerm
    wishartScalarLogDiff
  simp only [Complex.ofReal_one, one_mul]
  ring

/-- Exact multiplicative split for one diagonal factor. -/
theorem complexWishartDiagonalStageTransform_eq_identity_mul
    (m n : ℕ) (r : ℝ) (z : ℂ) :
    complexWishartDiagonalStageTransform m n r z =
      complexWishartDiagonalStageTransform m n 1 z *
        Complex.exp (wishartScalarLogTerm ((m : ℝ) / 2) r z) := by
  unfold complexWishartDiagonalStageTransform
  rw [complexWishartDiagonalStageExponent_eq_identity_add,
    Complex.exp_add]
  ring

/-- On a real argument, the branch-safe exponential is exactly the real
tilted-rate factor proved by the Bartlett integral. -/
theorem complexWishartDiagonalStageExp_ofReal
    {m r t : ℝ} (hm : 0 < m) (haff : 0 < m / 2 + r * t) :
    Complex.exp (complexWishartDiagonalStageExponent m r (t : ℂ)) =
      (((1 / 2 : ℝ) ^ (m / 2) /
        ((1 / 2 : ℝ) + t * r / m) ^ (m / 2 + t) : ℝ) : ℂ) := by
  have halpha : 0 < m / 2 := by positivity
  have hrate : 0 < (1 / 2 : ℝ) + t * r / m := by
    rw [show (1 / 2 : ℝ) + t * r / m = (m / 2 + r * t) / m by
      field_simp [hm.ne']]
    positivity
  have hhalfEq : (1 / 2 : ℝ) = (m / 2) / m := by
    field_simp [hm.ne']
  have hrateEq :
      (1 / 2 : ℝ) + t * r / m = (m / 2 + r * t) / m := by
    field_simp [hm.ne']
  have hlogHalf :
      Real.log (1 / 2 : ℝ) = Real.log (m / 2) - Real.log m := by
    rw [hhalfEq, Real.log_div halpha.ne' hm.ne']
  have hlogRate :
      Real.log ((1 / 2 : ℝ) + t * r / m) =
        Real.log (m / 2 + r * t) - Real.log m := by
    rw [hrateEq, Real.log_div haff.ne' hm.ne']
  have hexponent :
      complexWishartDiagonalStageExponent m r (t : ℂ) =
        (((m / 2) * Real.log (1 / 2 : ℝ) -
          (m / 2 + t) *
            Real.log ((1 / 2 : ℝ) + t * r / m) : ℝ) : ℂ) := by
    unfold complexWishartDiagonalStageExponent
    dsimp
    rw [hlogHalf, hlogRate]
    have haffC :
        ((m / 2 : ℝ) : ℂ) + (r : ℂ) * (t : ℂ) =
          ((m / 2 + r * t : ℝ) : ℂ) := by
      push_cast
      ring
    rw [haffC, ← Complex.ofReal_log haff.le]
    push_cast
    ring
  rw [hexponent, ← Complex.ofReal_exp]
  norm_cast
  rw [Real.rpow_def_of_pos (by norm_num : 0 < (1 / 2 : ℝ)),
    Real.rpow_def_of_pos hrate, ← Real.exp_sub]
  congr 1
  ring

/-- The complex product restricts on its real domain to the exact real
Bartlett Mellin--Laplace factor. -/
theorem ofReal_wishartDiagonalStageTransform_eq_complex
    {m n : ℕ} {r t : ℝ} (hm : 0 < m) (hnm : n < m)
    (_ht : 0 < (((m - n : ℕ) : ℝ) / 2) + t)
    (haff : 0 < (m : ℝ) / 2 + r * t) :
    (wishartDiagonalStageTransform m n t (t * r / m) : ℂ) =
      complexWishartDiagonalStageTransform m n r (t : ℂ) := by
  have hres : 0 < (((m - n : ℕ) : ℝ) / 2) := by
    have : 0 < m - n := Nat.sub_pos_of_lt hnm
    positivity
  unfold wishartDiagonalStageTransform
    complexWishartDiagonalStageTransform
  rw [complexWishartDiagonalStageExp_ofReal (by exact_mod_cast hm) haff]
  rw [show (((((m - n : ℕ) : ℝ) / 2 : ℝ) : ℂ) + (t : ℂ)) =
      (((((m - n : ℕ) : ℝ) / 2) + t : ℝ) : ℂ) by
    push_cast
    ring]
  rw [show (((((m - n : ℕ) : ℝ) / 2 : ℝ) : ℂ) * 1) =
      (((((m - n : ℕ) : ℝ) / 2) : ℝ) : ℂ) by ring]
  rw [Complex.Gamma_ofReal, Complex.Gamma_ofReal]
  push_cast
  rfl

/-- Exact branch-safe finite transform identity
`T_R=T_I*exp(D_A)`. -/
theorem complexWishartCorrelationTransform_eq_identity_mul_exp_correction
    {p : ℕ} (R : CorrelationMatrix p) (m : ℕ) (z : ℂ) :
    complexWishartCorrelationTransform R m z =
      complexWishartIdentityTransform m p z *
        Complex.exp (wishartPopulationCorrection R (m : ℝ) z) := by
  unfold complexWishartCorrelationTransform complexWishartIdentityTransform
    wishartPopulationCorrection
  rw [show (∏ i : Fin p, complexWishartDiagonalStageTransform m i.1
      (1 + R.deviationEigenvalues i) z) =
      ∏ i : Fin p, (complexWishartDiagonalStageTransform m i.1 1 z *
        Complex.exp (wishartScalarLogTerm ((m : ℝ) / 2)
          (1 + R.deviationEigenvalues i) z)) by
    apply Finset.prod_congr rfl
    intro i _hi
    exact complexWishartDiagonalStageTransform_eq_identity_mul
      m i.1 (1 + R.deviationEigenvalues i) z]
  rw [Finset.prod_mul_distrib, ← Complex.exp_sum]

/-- A single complex diagonal factor is nonzero whenever its shifted Gamma
shape has positive real part. -/
theorem complexWishartDiagonalStageTransform_ne_zero
    {m n : ℕ} {r : ℝ} {z : ℂ}
    (hshape : 0 <
      ((((((m - n : ℕ) : ℝ) / 2 : ℝ) : ℂ) + z).re))
    (hres : 0 < (((m - n : ℕ) : ℝ) / 2)) :
    complexWishartDiagonalStageTransform m n r z ≠ 0 := by
  unfold complexWishartDiagonalStageTransform
  exact mul_ne_zero
    (div_ne_zero
      (Complex.Gamma_ne_zero_of_re_pos hshape)
      (Complex.Gamma_ne_zero_of_re_pos (by simpa using hres)))
    (Complex.exp_ne_zero _)

/-- The full correlation transform is nonzero on the entire imaginary axis
when `p≤m`.  This is the branch-free nonvanishing certificate needed before
choosing an additive cumulant logarithm. -/
theorem complexWishartCorrelationTransform_ne_zero_imaginary
    {p m : ℕ} (R : CorrelationMatrix p) (hp : p ≤ m) (u : ℝ) :
    complexWishartCorrelationTransform R m ((u : ℂ) * Complex.I) ≠ 0 := by
  unfold complexWishartCorrelationTransform
  apply Finset.prod_ne_zero_iff.mpr
  intro i _hi
  have hinm : i.1 < m := lt_of_lt_of_le i.2 hp
  have hsub : 0 < m - i.1 := Nat.sub_pos_of_lt hinm
  apply complexWishartDiagonalStageTransform_ne_zero
  · simpa using (show 0 < (((m - i.1 : ℕ) : ℝ) / 2) by positivity)
  · positivity

/-- Identity specialization of the preceding global nonvanishing result. -/
theorem complexWishartIdentityTransform_ne_zero_imaginary
    {p m : ℕ} (hp : p ≤ m) (u : ℝ) :
    complexWishartIdentityTransform m p ((u : ℂ) * Complex.I) ≠ 0 := by
  unfold complexWishartIdentityTransform
  apply Finset.prod_ne_zero_iff.mpr
  intro i _hi
  have hinm : i.1 < m := lt_of_lt_of_le i.2 hp
  have hsub : 0 < m - i.1 := Nat.sub_pos_of_lt hinm
  apply complexWishartDiagonalStageTransform_ne_zero
  · simpa using (show 0 < (((m - i.1 : ℕ) : ℝ) / 2) by positivity)
  · positivity

end

end LogdetLean
