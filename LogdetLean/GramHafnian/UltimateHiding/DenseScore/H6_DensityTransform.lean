import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H6_CoordinateAlgebra
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic

/-!
# H6 finite-coordinate density transformation

This module proves the exact finite-product algebra behind the change
`lambda_i = x_i / (1+x_i)`.  It does not assert a Takagi decomposition, a
matrix-density theorem, or any measure-level change of variables.
-/

open scoped BigOperators
open Finset Set

namespace H6DensityTransform

noncomputable section

open H6CoordinateAlgebra

/-- The finite set of ordered representatives `(i,j)` with `i < j`. -/
def strictPairs (N : ℕ) : Finset (Fin N × Fin N) :=
  (Finset.univ ×ˢ Finset.univ).filter fun p ↦ p.1 < p.2

@[simp]
theorem mem_strictPairs {N : ℕ} {p : Fin N × Fin N} :
    p ∈ strictPairs N ↔ p.1 < p.2 := by
  simp [strictPairs]

/-- Absolute Vandermonde product over `i < j`. -/
def vandermondeAbs (N : ℕ) (x : Fin N → ℝ) : ℝ :=
  ∏ p ∈ strictPairs N, |x p.1 - x p.2|

/-- The product of the two endpoint weights over every pair `i < j`. -/
def pairEndpointProduct {M : Type*} [CommMonoid M]
    (N : ℕ) (a : Fin N → M) : M :=
  ∏ p ∈ strictPairs N, a p.1 * a p.2

/-- Every coordinate occurs in exactly `N-1` unordered pairs. -/
theorem pairEndpointProduct_eq_coordinatePowers
    {M : Type*} [CommMonoid M] (N : ℕ) (a : Fin N → M) :
    pairEndpointProduct N a = ∏ i : Fin N, a i ^ (N - 1) := by
  classical
  unfold pairEndpointProduct
  rw [Finset.prod_mul_distrib]
  have hleft :
      (∏ p ∈ strictPairs N, a p.1) =
        ∏ i : Fin N, a i ^ #(Finset.Ioi i) := by
    rw [Finset.prod_finset_product (strictPairs N) Finset.univ
      (fun i ↦ Finset.Ioi i) (by intro p; simp)]
    simp
  have hright :
      (∏ p ∈ strictPairs N, a p.2) =
        ∏ i : Fin N, a i ^ #(Finset.Iio i) := by
    rw [Finset.prod_finset_product_right (strictPairs N) Finset.univ
      (fun i ↦ Finset.Iio i) (by intro p; simp)]
    simp
  rw [hleft, hright, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _hi
  rw [← pow_add]
  congr 1
  simp only [Fin.card_Ioi, Fin.card_Iio]
  omega

/-- Exact transformation of the Vandermonde product, retaining the pair
denominator before rearranging it coordinatewise. -/
theorem vandermondeAbs_inverseVector_pairProduct
    {N : ℕ} {x : Fin N → ℝ} (hx : x ∈ openPositiveOrthant N) :
    vandermondeAbs N (betaPrimeInverseVector N x) =
      vandermondeAbs N x /
        pairEndpointProduct N (fun i ↦ 1 + x i) := by
  classical
  rw [vandermondeAbs, vandermondeAbs, pairEndpointProduct,
    ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hxp : x p.1 ≠ -1 := by
    have := hx p.1
    linarith
  have hxq : x p.2 ≠ -1 := by
    have := hx p.2
    linarith
  simp only [betaPrimeInverseVector]
  rw [betaPrimeInverse_sub _ _ hxp hxq, abs_div]
  have hdenpos : 0 < (1 + x p.1) * (1 + x p.2) :=
    mul_pos (by linarith [hx p.1]) (by linarith [hx p.2])
  rw [abs_of_pos hdenpos]

/-- Coordinatewise rearrangement of the Vandermonde denominator. -/
theorem vandermondeAbs_inverseVector
    {N : ℕ} {x : Fin N → ℝ} (hx : x ∈ openPositiveOrthant N) :
    vandermondeAbs N (betaPrimeInverseVector N x) =
      vandermondeAbs N x /
        ∏ i : Fin N, (1 + x i) ^ (N - 1) := by
  rw [vandermondeAbs_inverseVector_pairProduct hx,
    pairEndpointProduct_eq_coordinatePowers]

/-- Full product of the scalar inverse Jacobians. -/
def inverseJacobianProduct (N : ℕ) (x : Fin N → ℝ) : ℝ :=
  ∏ i : Fin N, betaPrimeInverseJacobian (x i)

/-- Product of positive-coordinate real powers. -/
def positiveCoordinateRpowProduct (N : ℕ) (q : ℝ)
    (x : Fin N → ℝ) : ℝ :=
  ∏ i : Fin N, Real.rpow (1 + x i) q

theorem positiveCoordinateRpowProduct_add
    {N : ℕ} {x : Fin N → ℝ} (hx : x ∈ openPositiveOrthant N)
    (a b : ℝ) :
    positiveCoordinateRpowProduct N a x *
        positiveCoordinateRpowProduct N b x =
      positiveCoordinateRpowProduct N (a + b) x := by
  classical
  rw [positiveCoordinateRpowProduct, positiveCoordinateRpowProduct,
    positiveCoordinateRpowProduct, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _hi
  exact (Real.rpow_add (by linarith [hx i]) a b).symm

theorem positiveCoordinateRpowProduct_neg
    {N : ℕ} {x : Fin N → ℝ} (hx : x ∈ openPositiveOrthant N)
    (q : ℝ) :
    positiveCoordinateRpowProduct N (-q) x =
      (positiveCoordinateRpowProduct N q x)⁻¹ := by
  classical
  unfold positiveCoordinateRpowProduct
  calc
    (∏ i : Fin N, Real.rpow (1 + x i) (-q)) =
        ∏ i : Fin N, (Real.rpow (1 + x i) q)⁻¹ := by
      apply Finset.prod_congr rfl
      intro i _hi
      exact Real.rpow_neg (by linarith [hx i]) q
    _ = (∏ i : Fin N, Real.rpow (1 + x i) q)⁻¹ := by
      rw [Finset.prod_inv_distrib]

theorem pairEndpointProduct_eq_positiveCoordinateRpowProduct
    {N : ℕ} {x : Fin N → ℝ} :
    pairEndpointProduct N (fun i ↦ 1 + x i) =
      positiveCoordinateRpowProduct N ((N - 1 : ℕ) : ℝ) x := by
  rw [pairEndpointProduct_eq_coordinatePowers]
  unfold positiveCoordinateRpowProduct
  apply Finset.prod_congr rfl
  intro i _hi
  exact (Real.rpow_natCast (1 + x i) (N - 1)).symm

theorem vandermondeAbs_inverseVector_rpow
    {N : ℕ} {x : Fin N → ℝ} (hx : x ∈ openPositiveOrthant N) :
    vandermondeAbs N (betaPrimeInverseVector N x) =
      vandermondeAbs N x *
        positiveCoordinateRpowProduct N (-((N - 1 : ℕ) : ℝ)) x := by
  rw [vandermondeAbs_inverseVector_pairProduct hx,
    pairEndpointProduct_eq_positiveCoordinateRpowProduct,
    positiveCoordinateRpowProduct_neg hx]
  rfl

/-- The complete inverse Jacobian is the coordinate-power product with
exponent `-2`. -/
theorem inverseJacobianProduct_eq_rpow
    {N : ℕ} {x : Fin N → ℝ} (hx : x ∈ openPositiveOrthant N) :
    inverseJacobianProduct N x =
      positiveCoordinateRpowProduct N (-2) x := by
  classical
  unfold inverseJacobianProduct positiveCoordinateRpowProduct
  apply Finset.prod_congr rfl
  intro i _hi
  unfold betaPrimeInverseJacobian
  symm
  have hbase : 0 ≤ 1 + x i := by linarith [hx i]
  calc
    Real.rpow (1 + x i) (-2 : ℝ) =
        (Real.rpow (1 + x i) (2 : ℝ))⁻¹ := by
      simpa only [Real.rpow_eq_pow] using
        (Real.rpow_neg hbase (2 : ℝ))
    _ = ((1 + x i) ^ (2 : ℕ))⁻¹ := by
      exact congrArg Inv.inv (Real.rpow_natCast (1 + x i) 2)
    _ = 1 / (1 + x i) ^ 2 := by
      rw [one_div]

/-- Boundary-weight product in the original beta coordinates. -/
def unitBoundaryRpowProduct (N : ℕ) (alpha : ℝ)
    (lambda : Fin N → ℝ) : ℝ :=
  ∏ i : Fin N, Real.rpow (1 - lambda i) alpha

theorem unitBoundaryRpowProduct_inverseVector
    {N : ℕ} {x : Fin N → ℝ} (hx : x ∈ openPositiveOrthant N)
    (alpha : ℝ) :
    unitBoundaryRpowProduct N alpha (betaPrimeInverseVector N x) =
      positiveCoordinateRpowProduct N (-alpha) x := by
  classical
  unfold unitBoundaryRpowProduct positiveCoordinateRpowProduct
  apply Finset.prod_congr rfl
  intro i _hi
  have hden : 1 + x i ≠ 0 := by linarith [hx i]
  have hone : 1 - betaPrimeInverse (x i) = (1 + x i)⁻¹ := by
    unfold betaPrimeInverse
    field_simp [hden]
    ring
  rw [betaPrimeInverseVector, hone]
  exact (Real.rpow_neg_eq_inv_rpow (1 + x i) alpha).symm

/-- COE exponent in the squared-Takagi eigenvalue density. -/
def coeEigenvalueExponent (N K : ℕ) : ℝ :=
  ((K : ℝ) - 2 * (N : ℝ) - 1) / 2

/-- The exact exponent bookkeeping in the beta-to-beta-prime change. -/
theorem coeEigenvalueExponent_add_pairCount_add_jacobian
    {N K : ℕ} (hN : 1 ≤ N) :
    coeEigenvalueExponent N K + ((N - 1 : ℕ) : ℝ) + 2 =
      ((K : ℝ) + 1) / 2 := by
  unfold coeEigenvalueExponent
  rw [Nat.cast_sub hN]
  push_cast
  ring

/-- Unnormalized squared-Takagi eigenvalue weight. -/
def coeEigenvalueWeight (N : ℕ) (alpha : ℝ)
    (lambda : Fin N → ℝ) : ℝ :=
  vandermondeAbs N lambda * unitBoundaryRpowProduct N alpha lambda

/-- Unnormalized beta-prime eigenvalue weight. -/
def betaPrimeEigenvalueWeight (N : ℕ) (q : ℝ)
    (x : Fin N → ℝ) : ℝ :=
  vandermondeAbs N x * positiveCoordinateRpowProduct N (-q) x

/-- Exact pointwise transformed-density identity on the positive orthant.

This is the full algebraic density/Jacobian computation.  Promoting it to an
equality of measures still requires a finite-dimensional change-of-variables
theorem and the Takagi-coordinate density theorem. -/
theorem coeWeight_mul_inverseJacobian_eq_betaPrimeWeight
    {N K : ℕ} (hN : 1 ≤ N) {x : Fin N → ℝ}
    (hx : x ∈ openPositiveOrthant N) :
    coeEigenvalueWeight N (coeEigenvalueExponent N K)
          (betaPrimeInverseVector N x) * inverseJacobianProduct N x =
      betaPrimeEigenvalueWeight N (((K : ℝ) + 1) / 2) x := by
  rw [coeEigenvalueWeight, betaPrimeEigenvalueWeight,
    vandermondeAbs_inverseVector_rpow hx,
    unitBoundaryRpowProduct_inverseVector hx,
    inverseJacobianProduct_eq_rpow hx]
  rw [mul_assoc, positiveCoordinateRpowProduct_add hx,
    mul_assoc, positiveCoordinateRpowProduct_add hx]
  congr 2
  have hexp := coeEigenvalueExponent_add_pairCount_add_jacobian
    (N := N) (K := K) hN
  linarith

end

end H6DensityTransform
