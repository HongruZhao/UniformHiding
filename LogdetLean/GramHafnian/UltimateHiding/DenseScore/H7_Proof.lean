import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CubicDifferentialBasics
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Tactic

/-!
# Assumption-free core for the H7 cubic differential

This module does not use
`coeCorner_cubicDifferentialWitness_external_derived` or any other scientific
axiom.  It constructs the finite-dimensional object from which the H16
witness must be obtained:

* an explicit arbitrary-direction determinant likelihood, including the
  complex-symmetric congruence Jacobian;
* a genuine third Frechet differential in the real matrix coordinates;
* a canonical six-term symmetrization whose diagonal is unchanged; and
* the exact bridge between a third Frechet differential on a linear line and
  the ordinary third iterated derivative.

The full `ConcreteCubicDifferentialWitness` is deliberately not asserted here.
To fill that structure without an external input one must still prove that the
multivariate likelihood is `C^3` near zero on supported states, identify its
three diagonal restrictions with the existing rank-one, centered, and central
score formulas, and prove the two projective integrability/mean fields.  None
of those obligations is replaced by a hypothesis or a placeholder below.

The internal `h16...` prefix is retained from the earlier reduction prototype;
these declarations are now the installed H7 reduction core.
-/

open Function
open scoped Matrix

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- Reconstruct a complex matrix from its entrywise real and imaginary
coordinates. -/
def concreteMatrixOfRealCoordinates {N : ℕ}
    (x : ConcreteMatrixRealCoordinates N) : ConcreteMatrixState N :=
  fun i j => ⟨x i j 0, x i j 1⟩

/-- Reconstructing the real coordinates of a complex matrix is exact. -/
theorem concreteMatrixOfRealCoordinates_coordinates
    {N : ℕ} (A : ConcreteMatrixState N) :
    concreteMatrixOfRealCoordinates (concreteMatrixRealCoordinates A) = A := by
  ext i j
  apply Complex.ext <;>
    simp [concreteMatrixOfRealCoordinates, concreteMatrixRealCoordinates]

/-- Extracting the coordinates of a reconstructed matrix is exact. -/
theorem concreteMatrixRealCoordinates_ofCoordinates
    {N : ℕ} (x : ConcreteMatrixRealCoordinates N) :
    concreteMatrixRealCoordinates (concreteMatrixOfRealCoordinates x) = x := by
  ext i j b
  fin_cases b <;>
    simp [concreteMatrixOfRealCoordinates, concreteMatrixRealCoordinates]

/-- The coordinate map used by `ConcreteCubicDifferentialWitness` is a real
linear equivalence, not merely an encoding. -/
def concreteMatrixRealCoordinatesLinearEquiv (N : ℕ) :
    ConcreteMatrixState N ≃ₗ[ℝ] ConcreteMatrixRealCoordinates N where
  toFun := concreteMatrixRealCoordinates
  invFun := concreteMatrixOfRealCoordinates
  left_inv := concreteMatrixOfRealCoordinates_coordinates
  right_inv := concreteMatrixRealCoordinates_ofCoordinates
  map_add' := concreteMatrixRealCoordinates_add
  map_smul' := concreteMatrixRealCoordinates_smul

/-- In particular, the real-coordinate map loses no matrix information. -/
theorem concreteMatrixRealCoordinates_injective_internal {N : ℕ} :
    Function.Injective
      (concreteMatrixRealCoordinates :
        ConcreteMatrixState N → ConcreteMatrixRealCoordinates N) :=
  (concreteMatrixRealCoordinatesLinearEquiv N).injective

/-- Determinant at the inverse image of an arbitrary real congruence
direction.  The parameter has been absorbed into `H`, so the inverse flow is
evaluated at time `-1`. -/
def h16GeneralCOEInverseDeterminant {N : ℕ} (K : ℕ)
    (H A : ConcreteMatrixState N) : ℝ :=
  let C := unscaleCOECorner K A
  let CH := transposeCongruenceFlow H (-1 : ℝ) C
  (Matrix.det (1 - CH.conjTranspose * CH)).re

/-- Explicit interior likelihood for an arbitrary congruence direction.

For `C -> exp(H) C exp(H)^T`, the real Jacobian on complex-symmetric
coordinates is `exp(2 (N+1) Re Tr H)`.  The first factor below is its inverse;
the second is the determinant-density ratio. -/
def h16GeneralCOELikelihoodCore (N K : ℕ)
    (H A : ConcreteMatrixState N) : ℝ := by
  classical
  exact if concreteCOEBaseDeterminant K A = 0 then 1 else
    Real.exp (-2 * ((N : ℝ) + 1) * (Matrix.trace H).re) *
      Real.rpow
        (h16GeneralCOEInverseDeterminant K H A /
          concreteCOEBaseDeterminant K A)
        (coeCornerDensityExponent N K)

/-- The arbitrary-direction likelihood is normalized at the zero direction
on every supported state. -/
theorem h16GeneralCOELikelihoodCore_zero_on_support
    {N K : ℕ} (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    h16GeneralCOELikelihoodCore N K 0 A = 1 := by
  have hbase : concreteCOEBaseDeterminant K A ≠ 0 :=
    ((RCLike.lt_iff_re_im.mp hsupport.det_pos).1).ne'
  have hinverse : h16GeneralCOEInverseDeterminant K 0 A =
      concreteCOEBaseDeterminant K A := by
    simp [h16GeneralCOEInverseDeterminant, concreteCOEBaseDeterminant,
      transposeCongruenceFlow, transposeCongruence]
  unfold h16GeneralCOELikelihoodCore
  rw [if_neg hbase, hinverse, div_self hbase]
  simp

/-- The same likelihood expressed on the exact real coordinate space used by
H7. -/
def h16CoordinateLikelihoodCore {N : ℕ} (K : ℕ)
    (A : ConcreteMatrixState N) (x : ConcreteMatrixRealCoordinates N) : ℝ :=
  h16GeneralCOELikelihoodCore N K (concreteMatrixOfRealCoordinates x) A

/-- The raw third Frechet differential of the explicit coordinate
likelihood.  Continuity and trilinearity are encoded in the codomain type. -/
def h16CoordinateThirdFrechetDifferential {N : ℕ} (K : ℕ)
    (A : ConcreteMatrixState N) :
    ContinuousMultilinearMap ℝ
      (fun _ : Fin 3 => ConcreteMatrixRealCoordinates N) ℝ :=
  iteratedFDeriv ℝ 3 (h16CoordinateLikelihoodCore K A) 0

/-- Canonical symmetrization of a continuous real trilinear map.  This value
is the average over all six permutations. -/
def h16SymmetrizedThirdFrechetValue
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (D : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => V) ℝ)
    (x y z : V) : ℝ :=
  (D ![x, y, z] + D ![x, z, y] + D ![y, x, z] +
      D ![y, z, x] + D ![z, x, y] + D ![z, y, x]) / 6

/-- The six-term symmetrization is invariant under swapping the first two
arguments. -/
theorem h16SymmetrizedThirdFrechetValue_swap_first
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (D : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => V) ℝ)
    (x y z : V) :
    h16SymmetrizedThirdFrechetValue D x y z =
      h16SymmetrizedThirdFrechetValue D y x z := by
  unfold h16SymmetrizedThirdFrechetValue
  ring

/-- The six-term symmetrization is invariant under swapping the final two
arguments. -/
theorem h16SymmetrizedThirdFrechetValue_swap_last
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (D : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => V) ℝ)
    (x y z : V) :
    h16SymmetrizedThirdFrechetValue D x y z =
      h16SymmetrizedThirdFrechetValue D x z y := by
  unfold h16SymmetrizedThirdFrechetValue
  ring

/-- Symmetrization does not alter the cubic diagonal. -/
theorem h16SymmetrizedThirdFrechetValue_diagonal
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (D : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => V) ℝ)
    (x : V) :
    h16SymmetrizedThirdFrechetValue D x x x = D ![x, x, x] := by
  unfold h16SymmetrizedThirdFrechetValue
  ring

/-- Candidate symmetric cubic value obtained from the explicit H7
likelihood. -/
def h16CoordinateCubicValue {N : ℕ} (K : ℕ)
    (A : ConcreteMatrixState N) (x y z : ConcreteMatrixRealCoordinates N) : ℝ :=
  h16SymmetrizedThirdFrechetValue
    (h16CoordinateThirdFrechetDifferential K A) x y z

/-- The coordinate candidate has the first H7 symmetry. -/
theorem h16CoordinateCubicValue_swap_first
    {N K : ℕ} (A : ConcreteMatrixState N)
    (x y z : ConcreteMatrixRealCoordinates N) :
    h16CoordinateCubicValue K A x y z =
      h16CoordinateCubicValue K A y x z :=
  h16SymmetrizedThirdFrechetValue_swap_first _ _ _ _

/-- The coordinate candidate has the second H7 symmetry. -/
theorem h16CoordinateCubicValue_swap_last
    {N K : ℕ} (A : ConcreteMatrixState N)
    (x y z : ConcreteMatrixRealCoordinates N) :
    h16CoordinateCubicValue K A x y z =
      h16CoordinateCubicValue K A x z y :=
  h16SymmetrizedThirdFrechetValue_swap_last _ _ _ _

/-- On the diagonal, the candidate is exactly the unsymmetrized third Frechet
differential of the explicit likelihood. -/
theorem h16CoordinateCubicValue_diagonal
    {N K : ℕ} (A : ConcreteMatrixState N)
    (x : ConcreteMatrixRealCoordinates N) :
    h16CoordinateCubicValue K A x x x =
      h16CoordinateThirdFrechetDifferential K A ![x, x, x] :=
  h16SymmetrizedThirdFrechetValue_diagonal _ _

/-- A third Frechet differential on a linear line is the ordinary third
iterated derivative of the restricted scalar path. -/
theorem h16_iteratedDeriv_linear_restriction_three
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : V → ℝ) (hf : ContDiff ℝ 3 f) (x : V) :
    iteratedDeriv 3 (fun t : ℝ => f (t • x)) 0 =
      iteratedFDeriv ℝ 3 f 0 ![x, x, x] := by
  let L : ℝ →L[ℝ] V := (ContinuousLinearMap.id ℝ ℝ).smulRight x
  have hfun : (fun t : ℝ => f (t • x)) = f ∘ L := by
    funext t
    simp [L]
  have hcomp := L.iteratedFDeriv_comp_right (f := f) (i := 3) hf (0 : ℝ)
    (by norm_num)
  rw [hfun, iteratedDeriv_eq_iteratedFDeriv, hcomp]
  have hdiag : (fun _ : Fin 3 => x) = ![x, x, x] := by
    funext i
    fin_cases i <;> rfl
  simp [ContinuousMultilinearMap.compContinuousLinearMap_apply, L, hdiag]

/-- Consequently, once local smoothness of the explicit coordinate
likelihood has been established, its candidate diagonal is the third
one-parameter density derivative.  This is a generic calculus theorem, not a
scientific input. -/
theorem h16CoordinateCubicValue_diagonal_eq_iteratedDeriv
    {N K : ℕ} (A : ConcreteMatrixState N)
    (hC3 : ContDiff ℝ 3 (h16CoordinateLikelihoodCore K A))
    (x : ConcreteMatrixRealCoordinates N) :
    h16CoordinateCubicValue K A x x x =
      iteratedDeriv 3
        (fun t : ℝ => h16CoordinateLikelihoodCore K A (t • x)) 0 := by
  rw [h16CoordinateCubicValue_diagonal]
  exact (h16_iteratedDeriv_linear_restriction_three
    (h16CoordinateLikelihoodCore K A) hC3 x).symm

#print axioms concreteMatrixOfRealCoordinates_coordinates
#print axioms concreteMatrixRealCoordinates_ofCoordinates
#print axioms concreteMatrixRealCoordinates_injective_internal
#print axioms h16GeneralCOELikelihoodCore_zero_on_support
#print axioms h16SymmetrizedThirdFrechetValue_swap_first
#print axioms h16SymmetrizedThirdFrechetValue_swap_last
#print axioms h16SymmetrizedThirdFrechetValue_diagonal
#print axioms h16CoordinateCubicValue_swap_first
#print axioms h16CoordinateCubicValue_swap_last
#print axioms h16CoordinateCubicValue_diagonal
#print axioms h16_iteratedDeriv_linear_restriction_three
#print axioms h16CoordinateCubicValue_diagonal_eq_iteratedDeriv

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
