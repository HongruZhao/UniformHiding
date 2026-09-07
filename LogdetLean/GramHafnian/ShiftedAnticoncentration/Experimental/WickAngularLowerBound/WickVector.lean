import LogdetLean.GramHafnian.ShiftedAnticoncentration.Experimental.WickAngularLowerBound.SphereLinearFormMoment
import LogdetLean.GramHafnian.WickRegrouping
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# Literal Wick vector representation of the odd cofactor combination

The central identity represents the cofactor combination as the expectation
of a real-Gaussian Wick vector.  It is proved from the already verified full
Gram-hafnian auxiliary-field identity by inserting one coordinate basis
column.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Real BigOperators

namespace LogdetLean.GramHafnian

noncomputable section

namespace WickAngularLowerBound

/-- Split a product over all `2n` column indices into the nonfinal indices
and the distinguished final index. -/
theorem prod_fin_eq_prod_odd_mul_last
    {n : ℕ} (hn : 1 ≤ n) (f : Fin (2 * n) → ℂ) :
    (∏ i, f i) =
      (∏ j : OddCofactorIndex n hn, f j.1) * f (evenLastIndex n hn) := by
  classical
  let p : Fin (2 * n) → Prop := fun i ↦ i ≠ evenLastIndex n hn
  let e := Equiv.sumCompl p
  calc
    (∏ i, f i) = ∏ z : OddCofactorIndex n hn ⊕
        LastCofactorComplement n hn, f (e z) := by
      exact (Fintype.prod_equiv e (fun z ↦ f (e z)) f (fun _ ↦ rfl)).symm
    _ = (∏ j : OddCofactorIndex n hn, f (e (Sum.inl j))) *
          ∏ q : LastCofactorComplement n hn, f (e (Sum.inr q)) := by
      rw [Fintype.prod_sum_type]
    _ = (∏ j : OddCofactorIndex n hn, f j.1) *
          f (evenLastIndex n hn) := by
      congr 1
      rw [Fintype.prod_unique]
      rfl

/-- Coordinate basis column. -/
def coordinateBasisColumn {k : ℕ} (p : Fin k) : Fin k → ℂ :=
  fun q ↦ if q = p then 1 else 0

/-- The final coordinate form of a basis column is the corresponding real
Gaussian coordinate. -/
theorem sum_real_mul_coordinateBasisColumn
    {k : ℕ} (g : Fin k → ℝ) (p : Fin k) :
    (∑ q, (g q : ℂ) * coordinateBasisColumn p q) = (g p : ℂ) := by
  classical
  simp [coordinateBasisColumn]

theorem sum_coordinateBasisColumn_mul
    {k : ℕ} (z : Fin k → ℂ) (p : Fin k) :
    (∑ q, coordinateBasisColumn p q * z q) = z p := by
  classical
  simp [coordinateBasisColumn]

/-- Product of all odd spherical transpose forms against a real vector. -/
def oddSphereLinearProduct
    {n k : ℕ} (hn : 1 ≤ n)
    (u : RadialLowerBoundAlt.CofactorIdx n hn →
      RadialLowerBoundAlt.Direction k)
    (g : Fin k → ℝ) : ℂ :=
  ∏ j, sphereTransposeLinearForm (fun p ↦ (g p : ℂ)) (u j)

/-- Euclidean Wick vector whose expectation is the cofactor combination. -/
def wickVector
    {n k : ℕ} (hn : 1 ≤ n)
    (u : RadialLowerBoundAlt.CofactorIdx n hn →
      RadialLowerBoundAlt.Direction k)
    (g : Fin k → ℝ) : CircularEuclideanSpace k :=
  WithLp.toLp 2 fun p ↦ (g p : ℂ) * oddSphereLinearProduct hn u g

/-- A full auxiliary-field product with a basis final column is exactly one
coordinate of the Wick vector. -/
theorem complexAuxiliaryFieldProduct_basis_last
    {n k : ℕ} (hn : 1 ≤ n)
    (u : RadialLowerBoundAlt.CofactorIdx n hn →
      RadialLowerBoundAlt.Direction k)
    (g : Fin k → ℝ) (p : Fin k) :
    complexAuxiliaryFieldProduct
        (rowMatrix (lastColumnProductEquiv n k hn
          (RadialLowerBoundAlt.directionColumns hn u,
            coordinateBasisColumn p))) g =
      (g p : ℂ) * oddSphereLinearProduct hn u g := by
  unfold complexAuxiliaryFieldProduct oddSphereLinearProduct rowMatrix
  rw [prod_fin_eq_prod_odd_mul_last hn]
  rw [lastColumnProductEquiv_apply_last,
    sum_real_mul_coordinateBasisColumn]
  have hodd :
      (∏ j : OddCofactorIndex n hn,
        ∑ a, (g a : ℂ) *
          lastColumnProductEquiv n k hn
            (RadialLowerBoundAlt.directionColumns hn u,
              coordinateBasisColumn p) j.1 a) =
        oddSphereLinearProduct hn u g := by
    apply Fintype.prod_congr
    intro j
    rw [lastColumnProductEquiv_apply_nonlast]
    unfold sphereTransposeLinearForm RadialLowerBoundAlt.directionColumns
    apply Finset.sum_congr rfl
    intro a _ha
    ring
  rw [hodd]
  simp [oddSphereLinearProduct, mul_comm]

/-- Auxiliary products are integrable under the iid real standard Gaussian
field. -/
theorem integrable_complexAuxiliaryFieldProduct
    {n k : ℕ} (X : Fin k → Fin (2 * n) → ℂ) :
    Integrable (complexAuxiliaryFieldProduct X)
      (standardRealGaussianVector k) := by
  rw [show complexAuxiliaryFieldProduct X =
      fun g ↦ ∑ c : Fin (2 * n) → Fin k,
        complexColoringCoefficient X c * complexRealColorProduct c g by
    funext g
    rw [complexAuxiliaryFieldProduct_eq_coloringSum]
    apply Finset.sum_congr rfl
    intro c _hc
    rw [complexRealColorProduct_eq_coordinatePowers]]
  exact integrable_finsetSum Finset.univ fun c _hc ↦
    (integrable_complexRealColorProduct c).const_mul _

/-- Coordinate form of the Wick identity. -/
theorem integral_wickVector_apply_eq_pastCofactorCombination
    {n k : ℕ} (hn : 1 ≤ n)
    (u : RadialLowerBoundAlt.CofactorIdx n hn →
      RadialLowerBoundAlt.Direction k)
    (p : Fin k) :
    (∫ g, wickVector hn u g p ∂standardRealGaussianVector k) =
      pastCofactorCombination hn
        (RadialLowerBoundAlt.directionColumns hn u) p := by
  let X : Fin k → Fin (2 * n) → ℂ :=
    rowMatrix (lastColumnProductEquiv n k hn
      (RadialLowerBoundAlt.directionColumns hn u, coordinateBasisColumn p))
  have haux := integral_complexAuxiliaryFieldProduct_eq_gramHafnian X
  have hgram := gramHafnian_lastColumnProductEquiv_eq_conditionalLinearForm hn
    (RadialLowerBoundAlt.directionColumns hn u, coordinateBasisColumn p)
  calc
    (∫ g, wickVector hn u g p ∂standardRealGaussianVector k) =
        ∫ g, complexAuxiliaryFieldProduct X g
          ∂(Measure.pi fun _ : Fin k ↦ gaussianReal 0 1) := by
      unfold standardRealGaussianVector
      apply integral_congr_ae
      filter_upwards [] with g
      rw [complexAuxiliaryFieldProduct_basis_last hn u g p]
      rfl
    _ = gramHafnian X := haux
    _ = gramHafnianObservable n k
        (lastColumnProductEquiv n k hn
          (RadialLowerBoundAlt.directionColumns hn u,
            coordinateBasisColumn p)) := rfl
    _ = conditionalCircularLinearForm (pastCofactorCombination hn)
        (RadialLowerBoundAlt.directionColumns hn u,
          coordinateBasisColumn p) := hgram
    _ = pastCofactorCombination hn
        (RadialLowerBoundAlt.directionColumns hn u) p := by
      unfold conditionalCircularLinearForm iidCircularTransposeLinearForm
      exact sum_coordinateBasisColumn_mul _ p

/-- The literal Wick vector is Bochner integrable. -/
theorem integrable_wickVector
    {n k : ℕ} (hn : 1 ≤ n)
    (u : RadialLowerBoundAlt.CofactorIdx n hn →
      RadialLowerBoundAlt.Direction k) :
    Integrable (wickVector hn u) (standardRealGaussianVector k) := by
  apply Integrable.of_eval_piLp
  intro p
  let X : Fin k → Fin (2 * n) → ℂ :=
    rowMatrix (lastColumnProductEquiv n k hn
      (RadialLowerBoundAlt.directionColumns hn u, coordinateBasisColumn p))
  apply (integrable_complexAuxiliaryFieldProduct X).congr
  filter_upwards [] with g
  change complexAuxiliaryFieldProduct X g = wickVector hn u g p
  exact complexAuxiliaryFieldProduct_basis_last hn u g p

/-- Vector-valued form of the Wick identity. -/
theorem integral_wickVector_eq_pastCofactorCombination
    {n k : ℕ} (hn : 1 ≤ n)
    (u : RadialLowerBoundAlt.CofactorIdx n hn →
      RadialLowerBoundAlt.Direction k) :
    (∫ g, wickVector hn u g ∂standardRealGaussianVector k) =
      WithLp.toLp 2 (pastCofactorCombination hn
        (RadialLowerBoundAlt.directionColumns hn u)) := by
  ext p
  rw [eval_integral_piLp
    (fun q ↦ (integrable_wickVector hn u).eval_piLp q) p]
  exact integral_wickVector_apply_eq_pastCofactorCombination hn u p

/-- Complexification preserves the Euclidean norm of a real coordinate
vector. -/
theorem norm_complexified_real
    {k : ℕ} (g : Fin k → ℝ) :
    ‖WithLp.toLp 2 (fun p ↦ (g p : ℂ))‖ =
      ‖WithLp.toLp 2 g‖ := by
  rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
  congr 1
  apply Finset.sum_congr rfl
  intro p _hp
  simp

/-- Pointwise norm of the Wick vector. -/
theorem norm_wickVector
    {n k : ℕ} (hn : 1 ≤ n)
    (u : RadialLowerBoundAlt.CofactorIdx n hn →
      RadialLowerBoundAlt.Direction k)
    (g : Fin k → ℝ) :
    ‖wickVector hn u g‖ =
      ‖WithLp.toLp 2 g‖ *
        ∏ j, ‖sphereTransposeLinearForm
          (fun p ↦ (g p : ℂ)) (u j)‖ := by
  have hvec : wickVector hn u g =
      oddSphereLinearProduct hn u g •
        WithLp.toLp 2 (fun p ↦ (g p : ℂ)) := by
    ext p
    simp [wickVector, oddSphereLinearProduct]
    ring
  rw [hvec, norm_smul, norm_complexified_real]
  rw [show ‖oddSphereLinearProduct hn u g‖ =
      ∏ j, ‖sphereTransposeLinearForm
        (fun p ↦ (g p : ℂ)) (u j)‖ by
    simp [oddSphereLinearProduct]]
  ring

/-- The square root of the literal angular energy is the Euclidean norm of
the cofactor-combination vector. -/
theorem sqrt_angularEnergy_eq_norm_cofactorCombination
    {n k : ℕ} (hn : 1 ≤ n)
    (u : RadialLowerBoundAlt.CofactorIdx n hn →
      RadialLowerBoundAlt.Direction k) :
    Real.sqrt (RadialLowerBoundAlt.angularEnergy hn u) =
      ‖WithLp.toLp 2 (pastCofactorCombination hn
        (RadialLowerBoundAlt.directionColumns hn u))‖ := by
  unfold RadialLowerBoundAlt.angularEnergy
  rw [pastCofactorV_eq_coefficientEnergy, PiLp.norm_eq_of_L2]
  rfl

/-- Pointwise Minkowski estimate furnished by the Wick vector. -/
theorem sqrt_angularEnergy_le_integral_wickNorm
    {n k : ℕ} (hn : 1 ≤ n)
    (u : RadialLowerBoundAlt.CofactorIdx n hn →
      RadialLowerBoundAlt.Direction k) :
    Real.sqrt (RadialLowerBoundAlt.angularEnergy hn u) ≤
      ∫ g, ‖WithLp.toLp 2 g‖ *
        (∏ j, ‖sphereTransposeLinearForm
          (fun p ↦ (g p : ℂ)) (u j)‖)
        ∂standardRealGaussianVector k := by
  calc
    Real.sqrt (RadialLowerBoundAlt.angularEnergy hn u) =
        ‖∫ g, wickVector hn u g ∂standardRealGaussianVector k‖ := by
      rw [integral_wickVector_eq_pastCofactorCombination hn u,
        sqrt_angularEnergy_eq_norm_cofactorCombination hn u]
    _ ≤ ∫ g, ‖wickVector hn u g‖
          ∂standardRealGaussianVector k :=
      norm_integral_le_integral_norm _
    _ = ∫ g, ‖WithLp.toLp 2 g‖ *
          (∏ j, ‖sphereTransposeLinearForm
            (fun p ↦ (g p : ℂ)) (u j)‖)
          ∂standardRealGaussianVector k := by
      apply integral_congr_ae
      filter_upwards [] with g
      exact norm_wickVector hn u g

end WickAngularLowerBound

end

end LogdetLean.GramHafnian
