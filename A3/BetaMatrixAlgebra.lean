import A3.HermitianCongruenceJacobian
import A3.WishartCholeskyCoordinates

open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder MatrixOrder
open Matrix MeasureTheory Set

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

namespace A3Research

variable {n : ℕ} {K : Type*} [RCLike K]

def hermitianCoordinateConjugationLinearEquiv
    (C : Matrix (Fin n) (Fin n) K) (hC : IsUnit C) :
    HermitianCoordinates n K ≃ₗ[ℝ] HermitianCoordinates n K where
  toLinearMap := hermitianCoordinateConjugationLinearMap C
  invFun := hermitianCoordinateConjugationLinearMap C⁻¹
  left_inv := by
    intro x
    change (hermitianCoordinateConjugationLinearMap C⁻¹ *
      hermitianCoordinateConjugationLinearMap C) x = x
    rw [← hermitianCoordinateConjugation_mul,
      Matrix.nonsing_inv_mul C ((Matrix.isUnit_iff_isUnit_det C).mp hC),
      hermitianCoordinateConjugation_one]
    rfl
  right_inv := by
    intro x
    change (hermitianCoordinateConjugationLinearMap C *
      hermitianCoordinateConjugationLinearMap C⁻¹) x = x
    rw [← hermitianCoordinateConjugation_mul,
      Matrix.mul_nonsing_inv C ((Matrix.isUnit_iff_isUnit_det C).mp hC),
      hermitianCoordinateConjugation_one]
    rfl

def hermitianBetaDomain (n : ℕ) (K : Type*) [RCLike K] :
    Set (HermitianCoordinates n K) :=
  {x | (hermitianMatrixOfCoordinates x).PosDef ∧
    (1 - hermitianMatrixOfCoordinates x).PosDef}

def hermitianSumSlice (S : Matrix (Fin n) (Fin n) K) :
    Set (HermitianCoordinates n K) :=
  {x | (hermitianMatrixOfCoordinates x).PosDef ∧
    (S - hermitianMatrixOfCoordinates x).PosDef}

theorem hermitianConjugation_complement
    {C : Matrix (Fin n) (Fin n) K} (hC : C.IsHermitian)
    (x : HermitianCoordinates n K) :
    C * C - hermitianMatrixOfCoordinates (hermitianCoordinateConjugationLinearMap C x) =
      C * (1 - hermitianMatrixOfCoordinates x) * C.conjTranspose := by
  rw [hermitianCoordinateConjugation_reconstruct, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_one, hC.eq]

theorem hermitianConjugation_mem_sumSlice_iff
    {C : Matrix (Fin n) (Fin n) K} (hC : C.PosDef) (x : HermitianCoordinates n K) :
    hermitianCoordinateConjugationLinearMap C x ∈ hermitianSumSlice (C * C) ↔
      x ∈ hermitianBetaDomain n K := by
  change (hermitianMatrixOfCoordinates (hermitianCoordinateConjugationLinearMap C x)).PosDef ∧
    (C * C - hermitianMatrixOfCoordinates (hermitianCoordinateConjugationLinearMap C x)).PosDef ↔
      (hermitianMatrixOfCoordinates x).PosDef ∧ (1 - hermitianMatrixOfCoordinates x).PosDef
  rw [hermitianConjugation_complement hC.isHermitian,
    hermitianCoordinateConjugation_reconstruct, ← Matrix.star_eq_conjTranspose,
    hC.isUnit.posDef_star_right_conjugate_iff, hC.isUnit.posDef_star_right_conjugate_iff]

theorem hermitianConjugation_image_betaDomain
    {C : Matrix (Fin n) (Fin n) K} (hC : C.PosDef) :
    hermitianCoordinateConjugationLinearMap C '' hermitianBetaDomain n K =
      hermitianSumSlice (C * C) := by
  apply Set.ext
  intro y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (hermitianConjugation_mem_sumSlice_iff hC x).mpr hx
  · intro hy
    let e := hermitianCoordinateConjugationLinearEquiv C hC.isUnit
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    apply (hermitianConjugation_mem_sumSlice_iff hC (e.symm y)).mp
    simpa only [show hermitianCoordinateConjugationLinearMap C = e.toLinearMap from rfl,
      LinearEquiv.coe_toLinearMap, e.apply_symm_apply] using hy

theorem posDef_cfc_sqrt {S : Matrix (Fin n) (Fin n) K} (hS : S.PosDef) :
    (CFC.sqrt S).PosDef := hS.isStrictlyPositive.sqrt.posDef

theorem abs_det_hermitianCoordinateConjugation_sqrt
    {S : Matrix (Fin n) (Fin n) K} (hS : S.PosDef) :
    |LinearMap.det (hermitianCoordinateConjugationLinearMap (CFC.sqrt S))| =
      (RCLike.re S.det) ^ (1 + (Module.finrank ℝ K : ℝ) * (n - 1 : ℕ) / 2) := by
  rw [abs_det_hermitianCoordinateConjugation_posDef_square (posDef_cfc_sqrt hS),
    CFC.sqrt_mul_sqrt_self S hS.posSemidef.nonneg]

theorem hermitianConjugation_sqrt_mem_sumSlice_iff
    {S : Matrix (Fin n) (Fin n) K} (hS : S.PosDef) (x : HermitianCoordinates n K) :
    hermitianCoordinateConjugationLinearMap (CFC.sqrt S) x ∈ hermitianSumSlice S ↔
      x ∈ hermitianBetaDomain n K := by
  have h := hermitianConjugation_mem_sumSlice_iff (posDef_cfc_sqrt hS) x
  rwa [CFC.sqrt_mul_sqrt_self S hS.posSemidef.nonneg] at h

section Measurable
variable [MeasurableSpace K] [BorelSpace K] [PolishSpace K]

theorem measurableSet_posDef_of_isHermitian {Ω : Type*} [MeasurableSpace Ω]
    (f : Ω → Matrix (Fin n) (Fin n) K) (hf : Measurable f)
    (hH : ∀ x, (f x).IsHermitian) : MeasurableSet {x | (f x).PosDef} := by
  have hm := measurable_hermitian_eigenvalues f hH hf
  have hs : {x | (f x).PosDef} = {x | ∀ i, 0 < (hH x).eigenvalues i} := by
    ext x
    exact (hH x).posDef_iff_eigenvalues_pos
  rw [hs]
  convert! (MeasurableSet.iInter fun i : Fin n ↦
    (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ))).preimage
      ((measurable_pi_apply i).comp hm)) using 1
  ext x
  simp

theorem measurableSet_posDef_hermitianCoordinates :
    MeasurableSet (wishartPositiveDefiniteDomain n K) :=
  measurableSet_posDef_of_isHermitian hermitianMatrixOfCoordinates
    continuous_hermitianMatrixOfCoordinates.measurable hermitianMatrixOfCoordinates_isHermitian

theorem measurableSet_hermitianBetaDomain : MeasurableSet (hermitianBetaDomain n K) := by
  exact measurableSet_posDef_hermitianCoordinates.inter
    (measurableSet_posDef_of_isHermitian (fun x ↦ 1 - hermitianMatrixOfCoordinates x)
      (continuous_const.sub continuous_hermitianMatrixOfCoordinates).measurable
      (fun x ↦ Matrix.isHermitian_one.sub (hermitianMatrixOfCoordinates_isHermitian x)))

end Measurable

end A3Research
