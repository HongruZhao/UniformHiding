import A3.HermitianSpectrum
import A3.PolynomialRCLikeRealInputNullity
import Mathlib.RingTheory.Polynomial.Resultant.Basic

open scoped BigOperators Matrix.Norms.Elementwise
open Matrix MeasureTheory Polynomial
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace A3Research

variable {n : ℕ} {K : Type*} [RCLike K]

abbrev HermitianRealCoordinateIndex (n : ℕ) (K : Type*) [RCLike K] :=
  Fin (Module.finrank ℝ (HermitianCoordinates n K))

def hermitianRealBasis (n : ℕ) (K : Type*) [RCLike K] :
    Module.Basis (HermitianRealCoordinateIndex n K) ℝ (HermitianCoordinates n K) :=
  Module.finBasis ℝ (HermitianCoordinates n K)

def hermitianBasisPolynomialMatrix (n : ℕ) (K : Type*) [RCLike K] :
    Matrix (Fin n) (Fin n) (MvPolynomial (HermitianRealCoordinateIndex n K) K) := by
  classical
  exact fun i j ↦ ∑ k, MvPolynomial.C
    (hermitianMatrixOfCoordinates (hermitianRealBasis n K k) i j) * MvPolynomial.X k

theorem eval_hermitianBasisPolynomialMatrix (x : HermitianRealCoordinateIndex n K → ℝ) :
    (MvPolynomial.eval (fun k ↦ (x k : K))).mapMatrix
      (hermitianBasisPolynomialMatrix n K) =
      hermitianMatrixOfCoordinates ((hermitianRealBasis n K).equivFun.symm x) := by
  classical
  ext i j
  change MvPolynomial.eval (fun k ↦ (x k : K)) (hermitianBasisPolynomialMatrix n K i j) = _
  simp only [hermitianBasisPolynomialMatrix, map_sum, map_mul,
    MvPolynomial.eval_C, MvPolynomial.eval_X, Module.Basis.equivFun_symm_apply]
  rw [show hermitianMatrixOfCoordinates (∑ k, x k • hermitianRealBasis n K k) =
      ∑ k, x k • hermitianMatrixOfCoordinates (hermitianRealBasis n K k) from
    by
      change (hermitianMatrixOfCoordinatesLinearMap n K) (∑ k, x k • hermitianRealBasis n K k) = _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro k _
      exact (hermitianMatrixOfCoordinatesLinearMap n K).map_smul (x k) _]
  simp only [Matrix.sum_apply, Matrix.smul_apply, RCLike.real_smul_eq_coe_mul]
  apply Finset.sum_congr rfl
  intro k _
  exact mul_comm _ _

def hermitianSpectrumResultantPolynomial (n : ℕ) (K : Type*) [RCLike K] :
    MvPolynomial (HermitianRealCoordinateIndex n K) K :=
  let p := (hermitianBasisPolynomialMatrix n K).charpoly
  Polynomial.resultant p p.derivative n (n - 1)

theorem eval_hermitianSpectrumResultantPolynomial (x : HermitianRealCoordinateIndex n K → ℝ) :
    MvPolynomial.eval (fun i ↦ (x i : K)) (hermitianSpectrumResultantPolynomial n K) =
      let p := (hermitianMatrixOfCoordinates ((hermitianRealBasis n K).equivFun.symm x)).charpoly
      Polynomial.resultant p p.derivative n (n - 1) := by
  dsimp only [hermitianSpectrumResultantPolynomial]
  rw [← Polynomial.resultant_map_map, ← Polynomial.derivative_map]
  have hmap := Matrix.charpoly_map (hermitianBasisPolynomialMatrix n K)
    (MvPolynomial.eval (fun i ↦ (x i : K)))
  have hM := eval_hermitianBasisPolynomialMatrix (n := n) (K := K) x
  change (hermitianBasisPolynomialMatrix n K).map
    (MvPolynomial.eval (fun i ↦ (x i : K))) = _ at hM
  rw [← hmap, hM]

theorem hermitianSpectrumResultantPolynomial_ne_zero (n : ℕ) (K : Type*) [RCLike K] :
    hermitianSpectrumResultantPolynomial n K ≠ 0 := by
  let H : Matrix (Fin n) (Fin n) K := Matrix.diagonal (fun i ↦ (i.val : K))
  have hH : H.IsHermitian := by
    apply Matrix.isHermitian_diagonal_iff.mpr
    intro i
    simp only [IsSelfAdjoint, star_natCast]
  let x := (hermitianRealBasis n K).equivFun (hermitianCoordinateProjection H)
  have hM : hermitianMatrixOfCoordinates ((hermitianRealBasis n K).equivFun.symm x) = H := by
    rw [show (hermitianRealBasis n K).equivFun.symm x = hermitianCoordinateProjection H from
      (hermitianRealBasis n K).equivFun.symm_apply_apply _]
    exact hermitianMatrixOfCoordinates_projection H hH
  have hsep : H.charpoly.Separable := by
    rw [Matrix.charpoly_diagonal]
    exact Polynomial.separable_prod_X_sub_C_iff.mpr (fun i j h ↦ Fin.ext (by exact_mod_cast h))
  have hres : Polynomial.resultant H.charpoly H.charpoly.derivative n (n - 1) ≠ 0 := by
    have hc := Polynomial.resultant_ne_zero H.charpoly H.charpoly.derivative
      ((Polynomial.separable_def _).mp hsep)
    simpa only [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin,
      Polynomial.natDegree_derivative] using hc
  intro h
  have hv := congrArg (MvPolynomial.eval (fun i ↦ (x i : K))) h
  rw [eval_hermitianSpectrumResultantPolynomial, hM, map_zero] at hv
  exact hres hv

theorem canonicalHermitianSpectrum_injective_of_resultant_ne_zero
    (x : HermitianCoordinates n K)
    (hres : Polynomial.resultant (hermitianMatrixOfCoordinates x).charpoly
      (hermitianMatrixOfCoordinates x).charpoly.derivative n (n - 1) ≠ 0) :
    Function.Injective (canonicalHermitianSpectrum x) := by
  have hres' : Polynomial.resultant (hermitianMatrixOfCoordinates x).charpoly
      (hermitianMatrixOfCoordinates x).charpoly.derivative ≠ 0 := by
    simpa only [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin,
      Polynomial.natDegree_derivative] using hres
  have hsep : (hermitianMatrixOfCoordinates x).charpoly.Separable :=
    (Polynomial.separable_def _).mpr
      ((Polynomial.isUnit_resultant_iff_isCoprime
        (Matrix.charpoly_monic (hermitianMatrixOfCoordinates x))).mp
          (isUnit_iff_ne_zero.mpr hres'))
  rw [(hermitianMatrixOfCoordinates_isHermitian x).charpoly_eq] at hsep
  have hinj := Polynomial.separable_prod_X_sub_C_iff.mp hsep
  intro i j hij
  apply hinj
  exact congrArg (algebraMap ℝ K) hij

section Measure
variable [MeasureSpace K] [BorelSpace K] [PolishSpace K]
  [(hermitianCoordinateVolume n K).IsAddHaarMeasure]

theorem measurableSet_injective_canonicalHermitianSpectrum :
    MeasurableSet {x : HermitianCoordinates n K | Function.Injective (canonicalHermitianSpectrum x)} := by
  have hspectrum := measurable_canonicalHermitianSpectrum (n := n) (K := K)
  simp only [Function.Injective, Set.setOf_forall]
  refine MeasurableSet.iInter fun i ↦ MeasurableSet.iInter fun j ↦ ?_
  by_cases hij : i = j
  · simp only [hij, implies_true, Set.setOf_true]
    exact MeasurableSet.univ
  · simp only [hij, imp_false]
    simpa only [Set.compl_setOf, Function.comp_def] using
      (((measurable_pi_apply i).comp hspectrum).eq
        ((measurable_pi_apply j).comp hspectrum)).setOf.compl

/-- Repeated eigenvalues form an actual null set in independent Hermitian coordinates. -/
theorem ae_injective_canonicalHermitianSpectrum :
    ∀ᵐ x ∂(hermitianCoordinateVolume n K), Function.Injective (canonicalHermitianSpectrum x) := by
  let e := (hermitianRealBasis n K).equivFun.toContinuousLinearEquiv
  have hpoly := ae_rclikeMvPolynomial_eval_realInput_ne_zero K
    (hermitianSpectrumResultantPolynomial n K) (hermitianSpectrumResultantPolynomial_ne_zero n K)
  have hsrc : ∀ᵐ y ∂(volume : Measure (HermitianRealCoordinateIndex n K → ℝ)),
      Function.Injective (canonicalHermitianSpectrum (e.symm y)) := by
    filter_upwards [hpoly] with y hy
    apply canonicalHermitianSpectrum_injective_of_resultant_ne_zero
    simpa only [eval_hermitianSpectrumResultantPolynomial, e,
      LinearEquiv.coe_toContinuousLinearEquiv_symm'] using hy
  have hac : Measure.map e (hermitianCoordinateVolume n K) ≪
      (volume : Measure (HermitianRealCoordinateIndex n K → ℝ)) :=
    Measure.absolutelyContinuous_isAddHaarMeasure _ _
  have hmap := hac.ae_le hsrc
  have hset : MeasurableSet {y : HermitianRealCoordinateIndex n K → ℝ |
      Function.Injective (canonicalHermitianSpectrum (e.symm y))} :=
    measurableSet_injective_canonicalHermitianSpectrum.preimage e.symm.continuous.measurable
  have hback := (ae_map_iff e.continuous.measurable.aemeasurable hset).mp hmap
  filter_upwards [hback] with x hx
  simpa only [e.symm_apply_apply] using hx

end Measure
end A3Research
