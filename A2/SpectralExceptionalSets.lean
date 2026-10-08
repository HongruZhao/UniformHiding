import A2.RealImagCoordinates
import A2.SpectrumMeasurable
import A2.SpectrumPositivity
import Mathlib.RingTheory.Polynomial.Resultant.Basic

open scoped BigOperators
open MeasureTheory Matrix Polynomial
open LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

namespace A2Research

/-- The fixed-degree resultant detects repeated roots of the literal Hermitian
gap's characteristic polynomial, with polynomial dependence on real coordinates. -/
def gapSpectrumResultantPolynomial (N : ℕ) :
    MvPolynomial (RealImagCoordinateIndex N) ℂ :=
  let p := (hermitianGapPolynomialMatrix N).charpoly
  Polynomial.resultant p p.derivative N (N - 1)

theorem eval_gapSpectrumResultantPolynomial (N : ℕ)
    (x : RealImagCoordinateIndex N → ℝ) :
    MvPolynomial.eval (fun i ↦ (x i : ℂ)) (gapSpectrumResultantPolynomial N) =
      let p := (coeHermitianGap
        (complexSymmetricMatrixOfCoordinates (realImagToCoordinates N x))).charpoly
      Polynomial.resultant p p.derivative N (N - 1) := by
  dsimp only [gapSpectrumResultantPolynomial]
  rw [← Polynomial.resultant_map_map, ← Polynomial.derivative_map]
  have hmap := Matrix.charpoly_map (hermitianGapPolynomialMatrix N)
    (MvPolynomial.eval (fun i ↦ (x i : ℂ)))
  have hM := eval_hermitianGapPolynomialMatrix N x
  change (hermitianGapPolynomialMatrix N).map
    (MvPolynomial.eval (fun i ↦ (x i : ℂ))) = _ at hM
  rw [← hmap, hM]

def distinctDiagonalRealImagCoordinates (N : ℕ) : RealImagCoordinateIndex N → ℝ :=
  Sum.elim (fun ij ↦ if ij.1.1 = ij.1.2 then (ij.1.1.val : ℝ) + 1 else 0) (fun _ ↦ 0)

theorem matrixOf_distinctDiagonalRealImagCoordinates (N : ℕ) :
    complexSymmetricMatrixOfCoordinates
      (realImagToCoordinates N (distinctDiagonalRealImagCoordinates N)) =
      Matrix.diagonal (fun i : Fin N ↦ ((i.val : ℝ) + 1 : ℂ)) := by
  ext i j
  by_cases hij : i ≤ j <;> by_cases heq : i = j <;>
    simp [complexSymmetricMatrixOfCoordinates, realImagToCoordinates,
      distinctDiagonalRealImagCoordinates, hij, heq, Matrix.diagonal_apply, eq_comm]

theorem gapOf_distinctDiagonalRealImagCoordinates (N : ℕ) :
    coeHermitianGap (complexSymmetricMatrixOfCoordinates
      (realImagToCoordinates N (distinctDiagonalRealImagCoordinates N))) =
      Matrix.diagonal (fun i : Fin N ↦ (1 - (((i.val : ℝ) + 1 : ℂ) ^ 2))) := by
  rw [matrixOf_distinctDiagonalRealImagCoordinates]
  simp [coeHermitianGap, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
    pow_two, ← Matrix.diagonal_one, ← Matrix.diagonal_sub]

theorem distinctDiagonalGapValues_injective (N : ℕ) :
    Function.Injective (fun i : Fin N ↦ (1 - (((i.val : ℝ) + 1 : ℂ) ^ 2))) := by
  intro i j h
  have hre := congrArg Complex.re h
  simp [pow_two, Complex.mul_re] at hre
  have hi : 0 ≤ (i.val : ℝ) := Nat.cast_nonneg _
  have hj : 0 ≤ (j.val : ℝ) := Nat.cast_nonneg _
  have hval : (i.val : ℝ) = (j.val : ℝ) := by nlinarith
  exact Fin.ext (by exact_mod_cast hval)

theorem gapSpectrumResultantPolynomial_ne_zero (N : ℕ) :
    gapSpectrumResultantPolynomial N ≠ 0 := by
  let x := distinctDiagonalRealImagCoordinates N
  let A := coeHermitianGap (complexSymmetricMatrixOfCoordinates (realImagToCoordinates N x))
  have hsep : A.charpoly.Separable := by
    dsimp only [A, x]
    rw [gapOf_distinctDiagonalRealImagCoordinates, Matrix.charpoly_diagonal]
    exact Polynomial.separable_prod_X_sub_C_iff.mpr (distinctDiagonalGapValues_injective N)
  have hres : Polynomial.resultant A.charpoly A.charpoly.derivative N (N - 1) ≠ 0 := by
    have hc := Polynomial.resultant_ne_zero A.charpoly A.charpoly.derivative
      ((Polynomial.separable_def _).mp hsep)
    simpa only [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin,
      Polynomial.natDegree_derivative] using hc
  intro h
  have hv := congrArg (MvPolynomial.eval (fun i ↦ (x i : ℂ))) h
  rw [eval_gapSpectrumResultantPolynomial, map_zero] at hv
  exact hres hv

/-- Nonzero characteristic-resultant implies distinct literal Mathlib eigenvalues. -/
theorem eigenvalues_injective_of_gapResultant_ne_zero {N : ℕ}
    (C : Matrix (Fin N) (Fin N) ℂ)
    (hres : Polynomial.resultant (coeHermitianGap C).charpoly
      (coeHermitianGap C).charpoly.derivative N (N - 1) ≠ 0) :
    Function.Injective (canonicalGapSquaredSpectrum N C) := by
  have hres' : Polynomial.resultant (coeHermitianGap C).charpoly
      (coeHermitianGap C).charpoly.derivative ≠ 0 := by
    simpa only [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin,
      Polynomial.natDegree_derivative] using hres
  have hsep : (coeHermitianGap C).charpoly.Separable :=
    (Polynomial.separable_def _).mpr
      ((Polynomial.isUnit_resultant_iff_isCoprime
        (Matrix.charpoly_monic (coeHermitianGap C))).mp (isUnit_iff_ne_zero.mpr hres'))
  rw [(coeHermitianGap_isHermitian C).charpoly_eq] at hsep
  have hinj := Polynomial.separable_prod_X_sub_C_iff.mp hsep
  intro i j hij
  apply hinj
  dsimp only [canonicalGapSquaredSpectrum] at hij
  have hv : (coeHermitianGap_isHermitian C).eigenvalues i =
      (coeHermitianGap_isHermitian C).eigenvalues j := by linarith only [hij]
  exact congrArg (algebraMap ℝ ℂ) hv

/-- The regular squared-Takagi spectrum has no collisions almost everywhere
for the literal independent complex-symmetric coordinates. -/
theorem ae_injective_canonicalGapSquaredSpectrum_coordinateVolume (N : ℕ) :
    ∀ᵐ x ∂(complexSymmetricCoordinateVolume N),
      Function.Injective (canonicalGapSquaredSpectrum N
        (complexSymmetricMatrixOfCoordinates x)) := by
  have hpoly := ae_complexMvPolynomial_eval_realInput_ne_zero
    (gapSpectrumResultantPolynomial N) (gapSpectrumResultantPolynomial_ne_zero N)
  have hspectrum := (measurable_canonicalGapSquaredSpectrum N).comp
    (measurable_complexSymmetricMatrixOfCoordinates N)
  have hs : MeasurableSet {x : ComplexSymmetricCoordinates N |
      Function.Injective (canonicalGapSquaredSpectrum N
        (complexSymmetricMatrixOfCoordinates x))} := by
    simp only [Function.Injective, Set.setOf_forall]
    refine MeasurableSet.iInter fun i ↦ MeasurableSet.iInter fun j ↦ ?_
    by_cases hij : i = j
    · simp only [hij, implies_true, Set.setOf_true]
      exact MeasurableSet.univ
    · simp only [hij, imp_false]
      simpa only [Set.compl_setOf, Function.comp_def] using
        (((measurable_pi_apply i).comp hspectrum).eq
          ((measurable_pi_apply j).comp hspectrum)).setOf.compl
  have hsrc : ∀ᵐ x ∂(volume : Measure (RealImagCoordinateIndex N → ℝ)),
      Function.Injective (canonicalGapSquaredSpectrum N
        (complexSymmetricMatrixOfCoordinates (realImagToCoordinates N x))) := by
    filter_upwards [hpoly] with x hx
    rw [eval_gapSpectrumResultantPolynomial] at hx
    exact eigenvalues_injective_of_gapResultant_ne_zero _ hx
  rw [← (measurePreserving_realImagToCoordinates N).map_eq]
  exact (ae_map_iff (measurePreserving_realImagToCoordinates N).measurable.aemeasurable hs).mpr hsrc

theorem ae_positive_injective_canonicalGapSquaredSpectrum_coordinateVolume (N : ℕ) :
    ∀ᵐ x ∂(complexSymmetricCoordinateVolume N),
      (∀ i, 0 < canonicalGapSquaredSpectrum N (complexSymmetricMatrixOfCoordinates x) i) ∧
      Function.Injective (canonicalGapSquaredSpectrum N (complexSymmetricMatrixOfCoordinates x)) := by
  filter_upwards [ae_det_ne_zero_complexSymmetricCoordinateVolume N,
    ae_injective_canonicalGapSquaredSpectrum_coordinateVolume N] with x hdet hinj
  exact ⟨fun i ↦ canonicalGapSquaredSpectrum_pos_of_det_ne_zero _ hdet i, hinj⟩

theorem ae_positive_injective_canonicalGapSquaredSpectrum_matrixVolume (N : ℕ) :
    ∀ᵐ C ∂(complexSymmetricMatrixVolume N),
      (∀ i, 0 < canonicalGapSquaredSpectrum N C i) ∧
      Function.Injective (canonicalGapSquaredSpectrum N C) := by
  let P : Matrix (Fin N) (Fin N) ℂ → Prop := fun C ↦
    (∀ i, 0 < canonicalGapSquaredSpectrum N C i) ∧
      Function.Injective (canonicalGapSquaredSpectrum N C)
  have hs : MeasurableSet {C | P C} := by
    dsimp only [P, Function.Injective]
    simp only [Set.setOf_and, Set.setOf_forall]
    refine MeasurableSet.inter ?_ ?_
    · exact MeasurableSet.iInter fun i ↦ measurableSet_lt measurable_const
        ((measurable_pi_apply i).comp (measurable_canonicalGapSquaredSpectrum N))
    · refine MeasurableSet.iInter fun i ↦ MeasurableSet.iInter fun j ↦ ?_
      by_cases hij : i = j
      · simp only [hij, implies_true, Set.setOf_true]
        exact MeasurableSet.univ
      · simp only [hij, imp_false]
        simpa only [Set.compl_setOf, Function.comp_def] using
          (((measurable_pi_apply i).comp (measurable_canonicalGapSquaredSpectrum N)).eq
            ((measurable_pi_apply j).comp (measurable_canonicalGapSquaredSpectrum N))).setOf.compl
  rw [complexSymmetricMatrixVolume]
  exact (ae_map_iff (measurable_complexSymmetricMatrixOfCoordinates N).aemeasurable hs).mpr
    (ae_positive_injective_canonicalGapSquaredSpectrum_coordinateVolume N)

end A2Research
