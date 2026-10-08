import A2.CoordinateExceptionalSets
import A2.PolynomialRealInputNullity

open MeasureTheory Matrix
open LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

namespace A2Research

abbrev RealImagCoordinateIndex (N : ℕ) :=
  ComplexSymmetricCoordinateIndex N ⊕ ComplexSymmetricCoordinateIndex N

def realImagToCoordinates (N : ℕ) (x : RealImagCoordinateIndex N → ℝ) :
    ComplexSymmetricCoordinates N :=
  fun ij ↦ (x (.inl ij) : ℂ) + (x (.inr ij) : ℂ) * Complex.I

theorem measurePreserving_realImagToCoordinates (N : ℕ) :
    MeasurePreserving (realImagToCoordinates N)
      (volume : Measure (RealImagCoordinateIndex N → ℝ))
      (complexSymmetricCoordinateVolume N) := by
  let s := MeasurableEquiv.sumPiEquivProdPi
    (fun _ : RealImagCoordinateIndex N ↦ ℝ)
  let a := MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ
    (ComplexSymmetricCoordinateIndex N)
  let c := MeasurableEquiv.piCongrRight (fun _ : ComplexSymmetricCoordinateIndex N ↦
    Complex.measurableEquivRealProd.symm)
  have hs := volume_measurePreserving_sumPiEquivProdPi
    (fun _ : RealImagCoordinateIndex N ↦ ℝ)
  have ha := (volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ
    (ComplexSymmetricCoordinateIndex N)).symm
  have hc := volume_preserving_pi (fun _ : ComplexSymmetricCoordinateIndex N ↦
    Complex.volume_preserving_equiv_real_prod.symm)
  have h := hc.comp (ha.comp hs)
  convert h using 1
  · funext x ij
    apply Complex.ext <;>
      simp [realImagToCoordinates, Function.comp_def,
        MeasurableEquiv.sumPiEquivProdPi, MeasurableEquiv.arrowProdEquivProdArrow,
        Equiv.sumPiEquivProdPi, Equiv.arrowProdEquivProdArrow]
  · rfl

def complexCoordinatePolynomial {N : ℕ} (ij : ComplexSymmetricCoordinateIndex N) :
    MvPolynomial (RealImagCoordinateIndex N) ℂ :=
  MvPolynomial.X (.inl ij) + MvPolynomial.C Complex.I * MvPolynomial.X (.inr ij)

def conjugateCoordinatePolynomial {N : ℕ} (ij : ComplexSymmetricCoordinateIndex N) :
    MvPolynomial (RealImagCoordinateIndex N) ℂ :=
  MvPolynomial.X (.inl ij) - MvPolynomial.C Complex.I * MvPolynomial.X (.inr ij)

def symmetricRealImagPolynomialMatrix (N : ℕ) :
    Matrix (Fin N) (Fin N) (MvPolynomial (RealImagCoordinateIndex N) ℂ) :=
  fun i j ↦ if h : i ≤ j then complexCoordinatePolynomial ⟨(i, j), h⟩
    else complexCoordinatePolynomial ⟨(j, i), le_of_lt (lt_of_not_ge h)⟩

def conjugateSymmetricRealImagPolynomialMatrix (N : ℕ) :
    Matrix (Fin N) (Fin N) (MvPolynomial (RealImagCoordinateIndex N) ℂ) :=
  fun i j ↦ if h : i ≤ j then conjugateCoordinatePolynomial ⟨(i, j), h⟩
    else conjugateCoordinatePolynomial ⟨(j, i), le_of_lt (lt_of_not_ge h)⟩

theorem eval_symmetricRealImagPolynomialMatrix (N : ℕ)
    (x : RealImagCoordinateIndex N → ℝ) :
    (MvPolynomial.eval (fun i ↦ (x i : ℂ))).mapMatrix
        (symmetricRealImagPolynomialMatrix N) =
      complexSymmetricMatrixOfCoordinates (realImagToCoordinates N x) := by
  ext i j
  by_cases hij : i ≤ j <;>
    simp [symmetricRealImagPolynomialMatrix, complexSymmetricMatrixOfCoordinates,
      complexCoordinatePolynomial, realImagToCoordinates, hij, mul_comm]

theorem eval_conjugateSymmetricRealImagPolynomialMatrix (N : ℕ)
    (x : RealImagCoordinateIndex N → ℝ) :
    (MvPolynomial.eval (fun i ↦ (x i : ℂ))).mapMatrix
        (conjugateSymmetricRealImagPolynomialMatrix N) =
      (complexSymmetricMatrixOfCoordinates (realImagToCoordinates N x)).map star := by
  ext i j
  by_cases hij : i ≤ j <;>
    simp [conjugateSymmetricRealImagPolynomialMatrix, complexSymmetricMatrixOfCoordinates,
      conjugateCoordinatePolynomial, realImagToCoordinates, hij, mul_comm, sub_eq_add_neg]

def hermitianGapPolynomialMatrix (N : ℕ) :
    Matrix (Fin N) (Fin N) (MvPolynomial (RealImagCoordinateIndex N) ℂ) :=
  1 - (conjugateSymmetricRealImagPolynomialMatrix N).transpose *
    symmetricRealImagPolynomialMatrix N

theorem eval_hermitianGapPolynomialMatrix (N : ℕ)
    (x : RealImagCoordinateIndex N → ℝ) :
    (MvPolynomial.eval (fun i ↦ (x i : ℂ))).mapMatrix
        (hermitianGapPolynomialMatrix N) =
      coeHermitianGap (complexSymmetricMatrixOfCoordinates (realImagToCoordinates N x)) := by
  rw [hermitianGapPolynomialMatrix, map_sub, map_mul, map_one]
  have ht : (MvPolynomial.eval (fun i ↦ (x i : ℂ))).mapMatrix
      (conjugateSymmetricRealImagPolynomialMatrix N).transpose =
      ((MvPolynomial.eval (fun i ↦ (x i : ℂ))).mapMatrix
        (conjugateSymmetricRealImagPolynomialMatrix N)).transpose := rfl
  rw [ht, eval_conjugateSymmetricRealImagPolynomialMatrix,
    eval_symmetricRealImagPolynomialMatrix]
  rfl

end A2Research
