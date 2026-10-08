import A3.HermitianCoordinates
import A2.UnitaryCongruenceAlgebra

open Matrix Complex
open scoped BigOperators ComplexOrder Matrix.Norms.Elementwise

noncomputable section
namespace A1Research

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

abbrev DoubledIndex (m : ℕ) := Fin m ⊕ Fin m

def doubledHermitianPart {m : ℕ} (W : Matrix (DoubledIndex m) (DoubledIndex m) ℝ) :
    Matrix (Fin m) (Fin m) ℂ := fun i j ↦
  ((W (.inl i) (.inl j) + W (.inr i) (.inr j) : ℝ) : ℂ) +
    Complex.I * ((W (.inl i) (.inr j) - W (.inr i) (.inl j) : ℝ) : ℂ)

def doubledSymmetricPart {m : ℕ} (W : Matrix (DoubledIndex m) (DoubledIndex m) ℝ) :
    Matrix (Fin m) (Fin m) ℂ := fun i j ↦
  ((W (.inl i) (.inl j) - W (.inr i) (.inr j) : ℝ) : ℂ) +
    Complex.I * ((W (.inl i) (.inr j) + W (.inr i) (.inl j) : ℝ) : ℂ)

def complexPairRealMatrix {m : ℕ} (T Z : Matrix (Fin m) (Fin m) ℂ) :
    Matrix (DoubledIndex m) (DoubledIndex m) ℝ :=
  Matrix.fromBlocks
    (fun i j ↦ ((T i j).re + (Z i j).re) / 2)
    (fun i j ↦ ((T i j).im + (Z i j).im) / 2)
    (fun i j ↦ ((Z i j).im - (T i j).im) / 2)
    (fun i j ↦ ((T i j).re - (Z i j).re) / 2)

theorem complexPairRealMatrix_doubledParts {m : ℕ}
    (W : Matrix (DoubledIndex m) (DoubledIndex m) ℝ) :
    complexPairRealMatrix (doubledHermitianPart W) (doubledSymmetricPart W) = W := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [complexPairRealMatrix, doubledHermitianPart, doubledSymmetricPart] <;> ring

theorem doubledParts_complexPairRealMatrix {m : ℕ} (T Z : Matrix (Fin m) (Fin m) ℂ) :
    (doubledHermitianPart (complexPairRealMatrix T Z),
      doubledSymmetricPart (complexPairRealMatrix T Z)) = (T, Z) := by
  apply Prod.ext <;> ext i j <;> apply Complex.ext <;>
    simp [complexPairRealMatrix, doubledHermitianPart, doubledSymmetricPart] <;> ring

/-- The doubled-real and augmented complex coordinates are globally linearly equivalent. -/
def doubledRealComplexPairMatrixLinearEquiv (m : ℕ) :
    Matrix (DoubledIndex m) (DoubledIndex m) ℝ ≃ₗ[ℝ]
      Matrix (Fin m) (Fin m) ℂ × Matrix (Fin m) (Fin m) ℂ where
  toFun W := (doubledHermitianPart W, doubledSymmetricPart W)
  invFun x := complexPairRealMatrix x.1 x.2
  left_inv := complexPairRealMatrix_doubledParts
  right_inv := fun x ↦ doubledParts_complexPairRealMatrix x.1 x.2
  map_add' W V := by
    apply Prod.ext <;> ext i j <;> apply Complex.ext <;>
      simp [doubledHermitianPart, doubledSymmetricPart] <;> ring
  map_smul' r W := by
    apply Prod.ext <;> ext i j <;> apply Complex.ext <;>
      simp [doubledHermitianPart, doubledSymmetricPart, Complex.real_smul] <;> ring

theorem doubledHermitianPart_isHermitian {m : ℕ}
    (W : Matrix (DoubledIndex m) (DoubledIndex m) ℝ) (hW : W.IsSymm) :
    (doubledHermitianPart W).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  have h11 := hW.apply (.inl i) (.inl j)
  have h22 := hW.apply (.inr i) (.inr j)
  have h12 := hW.apply (.inl i) (.inr j)
  have h21 := hW.apply (.inr i) (.inl j)
  apply Complex.ext <;> simp only [doubledHermitianPart, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.star_def, Complex.conj_re, Complex.conj_im] <;>
    simp only [zero_mul, one_mul, mul_zero, zero_sub, zero_add, add_zero] <;> linarith

theorem doubledSymmetricPart_isSymm {m : ℕ}
    (W : Matrix (DoubledIndex m) (DoubledIndex m) ℝ) (hW : W.IsSymm) :
    (doubledSymmetricPart W).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  have h11 := hW.apply (.inl i) (.inl j)
  have h22 := hW.apply (.inr i) (.inr j)
  have h12 := hW.apply (.inl i) (.inr j)
  have h21 := hW.apply (.inr i) (.inl j)
  apply Complex.ext <;> simp [doubledSymmetricPart] <;> linarith

theorem complexPairRealMatrix_isSymm {m : ℕ} (T Z : Matrix (Fin m) (Fin m) ℂ)
    (hT : T.IsHermitian) (hZ : Z.IsSymm) : (complexPairRealMatrix T Z).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  rcases i with i | i <;> rcases j with j | j
  all_goals
    have ht := hT.apply i j
    have hz := hZ.apply i j
    have htr := congrArg Complex.re ht
    have hti := congrArg Complex.im ht
    have hzr := congrArg Complex.re hz
    have hzi := congrArg Complex.im hz
    simp only [Complex.star_def, Complex.conj_re, Complex.conj_im] at htr hti
    simp [complexPairRealMatrix]
    linarith

def doubledIndexEquiv (m : ℕ) : DoubledIndex m ≃ Fin (2 * m) :=
  finSumFinEquiv.trans (finCongr (by omega))

end A1Research
