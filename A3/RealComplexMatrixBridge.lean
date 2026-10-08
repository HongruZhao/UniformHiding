import A3.JacobiCommonScale
import A3.HermitianSpectrum

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section
namespace A3Research

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

def realMatrixComplexEmbedding {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) :
    Matrix (Fin n) (Fin m) ℂ := A.map Complex.ofRealHom

theorem realMatrixComplexEmbedding_mul {n m r : ℕ}
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin r) ℝ) :
    realMatrixComplexEmbedding (A * B) =
      realMatrixComplexEmbedding A * realMatrixComplexEmbedding B :=
  Matrix.map_mul (f := Complex.ofRealHom)

theorem realMatrixComplexEmbedding_add {n m : ℕ}
    (A B : Matrix (Fin n) (Fin m) ℝ) :
    realMatrixComplexEmbedding (A + B) =
      realMatrixComplexEmbedding A + realMatrixComplexEmbedding B := by
  ext i j
  simp [realMatrixComplexEmbedding]

theorem realMatrixComplexEmbedding_smul {n m : ℕ} (c : ℝ)
    (A : Matrix (Fin n) (Fin m) ℝ) :
    realMatrixComplexEmbedding (c • A) = c • realMatrixComplexEmbedding A := by
  ext i j
  simp [realMatrixComplexEmbedding, Matrix.smul_apply]

theorem realMatrixComplexEmbedding_conjTranspose {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) ℝ) :
    realMatrixComplexEmbedding A.conjTranspose =
      (realMatrixComplexEmbedding A).conjTranspose := by
  ext i j
  simp [realMatrixComplexEmbedding, Matrix.conjTranspose_apply]

theorem realMatrixComplexEmbedding_one (n : ℕ) :
    realMatrixComplexEmbedding (1 : Matrix (Fin n) (Fin n) ℝ) = 1 := by
  exact Complex.ofRealHom.mapMatrix.map_one

theorem realMatrixComplexEmbedding_isHermitian {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) :
    (realMatrixComplexEmbedding A).IsHermitian := by
  change (realMatrixComplexEmbedding A).conjTranspose = realMatrixComplexEmbedding A
  rw [← realMatrixComplexEmbedding_conjTranspose, hA.eq]

theorem realMatrixComplexEmbedding_posSemidef {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef) :
    (realMatrixComplexEmbedding A).PosSemidef := by
  let S := CFC.sqrt A
  have hS : S.IsHermitian := (CFC.sqrt_nonneg A).posSemidef.isHermitian
  have hsquare : S * S = A := CFC.sqrt_mul_sqrt_self A hA.nonneg
  have h := Matrix.posSemidef_self_mul_conjTranspose (realMatrixComplexEmbedding S)
  rw [← realMatrixComplexEmbedding_conjTranspose, hS.eq,
    ← realMatrixComplexEmbedding_mul, hsquare] at h
  exact h

theorem realMatrixComplexEmbedding_posDef {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) :
    (realMatrixComplexEmbedding A).PosDef := by
  apply (realMatrixComplexEmbedding_posSemidef hA.posSemidef).posDef_iff_isUnit.mpr
  exact hA.isUnit.map Complex.ofRealHom.mapMatrix

theorem realMatrixComplexEmbedding_inv {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) :
    (realMatrixComplexEmbedding A)⁻¹ = realMatrixComplexEmbedding A⁻¹ := by
  apply Matrix.inv_eq_right_inv
  rw [← realMatrixComplexEmbedding_mul,
    Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit),
    realMatrixComplexEmbedding_one]

theorem realMatrixComplexEmbedding_sqrt {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef) :
    CFC.sqrt (realMatrixComplexEmbedding A) = realMatrixComplexEmbedding (CFC.sqrt A) := by
  apply (CFC.sqrt_eq_iff _ _ (realMatrixComplexEmbedding_posSemidef hA).nonneg
    (realMatrixComplexEmbedding_posSemidef (CFC.sqrt_nonneg A).posSemidef).nonneg).mpr
  rw [← realMatrixComplexEmbedding_mul, CFC.sqrt_mul_sqrt_self A hA.nonneg]

def realHermitianCoordinatesEmbedding {n : ℕ} (x : HermitianCoordinates n ℝ) :
    HermitianCoordinates n ℂ := (x.1, fun ij ↦ (x.2 ij : ℂ))

theorem measurable_realHermitianCoordinatesEmbedding (n : ℕ) :
    Measurable (realHermitianCoordinatesEmbedding : HermitianCoordinates n ℝ → _) := by
  unfold realHermitianCoordinatesEmbedding
  fun_prop

theorem hermitianMatrixOfCoordinates_realEmbedding {n : ℕ} (x : HermitianCoordinates n ℝ) :
    hermitianMatrixOfCoordinates (realHermitianCoordinatesEmbedding x) =
      realMatrixComplexEmbedding (hermitianMatrixOfCoordinates x) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [realHermitianCoordinatesEmbedding, realMatrixComplexEmbedding]
  · by_cases hlt : i < j <;>
      simp [hermitianMatrixOfCoordinates, realHermitianCoordinatesEmbedding,
        realMatrixComplexEmbedding, hij, hlt]

theorem betaMatrixJacobiCoordinates_realEmbedding {n : ℕ}
    (p : HermitianCoordinates n ℝ × HermitianCoordinates n ℝ)
    (hsum : (hermitianMatrixOfCoordinates p.1 + hermitianMatrixOfCoordinates p.2).PosDef) :
    betaMatrixJacobiCoordinates
      (realHermitianCoordinatesEmbedding p.1, realHermitianCoordinatesEmbedding p.2) =
      realHermitianCoordinatesEmbedding (betaMatrixJacobiCoordinates p) := by
  apply (hermitianCoordinatesLinearEquiv n ℂ).injective
  apply Subtype.ext
  change hermitianMatrixOfCoordinates
    (betaMatrixJacobiCoordinates
      (realHermitianCoordinatesEmbedding p.1, realHermitianCoordinatesEmbedding p.2)) =
    hermitianMatrixOfCoordinates
      (realHermitianCoordinatesEmbedding (betaMatrixJacobiCoordinates p))
  unfold betaMatrixJacobiCoordinates
  rw [hermitianCoordinateConjugation_reconstruct,
    hermitianMatrixOfCoordinates_realEmbedding,
    hermitianMatrixOfCoordinates_realEmbedding,
    hermitianMatrixOfCoordinates_realEmbedding,
    hermitianCoordinateConjugation_reconstruct,
    ← realMatrixComplexEmbedding_add,
    realMatrixComplexEmbedding_sqrt hsum.posSemidef]
  have hS : (CFC.sqrt (hermitianMatrixOfCoordinates p.1 +
      hermitianMatrixOfCoordinates p.2)).PosDef := hsum.isStrictlyPositive.sqrt.posDef
  rw [realMatrixComplexEmbedding_inv hS,
    ← realMatrixComplexEmbedding_conjTranspose,
    ← realMatrixComplexEmbedding_mul, ← realMatrixComplexEmbedding_mul]

end A3Research
