import A1.DoubledRealCoordinates

open Matrix Complex
open scoped BigOperators ComplexOrder Matrix.Norms.Elementwise

noncomputable section
namespace A1Research

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

def doubledAugmentationMatrix (m : ℕ) : Matrix (DoubledIndex m) (DoubledIndex m) ℂ :=
  Matrix.fromBlocks 1 1 (Complex.I • (1 : Matrix (Fin m) (Fin m) ℂ))
    (-Complex.I • (1 : Matrix (Fin m) (Fin m) ℂ))

def augmentedComplexPair {m : ℕ} (T Z : Matrix (Fin m) (Fin m) ℂ) :
    Matrix (DoubledIndex m) (DoubledIndex m) ℂ :=
  Matrix.fromBlocks T (Z.map star) Z (T.map star)

theorem doubledAugmentation_conjTranspose_mul (m : ℕ) :
    (doubledAugmentationMatrix m).conjTranspose * doubledAugmentationMatrix m =
      (2 : ℂ) • (1 : Matrix (DoubledIndex m) (DoubledIndex m) ℂ) := by
  simp [doubledAugmentationMatrix, Matrix.fromBlocks_conjTranspose,
    Matrix.fromBlocks_multiply, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
    Complex.star_def, Complex.I_mul_I, ← Matrix.fromBlocks_one, ← Matrix.fromBlocks_smul]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.fromBlocks, Matrix.one_apply, Pi.smul_apply, smul_eq_mul] <;>
    split_ifs <;> norm_num

theorem doubledAugmentation_mul_conjTranspose (m : ℕ) :
    doubledAugmentationMatrix m * (doubledAugmentationMatrix m).conjTranspose =
      (2 : ℂ) • (1 : Matrix (DoubledIndex m) (DoubledIndex m) ℂ) := by
  simp [doubledAugmentationMatrix, Matrix.fromBlocks_conjTranspose,
    Matrix.fromBlocks_multiply, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
    Complex.star_def, Complex.I_mul_I, ← Matrix.fromBlocks_one, ← Matrix.fromBlocks_smul]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.fromBlocks, Matrix.one_apply, Pi.smul_apply, smul_eq_mul] <;>
    split_ifs <;> norm_num

theorem doubledAugmentation_isUnit (m : ℕ) : IsUnit (doubledAugmentationMatrix m) := by
  refine ⟨⟨doubledAugmentationMatrix m,
    (1 / 2 : ℂ) • (doubledAugmentationMatrix m).conjTranspose, ?_, ?_⟩, rfl⟩
  · rw [Matrix.mul_smul, doubledAugmentation_mul_conjTranspose, smul_smul]
    norm_num
  · rw [Matrix.smul_mul, doubledAugmentation_conjTranspose_mul, smul_smul]
    norm_num

/-- The augmented covariance is the literal congruence of the doubled real matrix. -/
theorem augmentedComplexPair_doubledParts {m : ℕ}
    (W : Matrix (DoubledIndex m) (DoubledIndex m) ℝ) :
    augmentedComplexPair (doubledHermitianPart W) (doubledSymmetricPart W) =
      (doubledAugmentationMatrix m).conjTranspose * W.map Complex.ofReal *
        doubledAugmentationMatrix m := by
  have hblocks : W.map Complex.ofReal =
      Matrix.fromBlocks (fun i j ↦ (W (.inl i) (.inl j) : ℂ))
        (fun i j ↦ (W (.inl i) (.inr j) : ℂ))
        (fun i j ↦ (W (.inr i) (.inl j) : ℂ))
        (fun i j ↦ (W (.inr i) (.inr j) : ℂ)) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> rfl
  rw [hblocks]
  simp only [doubledAugmentationMatrix, Matrix.fromBlocks_conjTranspose,
    Matrix.fromBlocks_multiply, Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [augmentedComplexPair, doubledHermitianPart, doubledSymmetricPart, Complex.star_def]
  all_goals ring_nf; simp [Complex.I_sq]
  all_goals ring

theorem doubledAugmentation_det_norm (m : ℕ) :
    star (doubledAugmentationMatrix m).det * (doubledAugmentationMatrix m).det =
      (2 : ℂ) ^ (2 * m) := by
  have h := congrArg Matrix.det (doubledAugmentation_conjTranspose_mul m)
  simp only [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_smul, Matrix.det_one,
    mul_one, Fintype.card_sum, Fintype.card_fin] at h
  simpa only [two_mul] using h

theorem augmentedComplexPair_doubledParts_det {m : ℕ}
    (W : Matrix (DoubledIndex m) (DoubledIndex m) ℝ) :
    (augmentedComplexPair (doubledHermitianPart W) (doubledSymmetricPart W)).det =
      (2 : ℂ) ^ (2 * m) * (W.det : ℂ) := by
  rw [augmentedComplexPair_doubledParts, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_conjTranspose]
  have hmap : (W.map Complex.ofReal).det = (W.det : ℂ) := (Complex.ofRealHom.map_det W).symm
  rw [hmap]
  calc
    star (doubledAugmentationMatrix m).det * (W.det : ℂ) * (doubledAugmentationMatrix m).det =
        (star (doubledAugmentationMatrix m).det * (doubledAugmentationMatrix m).det) *
          (W.det : ℂ) := by ring
    _ = _ := by rw [doubledAugmentation_det_norm]

theorem doubledReal_trace {m : ℕ}
    (W : Matrix (DoubledIndex m) (DoubledIndex m) ℝ) :
    W.trace = (doubledHermitianPart W).trace.re := by
  simp [Matrix.trace, Fintype.sum_sum_type, doubledHermitianPart, Finset.sum_add_distrib]

end A1Research
