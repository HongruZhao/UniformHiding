import A1.DoubledAugmentedGram
import A1.DoubledRealCoordinateEquiv
import A1.RealComplexPosDef
import A1.NormalizedTransposeGram
import A3.BetaMatrixAlgebra

open Matrix Complex
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section
namespace A1Research

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

def normalizedAugmentedPair {m : ℕ} (C : Matrix (Fin m) (Fin m) ℂ) :
    Matrix (DoubledIndex m) (DoubledIndex m) ℂ :=
  Matrix.fromBlocks 1 C.conjTranspose C 1

theorem normalizedAugmentedPair_det {m : ℕ} (C : Matrix (Fin m) (Fin m) ℂ) :
    (normalizedAugmentedPair C).det = (1 - C.conjTranspose * C).det :=
  Matrix.det_fromBlocks_one₂₂ _ _ _

theorem normalizedAugmentedPair_posDef_iff {m : ℕ}
    (C : Matrix (Fin m) (Fin m) ℂ) :
    (normalizedAugmentedPair C).PosDef ↔ (1 - C.conjTranspose * C).PosDef := by
  letI : Invertible (1 : Matrix (Fin m) (Fin m) ℂ) := ⟨1, by simp, by simp⟩
  have hpsd : (normalizedAugmentedPair C).PosSemidef ↔
      (1 - C.conjTranspose * C).PosSemidef := by
    simpa [normalizedAugmentedPair] using
      (Matrix.PosDef.fromBlocks₂₂ (1 : Matrix (Fin m) (Fin m) ℂ)
        C.conjTranspose Matrix.PosDef.one)
  constructor
  · intro h
    apply (hpsd.mp h.posSemidef).posDef_iff_det_ne_zero.mpr
    rw [← normalizedAugmentedPair_det]
    exact h.det_pos.ne'
  · intro h
    apply (hpsd.mpr h.posSemidef).posDef_iff_det_ne_zero.mpr
    rw [normalizedAugmentedPair_det]
    exact h.det_pos.ne'

def augmentedSqrtMatrix {m : ℕ} (L : Matrix (Fin m) (Fin m) ℂ) :
    Matrix (DoubledIndex m) (DoubledIndex m) ℂ := Matrix.fromBlocks L 0 0 L.transpose

theorem augmentedSqrtMatrix_isUnit {m : ℕ} {L : Matrix (Fin m) (Fin m) ℂ}
    (hL : IsUnit L) : IsUnit (augmentedSqrtMatrix L) :=
  Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨hL, by simpa only [Matrix.isUnit_transpose] using hL⟩

theorem augmentedComplexPair_of_hermitian_symm {m : ℕ}
    {T Z : Matrix (Fin m) (Fin m) ℂ} (hT : T.IsHermitian) (hZ : Z.IsSymm) :
    augmentedComplexPair T Z = Matrix.fromBlocks T Z.conjTranspose Z T.transpose := by
  have hTm : T.map star = T.transpose := by rw [← Matrix.conjTranspose_transpose, hT.eq]
  have hZm : Z.map star = Z.conjTranspose := by
    rw [← Matrix.transpose_conjTranspose, hZ]
  simp only [augmentedComplexPair, hTm, hZm]

theorem augmentedComplexPair_sqrt_congruence {m : ℕ}
    {L C : Matrix (Fin m) (Fin m) ℂ} (hL : L.IsHermitian) (hC : C.IsSymm) :
    augmentedComplexPair (L * L) (L.transpose * C * L) =
      augmentedSqrtMatrix L * normalizedAugmentedPair C *
        (augmentedSqrtMatrix L).conjTranspose := by
  have hT : (L * L).IsHermitian := by
    change (L * L).conjTranspose = L * L
    rw [Matrix.conjTranspose_mul, hL.eq]
  have hZ : (L.transpose * C * L).IsSymm := by
    simpa only [Matrix.transpose_transpose] using
      (A2Research.isSymm_matrixCongruence L.transpose C hC)
  rw [augmentedComplexPair_of_hermitian_symm hT hZ]
  simp only [augmentedSqrtMatrix, normalizedAugmentedPair, Matrix.fromBlocks_conjTranspose,
    Matrix.fromBlocks_multiply, Matrix.conjTranspose_zero, Matrix.conjTranspose_mul,
    hL.eq, hL.transpose.eq, Matrix.transpose_mul, Matrix.mul_zero, Matrix.zero_mul,
    zero_add, add_zero, Matrix.mul_one, Matrix.one_mul, mul_assoc]

theorem augmentedComplexPair_sqrt_posDef_iff {m : ℕ}
    {L C : Matrix (Fin m) (Fin m) ℂ} (hL : L.PosDef) (hC : C.IsSymm) :
    (augmentedComplexPair (L * L) (L.transpose * C * L)).PosDef ↔
      (1 - C.conjTranspose * C).PosDef := by
  rw [augmentedComplexPair_sqrt_congruence hL.isHermitian hC]
  rw [← Matrix.star_eq_conjTranspose,
    (augmentedSqrtMatrix_isUnit hL.isUnit).posDef_star_right_conjugate_iff]
  exact normalizedAugmentedPair_posDef_iff C

theorem augmentedComplexPair_sqrt_det {m : ℕ}
    {L C : Matrix (Fin m) (Fin m) ℂ} (hL : L.IsHermitian) (hC : C.IsSymm) :
    (augmentedComplexPair (L * L) (L.transpose * C * L)).det =
      ((L * L).det) ^ 2 * (1 - C.conjTranspose * C).det := by
  rw [augmentedComplexPair_sqrt_congruence hL hC, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_conjTranspose, augmentedSqrtMatrix, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_transpose, normalizedAugmentedPair_det]
  have hd : star L.det = L.det := by
    rw [← Matrix.det_conjTranspose, hL.eq]
  simp only [star_mul, hd, Matrix.det_mul]
  ring

theorem normalizedComplexPairOverlap_isSymm {m : ℕ}
    {T Z : Matrix (Fin m) (Fin m) ℂ} (hZ : Z.IsSymm) :
    (normalizedComplexPairOverlap T Z).IsSymm := by
  have hi : (CFC.sqrt T).transpose⁻¹ = ((CFC.sqrt T)⁻¹).transpose :=
    (Matrix.transpose_nonsing_inv _).symm
  unfold normalizedComplexPairOverlap
  rw [hi]
  simpa only [Matrix.transpose_transpose] using
    (A2Research.isSymm_matrixCongruence ((CFC.sqrt T)⁻¹).transpose Z hZ)

theorem normalizedComplexPairOverlap_recover {m : ℕ}
    {T Z : Matrix (Fin m) (Fin m) ℂ} (hT : T.PosDef) :
    (CFC.sqrt T).transpose * normalizedComplexPairOverlap T Z * CFC.sqrt T = Z := by
  let L := CFC.sqrt T
  have hL : IsUnit L := (A3Research.posDef_cfc_sqrt hT).isUnit
  have hLt : IsUnit L.transpose := by simpa only [Matrix.isUnit_transpose] using hL
  unfold normalizedComplexPairOverlap
  change L.transpose * (L.transpose⁻¹ * Z * L⁻¹) * L = Z
  rw [← mul_assoc, ← mul_assoc,
    Matrix.mul_nonsing_inv L.transpose ((Matrix.isUnit_iff_isUnit_det _).mp hLt),
    one_mul, mul_assoc,
    Matrix.nonsing_inv_mul L ((Matrix.isUnit_iff_isUnit_det _).mp hL), mul_one]

end A1Research
