import A2.TakagiCayley

open scoped Matrix ComplexOrder MatrixOrder

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

def takagiSkewHermitianSpace (N : ℕ) : Submodule ℝ (Matrix (Fin N) (Fin N) ℂ) where
  carrier := {H | H.conjTranspose = -H}
  zero_mem' := by simp
  add_mem' := by
    intro H K hH hK
    change (H + K).conjTranspose = -(H + K)
    rw [Matrix.conjTranspose_add, hH, hK]
    abel
  smul_mem' := by intro r H hH; simp only [Set.mem_setOf_eq] at *; simp [hH]

def takagiCayleyAngularTangent {N : ℕ} (H D : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  (2 : ℝ) • ((1 + H)⁻¹ * D * (1 - H)⁻¹)

def takagiCayleyAngularInverse {N : ℕ} (H D : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  (1 / 2 : ℝ) • ((1 + H) * D * (1 - H))

theorem takagiCayleyAngularTangent_skewHermitian {N : ℕ}
    (H D : Matrix (Fin N) (Fin N) ℂ) (hH : H.conjTranspose = -H)
    (hD : D.conjTranspose = -D) :
    (takagiCayleyAngularTangent H D).conjTranspose = -takagiCayleyAngularTangent H D := by
  unfold takagiCayleyAngularTangent
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_add, Matrix.conjTranspose_one, hH, hD]
  simp only [star_trivial, sub_neg_eq_add, Matrix.neg_mul, Matrix.mul_neg,
    smul_neg, Matrix.mul_assoc, sub_eq_add_neg, neg_neg]

theorem takagiCayleyAngularInverse_skewHermitian {N : ℕ}
    (H D : Matrix (Fin N) (Fin N) ℂ) (hH : H.conjTranspose = -H)
    (hD : D.conjTranspose = -D) :
    (takagiCayleyAngularInverse H D).conjTranspose = -takagiCayleyAngularInverse H D := by
  unfold takagiCayleyAngularInverse
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_sub, Matrix.conjTranspose_add, Matrix.conjTranspose_one, hH, hD]
  simp only [star_trivial, sub_neg_eq_add, Matrix.neg_mul, Matrix.mul_neg,
    smul_neg, Matrix.mul_assoc, sub_eq_add_neg, neg_neg]

theorem takagiCayleyAngularInverse_tangent {N : ℕ}
    (H D : Matrix (Fin N) (Fin N) ℂ) (hH : H.conjTranspose = -H) :
    takagiCayleyAngularInverse H (takagiCayleyAngularTangent H D) = D := by
  have hp := (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_one_add_skewHermitian H hH)
  have hm := (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_one_sub_skewHermitian H hH)
  simp only [takagiCayleyAngularInverse, takagiCayleyAngularTangent,
    Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  norm_num
  simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hp, one_mul]
  exact Matrix.nonsing_inv_mul_cancel_right _ _ hm

theorem takagiCayleyAngularTangent_inverse {N : ℕ}
    (H D : Matrix (Fin N) (Fin N) ℂ) (hH : H.conjTranspose = -H) :
    takagiCayleyAngularTangent H (takagiCayleyAngularInverse H D) = D := by
  have hp := (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_one_add_skewHermitian H hH)
  have hm := (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_one_sub_skewHermitian H hH)
  simp only [takagiCayleyAngularInverse, takagiCayleyAngularTangent,
    Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  norm_num
  simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hp, one_mul]
  exact Matrix.mul_nonsing_inv_cancel_right _ _ hm

def takagiCayleyAngularEquiv {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ)
    (hH : H.conjTranspose = -H) : takagiSkewHermitianSpace N ≃ₗ[ℝ] takagiSkewHermitianSpace N where
  toFun D := ⟨takagiCayleyAngularTangent H D,
    takagiCayleyAngularTangent_skewHermitian H D hH D.property⟩
  invFun D := ⟨takagiCayleyAngularInverse H D,
    takagiCayleyAngularInverse_skewHermitian H D hH D.property⟩
  left_inv D := Subtype.ext (takagiCayleyAngularInverse_tangent H D hH)
  right_inv D := Subtype.ext (takagiCayleyAngularTangent_inverse H D hH)
  map_add' D E := by
    apply Subtype.ext
    simp [takagiCayleyAngularTangent, Matrix.mul_add, Matrix.add_mul, smul_add]
  map_smul' a D := by
    apply Subtype.ext
    change (2 : ℝ) • ((1 + H)⁻¹ * (a • (D : Matrix (Fin N) (Fin N) ℂ)) * (1 - H)⁻¹) =
      a • ((2 : ℝ) • ((1 + H)⁻¹ * (D : Matrix (Fin N) (Fin N) ℂ) * (1 - H)⁻¹))
    simp only [Matrix.mul_smul, Matrix.smul_mul]
    exact smul_comm _ _ _

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
