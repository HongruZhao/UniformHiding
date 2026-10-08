import A2.TakagiCayleyChart
import A2.MatrixInverseDerivative

open scoped Matrix Matrix.Norms.Elementwise

noncomputable section

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

def takagiCayleyMatrixDerivative {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin N) (Fin N) ℂ →L[ℝ] Matrix (Fin N) (Fin N) ℂ :=
  (2 : ℝ) • ((mulLeftLinearMap (Fin N) ℝ (1 - H)⁻¹).toContinuousLinearMap.comp
    (mulRightLinearMap (Fin N) ℝ (1 - H)⁻¹).toContinuousLinearMap)

@[simp] theorem takagiCayleyMatrixDerivative_apply {N : ℕ}
    (H D : Matrix (Fin N) (Fin N) ℂ) :
    takagiCayleyMatrixDerivative H D = (2 : ℝ) • ((1 - H)⁻¹ * D * (1 - H)⁻¹) := by
  simp [takagiCayleyMatrixDerivative, Matrix.mul_assoc]

theorem takagiCayleyMatrixDerivative_product_rule {N : ℕ}
    (H D : Matrix (Fin N) (Fin N) ℂ) (hH : H.conjTranspose = -H) :
    takagiCayleyMatrixDerivative H D =
      D * (1 - H)⁻¹ + (1 + H) * ((1 - H)⁻¹ * D * (1 - H)⁻¹) := by
  rw [takagiCayleyMatrixDerivative_apply]
  have hc := takagiCayley_add_one H hH
  calc
    (2 : ℝ) • ((1 - H)⁻¹ * D * (1 - H)⁻¹) =
        (takagiCayley H + 1) * D * (1 - H)⁻¹ := by
      rw [hc, two_smul ℝ]
      noncomm_ring
    _ = D * (1 - H)⁻¹ + (1 + H) * ((1 - H)⁻¹ * D * (1 - H)⁻¹) := by
      unfold takagiCayley
      noncomm_ring

theorem hasFDerivAt_takagiCayley {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ)
    (hH : H.conjTranspose = -H) :
    HasFDerivAt (@takagiCayley N) (takagiCayleyMatrixDerivative H) H := by
  have hd : (1 - H).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (isUnit_one_sub_skewHermitian H hH)).ne_zero
  have hminus : HasFDerivAt (fun K : Matrix (Fin N) (Fin N) ℂ => 1 - K)
      (-ContinuousLinearMap.id ℝ _) H := (hasFDerivAt_id H).const_sub 1
  have hi := (A2Research.hasFDerivAt_matrix_nonsing_inv (1 - H) hd).comp H hminus
  have hp := A2Research.hasFDerivAt_matrix_mul ((hasFDerivAt_id H).const_add 1) hi
  have heq : takagiCayleyMatrixDerivative H =
      A2Research.matrixMulDerivative (1 + H) (1 - H)⁻¹ (ContinuousLinearMap.id ℝ _)
        ((A2Research.matrixInverseDerivative (1 - H)).comp (-ContinuousLinearMap.id ℝ _)) := by
    apply ContinuousLinearMap.ext
    intro D
    simp only [A2Research.matrixMulDerivative_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.neg_apply,
      A2Research.matrixInverseDerivative_apply, Matrix.mul_neg, Matrix.neg_mul, neg_neg]
    exact takagiCayleyMatrixDerivative_product_rule H D hH
  rw [heq]
  exact hp

theorem takagiCayley_conjTranspose_mul_inverse {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ)
    (hH : H.conjTranspose = -H) :
    (takagiCayley H).conjTranspose * (1 - H)⁻¹ = (1 + H)⁻¹ := by
  have hm := (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_one_sub_skewHermitian H hH)
  unfold takagiCayley
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv,
    Matrix.conjTranspose_sub, Matrix.conjTranspose_add, Matrix.conjTranspose_one, hH]
  simp only [sub_neg_eq_add, ← sub_eq_add_neg]
  rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hm, mul_one]

theorem takagiCayleyMatrixDerivative_leftTrivialized {N : ℕ}
    (H D : Matrix (Fin N) (Fin N) ℂ) (hH : H.conjTranspose = -H) :
    (takagiCayley H).conjTranspose * takagiCayleyMatrixDerivative H D =
      takagiCayleyAngularTangent H D := by
  rw [takagiCayleyMatrixDerivative_apply, Matrix.mul_smul]
  change (2 : ℝ) • ((takagiCayley H).conjTranspose * ((1 - H)⁻¹ * D * (1 - H)⁻¹)) = _
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc,
    takagiCayley_conjTranspose_mul_inverse H hH]
  rfl

def takagiAngularSkewCLM (N : ℕ) :
    TakagiAngularCoordinates N →L[ℝ] Matrix (Fin N) (Fin N) ℂ :=
  (((takagiSkewHermitianSpace N).subtype).comp (takagiAngularSkewEquiv N).toLinearMap).toContinuousLinearMap

def takagiAngularCayleyMatrixDerivative {N : ℕ} (a : TakagiAngularCoordinates N) :
    TakagiAngularCoordinates N →L[ℝ] Matrix (Fin N) (Fin N) ℂ :=
  (takagiCayleyMatrixDerivative (takagiAngularSkewEquiv N a)).comp (takagiAngularSkewCLM N)

theorem hasFDerivAt_takagiAngularCayley {N : ℕ} (a : TakagiAngularCoordinates N) :
    HasFDerivAt (fun b => ((takagiAngularCayley b) : Matrix (Fin N) (Fin N) ℂ))
      (takagiAngularCayleyMatrixDerivative a) a := by
  exact (hasFDerivAt_takagiCayley ((takagiAngularSkewEquiv N a) : Matrix (Fin N) (Fin N) ℂ)
    (show ((takagiAngularSkewEquiv N a) : Matrix (Fin N) (Fin N) ℂ).conjTranspose =
      -(takagiAngularSkewEquiv N a) from (takagiAngularSkewEquiv N a).property)).comp
      a (takagiAngularSkewCLM N).hasFDerivAt

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
