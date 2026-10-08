import A3.HermitianDiagonalJacobian
import A3.MatrixInverseDerivativeRCLike

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.Elementwise ContDiff

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

namespace A3Research

variable {n : ℕ} {K : Type*} [RCLike K]

theorem isUnit_one_sub_hermitianSkew (H : Matrix (Fin n) (Fin n) K)
    (hH : H.conjTranspose = -H) : IsUnit (1 - H) := by
  classical
  have hGram : ((1 - H).conjTranspose * (1 - H)).PosDef := by
    have he : (1 - H).conjTranspose * (1 - H) = 1 + H.conjTranspose * H := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hH]
      noncomm_ring
    rw [he]
    exact Matrix.PosDef.one.add_posSemidef (Matrix.posSemidef_conjTranspose_mul_self H)
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  have hg := (Matrix.isUnit_iff_isUnit_det _).mp hGram.isUnit
  rw [Matrix.det_mul] at hg
  exact isUnit_of_mul_isUnit_right hg

theorem isUnit_one_add_hermitianSkew (H : Matrix (Fin n) (Fin n) K)
    (hH : H.conjTranspose = -H) : IsUnit (1 + H) := by
  simpa using isUnit_one_sub_hermitianSkew (-H) (by simpa using congrArg Neg.neg hH)

def hermitianCayleyMatrix (H : Matrix (Fin n) (Fin n) K) :
    Matrix (Fin n) (Fin n) K := (1 + H) * (1 - H)⁻¹

theorem hermitianCayleyMatrix_mul_one_sub (H : Matrix (Fin n) (Fin n) K)
    (hH : H.conjTranspose = -H) : hermitianCayleyMatrix H * (1 - H) = 1 + H :=
  Matrix.nonsing_inv_mul_cancel_right _ _
    ((Matrix.isUnit_iff_isUnit_det _).mp (isUnit_one_sub_hermitianSkew H hH))

theorem hermitianCayleyMatrix_mem_unitaryGroup (H : Matrix (Fin n) (Fin n) K)
    (hH : H.conjTranspose = -H) : hermitianCayleyMatrix H ∈ Matrix.unitaryGroup (Fin n) K := by
  classical
  apply Matrix.mem_unitaryGroup_iff'.mpr
  change (hermitianCayleyMatrix H).conjTranspose * hermitianCayleyMatrix H = 1
  have hu := isUnit_one_sub_hermitianSkew H hH
  have hus : IsUnit (1 - H).conjTranspose := by
    simpa only [Matrix.star_eq_conjTranspose] using hu.star
  apply hu.mul_right_cancel
  apply hus.mul_left_cancel
  have hg : (1 + H).conjTranspose * (1 + H) =
      (1 - H).conjTranspose * (1 - H) := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hH]
    noncomm_ring
  calc
    (1 - H).conjTranspose *
        ((hermitianCayleyMatrix H).conjTranspose * hermitianCayleyMatrix H * (1 - H)) =
        (hermitianCayleyMatrix H * (1 - H)).conjTranspose *
          (hermitianCayleyMatrix H * (1 - H)) := by
      rw [Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    _ = (1 + H).conjTranspose * (1 + H) := by rw [hermitianCayleyMatrix_mul_one_sub H hH]
    _ = (1 - H).conjTranspose * (1 * (1 - H)) := by simpa using hg

def hermitianAngularCayley (a : HermitianCoordinateIndex n → K) :
    Matrix.unitaryGroup (Fin n) K :=
  ⟨hermitianCayleyMatrix (hermitianAngularSkewMatrix a),
    hermitianCayleyMatrix_mem_unitaryGroup _ (hermitianAngularSkewMatrix_skewHermitian a)⟩

@[simp] theorem hermitianAngularSkewMatrix_zero :
    hermitianAngularSkewMatrix (0 : HermitianCoordinateIndex n → K) = 0 :=
  (hermitianAngularSkewLinearMap n K).map_zero

@[simp] theorem hermitianAngularCayley_zero :
    hermitianAngularCayley (0 : HermitianCoordinateIndex n → K) = 1 := by
  apply Subtype.ext
  simp [hermitianAngularCayley, hermitianCayleyMatrix]

theorem hermitianCayleyMatrix_add_one (H : Matrix (Fin n) (Fin n) K)
    (hH : H.conjTranspose = -H) :
    hermitianCayleyMatrix H + 1 = (2 : Matrix (Fin n) (Fin n) K) * (1 - H)⁻¹ := by
  have hi := Matrix.mul_nonsing_inv (1 - H)
    ((Matrix.isUnit_iff_isUnit_det _).mp (isUnit_one_sub_hermitianSkew H hH))
  change (1 + H) * (1 - H)⁻¹ + 1 = _
  calc
    (1 + H) * (1 - H)⁻¹ + 1 =
        (1 + H) * (1 - H)⁻¹ + (1 - H) * (1 - H)⁻¹ := by rw [hi]
    _ = (2 : Matrix (Fin n) (Fin n) K) * (1 - H)⁻¹ := by noncomm_ring

def hermitianCayleyMatrixDerivative (H : Matrix (Fin n) (Fin n) K) :
    Matrix (Fin n) (Fin n) K →L[ℝ] Matrix (Fin n) (Fin n) K :=
  (2 : ℝ) • ((mulLeftLinearMap (Fin n) ℝ (1 - H)⁻¹).toContinuousLinearMap.comp
    (mulRightLinearMap (Fin n) ℝ (1 - H)⁻¹).toContinuousLinearMap)

@[simp] theorem hermitianCayleyMatrixDerivative_apply
    (H D : Matrix (Fin n) (Fin n) K) :
    hermitianCayleyMatrixDerivative H D =
      (2 : ℝ) • ((1 - H)⁻¹ * D * (1 - H)⁻¹) := by
  simp [hermitianCayleyMatrixDerivative, Matrix.mul_assoc]

theorem hermitianCayleyMatrixDerivative_product_rule
    (H D : Matrix (Fin n) (Fin n) K) (hH : H.conjTranspose = -H) :
    hermitianCayleyMatrixDerivative H D =
      D * (1 - H)⁻¹ + (1 + H) * ((1 - H)⁻¹ * D * (1 - H)⁻¹) := by
  rw [hermitianCayleyMatrixDerivative_apply]
  have hc := hermitianCayleyMatrix_add_one H hH
  calc
    (2 : ℝ) • ((1 - H)⁻¹ * D * (1 - H)⁻¹) =
        (hermitianCayleyMatrix H + 1) * D * (1 - H)⁻¹ := by
      rw [hc, two_smul ℝ]
      noncomm_ring
    _ = D * (1 - H)⁻¹ + (1 + H) * ((1 - H)⁻¹ * D * (1 - H)⁻¹) := by
      unfold hermitianCayleyMatrix
      noncomm_ring

theorem hasFDerivAt_hermitianCayleyMatrix (H : Matrix (Fin n) (Fin n) K)
    (hH : H.conjTranspose = -H) :
    HasFDerivAt (@hermitianCayleyMatrix n K _) (hermitianCayleyMatrixDerivative H) H := by
  have hd : (1 - H).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (isUnit_one_sub_hermitianSkew H hH)).ne_zero
  have hminus : HasFDerivAt (fun B : Matrix (Fin n) (Fin n) K ↦ 1 - B)
      (-ContinuousLinearMap.id ℝ _) H := (hasFDerivAt_id H).const_sub 1
  have hi := (hasFDerivAt_matrix_nonsing_inv_rclike (1 - H) hd).comp H hminus
  have hp := hasFDerivAt_matrix_mul_rclike ((hasFDerivAt_id H).const_add 1) hi
  have heq : hermitianCayleyMatrixDerivative H =
      matrixMulDerivativeRCLike (1 + H) (1 - H)⁻¹ (ContinuousLinearMap.id ℝ _)
        ((matrixInverseDerivativeRCLike (1 - H)).comp (-ContinuousLinearMap.id ℝ _)) := by
    apply ContinuousLinearMap.ext
    intro D
    simp only [matrixMulDerivativeRCLike_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.neg_apply,
      matrixInverseDerivativeRCLike_apply, Matrix.mul_neg, Matrix.neg_mul, neg_neg]
    exact hermitianCayleyMatrixDerivative_product_rule H D hH
  rw [heq]
  exact hp

def hermitianAngularSkewCLM (n : ℕ) (K : Type*) [RCLike K] :
    (HermitianCoordinateIndex n → K) →L[ℝ] Matrix (Fin n) (Fin n) K :=
  (hermitianAngularSkewLinearMap n K).toContinuousLinearMap

def hermitianAngularCayleyMatrixDerivative (a : HermitianCoordinateIndex n → K) :
    (HermitianCoordinateIndex n → K) →L[ℝ] Matrix (Fin n) (Fin n) K :=
  (hermitianCayleyMatrixDerivative (hermitianAngularSkewMatrix a)).comp
    (hermitianAngularSkewCLM n K)

theorem hasFDerivAt_hermitianAngularCayleyMatrix (a : HermitianCoordinateIndex n → K) :
    HasFDerivAt (fun b ↦ (hermitianAngularCayley b).val)
      (hermitianAngularCayleyMatrixDerivative a) a :=
  (hasFDerivAt_hermitianCayleyMatrix (hermitianAngularSkewMatrix a)
    (hermitianAngularSkewMatrix_skewHermitian a)).comp
      a (hermitianAngularSkewCLM n K).hasFDerivAt

theorem contDiff_hermitianAngularCayleyMatrix (k : ℕ∞ω) :
    ContDiff ℝ k (fun a : HermitianCoordinateIndex n → K ↦ (hermitianAngularCayley a).val) := by
  rw [contDiff_iff_contDiffAt]
  intro a
  have hs : ContDiff ℝ k (hermitianAngularSkewMatrix : (HermitianCoordinateIndex n → K) → _) :=
    (hermitianAngularSkewCLM n K).contDiff
  have hd : (1 - hermitianAngularSkewMatrix a).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp
      (isUnit_one_sub_hermitianSkew _ (hermitianAngularSkewMatrix_skewHermitian a))).ne_zero
  exact contDiffAt_matrix_mul (contDiffAt_const.add hs.contDiffAt)
    (contDiffAt_matrix_nonsing_inv (contDiffAt_const.sub hs.contDiffAt) hd)

theorem continuous_hermitianAngularCayley :
    Continuous (hermitianAngularCayley : (HermitianCoordinateIndex n → K) → _) :=
  (contDiff_hermitianAngularCayleyMatrix (n := n) (K := K) 0).continuous.subtype_mk _

end A3Research
