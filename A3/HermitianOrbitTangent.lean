import A3.HermitianOrbitCayley

open Filter
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.Elementwise ContDiff Topology

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace A3Research

variable {n : ℕ} {K : Type*} [RCLike K]

def hermitianCayleyLeftTangent (H D : Matrix (Fin n) (Fin n) K) :
    Matrix (Fin n) (Fin n) K :=
  (2 : ℝ) • ((1 + H)⁻¹ * D * (1 - H)⁻¹)

theorem hermitianCayleyLeftTangent_skewHermitian (H D : Matrix (Fin n) (Fin n) K)
    (hH : H.conjTranspose = -H) (hD : D.conjTranspose = -D) :
    (hermitianCayleyLeftTangent H D).conjTranspose = -hermitianCayleyLeftTangent H D := by
  simp only [hermitianCayleyLeftTangent, Matrix.conjTranspose_smul,
    star_trivial, Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv,
    Matrix.conjTranspose_add, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hH, hD,
    sub_neg_eq_add, ← sub_eq_add_neg, Matrix.mul_neg, Matrix.neg_mul, smul_neg]
  rw [Matrix.mul_assoc]

theorem hermitianCayleyMatrix_conjTranspose_mul_inverse (H : Matrix (Fin n) (Fin n) K)
    (hH : H.conjTranspose = -H) :
    (hermitianCayleyMatrix H).conjTranspose * (1 - H)⁻¹ = (1 + H)⁻¹ := by
  have hm := (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_one_sub_hermitianSkew H hH)
  unfold hermitianCayleyMatrix
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv,
    Matrix.conjTranspose_sub, Matrix.conjTranspose_add, Matrix.conjTranspose_one, hH]
  simp only [sub_neg_eq_add, ← sub_eq_add_neg]
  rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hm, mul_one]

theorem hermitianCayleyMatrixDerivative_leftTrivialized
    (H D : Matrix (Fin n) (Fin n) K) (hH : H.conjTranspose = -H) :
    (hermitianCayleyMatrix H).conjTranspose * hermitianCayleyMatrixDerivative H D =
      hermitianCayleyLeftTangent H D := by
  rw [hermitianCayleyMatrixDerivative_apply, Matrix.mul_smul]
  change (2 : ℝ) • ((hermitianCayleyMatrix H).conjTranspose *
    ((1 - H)⁻¹ * D * (1 - H)⁻¹)) = _
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc,
    hermitianCayleyMatrix_conjTranspose_mul_inverse H hH]
  rfl

def hermitianUpperProjectionLinearMap (n : ℕ) (K : Type*) [RCLike K] :
    Matrix (Fin n) (Fin n) K →ₗ[ℝ] (HermitianCoordinateIndex n → K) :=
  (LinearMap.snd ℝ (Fin n → ℝ) (HermitianCoordinateIndex n → K)).comp
    (hermitianCoordinateProjectionLinearMap n K)

def hermitianAngularLeftTangentLinearMap (a : HermitianCoordinateIndex n → K) :
    (HermitianCoordinateIndex n → K) →ₗ[ℝ] Matrix (Fin n) (Fin n) K :=
  (2 : ℝ) • ((mulLeftLinearMap (Fin n) ℝ (1 + hermitianAngularSkewMatrix a)⁻¹).comp
    ((mulRightLinearMap (Fin n) ℝ (1 - hermitianAngularSkewMatrix a)⁻¹).comp
      (hermitianAngularSkewLinearMap n K)))

@[simp] theorem hermitianAngularLeftTangentLinearMap_apply
    (a b : HermitianCoordinateIndex n → K) :
    hermitianAngularLeftTangentLinearMap a b =
      hermitianCayleyLeftTangent (hermitianAngularSkewMatrix a) (hermitianAngularSkewMatrix b) := by
  simp [hermitianAngularLeftTangentLinearMap, hermitianCayleyLeftTangent,
    hermitianAngularSkewLinearMap, Matrix.mul_assoc]

def hermitianAngularTangentOperator (a : HermitianCoordinateIndex n → K) :
    (HermitianCoordinateIndex n → K) →ₗ[ℝ] (HermitianCoordinateIndex n → K) :=
  (hermitianUpperProjectionLinearMap n K).comp (hermitianAngularLeftTangentLinearMap a)

@[simp] theorem hermitianAngularTangentOperator_apply (a b : HermitianCoordinateIndex n → K)
    (ij : HermitianCoordinateIndex n) :
    hermitianAngularTangentOperator a b ij =
      hermitianCayleyLeftTangent (hermitianAngularSkewMatrix a)
        (hermitianAngularSkewMatrix b) ij.1.1 ij.1.2 := by
  change hermitianAngularLeftTangentLinearMap a b ij.1.1 ij.1.2 = _
  rw [hermitianAngularLeftTangentLinearMap_apply]

theorem hermitianAngularTangentOperator_zero :
    hermitianAngularTangentOperator (0 : HermitianCoordinateIndex n → K) =
      (2 : ℝ) • LinearMap.id := by
  apply LinearMap.ext
  intro b
  funext ij
  simp [hermitianAngularTangentOperator_apply, hermitianCayleyLeftTangent]

theorem hermitianAngularTangentOperator_zero_det :
    LinearMap.det (hermitianAngularTangentOperator (0 : HermitianCoordinateIndex n → K)) =
      (2 : ℝ) ^ Module.finrank ℝ (HermitianCoordinateIndex n → K) := by
  rw [hermitianAngularTangentOperator_zero]
  simp

theorem contDiff_hermitianAngularTangentOperator_apply
    (k : ℕ∞ω) (b : HermitianCoordinateIndex n → K) :
    ContDiff ℝ k (fun a ↦ hermitianAngularTangentOperator a b) := by
  have hs : ContDiff ℝ k (hermitianAngularSkewMatrix : (HermitianCoordinateIndex n → K) → _) :=
    (hermitianAngularSkewCLM n K).contDiff
  have hiPlus : ContDiff ℝ k (fun a : HermitianCoordinateIndex n → K ↦
      (1 + hermitianAngularSkewMatrix a)⁻¹) := by
    rw [contDiff_iff_contDiffAt]
    intro a
    exact contDiffAt_matrix_nonsing_inv (contDiffAt_const.add hs.contDiffAt)
      ((Matrix.isUnit_iff_isUnit_det _).mp
        (isUnit_one_add_hermitianSkew _ (hermitianAngularSkewMatrix_skewHermitian a))).ne_zero
  have hiMinus : ContDiff ℝ k (fun a : HermitianCoordinateIndex n → K ↦
      (1 - hermitianAngularSkewMatrix a)⁻¹) := by
    rw [contDiff_iff_contDiffAt]
    intro a
    exact contDiffAt_matrix_nonsing_inv (contDiffAt_const.sub hs.contDiffAt)
      ((Matrix.isUnit_iff_isUnit_det _).mp
        (isUnit_one_sub_hermitianSkew _ (hermitianAngularSkewMatrix_skewHermitian a))).ne_zero
  have hm : ContDiff ℝ k (fun a : HermitianCoordinateIndex n → K ↦
      hermitianCayleyLeftTangent (hermitianAngularSkewMatrix a) (hermitianAngularSkewMatrix b)) :=
    ((contDiff_matrix_mul (contDiff_matrix_mul hiPlus contDiff_const) hiMinus).const_smul (2 : ℝ))
  convert! ((hermitianUpperProjectionLinearMap n K).toContinuousLinearMap.contDiff.comp hm) using 1
  funext a
  change hermitianUpperProjectionLinearMap n K (hermitianAngularLeftTangentLinearMap a b) =
    hermitianUpperProjectionLinearMap n K
      (hermitianCayleyLeftTangent (hermitianAngularSkewMatrix a) (hermitianAngularSkewMatrix b))
  rw [hermitianAngularLeftTangentLinearMap_apply]

theorem continuous_det_hermitianAngularTangentOperator :
    Continuous (fun a : HermitianCoordinateIndex n → K ↦
      LinearMap.det (hermitianAngularTangentOperator a)) := by
  classical
  let b := Module.finBasis ℝ (HermitianCoordinateIndex n → K)
  have hm : Continuous (fun a : HermitianCoordinateIndex n → K ↦
      LinearMap.toMatrix b b (hermitianAngularTangentOperator a)) := by
    refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
    simp only [LinearMap.toMatrix_apply]
    exact (continuous_apply i).comp
      (b.continuous_coe_repr.comp (contDiff_hermitianAngularTangentOperator_apply 0 (b j)).continuous)
  have heq : (fun a : HermitianCoordinateIndex n → K ↦
      LinearMap.det (hermitianAngularTangentOperator a)) =
      fun a ↦ (LinearMap.toMatrix b b (hermitianAngularTangentOperator a)).det := by
    funext a
    exact (LinearMap.det_toMatrix b _).symm
  rw [heq]
  exact hm.matrix_det

def hermitianAngularDensity (a : HermitianCoordinateIndex n → K) : ℝ :=
  |LinearMap.det (hermitianAngularTangentOperator a)|

theorem continuous_hermitianAngularDensity :
    Continuous (hermitianAngularDensity : (HermitianCoordinateIndex n → K) → _) :=
  continuous_det_hermitianAngularTangentOperator.abs

theorem exists_hermitianAngularDensity_positive_closedBall :
    ∃ r : ℝ, 0 < r ∧ ∀ a : HermitianCoordinateIndex n → K,
      a ∈ Metric.closedBall 0 r → 0 < hermitianAngularDensity a := by
  have hz : LinearMap.det (hermitianAngularTangentOperator
      (0 : HermitianCoordinateIndex n → K)) ≠ 0 := by
    rw [hermitianAngularTangentOperator_zero_det]
    positivity
  have he := continuous_det_hermitianAngularTangentOperator.continuousAt.eventually_ne hz
  rcases Metric.eventually_nhds_iff.mp he with ⟨r, hr, hball⟩
  refine ⟨r / 2, by positivity, fun a ha ↦ ?_⟩
  apply abs_pos.mpr
  apply hball
  exact (Metric.mem_closedBall.mp ha).trans_lt (by linarith)

def hermitianOrbitSourceDifferential (a : HermitianCoordinateIndex n → K) :
    HermitianCoordinates n K →ₗ[ℝ] HermitianCoordinates n K :=
  LinearMap.prodMap LinearMap.id (hermitianAngularTangentOperator a)

@[simp] theorem hermitianOrbitSourceDifferential_apply
    (a : HermitianCoordinateIndex n → K) (x : HermitianCoordinates n K) :
    hermitianOrbitSourceDifferential a x = (x.1, hermitianAngularTangentOperator a x.2) := rfl

theorem hermitianOrbitSourceDifferential_det (a : HermitianCoordinateIndex n → K) :
    LinearMap.det (hermitianOrbitSourceDifferential a) =
      LinearMap.det (hermitianAngularTangentOperator a) := by
  rw [hermitianOrbitSourceDifferential, LinearMap.det_prodMap, LinearMap.det_id, one_mul]

end A3Research
