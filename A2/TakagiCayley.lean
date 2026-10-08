import A2.OrbitJacobianTangent

/-! The Cayley parametrization on all skew-Hermitian matrices. -/

open scoped Matrix ComplexOrder MatrixOrder

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

theorem isUnit_one_sub_skewHermitian {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ)
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

theorem isUnit_one_add_skewHermitian {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ)
    (hH : H.conjTranspose = -H) : IsUnit (1 + H) := by
  simpa using isUnit_one_sub_skewHermitian (-H) (by simpa using congrArg Neg.neg hH)

def takagiCayley {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin N) (Fin N) ℂ := (1 + H) * (1 - H)⁻¹

theorem takagiCayley_mul_one_sub {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ)
    (hH : H.conjTranspose = -H) : takagiCayley H * (1 - H) = 1 + H := by
  exact Matrix.nonsing_inv_mul_cancel_right _ _
    ((Matrix.isUnit_iff_isUnit_det _).mp (isUnit_one_sub_skewHermitian H hH))

theorem takagiCayley_mem_unitaryGroup {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ)
    (hH : H.conjTranspose = -H) : takagiCayley H ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  classical
  apply Matrix.mem_unitaryGroup_iff'.mpr
  change (takagiCayley H).conjTranspose * takagiCayley H = 1
  have hu := isUnit_one_sub_skewHermitian H hH
  have hus : IsUnit (1 - H).conjTranspose := by simpa only [Matrix.star_eq_conjTranspose] using hu.star
  apply hu.mul_right_cancel
  apply hus.mul_left_cancel
  have hg : (1 + H).conjTranspose * (1 + H) =
      (1 - H).conjTranspose * (1 - H) := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hH]
    noncomm_ring
  calc
    (1 - H).conjTranspose * ((takagiCayley H).conjTranspose * takagiCayley H * (1 - H)) =
        (takagiCayley H * (1 - H)).conjTranspose * (takagiCayley H * (1 - H)) := by
      rw [Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    _ = (1 + H).conjTranspose * (1 + H) := by rw [takagiCayley_mul_one_sub H hH]
    _ = (1 - H).conjTranspose * (1 * (1 - H)) := by simpa using hg

def takagiCayleyUnitary {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ)
    (hH : H.conjTranspose = -H) : Matrix.unitaryGroup (Fin N) ℂ :=
  ⟨takagiCayley H, takagiCayley_mem_unitaryGroup H hH⟩

theorem takagiCayley_add_one {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ)
    (hH : H.conjTranspose = -H) : takagiCayley H + 1 = (2 : Matrix (Fin N) (Fin N) ℂ) * (1 - H)⁻¹ := by
  have hi := Matrix.mul_nonsing_inv (1 - H)
    ((Matrix.isUnit_iff_isUnit_det _).mp (isUnit_one_sub_skewHermitian H hH))
  change (1 + H) * (1 - H)⁻¹ + 1 = _
  calc
    (1 + H) * (1 - H)⁻¹ + 1 =
        (1 + H) * (1 - H)⁻¹ + (1 - H) * (1 - H)⁻¹ := by rw [hi]
    _ = (2 : Matrix (Fin N) (Fin N) ℂ) * (1 - H)⁻¹ := by noncomm_ring

theorem isUnit_takagiCayley_add_one {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ)
    (hH : H.conjTranspose = -H) : IsUnit (takagiCayley H + 1) := by
  rw [takagiCayley_add_one H hH]
  exact (Matrix.PosDef.ofNat 2).isUnit.mul
    ((Matrix.isUnit_nonsing_inv_iff).mpr (isUnit_one_sub_skewHermitian H hH))

def takagiCayleyInverse {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin N) (Fin N) ℂ := (U - 1) * (U + 1)⁻¹

theorem takagiCayleyInverse_takagiCayley {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ)
    (hH : H.conjTranspose = -H) : takagiCayleyInverse (takagiCayley H) = H := by
  have he : takagiCayley H - 1 = H * (takagiCayley H + 1) := by
    have hi := (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_one_sub_skewHermitian H hH)
    rw [takagiCayley_add_one H hH]
    unfold takagiCayley
    rw [add_mul, one_mul]
    have hi' := Matrix.mul_nonsing_inv (1 - H) hi
    calc
      (1 - H)⁻¹ + H * (1 - H)⁻¹ - 1 =
          (1 - H)⁻¹ + H * (1 - H)⁻¹ - (1 - H) * (1 - H)⁻¹ := by rw [hi']
      _ = H * ((2 : Matrix (Fin N) (Fin N) ℂ) * (1 - H)⁻¹) := by noncomm_ring
  unfold takagiCayleyInverse
  rw [he]
  exact Matrix.mul_nonsing_inv_cancel_right _ _
    ((Matrix.isUnit_iff_isUnit_det _).mp (isUnit_takagiCayley_add_one H hH))

theorem takagiCayley_injective_skewHermitian {N : ℕ}
    (H K : Matrix (Fin N) (Fin N) ℂ) (hH : H.conjTranspose = -H)
    (hK : K.conjTranspose = -K) (heq : takagiCayley H = takagiCayley K) : H = K := by
  simpa only [takagiCayleyInverse_takagiCayley H hH,
    takagiCayleyInverse_takagiCayley K hK] using congrArg takagiCayleyInverse heq

theorem commute_matrix_nonsing_inv {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℂ)
    (h : Commute A B) (hB : IsUnit B) : Commute A B⁻¹ := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).mp hB
  change A * B⁻¹ = B⁻¹ * A
  apply hB.mul_right_cancel
  calc
    A * B⁻¹ * B = A := Matrix.nonsing_inv_mul_cancel_right _ _ hd
    _ = B⁻¹ * (B * A) := (Matrix.nonsing_inv_mul_cancel_left _ _ hd).symm
    _ = B⁻¹ * (A * B) := by rw [h.eq]
    _ = B⁻¹ * A * B := (Matrix.mul_assoc _ _ _).symm

theorem takagiCayleyInverse_mul_add_one {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ)
    (hU : IsUnit (U + 1)) : takagiCayleyInverse U * (U + 1) = U - 1 := by
  exact Matrix.nonsing_inv_mul_cancel_right _ _ ((Matrix.isUnit_iff_isUnit_det _).mp hU)

theorem takagiCayleyInverse_skewHermitian {N : ℕ}
    (U : Matrix.unitaryGroup (Fin N) ℂ) (hU : IsUnit ((U : Matrix (Fin N) (Fin N) ℂ) + 1)) :
    (takagiCayleyInverse (U : Matrix (Fin N) (Fin N) ℂ)).conjTranspose =
      -takagiCayleyInverse (U : Matrix (Fin N) (Fin N) ℂ) := by
  have hs : IsUnit ((U : Matrix (Fin N) (Fin N) ℂ) + 1).conjTranspose := by
    simpa only [Matrix.star_eq_conjTranspose] using hU.star
  apply hU.mul_right_cancel
  apply hs.mul_left_cancel
  have hi := takagiCayleyInverse_mul_add_one (U : Matrix (Fin N) (Fin N) ℂ) hU
  have he := congrArg Matrix.conjTranspose hi
  rw [Matrix.conjTranspose_mul] at he
  calc
    ((U : Matrix (Fin N) (Fin N) ℂ) + 1).conjTranspose *
        ((takagiCayleyInverse (U : Matrix (Fin N) (Fin N) ℂ)).conjTranspose *
          ((U : Matrix (Fin N) (Fin N) ℂ) + 1)) =
        ((U : Matrix (Fin N) (Fin N) ℂ) - 1).conjTranspose *
          ((U : Matrix (Fin N) (Fin N) ℂ) + 1) := by
      rw [← Matrix.mul_assoc, he]
    _ = -(((U : Matrix (Fin N) (Fin N) ℂ) + 1).conjTranspose *
          ((U : Matrix (Fin N) (Fin N) ℂ) - 1)) := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_add, Matrix.conjTranspose_one]
      have hu : (U : Matrix (Fin N) (Fin N) ℂ).conjTranspose * U = 1 := U.property.1
      simp only [sub_mul, add_mul, mul_sub, mul_add, one_mul, mul_one, hu]
      abel
    _ = ((U : Matrix (Fin N) (Fin N) ℂ) + 1).conjTranspose *
        (-takagiCayleyInverse (U : Matrix (Fin N) (Fin N) ℂ) *
          ((U : Matrix (Fin N) (Fin N) ℂ) + 1)) := by
      rw [neg_mul, hi, Matrix.mul_neg]

theorem takagiCayley_takagiCayleyInverse {N : ℕ}
    (U : Matrix.unitaryGroup (Fin N) ℂ) (hU : IsUnit ((U : Matrix (Fin N) (Fin N) ℂ) + 1)) :
    takagiCayley (takagiCayleyInverse (U : Matrix (Fin N) (Fin N) ℂ)) = U := by
  let A : Matrix (Fin N) (Fin N) ℂ := U
  let K := takagiCayleyInverse A
  have hk : K.conjTranspose = -K := takagiCayleyInverse_skewHermitian U hU
  have hc0 : Commute A (A + 1) := by unfold Commute SemiconjBy; noncomm_ring
  have hc1 := commute_matrix_nonsing_inv A (A + 1) hc0 hU
  have hc : Commute A K :=
    ((Commute.refl A).sub_right (Commute.one_right A)).mul_right hc1
  have hi : K * (A + 1) = A - 1 := takagiCayleyInverse_mul_add_one A hU
  have he : A * (1 - K) = 1 + K := by
    rw [mul_sub, mul_one, hc.eq]
    have hi' : K * A + K = A - 1 := by simpa only [mul_add, mul_one] using hi
    ext i j
    have hij := congrArg (fun M : Matrix (Fin N) (Fin N) ℂ => M i j) hi'
    simp only [Matrix.add_apply, Matrix.sub_apply] at hij ⊢
    linear_combination -hij
  apply (isUnit_one_sub_skewHermitian K hk).mul_right_cancel
  exact (takagiCayley_mul_one_sub K hk).trans he.symm

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
