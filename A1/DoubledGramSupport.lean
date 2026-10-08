import A1.NormalizedAugmentedGram

open Matrix Complex
open A3Research
open LogdetLean.GramHafnian.UltimateHiding.DenseScore
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section
namespace A1Research

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

theorem doubledReal_posDef_iff_complexMap {m : ℕ}
    (W : Matrix (DoubledIndex m) (DoubledIndex m) ℝ) :
    W.PosDef ↔ (W.map Complex.ofReal).PosDef := by
  let e := (doubledIndexEquiv m).symm
  have h := real_posDef_iff_complexMap (W.submatrix e e)
  have hmap : (W.submatrix e e).map Complex.ofReal =
      (W.map Complex.ofReal).submatrix e e := rfl
  rw [hmap, posDef_submatrix_equiv_rclike e W,
    posDef_submatrix_equiv_rclike e (W.map Complex.ofReal)] at h
  exact h

theorem augmentedComplexPair_real_congruence {m : ℕ}
    (T Z : Matrix (Fin m) (Fin m) ℂ) :
    augmentedComplexPair T Z =
      (doubledAugmentationMatrix m).conjTranspose *
        (complexPairRealMatrix T Z).map Complex.ofReal * doubledAugmentationMatrix m := by
  have h := augmentedComplexPair_doubledParts (complexPairRealMatrix T Z)
  have hp := doubledParts_complexPairRealMatrix T Z
  have hT : doubledHermitianPart (complexPairRealMatrix T Z) = T := congrArg Prod.fst hp
  have hZ : doubledSymmetricPart (complexPairRealMatrix T Z) = Z := congrArg Prod.snd hp
  simpa only [hT, hZ] using h

theorem complexPairRealMatrix_posDef_iff_augmented {m : ℕ}
    (T Z : Matrix (Fin m) (Fin m) ℂ) :
    (complexPairRealMatrix T Z).PosDef ↔ (augmentedComplexPair T Z).PosDef := by
  rw [augmentedComplexPair_real_congruence, ← Matrix.star_eq_conjTranspose,
    (doubledAugmentation_isUnit m).posDef_star_left_conjugate_iff]
  exact doubledReal_posDef_iff_complexMap _

theorem augmentedComplexPair_posDef_hermitianPart {m : ℕ}
    {T Z : Matrix (Fin m) (Fin m) ℂ} (h : (augmentedComplexPair T Z).PosDef) : T.PosDef := by
  have ht := h.submatrix (e := Sum.inl) Sum.inl_injective
  have hmat : (augmentedComplexPair T Z).submatrix Sum.inl Sum.inl = T := by
    ext i j
    rfl
  rwa [hmat] at ht

theorem complexPairRealMatrix_posDef_iff_normalized {m : ℕ}
    {T Z : Matrix (Fin m) (Fin m) ℂ} (hZ : Z.IsSymm) :
    (complexPairRealMatrix T Z).PosDef ↔
      T.PosDef ∧ (1 - (normalizedComplexPairOverlap T Z).conjTranspose *
        normalizedComplexPairOverlap T Z).PosDef := by
  rw [complexPairRealMatrix_posDef_iff_augmented]
  constructor
  · intro h
    have hT := augmentedComplexPair_posDef_hermitianPart h
    refine ⟨hT, ?_⟩
    have hs := augmentedComplexPair_sqrt_posDef_iff
      (A3Research.posDef_cfc_sqrt hT) (normalizedComplexPairOverlap_isSymm (T := T) hZ)
    rw [CFC.sqrt_mul_sqrt_self T hT.posSemidef.nonneg,
      normalizedComplexPairOverlap_recover hT] at hs
    exact hs.mp h
  · rintro ⟨hT, hC⟩
    have hs := augmentedComplexPair_sqrt_posDef_iff
      (A3Research.posDef_cfc_sqrt hT) (normalizedComplexPairOverlap_isSymm (T := T) hZ)
    rw [CFC.sqrt_mul_sqrt_self T hT.posSemidef.nonneg,
      normalizedComplexPairOverlap_recover hT] at hs
    exact hs.mpr hC

theorem complexPairRealMatrix_scaled_posDef_iff {m : ℕ}
    {T C : Matrix (Fin m) (Fin m) ℂ} (hT : T.PosDef) (hC : C.IsSymm) :
    (complexPairRealMatrix T ((CFC.sqrt T).transpose * C * CFC.sqrt T)).PosDef ↔
      (1 - C.conjTranspose * C).PosDef := by
  rw [complexPairRealMatrix_posDef_iff_augmented]
  have hs := augmentedComplexPair_sqrt_posDef_iff (A3Research.posDef_cfc_sqrt hT) hC
  rwa [CFC.sqrt_mul_sqrt_self T hT.posSemidef.nonneg] at hs

theorem complexPairRealMatrix_scaled_det {m : ℕ}
    {T C : Matrix (Fin m) (Fin m) ℂ} (hT : T.PosDef) (hC : C.IsSymm) :
    (complexPairRealMatrix T ((CFC.sqrt T).transpose * C * CFC.sqrt T)).det =
      ((2 : ℝ) ^ (2 * m))⁻¹ * T.det.re ^ 2 * (1 - C.conjTranspose * C).det.re := by
  let Z := (CFC.sqrt T).transpose * C * CFC.sqrt T
  have hp := doubledParts_complexPairRealMatrix T Z
  have hd := augmentedComplexPair_doubledParts_det (complexPairRealMatrix T Z)
  have hpT : doubledHermitianPart (complexPairRealMatrix T Z) = T := congrArg Prod.fst hp
  have hpZ : doubledSymmetricPart (complexPairRealMatrix T Z) = Z := congrArg Prod.snd hp
  rw [hpT, hpZ] at hd
  have hs := augmentedComplexPair_sqrt_det (A3Research.posDef_cfc_sqrt hT).isHermitian hC
  rw [CFC.sqrt_mul_sqrt_self T hT.posSemidef.nonneg] at hs
  change (augmentedComplexPair T Z).det = T.det ^ 2 * _ at hs
  rw [hs] at hd
  have hr := congrArg Complex.re hd
  have hTreal : T.det = (T.det.re : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using (Complex.pos_iff.mp hT.det_pos).2.symm
  rw [hTreal] at hr
  have h2cast : (2 : ℂ) ^ (2 * m) = (((2 : ℝ) ^ (2 * m)) : ℂ) := by norm_cast
  rw [← Complex.ofReal_pow, h2cast] at hr
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, mul_zero, sub_zero] at hr
  simp only [← Complex.ofReal_pow, Complex.ofReal_re] at hr
  have h2 : (2 : ℝ) ^ (2 * m) ≠ 0 := pow_ne_zero _ (by norm_num)
  change _ = (2 ^ (2 * m))⁻¹ * T.det.re ^ 2 * _
  apply (mul_left_cancel₀ h2)
  rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ h2, one_mul]
  exact hr.symm

theorem complexPairRealMatrix_trace {m : ℕ}
    (T Z : Matrix (Fin m) (Fin m) ℂ) : (complexPairRealMatrix T Z).trace = T.trace.re := by
  have hp : doubledHermitianPart (complexPairRealMatrix T Z) = T :=
    congrArg Prod.fst (doubledParts_complexPairRealMatrix T Z)
  simpa only [hp] using doubledReal_trace (complexPairRealMatrix T Z)

end A1Research
