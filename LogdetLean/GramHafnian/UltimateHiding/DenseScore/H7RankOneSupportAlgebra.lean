import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H7RankTwoDeterminant
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.COESupportAlgebra
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ProjectiveTracePairHermitian
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CenteredFlowGeometry
import Mathlib.Tactic

/-!
# Public support algebra for the H7 rank-one determinant

The older support-algebra module intentionally kept its raw push-through
lemmas private.  This file proves the small public interface needed for the
literal rank-one likelihood, directly from positive definiteness and matrix
symmetry.  It contains no density, moment, or H7 assertion.
-/

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

def h7SupportH {N : ℕ} (K : ℕ) (A : ConcreteMatrixState N) :
    ConcreteMatrixState N :=
  let C := unscaleCOECorner K A
  1 - C.conjTranspose * C

def h7SupportG {N : ℕ} (K : ℕ) (A : ConcreteMatrixState N) :
    ConcreteMatrixState N :=
  let C := unscaleCOECorner K A
  1 - C * C.conjTranspose

def h7StarVector {N : ℕ} (v : ComplexUnitSphere N) : Fin N → ℂ :=
  fun i ↦ star (v.1 i)

theorem h7SupportH_posDef
    {N K : ℕ} (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    (h7SupportH K A).PosDef := by
  simpa [h7SupportH, coeCornerSupport] using hsupport

theorem h7SupportG_det_eq_supportH_det
    {N K : ℕ} (A : ConcreteMatrixState N) :
    (h7SupportG K A).det = (h7SupportH K A).det := by
  let C := unscaleCOECorner K A
  change (1 - C * C.conjTranspose).det =
    (1 - C.conjTranspose * C).det
  exact Matrix.det_one_sub_mul_comm C C.conjTranspose

theorem h7SupportH_isUnit
    {N K : ℕ} (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    IsUnit (h7SupportH K A) :=
  (h7SupportH_posDef A hsupport).isUnit

theorem h7SupportG_isUnit
    {N K : ℕ} (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    IsUnit (h7SupportG K A) := by
  rw [Matrix.isUnit_iff_isUnit_det, h7SupportG_det_eq_supportH_det A]
  exact (Matrix.isUnit_iff_isUnit_det (h7SupportH K A)).mp
    (h7SupportH_isUnit A hsupport)

theorem h7SupportG_mul_C_eq_C_mul_supportH
    {N K : ℕ} (A : ConcreteMatrixState N) :
    h7SupportG K A * unscaleCOECorner K A =
      unscaleCOECorner K A * h7SupportH K A := by
  unfold h7SupportG h7SupportH
  noncomm_ring

theorem h7SupportG_transpose_eq_supportH
    {N K : ℕ} (A : ConcreteMatrixState N)
    (hsymm : (unscaleCOECorner K A).IsSymm) :
    (h7SupportG K A).transpose = h7SupportH K A := by
  unfold h7SupportG h7SupportH
  rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul,
    hsymm.eq, hsymm.conjTranspose.eq]

theorem h7Support_inv_push_through
    {N K : ℕ} (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    (h7SupportG K A)⁻¹ * unscaleCOECorner K A =
      unscaleCOECorner K A * (h7SupportH K A)⁻¹ := by
  letI : Invertible (h7SupportH K A) :=
    (h7SupportH_isUnit A hsupport).invertible
  letI : Invertible (h7SupportG K A) :=
    (h7SupportG_isUnit A hsupport).invertible
  apply (Matrix.inv_mul_eq_iff_eq_mul_of_invertible
    (h7SupportG K A) (unscaleCOECorner K A)
    (unscaleCOECorner K A * (h7SupportH K A)⁻¹)).2
  rw [← Matrix.mul_assoc, h7SupportG_mul_C_eq_C_mul_supportH A,
    Matrix.mul_assoc, Matrix.mul_inv_of_invertible, Matrix.mul_one]

theorem h7SupportH_inv_transpose_eq_supportG_inv
    {N K : ℕ} (A : ConcreteMatrixState N)
    (hsymm : (unscaleCOECorner K A).IsSymm) :
    ((h7SupportH K A)⁻¹).transpose = (h7SupportG K A)⁻¹ := by
  have hHG : (h7SupportH K A).transpose = h7SupportG K A := by
    calc
      (h7SupportH K A).transpose =
          ((h7SupportG K A).transpose).transpose := by
            rw [h7SupportG_transpose_eq_supportH A hsymm]
      _ = h7SupportG K A := Matrix.transpose_transpose _
  rw [Matrix.transpose_nonsing_inv, hHG]

theorem h7SupportG_inv_eq_one_add_Z
    {N K : ℕ} (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    (h7SupportG K A)⁻¹ = 1 + concreteCOEZ K A := by
  let C := unscaleCOECorner K A
  let H := h7SupportH K A
  let G := h7SupportG K A
  letI : Invertible H := (h7SupportH_isUnit A hsupport).invertible
  letI : Invertible G := (h7SupportG_isUnit A hsupport).invertible
  have hinvOne :=
    (Matrix.inv_mul_eq_iff_eq_mul_of_invertible G 1
      (1 + C * H⁻¹ * C.conjTranspose)).2 (by
        rw [Matrix.mul_add, Matrix.mul_one]
        rw [show G * (C * H⁻¹ * C.conjTranspose) =
              C * C.conjTranspose by
          calc
            G * (C * H⁻¹ * C.conjTranspose) =
                (G * C) * H⁻¹ * C.conjTranspose := by noncomm_ring
            _ = (C * H) * H⁻¹ * C.conjTranspose := by
              rw [show G * C = C * H by
                simpa only [G, C, H] using
                  h7SupportG_mul_C_eq_C_mul_supportH A]
            _ = C * (H * H⁻¹) * C.conjTranspose := by noncomm_ring
            _ = C * C.conjTranspose := by
              rw [Matrix.mul_inv_of_invertible, Matrix.mul_one]]
        dsimp only [G, h7SupportG, C]
        noncomm_ring)
  calc
    (h7SupportG K A)⁻¹ = G⁻¹ := by rfl
    _ = G⁻¹ * 1 := (Matrix.mul_one _).symm
    _ = 1 + C * H⁻¹ * C.conjTranspose := hinvOne
    _ = 1 + concreteCOEZ K A := by
      unfold concreteCOEZ
      rfl

theorem h7ConcreteCOET_eq_C_mul_supportH_inv
    {N K : ℕ} (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    concreteCOET K A =
      unscaleCOECorner K A * (h7SupportH K A)⁻¹ := by
  unfold concreteCOET
  change (h7SupportG K A)⁻¹ * unscaleCOECorner K A = _
  exact h7Support_inv_push_through A hsupport

theorem h7SupportH_inv_isHermitian
    {N K : ℕ} (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    ((h7SupportH K A)⁻¹).IsHermitian :=
  (h7SupportH_posDef A hsupport).isHermitian.inv

theorem h7ConcreteCOET_conjTranspose_eq_supportH_inv_mul
    {N K : ℕ} (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    (concreteCOET K A).conjTranspose =
      (h7SupportH K A)⁻¹ *
        (unscaleCOECorner K A).conjTranspose := by
  rw [h7ConcreteCOET_eq_C_mul_supportH_inv A hsupport,
    Matrix.conjTranspose_mul,
    (h7SupportH_inv_isHermitian A hsupport).eq]

theorem complexProjectiveTracePair_eq_star_dot_mulVec
    {N : ℕ} (v : ComplexUnitSphere N) (M : ConcreteMatrixState N) :
    complexProjectiveTracePair v M =
      h7StarVector v ⬝ᵥ (M *ᵥ v.1) := by
  unfold complexProjectiveTracePair complexRankOneProjection h7StarVector
  rw [Matrix.dot_mulVec_eq_sum_sum]
  calc
    (∑ i, ∑ j, v.1 i * star (v.1 j) * M j i) =
        ∑ i, ∑ j, star (v.1 j) * M j i * v.1 i := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          ring
    _ = ∑ j, ∑ i, star (v.1 i) * M i j * v.1 j := by
      rw [Finset.sum_comm]

theorem concreteCOEB_eq_star_dot_mulVec
    {N K : ℕ} (v : ComplexUnitSphere N) (A : ConcreteMatrixState N) :
    concreteCOEB v K A =
      h7StarVector v ⬝ᵥ (concreteCOET K A *ᵥ h7StarVector v) := by
  unfold concreteCOEB h7StarVector
  rw [Matrix.dot_mulVec_eq_sum_sum, Finset.sum_comm]

theorem h7Plain_dot_conjTranspose_mulVec_eq_star_B
    {N K : ℕ} (v : ComplexUnitSphere N) (A : ConcreteMatrixState N) :
    v.1 ⬝ᵥ ((concreteCOET K A).conjTranspose *ᵥ v.1) =
      star (concreteCOEB v K A) := by
  have hstarstar : star (h7StarVector v) = v.1 := by
    funext i
    simp [h7StarVector]
  have hstarMul := Matrix.star_mulVec
    (concreteCOET K A) (h7StarVector v)
  calc
    v.1 ⬝ᵥ ((concreteCOET K A).conjTranspose *ᵥ v.1) =
        (v.1 ᵥ* (concreteCOET K A).conjTranspose) ⬝ᵥ v.1 :=
      Matrix.dotProduct_mulVec _ _ _
    _ = star (concreteCOET K A *ᵥ h7StarVector v) ⬝ᵥ
          star (h7StarVector v) := by
      rw [hstarMul, hstarstar]
    _ = star (h7StarVector v ⬝ᵥ
          (concreteCOET K A *ᵥ h7StarVector v)) :=
      Matrix.star_dotProduct_star _ _
    _ = star (concreteCOEB v K A) := by
      rw [concreteCOEB_eq_star_dot_mulVec]

/-- `concreteCOEX` is the real part of the projective trace pairing.

The proof is elementary and is kept locally so this support file does not
import the broader historical cubic-identification module. -/
theorem concreteCOEX_eq_re_complexProjectiveTracePair_h7
    {N K : ℕ} (v : ComplexUnitSphere N) (A : ConcreteMatrixState N) :
    concreteCOEX v K A =
      (complexProjectiveTracePair v (concreteCOEZ K A)).re := by
  unfold concreteCOEX concreteRealTrace
  rw [complexProjectiveTracePair_eq_trace]

theorem h7ProjectivePair_Z_eq_ofReal_X
    {N K : ℕ} (v : ComplexUnitSphere N) (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    complexProjectiveTracePair v (concreteCOEZ K A) =
      (concreteCOEX v K A : ℂ) := by
  have hre := concreteCOEX_eq_re_complexProjectiveTracePair_h7
    (K := K) v A
  have him := complexProjectiveTracePair_im_eq_zero_of_isHermitian
    v (concreteCOEZ K A) (concreteCOEZ_isHermitian_of_support A hsupport)
  apply Complex.ext
  · simpa using hre.symm
  · simpa using him

theorem h7StarVector_dot_self
    {N : ℕ} (v : ComplexUnitSphere N) :
    h7StarVector v ⬝ᵥ v.1 = 1 := by
  have hpair := complexProjectiveTracePair_eq_star_dot_mulVec
    v (1 : ConcreteMatrixState N)
  rw [complexProjectiveTracePair_eq_trace, Matrix.mul_one,
    trace_complexRankOneProjection] at hpair
  simpa using hpair.symm

theorem h7StarVector_dot_Z_mulVec
    {N K : ℕ} (v : ComplexUnitSphere N) (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    h7StarVector v ⬝ᵥ (concreteCOEZ K A *ᵥ v.1) =
      (concreteCOEX v K A : ℂ) := by
  calc
    h7StarVector v ⬝ᵥ (concreteCOEZ K A *ᵥ v.1) =
        complexProjectiveTracePair v (concreteCOEZ K A) :=
      (complexProjectiveTracePair_eq_star_dot_mulVec
        v (concreteCOEZ K A)).symm
    _ = (concreteCOEX v K A : ℂ) :=
      h7ProjectivePair_Z_eq_ofReal_X v A hsupport

theorem h7SupportH_inv_plain_star_pair
    {N K : ℕ} (v : ComplexUnitSphere N) (A : ConcreteMatrixState N)
    (hsymm : (unscaleCOECorner K A).IsSymm)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    v.1 ⬝ᵥ ((h7SupportH K A)⁻¹ *ᵥ h7StarVector v) =
      (1 + concreteCOEX v K A : ℝ) := by
  calc
    v.1 ⬝ᵥ ((h7SupportH K A)⁻¹ *ᵥ h7StarVector v) =
        h7StarVector v ⬝ᵥ
          (((h7SupportH K A)⁻¹).transpose *ᵥ v.1) :=
      (Matrix.dotProduct_transpose_mulVec
        ((h7SupportH K A)⁻¹) (h7StarVector v) v.1).symm
    _ = h7StarVector v ⬝ᵥ ((h7SupportG K A)⁻¹ *ᵥ v.1) := by
      rw [h7SupportH_inv_transpose_eq_supportG_inv A hsymm]
    _ = h7StarVector v ⬝ᵥ ((1 + concreteCOEZ K A) *ᵥ v.1) := by
      rw [h7SupportG_inv_eq_one_add_Z A hsupport]
    _ = h7StarVector v ⬝ᵥ v.1 +
          h7StarVector v ⬝ᵥ (concreteCOEZ K A *ᵥ v.1) := by
      rw [Matrix.add_mulVec, Matrix.one_mulVec, dotProduct_add]
    _ = (1 + concreteCOEX v K A : ℝ) := by
      rw [h7StarVector_dot_self,
        h7StarVector_dot_Z_mulVec v A hsupport]
      norm_num

theorem h7SupportH_inv_C_pair
    {N K : ℕ} (v : ComplexUnitSphere N) (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    (h7StarVector v ᵥ* unscaleCOECorner K A) ⬝ᵥ
        ((h7SupportH K A)⁻¹ *ᵥ
          ((unscaleCOECorner K A).conjTranspose *ᵥ v.1)) =
      (concreteCOEX v K A : ℂ) := by
  let C := unscaleCOECorner K A
  let H := h7SupportH K A
  change (h7StarVector v ᵥ* C) ⬝ᵥ
      (H⁻¹ *ᵥ (C.conjTranspose *ᵥ v.1)) = _
  calc
    (h7StarVector v ᵥ* C) ⬝ᵥ
        (H⁻¹ *ᵥ (C.conjTranspose *ᵥ v.1)) =
      h7StarVector v ⬝ᵥ
        (C *ᵥ (H⁻¹ *ᵥ (C.conjTranspose *ᵥ v.1))) :=
      (Matrix.dotProduct_mulVec (h7StarVector v) C _).symm
    _ = h7StarVector v ⬝ᵥ
        ((C * H⁻¹ * C.conjTranspose) *ᵥ v.1) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    _ = h7StarVector v ⬝ᵥ (concreteCOEZ K A *ᵥ v.1) := by
      unfold concreteCOEZ
      rfl
    _ = (concreteCOEX v K A : ℂ) :=
      h7StarVector_dot_Z_mulVec v A hsupport

theorem h7SupportH_inv_B_pair
    {N K : ℕ} (v : ComplexUnitSphere N) (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    (h7StarVector v ᵥ* unscaleCOECorner K A) ⬝ᵥ
        ((h7SupportH K A)⁻¹ *ᵥ h7StarVector v) =
      concreteCOEB v K A := by
  let C := unscaleCOECorner K A
  let H := h7SupportH K A
  change (h7StarVector v ᵥ* C) ⬝ᵥ (H⁻¹ *ᵥ h7StarVector v) = _
  calc
    (h7StarVector v ᵥ* C) ⬝ᵥ (H⁻¹ *ᵥ h7StarVector v) =
        h7StarVector v ⬝ᵥ (C *ᵥ (H⁻¹ *ᵥ h7StarVector v)) :=
      (Matrix.dotProduct_mulVec (h7StarVector v) C _).symm
    _ = h7StarVector v ⬝ᵥ ((C * H⁻¹) *ᵥ h7StarVector v) := by
      rw [Matrix.mulVec_mulVec]
    _ = h7StarVector v ⬝ᵥ (concreteCOET K A *ᵥ h7StarVector v) := by
      rw [h7ConcreteCOET_eq_C_mul_supportH_inv A hsupport]
    _ = concreteCOEB v K A :=
      (concreteCOEB_eq_star_dot_mulVec v A).symm

theorem h7SupportH_inv_starB_pair
    {N K : ℕ} (v : ComplexUnitSphere N) (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    v.1 ⬝ᵥ ((h7SupportH K A)⁻¹ *ᵥ
        ((unscaleCOECorner K A).conjTranspose *ᵥ v.1)) =
      star (concreteCOEB v K A) := by
  calc
    v.1 ⬝ᵥ ((h7SupportH K A)⁻¹ *ᵥ
        ((unscaleCOECorner K A).conjTranspose *ᵥ v.1)) =
      v.1 ⬝ᵥ (((h7SupportH K A)⁻¹ *
        (unscaleCOECorner K A).conjTranspose) *ᵥ v.1) := by
          rw [Matrix.mulVec_mulVec]
    _ = v.1 ⬝ᵥ ((concreteCOET K A).conjTranspose *ᵥ v.1) := by
      rw [h7ConcreteCOET_conjTranspose_eq_supportH_inv_mul A hsupport]
    _ = star (concreteCOEB v K A) :=
      h7Plain_dot_conjTranspose_mulVec_eq_star_B v A

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
