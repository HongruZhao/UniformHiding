import LogdetLean.GramHafnian.UltimateHiding.Dense.H1_HaarColumnParameter
import LogdetLean.GramHafnian.UltimateHiding.Dense.H1_RowDeletionGramAlgebra
import Mathlib.Tactic

open scoped InnerProductSpace RealInnerProductSpace ComplexConjugate Matrix
open MeasureTheory ProbabilityTheory

namespace LogdetLean.GramHafnian.UltimateHiding.Dense
noncomputable section

def h1TopCoordinates {N r : ℕ}
    (x : EuclideanSpace ℂ (Fin (N + r))) :
    EuclideanSpace ℂ (Fin N) :=
  WithLp.toLp 2 (fun i ↦ x (Fin.castAdd r i))

theorem h1TopRealProjection_eq_embed {N r : ℕ}
    (x : EuclideanSpace ℂ (Fin (N + r))) :
    ((h1TopRealSubspace N r).orthogonalProjectionOnto x :
        EuclideanSpace ℂ (Fin (N + r))) =
      (h1TopComplexEmbed N r (h1TopCoordinates x)).1 := by
  let K := h1TopRealSubspace N r
  let y : EuclideanSpace ℂ (Fin (N + r)) :=
    (h1TopComplexEmbed N r (h1TopCoordinates x)).1
  have hy : y ∈ K := (h1TopComplexEmbed N r (h1TopCoordinates x)).2
  have horth : x - y ∈ K.orthogonal := by
    intro w hw
    rw [real_inner_comm]
    simp only [PiLp.inner_apply]
    rw [Fin.sum_univ_add]
    have htop : (∑ i : Fin N,
        inner ℝ ((x - y) (Fin.castAdd r i))
          (w (Fin.castAdd r i))) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hyi : y (Fin.castAdd r i) = x (Fin.castAdd r i) := by
        simp [y, h1TopCoordinates]
      simp [hyi]
    have htail : (∑ j : Fin r,
        inner ℝ ((x - y) (Fin.natAdd N j))
          (w (Fin.natAdd N j))) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hwj : w (Fin.natAdd N j) = 0 := hw j
      rw [hwj]
      simp
    rw [htop, htail, add_zero]
  have hproj : K.starProjection x = y :=
    K.eq_starProjection_of_mem_orthogonal hy horth
  exact hproj

theorem h1TopRealIsometry_projection_eq_coordinates {N r : ℕ}
    (x : EuclideanSpace ℂ (Fin (N + r))) :
    h1TopRealIsometryEquiv N r
        ((h1TopRealSubspace N r).orthogonalProjectionOnto x) =
      h1TopCoordinates x := by
  ext i
  change ((h1TopRealSubspace N r).orthogonalProjectionOnto x :
      EuclideanSpace ℂ (Fin (N + r))) (Fin.castAdd r i) =
    x (Fin.castAdd r i)
  rw [h1TopRealProjection_eq_embed]
  simp [h1TopCoordinates]

theorem h1ColumnRankOne_eq_normSq_smul_directionProjection
    {N : ℕ} (hN : 1 ≤ N) (x : EuclideanSpace ℂ (Fin N)) :
    h1ColumnRankOne x =
      (((‖x‖ ^ 2 : ℝ) : ℂ) •
        complexRankOneProjection (h1GaussianComplexSphereDirection hN x)) := by
  by_cases hx : x = 0
  · subst x
    ext i j
    change (0 : ℂ) * star (0 : ℂ) =
      (((‖(0 : EuclideanSpace ℂ (Fin N))‖ ^ 2 : ℝ) : ℂ) *
        ((h1GaussianComplexSphereDirection hN 0).1 i *
          star ((h1GaussianComplexSphereDirection hN 0).1 j)))
    simp
  · ext i j
    change x i * star (x j) =
      ((‖x‖ ^ 2 : ℝ) : ℂ) *
        ((h1GaussianComplexSphereDirection hN x).1 i *
          star ((h1GaussianComplexSphereDirection hN x).1 j))
    rw [coe_h1GaussianComplexSphereDirection_of_ne hN hx,
      h1_unitDirection_eq_inv_norm_smul x hx]
    simp only [PiLp.smul_apply, Complex.real_smul,
      Complex.ofReal_inv, Complex.ofReal_pow]
    have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    rw [star_mul]
    have hstarInv : star ((((‖x‖ : ℝ) : ℂ))⁻¹) =
        (((‖x‖ : ℝ) : ℂ))⁻¹ := by simp
    rw [hstarInv]
    have hnC : ((‖x‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn
    field_simp [hnC]

theorem h1AmbientSphereParameter_rankOne {N r : ℕ}
    (hN : 1 ≤ N) (z : ComplexUnitSphere (N + r)) :
    h1ColumnRankOne (h1TopCoordinates z.1) =
      ((((1 - (h1AmbientSphereParameter (r := r) hN z).1 : ℝ) : ℂ)) •
        complexRankOneProjection
          (h1AmbientSphereParameter (r := r) hN z).2) := by
  let K := h1TopRealSubspace N r
  let top := ‖K.orthogonalProjectionOnto z.1‖ ^ 2
  let tail := ‖K.orthogonal.orthogonalProjectionOnto z.1‖ ^ 2
  have hcoord := h1TopRealIsometry_projection_eq_coordinates z.1
  have htop : top = ‖h1TopCoordinates z.1‖ ^ 2 := by
    have h := congrArg (fun x : EuclideanSpace ℂ (Fin N) ↦ ‖x‖ ^ 2) hcoord
    simpa [top] using h
  have hzNorm : ‖z.1‖ = 1 := mem_sphere_zero_iff_norm.mp z.2
  have hpyth : top + tail = 1 := by
    have h := K.norm_sq_eq_add_norm_sq_projection z.1
    rw [hzNorm] at h
    norm_num at h
    simpa [top, tail] using h.symm
  have hq :
      1 - (h1AmbientSphereParameter (r := r) hN z).1 =
        ‖h1TopCoordinates z.1‖ ^ 2 := by
    unfold h1AmbientSphereParameter h1AmbientGaussianParameter
      h1TopTailDataToParameter h1AmbientTopTailData
      h1TopDirectionEnergy LogdetLean.gammaRatio
    dsimp only
    change 1 - tail / (tail + top) = ‖h1TopCoordinates z.1‖ ^ 2
    rw [show tail + top = 1 by linarith [hpyth]]
    rw [div_one]
    linarith [hpyth, htop]
  have hv :
      (h1AmbientSphereParameter (r := r) hN z).2 =
        h1GaussianComplexSphereDirection hN (h1TopCoordinates z.1) := by
    unfold h1AmbientSphereParameter h1AmbientGaussianParameter
      h1TopTailDataToParameter h1AmbientTopTailData
      h1TopDirectionEnergy
    dsimp only
    rw [hcoord]
  calc
    h1ColumnRankOne (h1TopCoordinates z.1) =
        (((‖h1TopCoordinates z.1‖ ^ 2 : ℝ) : ℂ) •
          complexRankOneProjection
            (h1GaussianComplexSphereDirection hN (h1TopCoordinates z.1))) :=
      h1ColumnRankOne_eq_normSq_smul_directionProjection hN _
    _ = ((((1 - (h1AmbientSphereParameter (r := r) hN z).1 : ℝ) : ℂ)) •
        complexRankOneProjection
          (h1AmbientSphereParameter (r := r) hN z).2) := by
      rw [hq, hv]

theorem h1AmbientSphereParameter_fst_nonneg {N r : ℕ}
    (hN : 1 ≤ N) (z : ComplexUnitSphere (N + r)) :
    0 ≤ (h1AmbientSphereParameter (r := r) hN z).1 := by
  unfold h1AmbientSphereParameter h1AmbientGaussianParameter
    h1TopTailDataToParameter h1AmbientTopTailData
    h1TopDirectionEnergy LogdetLean.gammaRatio
  dsimp only
  exact div_nonneg (sq_nonneg _)
    (add_nonneg (sq_nonneg _) (sq_nonneg _))

theorem h1TopCoordinates_sphereDimCast_apply
    {N r a : ℕ} (h : a = N + r) (z : ComplexUnitSphere a)
    (i : Fin N) :
    h1TopCoordinates ((h1SphereDimCast h) z).1 i =
      z.1 (Fin.cast h.symm (Fin.castAdd r i)) := by
  subst a
  rfl

theorem h1TopCoordinates_haarColumn_eq_topLastColumn
    {N m : ℕ} (hNm : N ≤ m)
    (U : Matrix.unitaryGroup (Fin (m + 1)) ℂ) :
    h1TopCoordinates
        ((h1SphereDimCast
          (Nat.add_sub_of_le (hNm.trans (Nat.le_succ m))).symm)
          (haarLastColumnSphere
            (Nat.succ_le_succ (Nat.zero_le m)) U)).1 =
      h1TopLastColumn (hNm.trans (Nat.le_succ m)) U := by
  ext i
  rw [h1TopCoordinates_sphereDimCast_apply,
    haarLastColumnSphere_apply]
  unfold h1TopLastColumn
  congr 2

theorem h1AmbientUnitaryColumnParameter_rankOne
    {N m : ℕ} (hN : 1 ≤ N) (hNm : N ≤ m)
    (U : Matrix.unitaryGroup (Fin (m + 1)) ℂ) :
    h1ColumnRankOne
        (h1TopLastColumn (hNm.trans (Nat.le_succ m)) U) =
      ((((1 - (h1HaarColumnParameter hN hNm
          (haarLastColumnSphere
            (Nat.succ_le_succ (Nat.zero_le m)) U)).1 : ℝ) : ℂ)) •
        complexRankOneProjection
          (h1HaarColumnParameter hN hNm
            (haarLastColumnSphere
              (Nat.succ_le_succ (Nat.zero_le m)) U)).2) := by
  unfold h1HaarColumnParameter
  rw [← h1TopCoordinates_haarColumn_eq_topLastColumn hNm U]
  exact h1AmbientSphereParameter_rankOne hN _

theorem h1HaarColumnParameter_fst_nonneg
    {N m : ℕ} (hN : 1 ≤ N) (hNm : N ≤ m)
    (z : ComplexUnitSphere (m + 1)) :
    0 ≤ (h1HaarColumnParameter hN hNm z).1 := by
  unfold h1HaarColumnParameter
  exact h1AmbientSphereParameter_fst_nonneg hN _

end
end LogdetLean.GramHafnian.UltimateHiding.Dense

