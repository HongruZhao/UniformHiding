import A2.Target

/-!
# The exact real diagonal Jacobian in squared Takagi radii

The real coordinate model has one real/imaginary coordinate for every
independent upper-triangular complex entry.  At a positive diagonal Takagi
matrix the radial and angular tangent operator is diagonal in this model.
-/

open scoped BigOperators Matrix

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

abbrev TakagiRealCoordinateIndex (N : ℕ) := ComplexSymmetricCoordinateIndex N × Fin 2
abbrev TakagiRealCoordinates (N : ℕ) := TakagiRealCoordinateIndex N → ℝ

def takagiRealComplexCoordinatesEquiv (N : ℕ) :
    TakagiRealCoordinates N ≃ₗ[ℝ] ComplexSymmetricCoordinates N where
  toFun x ij := ⟨x (ij, 0), x (ij, 1)⟩
  invFun x p := if p.2 = 0 then (x p.1).re else (x p.1).im
  map_add' x y := by ext ij <;> rfl
  map_smul' a x := by
    funext ij
    apply Complex.ext <;> simp [Complex.real_smul]
  left_inv x := by
    funext ⟨ij, b⟩
    fin_cases b <;> rfl
  right_inv x := by
    funext ij
    apply Complex.ext <;> rfl

def takagiDiagonalDifferentialWeight {N : ℕ} (lambda : Fin N → ℝ)
    (p : TakagiRealCoordinateIndex N) : ℝ :=
  if p.1.val.1 = p.1.val.2 then
    if p.2 = 0 then (2 * Real.sqrt (lambda p.1.val.1))⁻¹
    else 2 * Real.sqrt (lambda p.1.val.1)
  else if p.2 = 0 then Real.sqrt (lambda p.1.val.2) - Real.sqrt (lambda p.1.val.1)
    else Real.sqrt (lambda p.1.val.2) + Real.sqrt (lambda p.1.val.1)

def takagiDiagonalDifferentialMatrix {N : ℕ} (lambda : Fin N → ℝ) :
    Matrix (TakagiRealCoordinateIndex N) (TakagiRealCoordinateIndex N) ℝ :=
  Matrix.diagonal (takagiDiagonalDifferentialWeight lambda)

def takagiDiagonalDifferential {N : ℕ} (lambda : Fin N → ℝ) :
    TakagiRealCoordinates N →ₗ[ℝ] TakagiRealCoordinates N :=
  (takagiDiagonalDifferentialMatrix lambda).toLin'

theorem takagiDiagonalDifferential_pairProduct {N : ℕ} (lambda : Fin N → ℝ)
    (hpos : ∀ i, 0 < lambda i) (ij : ComplexSymmetricCoordinateIndex N) :
    (∏ b : Fin 2, takagiDiagonalDifferentialWeight lambda (ij, b)) =
      if ij.val.1 = ij.val.2 then 1 else lambda ij.val.2 - lambda ij.val.1 := by
  classical
  rw [Fin.prod_univ_two]
  by_cases h : ij.val.1 = ij.val.2
  · have hs : 2 * Real.sqrt (lambda ij.val.2) ≠ 0 := by
      exact mul_ne_zero (by norm_num) (Real.sqrt_pos.mpr (hpos _)).ne'
    simp only [takagiDiagonalDifferentialWeight, h, if_pos,
      show (1 : Fin 2) ≠ 0 by decide, if_neg]
    exact inv_mul_cancel₀ hs
  · simp only [takagiDiagonalDifferentialWeight, h, if_false, if_pos]
    simp only [show (1 : Fin 2) ≠ 0 by decide, if_false]
    have hi := Real.sq_sqrt (le_of_lt (hpos ij.val.1))
    have hj := Real.sq_sqrt (le_of_lt (hpos ij.val.2))
    nlinarith

theorem prod_upper_diagonal_one_eq_prod_strict {N : ℕ} (f : Fin N × Fin N → ℝ) :
    (∏ ij : ComplexSymmetricCoordinateIndex N, if ij.val.1 = ij.val.2 then 1 else f ij.val) =
      ∏ p ∈ H6DensityTransform.strictPairs N, f p := by
  classical
  let upper : Finset (Fin N × Fin N) := Finset.univ.filter fun p => p.1 ≤ p.2
  have hu : ∀ p, p ∈ upper ↔ p.1 ≤ p.2 := by simp [upper]
  change (∏ ij : {p : Fin N × Fin N // p.1 ≤ p.2},
    (fun p : Fin N × Fin N => if p.1 = p.2 then 1 else f p) ij.val) = _
  rw [← Finset.prod_subtype upper hu (fun p => if p.1 = p.2 then 1 else f p)]
  have hstrict : H6DensityTransform.strictPairs N ⊆ upper := by
    intro p hp
    simp only [H6DensityTransform.strictPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
      true_and] at hp
    exact (hu p).mpr (le_of_lt hp)
  rw [← Finset.prod_subset hstrict]
  · apply Finset.prod_congr rfl
    intro p hp
    have hp' : p.1 < p.2 := by simpa [H6DensityTransform.strictPairs] using hp
    rw [if_neg (ne_of_lt hp')]
  · intro p hp hn
    have hp' := (hu p).mp hp
    have hn' : ¬ p.1 < p.2 := by simpa [H6DensityTransform.strictPairs] using hn
    have heq : p.1 = p.2 := le_antisymm hp' (le_of_not_gt hn')
    simp only [heq, if_pos]

theorem takagiDiagonalDifferentialMatrix_det {N : ℕ} (lambda : Fin N → ℝ)
    (hpos : ∀ i, 0 < lambda i) :
    (takagiDiagonalDifferentialMatrix lambda).det =
      ∏ p ∈ H6DensityTransform.strictPairs N, (lambda p.2 - lambda p.1) := by
  rw [takagiDiagonalDifferentialMatrix, Matrix.det_diagonal, Fintype.prod_prod_type]
  simp_rw [takagiDiagonalDifferential_pairProduct lambda hpos]
  exact prod_upper_diagonal_one_eq_prod_strict (fun p => lambda p.2 - lambda p.1)

theorem abs_takagiDiagonalDifferentialMatrix_det {N : ℕ} (lambda : Fin N → ℝ)
    (hpos : ∀ i, 0 < lambda i) :
    |(takagiDiagonalDifferentialMatrix lambda).det| = H6DensityTransform.vandermondeAbs N lambda := by
  rw [takagiDiagonalDifferentialMatrix_det lambda hpos]
  simp only [H6DensityTransform.vandermondeAbs, Finset.abs_prod, abs_sub_comm]

theorem takagiDiagonalDifferential_det {N : ℕ} (lambda : Fin N → ℝ)
    (hpos : ∀ i, 0 < lambda i) :
    LinearMap.det (takagiDiagonalDifferential lambda) =
      ∏ p ∈ H6DensityTransform.strictPairs N, (lambda p.2 - lambda p.1) := by
  rw [takagiDiagonalDifferential, ← LinearMap.det_toMatrix']
  simpa only [LinearMap.toMatrix'_toLin'] using
    takagiDiagonalDifferentialMatrix_det lambda hpos

theorem takagiDiagonalDifferential_det_ne_zero {N : ℕ} (lambda : Fin N → ℝ)
    (hpos : ∀ i, 0 < lambda i) (hdistinct : Function.Injective lambda) :
    LinearMap.det (takagiDiagonalDifferential lambda) ≠ 0 := by
  rw [takagiDiagonalDifferential_det lambda hpos]
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  have hp' : p.1 < p.2 := by simpa [H6DensityTransform.strictPairs] using hp
  exact sub_ne_zero.mpr (fun h => (ne_of_lt hp').symm (hdistinct h))

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
