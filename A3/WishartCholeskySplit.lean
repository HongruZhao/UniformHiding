import A3.WishartCholeskyCoordinates

open Matrix
open scoped BigOperators

noncomputable section

namespace A3Research

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {K : Type*} [RCLike K]

def wishartCoordinatesCons (p : ℝ) (z : Fin n → K) (y : HermitianCoordinates n K) :
    HermitianCoordinates (n + 1) K :=
  (Fin.cons p y.1, fun ij ↦
    if hi : ij.1.1 = 0 then
      z (ij.1.2.pred (ne_of_gt (lt_of_le_of_lt (Fin.zero_le _) ij.2)))
    else y.2 ⟨(ij.1.1.pred hi,
      ij.1.2.pred (ne_of_gt (lt_of_le_of_lt (Fin.zero_le _) ij.2))), by
        apply Fin.succ_lt_succ_iff.mp
        simpa only [Fin.succ_pred] using ij.2⟩)

@[simp] theorem wishartCoordinatesCons_diag_zero (p : ℝ) (z : Fin n → K)
    (y : HermitianCoordinates n K) : (wishartCoordinatesCons p z y).1 0 = p := by
  simp [wishartCoordinatesCons]

@[simp] theorem wishartCoordinatesCons_diag_succ (p : ℝ) (z : Fin n → K)
    (y : HermitianCoordinates n K) (i : Fin n) :
    (wishartCoordinatesCons p z y).1 i.succ = y.1 i := by
  simp [wishartCoordinatesCons]

@[simp] theorem wishartCoordinatesCons_upper_first (p : ℝ) (z : Fin n → K)
    (y : HermitianCoordinates n K) (j : Fin n) :
    (wishartCoordinatesCons p z y).2 ⟨(0, j.succ), Fin.succ_pos j⟩ = z j := by
  simp [wishartCoordinatesCons]

@[simp] theorem wishartCoordinatesCons_upper_succ (p : ℝ) (z : Fin n → K)
    (y : HermitianCoordinates n K) (ij : HermitianCoordinateIndex n) :
    (wishartCoordinatesCons p z y).2
      ⟨(ij.1.1.succ, ij.1.2.succ), Fin.succ_lt_succ_iff.mpr ij.2⟩ = y.2 ij := by
  simp [wishartCoordinatesCons]

def wishartCoordinatesSplit (x : HermitianCoordinates (n + 1) K) :
    ℝ × ((Fin n → K) × HermitianCoordinates n K) :=
  (x.1 0, (fun j ↦ x.2 ⟨(0, j.succ), Fin.succ_pos j⟩,
    (fun i ↦ x.1 i.succ,
      fun ij ↦ x.2 ⟨(ij.1.1.succ, ij.1.2.succ), Fin.succ_lt_succ_iff.mpr ij.2⟩)))

theorem wishartCoordinatesSplit_cons (p : ℝ) (z : Fin n → K)
    (y : HermitianCoordinates n K) :
    wishartCoordinatesSplit (wishartCoordinatesCons p z y) = (p, (z, y)) := by
  apply Prod.ext
  · simp [wishartCoordinatesSplit]
  · apply Prod.ext
    · funext j
      simp [wishartCoordinatesSplit]
    · apply Prod.ext <;> funext i <;> simp [wishartCoordinatesSplit]

theorem wishartCoordinatesCons_split (x : HermitianCoordinates (n + 1) K) :
    wishartCoordinatesCons (wishartCoordinatesSplit x).1
      (wishartCoordinatesSplit x).2.1 (wishartCoordinatesSplit x).2.2 = x := by
  apply Prod.ext
  · funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp [wishartCoordinatesSplit]
  · funext ij
    rcases Fin.eq_zero_or_eq_succ ij.1.1 with hi | ⟨i, hi⟩
    · have hj : ij.1.2 ≠ 0 := ne_of_gt (lt_of_le_of_lt (Fin.zero_le _) ij.2)
      obtain ⟨j, hj'⟩ := Fin.eq_succ_of_ne_zero hj
      have heq : ij = ⟨(0, j.succ), Fin.succ_pos j⟩ := by
        apply Subtype.ext
        exact Prod.ext hi hj'
      subst ij
      simp [wishartCoordinatesSplit]
    · have hj : ij.1.2 ≠ 0 := ne_of_gt (lt_of_le_of_lt (Fin.zero_le _) ij.2)
      obtain ⟨j, hj'⟩ := Fin.eq_succ_of_ne_zero hj
      have hij : i < j := Fin.succ_lt_succ_iff.mp (hi ▸ hj' ▸ ij.2)
      have heq : ij = ⟨(i.succ, j.succ), Fin.succ_lt_succ_iff.mpr hij⟩ := by
        apply Subtype.ext
        exact Prod.ext hi hj'
      subst ij
      simpa only [wishartCoordinatesSplit] using wishartCoordinatesCons_upper_succ
        (x.1 0) (fun j ↦ x.2 ⟨(0, j.succ), Fin.succ_pos j⟩)
        (fun i ↦ x.1 i.succ,
          fun ij ↦ x.2 ⟨(ij.1.1.succ, ij.1.2.succ), Fin.succ_lt_succ_iff.mpr ij.2⟩)
        ⟨(i, j), hij⟩

def wishartCoordinatesSplitLinearEquiv (n : ℕ) (K : Type*) [RCLike K] :
    HermitianCoordinates (n + 1) K ≃ₗ[ℝ]
      ℝ × ((Fin n → K) × HermitianCoordinates n K) where
  toFun := wishartCoordinatesSplit
  invFun := fun y ↦ wishartCoordinatesCons y.1 y.2.1 y.2.2
  left_inv := wishartCoordinatesCons_split
  right_inv := fun y ↦ wishartCoordinatesSplit_cons y.1 y.2.1 y.2.2
  map_add' := by
    intro x y
    rfl
  map_smul' := by
    intro r x
    rfl

theorem wishartCoordinatesCons_mem_domain (p : ℝ) (z : Fin n → K)
    (y : HermitianCoordinates n K) :
    wishartCoordinatesCons p z y ∈ wishartCholeskyDomain (n + 1) K ↔
      0 < p ∧ y ∈ wishartCholeskyDomain n K := by
  constructor
  · intro h
    exact ⟨by simpa using h 0, fun i ↦ by simpa using h i.succ⟩
  · rintro ⟨hp, hy⟩ i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simpa using hp
    · simpa using hy j

@[simp] theorem wishartCholeskyMatrix_cons_zero_zero (p : ℝ) (z : Fin n → K)
    (y : HermitianCoordinates n K) :
    wishartCholeskyMatrix (wishartCoordinatesCons p z y) 0 0 = (Real.sqrt p : K) := by
  simp

@[simp] theorem wishartCholeskyMatrix_cons_zero_succ (p : ℝ) (z : Fin n → K)
    (y : HermitianCoordinates n K) (j : Fin n) :
    wishartCholeskyMatrix (wishartCoordinatesCons p z y) 0 j.succ = 0 :=
  wishartCholeskyMatrix_triangular _ (Fin.succ_pos j)

@[simp] theorem wishartCholeskyMatrix_cons_succ_zero (p : ℝ) (z : Fin n → K)
    (y : HermitianCoordinates n K) (i : Fin n) :
    wishartCholeskyMatrix (wishartCoordinatesCons p z y) i.succ 0 = star (z i) := by
  rw [wishartCholeskyMatrix_lower _ ⟨(0, i.succ), Fin.succ_pos i⟩]
  simp

@[simp] theorem wishartCholeskyMatrix_cons_succ_succ (p : ℝ) (z : Fin n → K)
    (y : HermitianCoordinates n K) (i j : Fin n) :
    wishartCholeskyMatrix (wishartCoordinatesCons p z y) i.succ j.succ =
      wishartCholeskyMatrix y i j := by
  unfold wishartCholeskyMatrix
  by_cases hij : i = j
  · subst j
    simp
  · by_cases hji : j < i
    · simp only [Fin.succ_inj, dif_neg hij, Fin.succ_lt_succ_iff, dif_pos hji]
      rw [wishartCoordinatesCons_upper_succ p z y ⟨(j, i), hji⟩]
    · simp [hij, hji]

end A3Research
