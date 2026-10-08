import A3.HermitianCoordinates
import A3.WishartCholeskyFactorization

open Matrix MeasureTheory
open scoped BigOperators ComplexOrder

noncomputable section

namespace A3Research

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {K : Type*} [RCLike K]

/-- Squared positive diagonal pivots and the conjugates of strict lower entries. -/
def wishartCholeskyMatrix (x : HermitianCoordinates n K) : Matrix (Fin n) (Fin n) K :=
  fun i j ↦ if h : i = j then (Real.sqrt (x.1 i) : K)
    else if hlt : j < i then star (x.2 ⟨(j, i), hlt⟩) else 0

@[simp] theorem wishartCholeskyMatrix_diag (x : HermitianCoordinates n K) (i : Fin n) :
    wishartCholeskyMatrix x i i = (Real.sqrt (x.1 i) : K) := by
  simp [wishartCholeskyMatrix]

@[simp] theorem wishartCholeskyMatrix_lower (x : HermitianCoordinates n K)
    (ij : HermitianCoordinateIndex n) :
    wishartCholeskyMatrix x ij.1.2 ij.1.1 = star (x.2 ij) := by
  simp [wishartCholeskyMatrix, ne_of_gt ij.2, ij.2]

theorem wishartCholeskyMatrix_triangular (x : HermitianCoordinates n K) :
    (wishartCholeskyMatrix x).IsLowerTriangular := by
  intro i j hij
  change i < j at hij
  simp [wishartCholeskyMatrix, ne_of_lt hij, not_lt_of_ge hij.le]

def wishartCholeskyDomain (n : ℕ) (K : Type*) [RCLike K] :
    Set (HermitianCoordinates n K) := {x | ∀ i, 0 < x.1 i}

def wishartPositiveDefiniteDomain (n : ℕ) (K : Type*) [RCLike K] :
    Set (HermitianCoordinates n K) := {x | (hermitianMatrixOfCoordinates x).PosDef}

def wishartGramCoordinates (x : HermitianCoordinates n K) : HermitianCoordinates n K :=
  hermitianCoordinateProjection (wishartCholeskyMatrix x * (wishartCholeskyMatrix x).conjTranspose)

theorem hermitianMatrixOf_wishartGramCoordinates (x : HermitianCoordinates n K) :
    hermitianMatrixOfCoordinates (wishartGramCoordinates x) =
      wishartCholeskyMatrix x * (wishartCholeskyMatrix x).conjTranspose :=
  hermitianMatrixOfCoordinates_projection _ (isHermitian_mul_conjTranspose_self _)

theorem continuous_wishartCholeskyMatrix :
    Continuous (wishartCholeskyMatrix : HermitianCoordinates n K → _) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  unfold wishartCholeskyMatrix
  split_ifs <;> fun_prop

theorem continuous_wishartGramCoordinates :
    Continuous (wishartGramCoordinates : HermitianCoordinates n K → _) := by
  unfold wishartGramCoordinates
  have hstar : Continuous (fun x : HermitianCoordinates n K ↦
      (wishartCholeskyMatrix x).conjTranspose) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact ((continuous_apply i).comp
      ((continuous_apply j).comp continuous_wishartCholeskyMatrix)).star
  exact continuous_hermitianCoordinateProjection.comp
    (continuous_wishartCholeskyMatrix.mul hstar)

theorem wishartCholeskyMatrix_isUnit (x : HermitianCoordinates n K)
    (hx : x ∈ wishartCholeskyDomain n K) : IsUnit (wishartCholeskyMatrix x) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply isUnit_iff_ne_zero.mpr
  rw [Matrix.det_of_isLowerTriangular _ (wishartCholeskyMatrix_triangular x),
    Finset.prod_ne_zero_iff]
  intro i _
  simp only [wishartCholeskyMatrix_diag, ne_eq, RCLike.ofReal_eq_zero]
  exact (Real.sqrt_pos.mpr (hx i)).ne'

theorem wishartGramCoordinates_posDef (x : HermitianCoordinates n K)
    (hx : x ∈ wishartCholeskyDomain n K) :
    wishartGramCoordinates x ∈ wishartPositiveDefiniteDomain n K := by
  change (hermitianMatrixOfCoordinates (wishartGramCoordinates x)).PosDef
  rw [hermitianMatrixOf_wishartGramCoordinates]
  simpa only [Matrix.mul_one, Matrix.star_eq_conjTranspose] using
    (wishartCholeskyMatrix_isUnit x hx).posDef_star_right_conjugate_iff.mpr
      (show (1 : Matrix (Fin n) (Fin n) K).PosDef from Matrix.PosDef.one)

/-- Determinant in squared-pivot coordinates has no square-root factor left. -/
theorem det_wishartGramCoordinates (x : HermitianCoordinates n K)
    (hx : x ∈ wishartCholeskyDomain n K) :
    (hermitianMatrixOfCoordinates (wishartGramCoordinates x)).det =
      ((∏ i, x.1 i : ℝ) : K) := by
  rw [hermitianMatrixOf_wishartGramCoordinates, Matrix.det_mul,
    Matrix.det_conjTranspose,
    Matrix.det_of_isLowerTriangular _ (wishartCholeskyMatrix_triangular x),
    star_prod, ← Finset.prod_mul_distrib]
  simp only [wishartCholeskyMatrix_diag, RCLike.star_def, RCLike.conj_ofReal]
  simp only [← RCLike.ofReal_mul, Real.mul_self_sqrt (le_of_lt (hx _))]
  exact (map_prod (algebraMap ℝ K) _ _).symm

def wishartCoordinatesOfCholesky {S : Matrix (Fin n) (Fin n) K} (hS : S.PosDef) :
    HermitianCoordinates n K :=
  (fun i ↦ RCLike.re (wishartCholesky hS i i) ^ 2,
    fun ij ↦ star (wishartCholesky hS ij.1.2 ij.1.1))

theorem wishartCoordinatesOfCholesky_mem {S : Matrix (Fin n) (Fin n) K}
    (hS : S.PosDef) : wishartCoordinatesOfCholesky hS ∈ wishartCholeskyDomain n K := by
  intro i
  exact sq_pos_of_pos (wishartCholesky_diag_re_pos hS i)

theorem wishartCholeskyMatrix_ofCholesky {S : Matrix (Fin n) (Fin n) K}
    (hS : S.PosDef) : wishartCholeskyMatrix (wishartCoordinatesOfCholesky hS) =
      wishartCholesky hS := by
  ext i j
  rcases lt_trichotomy i j with hij | hij | hij
  · rw [wishartCholeskyMatrix_triangular _ hij, wishartCholesky_triangular hS hij]
  · subst j
    rw [wishartCholeskyMatrix_diag]
    change (Real.sqrt (RCLike.re (wishartCholesky hS i i) ^ 2) : K) = _
    rw [Real.sqrt_sq (wishartCholesky_diag_re_pos hS i).le]
    apply RCLike.ext <;>
      simp [wishartCholesky_diag_im_zero]
  · rw [wishartCholeskyMatrix_lower _ ⟨(j, i), hij⟩]
    simp only [wishartCoordinatesOfCholesky, star_star]

theorem wishartGramCoordinates_surjOn :
    Set.SurjOn (wishartGramCoordinates : HermitianCoordinates n K → _)
      (wishartCholeskyDomain n K) (wishartPositiveDefiniteDomain n K) := by
  intro y hy
  let x := wishartCoordinatesOfCholesky hy
  refine ⟨x, wishartCoordinatesOfCholesky_mem hy, ?_⟩
  change hermitianCoordinateProjection
    (wishartCholeskyMatrix (wishartCoordinatesOfCholesky hy) *
      (wishartCholeskyMatrix (wishartCoordinatesOfCholesky hy)).conjTranspose) = y
  rw [wishartCholeskyMatrix_ofCholesky, wishartCholesky_mul_conjTranspose,
    hermitianCoordinateProjection_ofCoordinates]

end A3Research
