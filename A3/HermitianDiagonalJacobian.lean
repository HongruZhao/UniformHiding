import A3.HermitianCoordinates

open scoped BigOperators Matrix

noncomputable section

namespace A3Research

variable {n : ℕ} {K : Type*} [RCLike K]

/-- A zero-diagonal skew-Hermitian matrix in the actual independent angular coordinates. -/
def hermitianAngularSkewMatrix (a : HermitianCoordinateIndex n → K) :
    Matrix (Fin n) (Fin n) K :=
  fun i j ↦ if h : i = j then 0
    else if hlt : i < j then a ⟨(i, j), hlt⟩
    else -star (a ⟨(j, i), lt_of_le_of_ne (le_of_not_gt hlt) (fun hji ↦ h hji.symm)⟩)

@[simp] theorem hermitianAngularSkewMatrix_diag (a : HermitianCoordinateIndex n → K)
    (i : Fin n) : hermitianAngularSkewMatrix a i i = 0 := by
  simp [hermitianAngularSkewMatrix]

@[simp] theorem hermitianAngularSkewMatrix_upper (a : HermitianCoordinateIndex n → K)
    (ij : HermitianCoordinateIndex n) : hermitianAngularSkewMatrix a ij.1.1 ij.1.2 = a ij := by
  simp [hermitianAngularSkewMatrix, ij.2, ne_of_lt ij.2]

@[simp] theorem hermitianAngularSkewMatrix_lower (a : HermitianCoordinateIndex n → K)
    (ij : HermitianCoordinateIndex n) :
    hermitianAngularSkewMatrix a ij.1.2 ij.1.1 = -star (a ij) := by
  simp [hermitianAngularSkewMatrix, ne_of_gt ij.2, not_lt_of_ge ij.2.le]

theorem hermitianAngularSkewMatrix_skewHermitian (a : HermitianCoordinateIndex n → K) :
    (hermitianAngularSkewMatrix a).conjTranspose = -hermitianAngularSkewMatrix a := by
  ext i j
  change star (hermitianAngularSkewMatrix a j i) = -hermitianAngularSkewMatrix a i j
  rcases lt_trichotomy i j with hij | hij | hij
  · rw [hermitianAngularSkewMatrix_lower a ⟨(i, j), hij⟩,
      hermitianAngularSkewMatrix_upper a ⟨(i, j), hij⟩]
    simp
  · subst j
    simp
  · rw [hermitianAngularSkewMatrix_lower a ⟨(j, i), hij⟩,
      hermitianAngularSkewMatrix_upper a ⟨(j, i), hij⟩]
    simp

def hermitianAngularSkewLinearMap (n : ℕ) (K : Type*) [RCLike K] :
    (HermitianCoordinateIndex n → K) →ₗ[ℝ] Matrix (Fin n) (Fin n) K where
  toFun := hermitianAngularSkewMatrix
  map_add' := by
    intro a b
    ext i j
    by_cases hij : i = j
    · simp [hermitianAngularSkewMatrix, hij]
    · by_cases hlt : i < j <;> simp [hermitianAngularSkewMatrix, hij, hlt, add_comm]
  map_smul' := by
    intro r a
    ext i j
    by_cases hij : i = j
    · simp [hermitianAngularSkewMatrix, hij]
    · by_cases hlt : i < j <;>
        simp [hermitianAngularSkewMatrix, hij, hlt, RCLike.real_smul_eq_coe_mul]

def hermitianDiagonalDifferential (lambda : Fin n → ℝ) :
    HermitianCoordinates n K →ₗ[ℝ] HermitianCoordinates n K :=
  LinearMap.prodMap LinearMap.id
    (LinearMap.pi fun ij ↦ ((lambda ij.1.2 - lambda ij.1.1) • (LinearMap.id : K →ₗ[ℝ] K)).comp
      (LinearMap.proj ij))

@[simp] theorem hermitianDiagonalDifferential_apply (lambda : Fin n → ℝ)
    (x : HermitianCoordinates n K) :
    hermitianDiagonalDifferential lambda x =
      (x.1, fun ij ↦ (lambda ij.1.2 - lambda ij.1.1) • x.2 ij) := rfl

def hermitianVandermonde (lambda : Fin n → ℝ) : ℝ :=
  ∏ ij : HermitianCoordinateIndex n, |lambda ij.1.2 - lambda ij.1.1|

theorem hermitianDiagonalDifferential_det (lambda : Fin n → ℝ) :
    LinearMap.det (hermitianDiagonalDifferential (K := K) lambda) =
      ∏ ij : HermitianCoordinateIndex n,
        (lambda ij.1.2 - lambda ij.1.1) ^ Module.finrank ℝ K := by
  rw [hermitianDiagonalDifferential, LinearMap.det_prodMap, LinearMap.det_id,
    one_mul, LinearMap.det_pi]
  simp

theorem abs_det_hermitianDiagonalDifferential (lambda : Fin n → ℝ) :
    |LinearMap.det (hermitianDiagonalDifferential (K := K) lambda)| =
      hermitianVandermonde lambda ^ Module.finrank ℝ K := by
  rw [hermitianDiagonalDifferential_det, Finset.abs_prod]
  simp_rw [abs_pow]
  rw [Finset.prod_pow]
  rfl

theorem abs_det_hermitianDiagonalDifferential_real (lambda : Fin n → ℝ) :
    |LinearMap.det (hermitianDiagonalDifferential (K := ℝ) lambda)| =
      hermitianVandermonde lambda := by
  simpa using abs_det_hermitianDiagonalDifferential (K := ℝ) lambda

theorem abs_det_hermitianDiagonalDifferential_complex (lambda : Fin n → ℝ) :
    |LinearMap.det (hermitianDiagonalDifferential (K := ℂ) lambda)| =
      hermitianVandermonde lambda ^ 2 := by
  simpa [Complex.finrank_real_complex] using
    abs_det_hermitianDiagonalDifferential (K := ℂ) lambda

theorem hermitianDiagonalDifferential_det_ne_zero (lambda : Fin n → ℝ)
    (hlambda : Function.Injective lambda) :
    LinearMap.det (hermitianDiagonalDifferential (K := K) lambda) ≠ 0 := by
  rw [hermitianDiagonalDifferential_det]
  apply Finset.prod_ne_zero_iff.mpr
  intro ij _
  apply pow_ne_zero
  exact sub_ne_zero.mpr (fun h ↦ (ne_of_lt ij.2).symm (hlambda h))

/-- The actual diagonal orbit tangent, before unitary conjugation. -/
def hermitianDiagonalOrbitTangent (lambda : Fin n → ℝ) (x : HermitianCoordinates n K) :
    Matrix (Fin n) (Fin n) K :=
  hermitianAngularSkewMatrix x.2 * Matrix.diagonal (fun i ↦ (lambda i : K)) -
    Matrix.diagonal (fun i ↦ (lambda i : K)) * hermitianAngularSkewMatrix x.2 +
      Matrix.diagonal (fun i ↦ (x.1 i : K))

theorem hermitianDiagonalOrbitTangent_reconstruct (lambda : Fin n → ℝ)
    (x : HermitianCoordinates n K) :
    hermitianMatrixOfCoordinates (hermitianDiagonalDifferential lambda x) =
      hermitianDiagonalOrbitTangent lambda x := by
  ext i j
  simp only [hermitianDiagonalOrbitTangent, Matrix.sub_apply, Matrix.add_apply,
    Matrix.mul_diagonal, Matrix.diagonal_mul]
  rcases lt_trichotomy i j with hij | hij | hij
  · rw [hermitianMatrixOfCoordinates_upper _ ⟨(i, j), hij⟩,
      hermitianAngularSkewMatrix_upper _ ⟨(i, j), hij⟩]
    simp [hermitianDiagonalDifferential, ne_of_lt hij,
      RCLike.real_smul_eq_coe_mul]
    ring
  · subst j
    simp
  · rw [hermitianMatrixOfCoordinates_lower _ ⟨(j, i), hij⟩,
      hermitianAngularSkewMatrix_lower _ ⟨(j, i), hij⟩]
    simp [hermitianDiagonalDifferential, ne_of_gt hij,
      RCLike.real_smul_eq_coe_mul]
    ring

theorem hermitianVandermonde_eq_strictPairs (lambda : Fin n → ℝ) :
    hermitianVandermonde lambda =
      ∏ ij ∈ LogdetLean.GramHafnian.UltimateHiding.DenseScore.a2StrictPairs n,
        |lambda ij.2 - lambda ij.1| := by
  classical
  let s : Finset (Fin n × Fin n) := Finset.univ.filter fun ij ↦ ij.1 < ij.2
  have hs : ∀ ij, ij ∈ s ↔ ij.1 < ij.2 := by simp [s]
  change (∏ ij : {p : Fin n × Fin n // p.1 < p.2},
    (fun p : Fin n × Fin n ↦ |lambda p.2 - lambda p.1|) ij.val) = _
  rw [← Finset.prod_subtype s hs (fun p ↦ |lambda p.2 - lambda p.1|)]
  apply Finset.prod_congr
  · ext ij
    simp [s, LogdetLean.GramHafnian.UltimateHiding.DenseScore.a2StrictPairs]
  · intros
    rfl

end A3Research
