import A4.Target
import Mathlib.Analysis.Matrix.LDL
import Mathlib.LinearAlgebra.Matrix.Block

open scoped BigOperators Matrix

noncomputable section

namespace A4Research

open Matrix InnerProductSpace

/-- Gram--Schmidt preserves the coefficient on the original basis vector. -/
theorem gramSchmidt_repr_self {𝕜 E ι : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [LinearOrder ι]
    [LocallyFiniteOrderBot ι] [WellFoundedLT ι]
    (b : Module.Basis ι 𝕜 E) (i : ι) :
    b.repr (gramSchmidt 𝕜 b i) i = 1 := by
  have h := congrArg (fun x : E => b.repr x i) (gramSchmidt_def'' 𝕜 b i)
  simp only [map_add, map_sum, map_smul, Finsupp.add_apply,
    Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul] at h
  have hz : ∑ j ∈ Finset.Iio i,
      (inner 𝕜 (gramSchmidt 𝕜 b j) (b i) /
        (‖gramSchmidt 𝕜 b j‖ : 𝕜) ^ 2) * b.repr (gramSchmidt 𝕜 b j) i = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [gramSchmidt_triangular (Finset.mem_Iio.mp hj) b, mul_zero]
  simpa only [hz, add_zero, Module.Basis.repr_self_apply, ite_true] using h.symm

variable {n : Type*} [Fintype n] [LinearOrder n] [WellFoundedLT n]
    [LocallyFiniteOrderBot n] {S : Matrix n n ℝ}

/-- The Gram--Schmidt LDL inverse factor has unit diagonal. -/
theorem ldl_lowerInv_diag (hS : S.PosDef) (i : n) :
    LDL.lowerInv hS i i = 1 := by
  let := Sᵀ.toNormedAddCommGroup hS.transpose
  let := Sᵀ.toInnerProductSpace hS.transpose.posSemidef
  simpa only [Pi.basisFun_repr, LDL.lowerInv] using
    gramSchmidt_repr_self (Pi.basisFun ℝ n) i

/-- Both inverse and forward LDL factors are lower triangular. -/
theorem ldl_lowerInv_triangular (hS : S.PosDef) :
    (LDL.lowerInv hS).IsLowerTriangular := by
  intro i j hij
  exact LDL.lowerInv_triangular hS hij

theorem ldl_lower_triangular (hS : S.PosDef) :
    (LDL.lower hS).IsLowerTriangular := by
  exact blockTriangular_inv_of_blockTriangular (ldl_lowerInv_triangular hS)

omit [WellFoundedLT n] [LocallyFiniteOrderBot n] in
/-- A diagonal entry of a product of lower triangular matrices has only one
nonzero summand. -/
theorem lowerTriangular_mul_diag {A B : Matrix n n ℝ}
    (hA : A.IsLowerTriangular) (hB : B.IsLowerTriangular) (i : n) :
    (A * B) i i = A i i * B i i := by
  classical
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_single i
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with hj | hj
    · rw [hB hj, mul_zero]
    · rw [hA hj, zero_mul]
  · simp

theorem ldl_lower_diag (hS : S.PosDef) (i : n) :
    LDL.lower hS i i = 1 := by
  have h := congrArg (fun A : Matrix n n ℝ => A i i)
    (Matrix.mul_inv_of_invertible (LDL.lowerInv hS))
  rw [← LDL.lower, lowerTriangular_mul_diag
    (ldl_lowerInv_triangular hS) (ldl_lower_triangular hS),
    ldl_lowerInv_diag, one_mul, Matrix.one_apply_eq] at h
  exact h

/-- Every LDL diagonal coordinate is strictly positive. -/
theorem ldl_diagEntries_pos (hS : S.PosDef) (i : n) :
    0 < LDL.diagEntries hS i := by
  have hD : (LDL.diag hS).PosDef := by
    rw [LDL.diag_eq_lowerInv_conj]
    exact (isUnit_of_invertible (LDL.lowerInv hS)).posDef_star_right_conjugate_iff.mpr hS
  exact (posDef_diagonal_iff.mp hD) i

/-- The positive square roots of the LDL pivots. -/
def choleskyDiagonal (hS : S.PosDef) : Matrix n n ℝ :=
  diagonal (fun i => Real.sqrt (LDL.diagEntries hS i))

/-- A lower triangular real Cholesky factor obtained from the pinned LDL theorem. -/
def cholesky (hS : S.PosDef) : Matrix n n ℝ :=
  LDL.lower hS * choleskyDiagonal hS

theorem choleskyDiagonal_posDef (hS : S.PosDef) :
    (choleskyDiagonal hS).PosDef := by
  apply posDef_diagonal_iff.mpr
  intro i
  exact Real.sqrt_pos.mpr (ldl_diagEntries_pos hS i)

theorem choleskyDiagonal_mul_transpose (hS : S.PosDef) :
    choleskyDiagonal hS * (choleskyDiagonal hS)ᵀ = LDL.diag hS := by
  simp only [choleskyDiagonal, diagonal_transpose, diagonal_mul_diagonal, LDL.diag]
  congr 1
  ext i
  exact Real.mul_self_sqrt (ldl_diagEntries_pos hS i).le

theorem cholesky_triangular (hS : S.PosDef) :
    (cholesky hS).IsLowerTriangular := by
  exact (ldl_lower_triangular hS).mul (blockTriangular_diagonal _)

theorem cholesky_diag (hS : S.PosDef) (i : n) :
    cholesky hS i i = Real.sqrt (LDL.diagEntries hS i) := by
  simp only [cholesky, choleskyDiagonal, Matrix.mul_diagonal,
    ldl_lower_diag, one_mul]

theorem cholesky_diag_pos (hS : S.PosDef) (i : n) :
    0 < cholesky hS i i := by
  rw [cholesky_diag]
  exact Real.sqrt_pos.mpr (ldl_diagEntries_pos hS i)

/-- Every real positive definite matrix is the transpose square of the
explicit lower triangular factor above. -/
theorem cholesky_mul_transpose (hS : S.PosDef) :
    cholesky hS * (cholesky hS)ᵀ = S := by
  simp only [cholesky, transpose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (choleskyDiagonal hS), choleskyDiagonal_mul_transpose]
  simpa only [conjTranspose_eq_transpose_of_trivial, Matrix.mul_assoc] using
    LDL.lower_conj_diag hS

theorem cholesky_det_pos (hS : S.PosDef) :
    0 < Matrix.det (cholesky hS) := by
  rw [det_of_isLowerTriangular _ (cholesky_triangular hS)]
  exact Finset.prod_pos fun i _ => cholesky_diag_pos hS i

theorem cholesky_isUnit (hS : S.PosDef) : IsUnit (cholesky hS) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  exact isUnit_iff_ne_zero.mpr (cholesky_det_pos hS).ne'

/-- The triangular-coordinate determinant used by the Wishart density. -/
theorem determinant_eq_cholesky_diagonal_sq (hS : S.PosDef) :
    Matrix.det S = ∏ i : n, cholesky hS i i ^ 2 := by
  conv_lhs => rw [← cholesky_mul_transpose hS]
  rw [Matrix.det_mul, Matrix.det_transpose,
    det_of_isLowerTriangular _ (cholesky_triangular hS)]
  simpa only [pow_two] using (Finset.prod_mul_distrib
    (s := Finset.univ) (f := fun i : n => cholesky hS i i)
    (g := fun i : n => cholesky hS i i)).symm

theorem determinant_eq_ldl_pivots (hS : S.PosDef) :
    Matrix.det S = ∏ i : n, LDL.diagEntries hS i := by
  rw [determinant_eq_cholesky_diagonal_sq hS]
  apply Finset.prod_congr rfl
  intro i _
  rw [cholesky_diag, Real.sq_sqrt (ldl_diagEntries_pos hS i).le]

omit [WellFoundedLT n] [LocallyFiniteOrderBot n] in
theorem lowerTriangular_isUnit {L : Matrix n n ℝ}
    (hL : L.IsLowerTriangular) (hp : ∀ i, 0 < L i i) : IsUnit L := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply isUnit_iff_ne_zero.mpr
  rw [det_of_isLowerTriangular _ hL]
  exact (Finset.prod_pos fun i _ => hp i).ne'

omit [WellFoundedLT n] [LocallyFiniteOrderBot n] in
theorem lowerTriangular_inv_diag_pos {L : Matrix n n ℝ}
    (hL : L.IsLowerTriangular) (hp : ∀ i, 0 < L i i) (i : n) :
    0 < L⁻¹ i i := by
  let := (lowerTriangular_isUnit hL hp).invertible
  have hi : L⁻¹.IsLowerTriangular := blockTriangular_inv_of_blockTriangular hL
  have heq := congrArg (fun M : Matrix n n ℝ => M i i)
    (Matrix.inv_mul_of_invertible L)
  rw [lowerTriangular_mul_diag hi hL, Matrix.one_apply_eq] at heq
  have hprod : 0 < L⁻¹ i i * L i i := by rw [heq]; norm_num
  exact (mul_pos_iff_of_pos_right (hp i)).mp hprod

omit [WellFoundedLT n] [LocallyFiniteOrderBot n] in
/-- A lower triangular orthogonal real matrix with positive diagonal is the
identity. This proves uniqueness of positive-diagonal Cholesky coordinates. -/
theorem lowerTriangular_orthogonal_eq_one {U : Matrix n n ℝ}
    (hU : U.IsLowerTriangular) (hp : ∀ i, 0 < U i i)
    (ho : U * Uᵀ = 1) : U = 1 := by
  let := (lowerTriangular_isUnit hU hp).invertible
  have hi : U⁻¹.IsLowerTriangular := blockTriangular_inv_of_blockTriangular hU
  rw [Matrix.inv_eq_right_inv ho] at hi
  have hd : ∀ i, U i i = 1 := by
    intro i
    have heq := congrArg (fun M : Matrix n n ℝ => M i i) ho
    rw [lowerTriangular_mul_diag hU hi, Matrix.transpose_apply,
      Matrix.one_apply_eq] at heq
    nlinarith [hp i]
  ext i j
  by_cases hij : i = j
  · subst j
    simp [hd i]
  · rw [Matrix.one_apply_ne hij]
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact hU hlt
    · exact hi hgt

omit [WellFoundedLT n] [LocallyFiniteOrderBot n] in
/-- The square map is injective on lower triangular matrices with positive
diagonal, in every finite real dimension. -/
theorem cholesky_square_injective {A B : Matrix n n ℝ}
    (hA : A.IsLowerTriangular) (hB : B.IsLowerTriangular)
    (hpA : ∀ i, 0 < A i i) (hpB : ∀ i, 0 < B i i)
    (heq : A * Aᵀ = B * Bᵀ) : A = B := by
  let := (lowerTriangular_isUnit hB hpB).invertible
  have hBi : B⁻¹.IsLowerTriangular := blockTriangular_inv_of_blockTriangular hB
  let U := B⁻¹ * A
  have hU : U.IsLowerTriangular := hBi.mul hA
  have hpU : ∀ i, 0 < U i i := by
    intro i
    change 0 < (B⁻¹ * A) i i
    rw [lowerTriangular_mul_diag hBi hA]
    exact mul_pos (lowerTriangular_inv_diag_pos hB hpB i) (hpA i)
  have ho : U * Uᵀ = 1 := by
    calc
      U * Uᵀ = (B⁻¹ * (A * Aᵀ)) * (B⁻¹)ᵀ := by
        simp only [U, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = (B⁻¹ * (B * Bᵀ)) * (B⁻¹)ᵀ := by rw [heq]
      _ = (B⁻¹ * B) * (Bᵀ * (B⁻¹)ᵀ) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [Matrix.inv_mul_of_invertible, ← Matrix.transpose_mul,
        Matrix.inv_mul_of_invertible, Matrix.transpose_one, Matrix.one_mul]
  have hu : U = 1 := lowerTriangular_orthogonal_eq_one hU hpU ho
  calc
    A = B * (B⁻¹ * A) := (Matrix.mul_inv_cancel_left_of_invertible B A).symm
    _ = B := by rw [show B⁻¹ * A = 1 from hu, Matrix.mul_one]

/-- Positive-diagonal lower triangular real matrices. -/
def PositiveTriangular (n : Type*) [LT n] :=
  {L : Matrix n n ℝ // L.IsLowerTriangular ∧ ∀ i, 0 < L i i}

/-- Cholesky gives actual coordinates on the SPD cone; this is an equivalence,
not yet a differentiable change-of-variables assertion. -/
def choleskyEquiv : {S : Matrix n n ℝ // S.PosDef} ≃ PositiveTriangular n where
  toFun S := ⟨cholesky S.2, cholesky_triangular S.2, cholesky_diag_pos S.2⟩
  invFun L := ⟨L.1 * L.1ᵀ, by
    let := (lowerTriangular_isUnit L.2.1 L.2.2).invertible
    simpa only [conjTranspose_eq_transpose_of_trivial] using
      Matrix.PosDef.mul_conjTranspose_self L.1 (Matrix.vecMul_injective_of_invertible L.1)⟩
  left_inv S := by
    apply Subtype.ext
    exact cholesky_mul_transpose S.2
  right_inv L := by
    apply Subtype.ext
    apply cholesky_square_injective (cholesky_triangular _) L.2.1
      (cholesky_diag_pos _) L.2.2
    exact cholesky_mul_transpose _

end A4Research
