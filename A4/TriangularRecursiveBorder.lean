import A4.TriangularSchurComplement
import A4.WishartDensityBartlett

open scoped BigOperators Matrix
open MeasureTheory

noncomputable section
namespace A4Research

local instance (d : ℕ) : BorelSpace (MatsumotoPaper.RealMatrix d) := ⟨rfl⟩

/-- The lower triangular factor for one scalar border of an SPD matrix. -/
def bartlettBorderFactor {d : ℕ} (t : ℝ) (z : Fin d → ℝ)
    (V : MatsumotoPaper.SymPosDef d) : MatsumotoPaper.RealMatrix (d + 1) :=
  Matrix.of (Fin.cons (Fin.cons (positiveSqrt t) (0 : Fin d → ℝ))
    (fun i => Fin.cons (z i) (cholesky V.2 i)))

theorem bartlettBorderFactor_triangular {d : ℕ} (t : ℝ) (z : Fin d → ℝ)
    (V : MatsumotoPaper.SymPosDef d) :
    (bartlettBorderFactor t z V).IsLowerTriangular := by
  intro i j hij
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero => exact (lt_irrefl _ hij).elim
    | succ j => simp [bartlettBorderFactor]
  | succ i =>
    cases j using Fin.cases with
    | zero => exact (Fin.not_lt_zero _ hij).elim
    | succ j =>
      simp only [bartlettBorderFactor, Matrix.of_apply, Fin.cons_succ]
      exact cholesky_triangular V.2 (by simpa using hij)

theorem bartlettBorderFactor_diag_pos {d : ℕ} (t : ℝ) (z : Fin d → ℝ)
    (V : MatsumotoPaper.SymPosDef d) (i : Fin (d + 1)) :
    0 < bartlettBorderFactor t z V i i := by
  cases i using Fin.cases with
  | zero => simpa [bartlettBorderFactor] using positiveSqrt_pos t
  | succ i => simpa [bartlettBorderFactor] using cholesky_diag_pos V.2 i

/-- The first column plus an independent SPD tail, in total raw coordinates. -/
def bartlettBorderMatrix {d : ℕ} (t : ℝ) (z : Fin d → ℝ)
    (V : MatsumotoPaper.SymPosDef d) : MatsumotoPaper.RealMatrix (d + 1) :=
  matrixBorder (positiveSqrt t ^ 2) (fun i => positiveSqrt t * z i)
    (Matrix.of (fun i j => z i * z j + V.1 i j))

theorem bartlettBorderFactor_square {d : ℕ} (t : ℝ) (z : Fin d → ℝ)
    (V : MatsumotoPaper.SymPosDef d) :
    bartlettBorderFactor t z V * (bartlettBorderFactor t z V)ᵀ =
      bartlettBorderMatrix t z V := by
  ext i j
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero => simp [bartlettBorderFactor, bartlettBorderMatrix, Matrix.mul_apply, Fin.sum_univ_succ, pow_two]
    | succ j =>
      simp [bartlettBorderFactor, bartlettBorderMatrix, Matrix.mul_apply, Fin.sum_univ_succ]
  | succ i =>
    cases j using Fin.cases with
    | zero =>
      simp [bartlettBorderFactor, bartlettBorderMatrix, Matrix.mul_apply, Fin.sum_univ_succ,
        mul_comm]
    | succ j =>
      have h := congrFun (congrFun (cholesky_mul_transpose V.2) i) j
      simp only [Matrix.mul_apply, Matrix.transpose_apply] at h
      simp [bartlettBorderFactor, bartlettBorderMatrix, Matrix.mul_apply,
        Fin.sum_univ_succ, h]

/-- Bartlett's scalar border remains SPD even on the raw-coordinate null set. -/
def bartlettBorder {d : ℕ} (q : (ℝ × (Fin d → ℝ)) × MatsumotoPaper.SymPosDef d) :
    MatsumotoPaper.SymPosDef (d + 1) :=
  ⟨bartlettBorderMatrix q.1.1 q.1.2 q.2, by
    have hu := lowerTriangular_isUnit
      (bartlettBorderFactor_triangular q.1.1 q.1.2 q.2)
      (bartlettBorderFactor_diag_pos q.1.1 q.1.2 q.2)
    let := hu.invertible
    rw [← bartlettBorderFactor_square]
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.PosDef.mul_conjTranspose_self (bartlettBorderFactor q.1.1 q.1.2 q.2)
        (Matrix.vecMul_injective_of_invertible _)⟩

theorem measurable_bartlettBorder (d : ℕ) :
    Measurable (@bartlettBorder d) := by
  apply Measurable.subtype_mk
  change @Measurable _ (Fin (d + 1) → Fin (d + 1) → ℝ) _ (borel _)
    (fun q : (ℝ × (Fin d → ℝ)) × MatsumotoPaper.SymPosDef d =>
      bartlettBorderMatrix q.1.1 q.1.2 q.2)
  rw [← @BorelSpace.measurable_eq (Fin (d + 1) → Fin (d + 1) → ℝ) _
    MeasurableSpace.pi Pi.borelSpace]
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  have hu : Measurable (fun q : (ℝ × (Fin d → ℝ)) × MatsumotoPaper.SymPosDef d =>
      positiveSqrt q.1.1) := measurable_positiveSqrt.comp (measurable_fst.comp measurable_fst)
  have hz (i : Fin d) : Measurable
      (fun q : (ℝ × (Fin d → ℝ)) × MatsumotoPaper.SymPosDef d => q.1.2 i) := by fun_prop
  have hv (i j : Fin d) : Measurable
      (fun q : (ℝ × (Fin d → ℝ)) × MatsumotoPaper.SymPosDef d => q.2.1 i j) := by
    have hc : Continuous (fun A : MatsumotoPaper.RealMatrix d => A i j) := by fun_prop
    exact hc.borel_measurable.comp (measurable_subtype_coe.comp measurable_snd)
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero => simpa only [bartlettBorderMatrix, matrixBorder, Matrix.of_apply,
        Fin.cons_zero] using hu.pow_const 2
    | succ j => simpa only [bartlettBorderMatrix, matrixBorder, Matrix.of_apply,
        Fin.cons_zero, Fin.cons_succ] using hu.fun_mul (hz j)
  | succ i =>
    cases j using Fin.cases with
    | zero => simpa only [bartlettBorderMatrix, matrixBorder, Matrix.of_apply,
        Fin.cons_zero, Fin.cons_succ] using hu.fun_mul (hz i)
    | succ j => simpa only [bartlettBorderMatrix, matrixBorder, Matrix.of_apply,
        Fin.cons_succ] using ((hz i).fun_mul (hz j)).fun_add (hv i j)

/-- Splitting a bordered matrix action into its scalar and vector parts. -/
theorem matrixBorder_mulVec_cons {d : ℕ} (c : ℝ) (b : Fin d → ℝ)
    (D : MatsumotoPaper.RealMatrix d) (u : ℝ) (z : Fin d → ℝ) :
    matrixBorder c b D *ᵥ Fin.cons u z =
      Fin.cons (c * u + b ⬝ᵥ z) (u • b + D *ᵥ z) := by
  ext i
  cases i using Fin.cases <;>
    simp [matrixBorder, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mul_comm]

/-- The full quadratic form separates into the first-column tilt. -/
theorem matrixBorder_quadratic {d : ℕ} (c : ℝ) (b : Fin d → ℝ)
    (D : MatsumotoPaper.RealMatrix d) (u : ℝ) (z : Fin d → ℝ) :
    (Fin.cons u z) ⬝ᵥ (matrixBorder c b D *ᵥ Fin.cons u z) =
      c * u ^ 2 + z ⬝ᵥ (D *ᵥ z) + 2 * u * (b ⬝ᵥ z) := by
  rw [matrixBorder_mulVec_cons]
  change (Matrix.vecCons u z) ⬝ᵥ
    (Matrix.vecCons (c * u + b ⬝ᵥ z) (u • b + D *ᵥ z)) = _
  rw [Matrix.cons_dotProduct_cons, dotProduct_add, dotProduct_smul]
  simp only [smul_eq_mul]
  rw [dotProduct_comm z b]
  ring

theorem matrixTilt_border {d : ℕ}
    {theta : MatsumotoPaper.RealMatrix (d + 1)} (htheta : theta.IsHermitian) :
    theta = matrixBorder (theta 0 0) (fun i => theta 0 i.succ) (matrixTail theta) := by
  ext i j
  cases i using Fin.cases with
  | zero => cases j using Fin.cases <;> simp
  | succ i =>
    cases j using Fin.cases with
    | zero => exact congrFun (congrFun htheta.eq 0) i.succ
    | succ j => rfl

/-- The SPD tail is embedded with a zero first row and first column. -/
def matrixEmbedTail {d : ℕ} (V : MatsumotoPaper.RealMatrix d) :
    MatsumotoPaper.RealMatrix (d + 1) := matrixBorder 0 0 V

theorem bartlettBorderMatrix_rankOne {d : ℕ} (t : ℝ) (z : Fin d → ℝ)
    (V : MatsumotoPaper.SymPosDef d) :
    bartlettBorderMatrix t z V =
      Matrix.vecMulVec (Fin.cons (positiveSqrt t) z) (Fin.cons (positiveSqrt t) z) +
        matrixEmbedTail V.1 := by
  ext i j
  cases i using Fin.cases <;> cases j using Fin.cases <;>
    simp [bartlettBorderMatrix, matrixEmbedTail, Matrix.vecMulVec, pow_two, mul_comm]

theorem matrixEmbedTail_trace {d : ℕ} (theta : MatsumotoPaper.RealMatrix (d + 1))
    (V : MatsumotoPaper.RealMatrix d) :
    Matrix.trace (theta * matrixEmbedTail V) = Matrix.trace (matrixTail theta * V) := by
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, matrixTail, Matrix.submatrix,
    matrixEmbedTail, Fin.sum_univ_succ]

/-- Exact factorization of the bordered matrix's transform integrand. -/
theorem bartlettBorder_etr {d : ℕ} {theta : MatsumotoPaper.RealMatrix (d + 1)}
    (htheta : theta.IsHermitian) (q : (ℝ × (Fin d → ℝ)) × MatsumotoPaper.SymPosDef d)
    (ht : 0 < q.1.1) :
    MatsumotoPaper.etr (theta * (bartlettBorder q).1) =
      bartlettColumnTilt (theta 0 0) (matrixTail theta) (fun i => theta 0 i.succ)
        q.1.1 q.1.2 * MatsumotoPaper.etr (matrixTail theta * q.2.1) := by
  change Real.exp (Matrix.trace (theta * bartlettBorderMatrix q.1.1 q.1.2 q.2)) = _
  rw [bartlettBorderMatrix_rankOne, Matrix.mul_add, Matrix.trace_add,
    Matrix.mul_vecMulVec, Matrix.trace_vecMulVec,
    matrixEmbedTail_trace, dotProduct_comm]
  rw [matrixTilt_border htheta, matrixBorder_quadratic,
    positiveSqrt_eq_sqrt ht, Real.sq_sqrt ht.le, Real.exp_add]
  rfl

/-- The border determinant is the squared pivot times the tail determinant. -/
theorem bartlettBorder_det {d : ℕ}
    (q : (ℝ × (Fin d → ℝ)) × MatsumotoPaper.SymPosDef d) :
    Matrix.det (bartlettBorder q).1 = positiveSqrt q.1.1 ^ 2 * Matrix.det q.2.1 := by
  have hL : Matrix.det (bartlettBorderFactor q.1.1 q.1.2 q.2) =
      positiveSqrt q.1.1 * Matrix.det (cholesky q.2.2) := by
    rw [Matrix.det_succ_row_zero]
    simp [bartlettBorderFactor, Fin.sum_univ_succ, Matrix.submatrix,
      Fin.zero_succAbove]
    left
    congr 1
  have hV : Matrix.det q.2.1 = Matrix.det (cholesky q.2.2) ^ 2 := by
    have h := congrArg Matrix.det (cholesky_mul_transpose q.2.2)
    simpa only [Matrix.det_mul, Matrix.det_transpose, pow_two] using h.symm
  change Matrix.det (bartlettBorderMatrix q.1.1 q.1.2 q.2) = _
  rw [← bartlettBorderFactor_square, Matrix.det_mul, Matrix.det_transpose, hL, hV]
  ring

theorem bartlettBorder_det_of_pos {d : ℕ}
    (q : (ℝ × (Fin d → ℝ)) × MatsumotoPaper.SymPosDef d) (ht : 0 < q.1.1) :
    Matrix.det (bartlettBorder q).1 = q.1.1 * Matrix.det q.2.1 := by
  rw [bartlettBorder_det, positiveSqrt_eq_sqrt ht, Real.sq_sqrt ht.le]

end A4Research
