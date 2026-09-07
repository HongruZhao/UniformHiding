import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ClassicalCOEExternal
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H6_CoordinateAlgebra
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic
import Mathlib.Topology.Instances.Matrix

/-!
# The forward Takagi coordinate map used in H6

This file contains only finite-dimensional algebra and measurability.  For a
unitary matrix `U` and a nonnegative real vector `lambda`, it studies

`C = U * diagonal (sqrt lambda) * U.transpose`.

No distributional, Jacobian, or random-matrix input is used here.
-/

open scoped BigOperators ComplexConjugate ComplexOrder
open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open H6CoordinateAlgebra

/-- The nonnegative diagonal factor in the forward Takagi map. -/
def h6TakagiDiagonal {N : ℕ} (lambda : Fin N → ℝ) : ConcreteMatrixState N :=
  Matrix.diagonal fun i ↦ ((Real.sqrt (lambda i) : ℝ) : ℂ)

/-- The forward Takagi formula on an arbitrary complex matrix.  Keeping this
ambient version makes its coordinatewise measurability transparent. -/
def h6TakagiForwardMatrix {N : ℕ}
    (U : ConcreteMatrixState N) (lambda : Fin N → ℝ) : ConcreteMatrixState N :=
  U * h6TakagiDiagonal lambda * U.transpose

/-- The forward Takagi formula with the unitary constraint encoded in the
type of its first argument. -/
def h6TakagiForward {N : ℕ}
    (U : Matrix.unitaryGroup (Fin N) ℂ) (lambda : Fin N → ℝ) :
    ConcreteMatrixState N :=
  h6TakagiForwardMatrix U.1 lambda

/-- The diagonal square-root map is continuous. -/
theorem continuous_h6TakagiDiagonal (N : ℕ) :
    Continuous (h6TakagiDiagonal (N := N)) := by
  unfold h6TakagiDiagonal
  fun_prop

/-- The diagonal square-root map is measurable. -/
theorem measurable_h6TakagiDiagonal (N : ℕ) :
    Measurable (h6TakagiDiagonal (N := N)) := by
  refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
  simp only [h6TakagiDiagonal, Matrix.diagonal_apply]
  split_ifs <;> fun_prop

/-- The ambient forward Takagi map is jointly measurable. -/
theorem measurable_h6TakagiForwardMatrix (N : ℕ) :
    Measurable
      (fun p : ConcreteMatrixState N × (Fin N → ℝ) ↦
        h6TakagiForwardMatrix p.1 p.2) := by
  refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
  simp only [h6TakagiForwardMatrix, h6TakagiDiagonal, Matrix.mul_apply,
    Matrix.transpose_apply]
  fun_prop

/-- The unitary-constrained forward Takagi map is jointly measurable. -/
theorem measurable_h6TakagiForward (N : ℕ) :
    Measurable
      (fun p : Matrix.unitaryGroup (Fin N) ℂ × (Fin N → ℝ) ↦
        h6TakagiForward p.1 p.2) := by
  have hpair : Measurable
      (fun p : Matrix.unitaryGroup (Fin N) ℂ × (Fin N → ℝ) ↦
        ((p.1.1 : ConcreteMatrixState N), p.2)) :=
    (measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd
  simpa only [h6TakagiForward, Function.comp_def] using
    (measurable_h6TakagiForwardMatrix N).comp hpair

@[simp]
theorem h6TakagiDiagonal_transpose {N : ℕ} (lambda : Fin N → ℝ) :
    (h6TakagiDiagonal lambda).transpose = h6TakagiDiagonal lambda := by
  simp [h6TakagiDiagonal]

@[simp]
theorem h6TakagiDiagonal_conjTranspose {N : ℕ} (lambda : Fin N → ℝ) :
    (h6TakagiDiagonal lambda).conjTranspose = h6TakagiDiagonal lambda := by
  simp [h6TakagiDiagonal]

/-- Squaring the Takagi diagonal recovers `diagonal lambda`. -/
theorem h6TakagiDiagonal_mul_self {N : ℕ} (lambda : Fin N → ℝ)
    (hlambda : ∀ i, 0 ≤ lambda i) :
    h6TakagiDiagonal lambda * h6TakagiDiagonal lambda =
      Matrix.diagonal (fun i ↦ ((lambda i : ℝ) : ℂ)) := by
  rw [h6TakagiDiagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  norm_cast
  simpa [pow_two] using Real.sq_sqrt (hlambda i)

/-- Every output of the forward Takagi formula is complex symmetric. -/
theorem h6TakagiForwardMatrix_isSymm {N : ℕ}
    (U : ConcreteMatrixState N) (lambda : Fin N → ℝ) :
    (h6TakagiForwardMatrix U lambda).IsSymm := by
  simp [Matrix.IsSymm, h6TakagiForwardMatrix, Matrix.transpose_mul,
    Matrix.mul_assoc]

theorem h6TakagiForward_isSymm {N : ℕ}
    (U : Matrix.unitaryGroup (Fin N) ℂ) (lambda : Fin N → ℝ) :
    (h6TakagiForward U lambda).IsSymm := by
  exact h6TakagiForwardMatrix_isSymm U.1 lambda

/-! ## Deterministic trace factorization -/

theorem unitary_mul_conjTranspose
    {N : ℕ} (U : Matrix.unitaryGroup (Fin N) ℂ) :
    U.1 * U.1.conjTranspose = 1 := by
  simpa only [Matrix.star_eq_conjTranspose] using
    (Matrix.mem_unitaryGroup_iff.mp U.property)

theorem unitary_conjTranspose_mul
    {N : ℕ} (U : Matrix.unitaryGroup (Fin N) ℂ) :
    U.1.conjTranspose * U.1 = 1 := by
  simpa only [Matrix.star_eq_conjTranspose] using
    (Matrix.mem_unitaryGroup_iff'.mp U.property)

theorem unitary_transpose_mul_conjTranspose
    {N : ℕ} (U : Matrix.unitaryGroup (Fin N) ℂ) :
    U.1.transpose * U.1.transpose.conjTranspose = 1 := by
  have hmem : U.1.transpose ∈ Matrix.unitaryGroup (Fin N) ℂ :=
    Matrix.transpose_mem_unitaryGroup_iff.mpr U.property
  simpa only [Matrix.star_eq_conjTranspose] using
    (Matrix.mem_unitaryGroup_iff.mp hmem)

theorem unitary_transpose_conjTranspose_mul
    {N : ℕ} (U : Matrix.unitaryGroup (Fin N) ℂ) :
    U.1.transpose.conjTranspose * U.1.transpose = 1 := by
  have hmem : U.1.transpose ∈ Matrix.unitaryGroup (Fin N) ℂ :=
    Matrix.transpose_mem_unitaryGroup_iff.mpr U.property
  simpa only [Matrix.star_eq_conjTranspose] using
    (Matrix.mem_unitaryGroup_iff'.mp hmem)

theorem h6TakagiForward_conjTranspose
    {N : ℕ} (U : Matrix.unitaryGroup (Fin N) ℂ)
    (lambda : Fin N → ℝ) :
    (h6TakagiForward U lambda).conjTranspose =
      U.1.transpose.conjTranspose * h6TakagiDiagonal lambda *
        U.1.conjTranspose := by
  simp [h6TakagiForward, h6TakagiForwardMatrix,
    Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- The right Takagi factor cancels in `Cᴴ C`. -/
theorem h6TakagiForward_conjTranspose_mul_self
    {N : ℕ} (U : Matrix.unitaryGroup (Fin N) ℂ)
    (lambda : Fin N → ℝ) (hlambda : ∀ i, 0 ≤ lambda i) :
    (h6TakagiForward U lambda).conjTranspose *
        h6TakagiForward U lambda =
      U.1.transpose.conjTranspose *
        Matrix.diagonal (fun i ↦ ((lambda i : ℝ) : ℂ)) *
          U.1.transpose := by
  rw [h6TakagiForward_conjTranspose]
  unfold h6TakagiForward h6TakagiForwardMatrix
  calc
    (U.1.transpose.conjTranspose * h6TakagiDiagonal lambda *
          U.1.conjTranspose) *
        (U.1 * h6TakagiDiagonal lambda * U.1.transpose) =
      U.1.transpose.conjTranspose * h6TakagiDiagonal lambda *
        (U.1.conjTranspose * U.1) * h6TakagiDiagonal lambda *
          U.1.transpose := by noncomm_ring
    _ = U.1.transpose.conjTranspose * h6TakagiDiagonal lambda *
        h6TakagiDiagonal lambda * U.1.transpose := by
      rw [unitary_conjTranspose_mul]
      simp
    _ = U.1.transpose.conjTranspose *
        (h6TakagiDiagonal lambda * h6TakagiDiagonal lambda) *
          U.1.transpose := by noncomm_ring
    _ = U.1.transpose.conjTranspose *
        Matrix.diagonal (fun i ↦ ((lambda i : ℝ) : ℂ)) *
          U.1.transpose := by rw [h6TakagiDiagonal_mul_self lambda hlambda]

/-- Diagonal complement appearing between the two unitary right factors. -/
def h6TakagiComplementDiagonal {N : ℕ}
    (lambda : Fin N → ℝ) : ConcreteMatrixState N :=
  Matrix.diagonal fun i ↦ (((1 - lambda i) : ℝ) : ℂ)

theorem one_sub_h6TakagiForward_conjTranspose_mul_self
    {N : ℕ} (U : Matrix.unitaryGroup (Fin N) ℂ)
    (lambda : Fin N → ℝ) (hlambda : ∀ i, 0 ≤ lambda i) :
    1 - (h6TakagiForward U lambda).conjTranspose *
        h6TakagiForward U lambda =
      U.1.transpose.conjTranspose * h6TakagiComplementDiagonal lambda *
        U.1.transpose := by
  rw [h6TakagiForward_conjTranspose_mul_self U lambda hlambda]
  have hdiag :
      (1 : ConcreteMatrixState N) -
          Matrix.diagonal (fun i ↦ ((lambda i : ℝ) : ℂ)) =
        h6TakagiComplementDiagonal lambda := by
    ext i j
    by_cases hij : i = j <;>
      simp [h6TakagiComplementDiagonal, hij]
  calc
    1 - U.1.transpose.conjTranspose *
          Matrix.diagonal (fun i ↦ ((lambda i : ℝ) : ℂ)) *
            U.1.transpose =
        U.1.transpose.conjTranspose * U.1.transpose -
          U.1.transpose.conjTranspose *
            Matrix.diagonal (fun i ↦ ((lambda i : ℝ) : ℂ)) *
              U.1.transpose := by
      rw [unitary_transpose_conjTranspose_mul]
    _ = U.1.transpose.conjTranspose *
          (1 - Matrix.diagonal (fun i ↦ ((lambda i : ℝ) : ℂ))) *
            U.1.transpose := by noncomm_ring
    _ = U.1.transpose.conjTranspose * h6TakagiComplementDiagonal lambda *
          U.1.transpose := by rw [hdiag]

theorem h6TakagiComplementDiagonal_det_isUnit
    {N : ℕ} {lambda : Fin N → ℝ}
    (hlambda : ∀ i, lambda i < 1) :
    IsUnit (h6TakagiComplementDiagonal lambda).det := by
  rw [h6TakagiComplementDiagonal, Matrix.det_diagonal, isUnit_iff_ne_zero]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _hi
  exact_mod_cast (by linarith [hlambda i] : 1 - lambda i ≠ 0)

/-- Explicit inverse of the conjugated diagonal complement. -/
theorem one_sub_h6TakagiForward_conjTranspose_mul_self_inv
    {N : ℕ} (U : Matrix.unitaryGroup (Fin N) ℂ)
    (lambda : Fin N → ℝ) (hlambda : ∀ i, lambda i ∈ Set.Ioo (0 : ℝ) 1) :
    (1 - (h6TakagiForward U lambda).conjTranspose *
        h6TakagiForward U lambda)⁻¹ =
      U.1.transpose.conjTranspose * (h6TakagiComplementDiagonal lambda)⁻¹ *
        U.1.transpose := by
  rw [one_sub_h6TakagiForward_conjTranspose_mul_self U lambda
    (fun i ↦ (hlambda i).1.le)]
  apply Matrix.inv_eq_left_inv
  calc
    (U.1.transpose.conjTranspose * (h6TakagiComplementDiagonal lambda)⁻¹ *
          U.1.transpose) *
        (U.1.transpose.conjTranspose * h6TakagiComplementDiagonal lambda *
          U.1.transpose) =
      U.1.transpose.conjTranspose * (h6TakagiComplementDiagonal lambda)⁻¹ *
        (U.1.transpose * U.1.transpose.conjTranspose) *
          h6TakagiComplementDiagonal lambda * U.1.transpose := by noncomm_ring
    _ = U.1.transpose.conjTranspose * (h6TakagiComplementDiagonal lambda)⁻¹ *
          h6TakagiComplementDiagonal lambda * U.1.transpose := by
      rw [unitary_transpose_mul_conjTranspose]
      simp
    _ = U.1.transpose.conjTranspose *
          ((h6TakagiComplementDiagonal lambda)⁻¹ *
            h6TakagiComplementDiagonal lambda) * U.1.transpose := by noncomm_ring
    _ = U.1.transpose.conjTranspose * U.1.transpose := by
      rw [Matrix.nonsing_inv_mul _
        (h6TakagiComplementDiagonal_det_isUnit (fun i ↦ (hlambda i).2))]
      simp
    _ = 1 := unitary_transpose_conjTranspose_mul U

/-- The diagonal algebra inside the Takagi expression gives exactly
`lambda/(1-lambda)`, with no extra coordinate power. -/
theorem h6TakagiDiagonal_mul_complement_inv_mul_self
    {N : ℕ} (lambda : Fin N → ℝ)
    (hlambda : ∀ i, lambda i ∈ Set.Ioo (0 : ℝ) 1) :
    h6TakagiDiagonal lambda * (h6TakagiComplementDiagonal lambda)⁻¹ *
        h6TakagiDiagonal lambda =
      Matrix.diagonal (fun i ↦ ((betaPrimeForward (lambda i) : ℝ) : ℂ)) := by
  unfold h6TakagiDiagonal h6TakagiComplementDiagonal
  rw [Matrix.inv_diagonal]
  have hinvfun :
      Ring.inverse (fun i : Fin N ↦ (((1 - lambda i) : ℝ) : ℂ)) =
        fun i ↦ ((((1 - lambda i) : ℝ) : ℂ))⁻¹ := by
    have hv : IsUnit (fun i : Fin N ↦ (((1 - lambda i) : ℝ) : ℂ)) :=
      Pi.isUnit_iff.mpr fun i ↦ isUnit_iff_ne_zero.mpr <| by
        exact_mod_cast (by linarith [(hlambda i).2] : 1 - lambda i ≠ 0)
    have hmul := Ring.mul_inverse_cancel
      (fun i : Fin N ↦ (((1 - lambda i) : ℝ) : ℂ)) hv
    funext i
    have hne : (((1 - lambda i) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (by linarith [(hlambda i).2] : 1 - lambda i ≠ 0)
    have hi := congrFun hmul i
    change (((1 - lambda i) : ℝ) : ℂ) *
        Ring.inverse (fun j : Fin N ↦ (((1 - lambda j) : ℝ) : ℂ)) i = 1 at hi
    apply mul_left_cancel₀ hne
    rw [hi, mul_inv_cancel₀ hne]
  rw [hinvfun, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  norm_cast
  have hden : 1 - lambda i ≠ 0 := by linarith [(hlambda i).2]
  unfold betaPrimeForward
  field_simp [hden]
  nlinarith [Real.sq_sqrt (hlambda i).1.le]

@[simp]
theorem unscaleCOECorner_one {N : ℕ} (A : ConcreteMatrixState N) :
    unscaleCOECorner 1 A = A := by
  simp [unscaleCOECorner]

/-- Exact deterministic formula for the H6 matrix statistic in Takagi
coordinates. -/
theorem concreteCOEZ_one_h6TakagiForward
    {N : ℕ} (U : Matrix.unitaryGroup (Fin N) ℂ)
    (lambda : Fin N → ℝ) (hlambda : ∀ i, lambda i ∈ Set.Ioo (0 : ℝ) 1) :
    concreteCOEZ 1 (h6TakagiForward U lambda) =
      U.1 * Matrix.diagonal
        (fun i ↦ ((betaPrimeForward (lambda i) : ℝ) : ℂ)) *
          U.1.conjTranspose := by
  simp only [concreteCOEZ, unscaleCOECorner_one]
  rw [one_sub_h6TakagiForward_conjTranspose_mul_self_inv U lambda hlambda,
    h6TakagiForward_conjTranspose]
  unfold h6TakagiForward h6TakagiForwardMatrix
  calc
    (U.1 * h6TakagiDiagonal lambda * U.1.transpose) *
          (U.1.transpose.conjTranspose *
            (h6TakagiComplementDiagonal lambda)⁻¹ * U.1.transpose) *
        (U.1.transpose.conjTranspose * h6TakagiDiagonal lambda *
          U.1.conjTranspose) =
      U.1 * h6TakagiDiagonal lambda *
        (U.1.transpose * U.1.transpose.conjTranspose) *
          (h6TakagiComplementDiagonal lambda)⁻¹ *
            (U.1.transpose * U.1.transpose.conjTranspose) *
              h6TakagiDiagonal lambda * U.1.conjTranspose := by noncomm_ring
    _ = U.1 * h6TakagiDiagonal lambda *
          (h6TakagiComplementDiagonal lambda)⁻¹ *
            h6TakagiDiagonal lambda * U.1.conjTranspose := by
      rw [unitary_transpose_mul_conjTranspose]
      simp
    _ = U.1 *
          (h6TakagiDiagonal lambda *
            (h6TakagiComplementDiagonal lambda)⁻¹ *
              h6TakagiDiagonal lambda) * U.1.conjTranspose := by noncomm_ring
    _ = U.1 * Matrix.diagonal
          (fun i ↦ ((betaPrimeForward (lambda i) : ℝ) : ℂ)) *
            U.1.conjTranspose := by
      rw [h6TakagiDiagonal_mul_complement_inv_mul_self lambda hlambda]

/-- Powers commute with unitary conjugation. -/
theorem unitary_conjugate_pow
    {N : ℕ} (U : Matrix.unitaryGroup (Fin N) ℂ)
    (X : ConcreteMatrixState N) (m : ℕ) :
    (U.1 * X * U.1.conjTranspose) ^ m =
      U.1 * X ^ m * U.1.conjTranspose := by
  induction m with
  | zero =>
      simp only [pow_zero]
      simpa only [Matrix.mul_one] using (unitary_mul_conjTranspose U).symm
  | succ m ih =>
      rw [pow_succ, ih, pow_succ]
      calc
        (U.1 * X ^ m * U.1.conjTranspose) *
            (U.1 * X * U.1.conjTranspose) =
          U.1 * X ^ m * (U.1.conjTranspose * U.1) * X *
            U.1.conjTranspose := by noncomm_ring
        _ = U.1 * (X ^ m * X) * U.1.conjTranspose := by
          rw [unitary_conjTranspose_mul]
          simp
          noncomm_ring

theorem trace_unitary_conjugate_pow
    {N : ℕ} (U : Matrix.unitaryGroup (Fin N) ℂ)
    (X : ConcreteMatrixState N) (m : ℕ) :
    Matrix.trace ((U.1 * X * U.1.conjTranspose) ^ m) =
      Matrix.trace (X ^ m) := by
  rw [unitary_conjugate_pow]
  calc
    Matrix.trace (U.1 * X ^ m * U.1.conjTranspose) =
        Matrix.trace (U.1.conjTranspose * (U.1 * X ^ m)) := by
      rw [Matrix.trace_mul_cycle]
      congr 1
      noncomm_ring
    _ = Matrix.trace ((U.1.conjTranspose * U.1) * X ^ m) := by
      congr 1
      noncomm_ring
    _ = Matrix.trace (X ^ m) := by
      rw [unitary_conjTranspose_mul, one_mul]

/-- Every finite trace-power vector factors through the transformed squared
Takagi coordinates. -/
theorem concreteCOETracePowerVector_h6TakagiForward
    {r N : ℕ} (U : Matrix.unitaryGroup (Fin N) ℂ)
    (lambda : Fin N → ℝ) (hlambda : ∀ i, lambda i ∈ Set.Ioo (0 : ℝ) 1) :
    concreteCOETracePowerVector r N 1 (h6TakagiForward U lambda) =
      fun j ↦ ∑ i : Fin N, (betaPrimeForward (lambda i)) ^ (j.1 + 1) := by
  funext j
  unfold concreteCOETracePowerVector
  rw [concreteCOEZ_one_h6TakagiForward U lambda hlambda,
    trace_unitary_conjugate_pow]
  have hcomplex :
      Matrix.trace
          ((Matrix.diagonal
            (fun i ↦ ((betaPrimeForward (lambda i) : ℝ) : ℂ))) ^
              (j.1 + 1)) =
        ((∑ i : Fin N, (betaPrimeForward (lambda i)) ^ (j.1 + 1) : ℝ) : ℂ) := by
    rw [Matrix.diagonal_pow, Matrix.trace_diagonal]
    simp only [Pi.pow_apply]
    norm_cast
  have hre := congrArg Complex.re hcomplex
  norm_cast at hre

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
