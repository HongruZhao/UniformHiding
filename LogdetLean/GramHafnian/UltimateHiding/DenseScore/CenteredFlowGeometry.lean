import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ConcreteCenteredLikelihood
import LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep.ConcreteOrbitalEventGeometry
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Tactic

/-!
# Bridge between the literal centered exponential flow and the closed orbital factor

The analytic likelihood is expressed using the matrix exponential
`exp(t Q_v)`, whereas the one-column kernel uses the measurable closed form

`exp(-t/N) (I + (exp(t)-1) P_v)`.

This file proves their equality internally, together with `Tr Q_v=0`.  No
density, moment, score, total-variation, or hiding statement occurs here.
-/

open NormedSpace

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

set_option maxHeartbeats 800000

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep

/-- Every positive power of an idempotent matrix is itself. -/
theorem pow_succ_eq_of_matrix_idempotent
    {N : ℕ} (P : ConcreteMatrixState N) (hP : P * P = P) (r : ℕ) :
    P ^ (r + 1) = P := by
  induction r with
  | zero => simp
  | succ r ihr =>
      rw [pow_succ, ihr, hP]

/-- Powers of a scalar multiple of an idempotent matrix. -/
theorem smul_idempotent_pow_succ
    {N : ℕ} (P : ConcreteMatrixState N) (hP : P * P = P)
    (z : ℂ) (r : ℕ) :
    (z • P) ^ (r + 1) = z ^ (r + 1) • P := by
  rw [smul_pow, pow_succ_eq_of_matrix_idempotent P hP r]

/-- The rank-one projection has trace one. -/
theorem trace_complexRankOneProjection
    {N : ℕ} (v : ComplexUnitSphere N) :
    Matrix.trace (complexRankOneProjection v) = 1 := by
  have hvnorm : ‖v.1‖ = 1 := mem_sphere_zero_iff_norm.mp v.2
  have hsq := PiLp.norm_sq_eq_of_L2 (fun _ : Fin N ↦ ℂ) v.1
  rw [hvnorm] at hsq
  norm_num at hsq
  simp only [Matrix.trace, complexRankOneProjection]
  calc
    ∑ i, v.1 i * star (v.1 i) =
        ∑ i, ((‖v.1 i‖ ^ 2 : ℝ) : ℂ) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_comm]
      simpa [Complex.normSq_eq_norm_sq] using
        (Complex.normSq_eq_conj_mul_self (z := v.1 i)).symm
    _ = ((∑ i, ‖v.1 i‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]
    _ = 1 := by rw [hsq.symm]; norm_num

/-- The centered orbital direction is traceless. -/
theorem trace_concreteCenteredOrbitalDirection_eq_zero
    {N : ℕ} (hN : 1 ≤ N) (v : ComplexUnitSphere N) :
    Matrix.trace (concreteCenteredOrbitalDirection N v) = 0 := by
  have hNr : (N : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hN)
  simp only [concreteCenteredOrbitalDirection, Matrix.trace_sub,
    Matrix.trace_smul, trace_complexRankOneProjection]
  rw [Matrix.trace_one]
  simp only [Fintype.card_fin, smul_eq_mul]
  apply sub_eq_zero.mpr
  have hNrR : (N : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hN)
  norm_cast
  field_simp [hNrR]

/-- The nonconstant tail of the exponential series. -/
theorem complex_exp_sub_one_eq_tsum_succ (z : ℂ) :
    NormedSpace.exp z - 1 =
      ∑' r : ℕ, ((Nat.factorial (r + 1) : ℂ)⁻¹ * z ^ (r + 1)) := by
  have hs : Summable fun r : ℕ ↦
      ((Nat.factorial r : ℂ)⁻¹) • z ^ r :=
    NormedSpace.expSeries_summable' z
  have hsplit := hs.sum_add_tsum_nat_add 1
  rw [NormedSpace.exp_eq_tsum ℂ]
  simpa [Finset.sum_range_succ, smul_eq_mul, add_sub_cancel_left] using
    congrArg (fun w : ℂ ↦ w - 1) hsplit.symm

/-- Exponential of a scalar matrix. -/
theorem matrix_exp_smul_one {N : ℕ} (z : ℂ) :
    NormedSpace.exp (z • (1 : ConcreteMatrixState N)) =
      NormedSpace.exp z • (1 : ConcreteMatrixState N) := by
  have hdiag : z • (1 : ConcreteMatrixState N) =
      Matrix.diagonal (fun _ : Fin N ↦ z) := by
    ext i j
    simp [Matrix.smul_apply, Matrix.one_apply, Matrix.diagonal_apply]
  rw [hdiag, Matrix.exp_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simp
  · simp [Matrix.diagonal_apply, Matrix.one_apply, hij]

open scoped Matrix.Norms.Operator in
/-- Exponential of a scalar multiple of an idempotent matrix. -/
theorem matrix_exp_smul_idempotent
    {N : ℕ} (P : ConcreteMatrixState N) (hP : P * P = P) (z : ℂ) :
    NormedSpace.exp (z • P) =
      1 + (NormedSpace.exp z - 1) • P := by
  have hsMatrix : Summable fun r : ℕ ↦
      ((Nat.factorial r : ℂ)⁻¹) • (z • P) ^ r :=
    NormedSpace.expSeries_summable' (z • P)
  have hsplit := hsMatrix.sum_add_tsum_nat_add 1
  rw [NormedSpace.exp_eq_tsum ℂ]
  change (∑' r : ℕ,
      ((Nat.factorial r : ℂ)⁻¹) • (z • P) ^ r) =
    1 + (NormedSpace.exp z - 1) • P
  rw [← hsplit]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, one_smul]
  have hsScalar : Summable fun r : ℕ ↦
      ((Nat.factorial (r + 1) : ℂ)⁻¹) * z ^ (r + 1) := by
    have hs : Summable fun r : ℕ ↦
        ((Nat.factorial r : ℂ)⁻¹) * z ^ r := by
      simpa only [smul_eq_mul] using
        (NormedSpace.expSeries_summable' (𝔸 := ℂ) (𝕂 := ℂ) z)
    exact (summable_nat_add_iff 1).2 hs
  calc
    1 + ∑' r : ℕ,
        ((Nat.factorial (r + 1) : ℂ)⁻¹) • (z • P) ^ (r + 1) =
        1 + ∑' r : ℕ,
          (((Nat.factorial (r + 1) : ℂ)⁻¹) * z ^ (r + 1)) • P := by
      congr 1
      apply tsum_congr
      intro r
      rw [smul_idempotent_pow_succ P hP z r]
      simp only [smul_smul]
    _ = 1 + (∑' r : ℕ,
          ((Nat.factorial (r + 1) : ℂ)⁻¹) * z ^ (r + 1)) • P := by
      rw [hsScalar.tsum_smul_const P]
    _ = 1 + (NormedSpace.exp z - 1) • P := by
      rw [complex_exp_sub_one_eq_tsum_succ]

/-- The literal matrix exponential of `t Q_v` equals the measurable closed
orbital factor used by the one-column kernel. -/
theorem matrix_exp_centeredOrbitalDirection_eq_concreteOrbitalFactor
    {N : ℕ} (hN : 1 ≤ N) (t : ℝ) (v : ComplexUnitSphere N) :
    NormedSpace.exp
        (((t : ℂ)) • concreteCenteredOrbitalDirection N v) =
      concreteOrbitalFactor N t v := by
  let P := complexRankOneProjection v
  have hP : P * P = P :=
    complexRankOneProjection_mul_self v
  have hNr : (N : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hN)
  let a : ℂ := ((-t / (N : ℝ) : ℝ) : ℂ)
  let b : ℂ := (t : ℂ)
  have harg :
      b • concreteCenteredOrbitalDirection N v =
        a • (1 : ConcreteMatrixState N) + b • P := by
    unfold concreteCenteredOrbitalDirection P a b
    ext i j
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply,
      Matrix.one_apply]
    push_cast
    by_cases hij : i = j
    · subst j
      field_simp [hNr]
      ring
    · simp [hij]
  have hcomm : Commute
      (a • (1 : ConcreteMatrixState N)) (b • P) := by
    show (a • (1 : ConcreteMatrixState N)) * (b • P) =
      (b • P) * (a • (1 : ConcreteMatrixState N))
    rw [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one]
  rw [show ((t : ℂ)) = b by rfl, harg,
    Matrix.exp_add_of_commute _ _ hcomm,
    matrix_exp_smul_one, matrix_exp_smul_idempotent P hP]
  unfold concreteOrbitalFactor a b
  have ha : NormedSpace.exp ((-t / (N : ℝ) : ℝ) : ℂ) =
      ((Real.exp (-t / (N : ℝ)) : ℝ) : ℂ) := by
    rw [← NormedSpace.ofReal_exp_ℝ_ℝ, ← Real.exp_eq_exp_ℝ]
  have hb : NormedSpace.exp (t : ℂ) =
      ((Real.exp t : ℝ) : ℂ) := by
    rw [← NormedSpace.ofReal_exp_ℝ_ℝ, ← Real.exp_eq_exp_ℝ]
  rw [ha, hb]
  rw [Matrix.smul_mul, Matrix.one_mul]
  congr 2
  norm_cast

/-- Consequently, the exponential transpose-congruence flow used by the
likelihood is exactly the closed-form orbital matrix update used by the
same-beta one-column path. -/
theorem transposeCongruenceFlow_centered_eq_concreteOrbitalMatrixUpdate
    {N : ℕ} (hN : 1 ≤ N) (t : ℝ) (v : ComplexUnitSphere N)
    (A : ConcreteMatrixState N) :
    transposeCongruenceFlow (concreteCenteredOrbitalDirection N v) t A =
      concreteOrbitalMatrixUpdate N t v A := by
  unfold transposeCongruenceFlow transposeCongruence
    concreteOrbitalMatrixUpdate
  rw [matrix_exp_centeredOrbitalDirection_eq_concreteOrbitalFactor hN]

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
