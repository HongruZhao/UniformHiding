import LogdetLean.GramHafnian.UltimateHiding.Dense.RadialConcrete
import Mathlib.Tactic

/-!
# Exact central--orbital split of one Haar-column factor

The scalar coefficient and the traceless rank-one coefficient in the dense
one-column argument are functions of the same beta sample `q`.  This file
proves their pointwise matrix factorization.  It contains no probability,
score, moment, or hiding input.
-/

namespace LogdetLean.GramHafnian.UltimateHiding.Dense

noncomputable section

/-- Scalar congruence factor `exp(s) I`. -/
def concreteCentralFactor (N : ℕ) (s : ℝ) : ConcreteMatrixState N :=
  (((Real.exp s : ℝ) : ℂ)) • 1

/-- Congruence by the scalar factor `exp(s) I`. -/
def concreteCentralMatrixUpdate (N : ℕ) (s : ℝ)
    (A : ConcreteMatrixState N) : ConcreteMatrixState N :=
  concreteCentralFactor N s * A * (concreteCentralFactor N s).transpose

theorem measurable_concreteCentralMatrixUpdate (N : ℕ) (s : ℝ) :
    Measurable (concreteCentralMatrixUpdate N s) := by
  refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
  simp only [concreteCentralMatrixUpdate, concreteCentralFactor,
    Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply,
    Matrix.one_apply]
  fun_prop

/-- The real exponential of a half logarithm is the positive square root. -/
theorem exp_half_log_eq_sqrt {x : ℝ} (hx : 0 < x) :
    Real.exp ((1 / 2 : ℝ) * Real.log x) = Real.sqrt x := by
  have hsquare : Real.exp ((1 / 2 : ℝ) * Real.log x) ^ 2 = x := by
    rw [pow_two, ← Real.exp_add, ← two_mul]
    convert Real.exp_log hx using 1 <;> ring
  have hnonneg : 0 ≤ Real.exp ((1 / 2 : ℝ) * Real.log x) :=
    (Real.exp_pos _).le
  exact ((Real.sqrt_eq_iff_eq_sq hx.le hnonneg).2 hsquare.symm).symm

theorem exp_oneColumnScalarLog_eq_sqrt
    {m : ℕ} (hm : 1 ≤ m) :
    Real.exp (oneColumnScalarLog m) =
      Real.sqrt (1 + 1 / (m : ℝ)) := by
  unfold oneColumnScalarLog
  apply exp_half_log_eq_sqrt
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  positivity

theorem exp_oneColumnRankOneLog_eq_sqrt
    {q : ℝ} (hq : 0 < q) :
    Real.exp (oneColumnRankOneLog q) = Real.sqrt q := by
  exact exp_half_log_eq_sqrt hq

/-- Pointwise factorization with the **same** beta sample `q`:

`R(q,v) = exp(c(q)) I * exp(b(q) (P_v-I/N))`.

This is the correlation-sensitive algebra behind the one-column Taylor
argument. -/
theorem concreteOneColumnFactor_eq_central_mul_orbital
    {m N : ℕ} (hm : 1 ≤ m) (hN : 1 ≤ N)
    {q : ℝ} (hq : 0 < q) (v : ComplexUnitSphere N) :
    concreteOneColumnFactor m N q v =
      concreteCentralFactor N (oneColumnCenteredScalarLog m N q) *
        concreteOrbitalFactor N (oneColumnRankOneLog q) v := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hone : 0 < (1 + 1 / (m : ℝ)) := by positivity
  have hratio : (((m + 1 : ℕ) : ℝ) / (m : ℝ)) =
      1 + 1 / (m : ℝ) := by
    rw [Nat.cast_add, Nat.cast_one]
    field_simp
  have hcentral :
      Real.exp (oneColumnCenteredScalarLog m N q) *
          Real.exp (-oneColumnRankOneLog q / (N : ℝ)) =
        Real.sqrt (((m + 1 : ℕ) : ℝ) / (m : ℝ)) := by
    rw [← Real.exp_add]
    have hcancel :
        oneColumnCenteredScalarLog m N q -
            oneColumnRankOneLog q / (N : ℝ) =
          oneColumnScalarLog m := by
      unfold oneColumnCenteredScalarLog
      ring
    have hcancel' :
        oneColumnCenteredScalarLog m N q +
            -oneColumnRankOneLog q / (N : ℝ) =
          oneColumnScalarLog m := by
      unfold oneColumnCenteredScalarLog
      ring
    rw [hcancel', exp_oneColumnScalarLog_eq_sqrt hm, hratio]
  have hrank : Real.exp (oneColumnRankOneLog q) = Real.sqrt q :=
    exp_oneColumnRankOneLog_eq_sqrt hq
  unfold concreteOneColumnFactor concreteCentralFactor concreteOrbitalFactor
  simp only [Matrix.smul_mul, Matrix.one_mul, smul_smul]
  rw [← Complex.ofReal_mul, hcentral, hrank]

/-- The same pointwise split at the level of transpose congruence updates. -/
theorem concreteOneColumnMatrixUpdate_eq_central_orbital
    {m N : ℕ} (hm : 1 ≤ m) (hN : 1 ≤ N)
    {q : ℝ} (hq : 0 < q) (v : ComplexUnitSphere N)
    (A : ConcreteMatrixState N) :
    concreteOneColumnMatrixUpdate m N q v A =
      concreteCentralMatrixUpdate N (oneColumnCenteredScalarLog m N q)
        (concreteOrbitalMatrixUpdate N (oneColumnRankOneLog q) v A) := by
  rw [concreteOneColumnMatrixUpdate, concreteCentralMatrixUpdate,
    concreteOrbitalMatrixUpdate,
    concreteOneColumnFactor_eq_central_mul_orbital hm hN hq]
  simp only [Matrix.transpose_mul]
  simp [Matrix.mul_assoc]

end

end LogdetLean.GramHafnian.UltimateHiding.Dense
