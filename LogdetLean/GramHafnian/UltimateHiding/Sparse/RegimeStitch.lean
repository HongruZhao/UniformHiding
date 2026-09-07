import LogdetLean.GramHafnian.UltimateHiding.Sparse.InformationWrappers
import Mathlib.Analysis.Real.Sqrt

/-!
# Finite sparse regime stitch

This file contains the real inequalities converting the finite Haar block
estimate into the `N / sqrt M` rate when `K` is at most a fixed multiple of
`N`.  It also records why the complementary small ambient regime is absorbed
by the outer `min {1, ...}`.
-/

namespace LogdetLean.GramHafnian.UltimateHiding.Sparse

theorem sqrt_NK_le_sqrt_kappa_mul_N
    {N K kappa : ℝ} (hN : 0 ≤ N) (hkappa : 0 ≤ kappa)
    (hKupper : K ≤ kappa * N) :
    Real.sqrt (N * K) ≤ Real.sqrt kappa * N := by
  have hprod : N * K ≤ kappa * N ^ 2 := by
    nlinarith [mul_nonneg hN (sub_nonneg.mpr hKupper)]
  calc
    Real.sqrt (N * K) ≤ Real.sqrt (kappa * N ^ 2) :=
      Real.sqrt_le_sqrt hprod
    _ = Real.sqrt kappa * N := by
      rw [Real.sqrt_mul hkappa, Real.sqrt_sq_eq_abs, abs_of_nonneg hN]

theorem square_over_ambient_le_linear_sqrt_rate
    {N M : ℝ} (hN : 0 ≤ N) (hM : 0 < M) (hNM : N ^ 2 ≤ M) :
    N ^ 2 / M ≤ N / Real.sqrt M := by
  have hsqrtM : 0 < Real.sqrt M := Real.sqrt_pos.2 hM
  have hratio0 : 0 ≤ N / Real.sqrt M := div_nonneg hN hsqrtM.le
  have hratio1 : N / Real.sqrt M ≤ 1 := by
    rw [div_le_one hsqrtM]
    exact Real.le_sqrt_of_sq_le hNM
  have hsqrt_sq : (Real.sqrt M) ^ 2 = M := Real.sq_sqrt hM.le
  have heq : N ^ 2 / M = (N / Real.sqrt M) ^ 2 := by
    field_simp
    rw [hsqrt_sq]
  rw [heq]
  nlinarith [mul_nonneg hratio0 (sub_nonneg.mpr hratio1)]

/-- Conversion of the finite block rate to `N / sqrt M` in the sparse
`K ≤ kappa N` range. -/
theorem finite_sparse_rate_le_unified_rate
    {N K M kappa : ℝ}
    (hN : 0 ≤ N) (hM : 0 < M)
    (hkappa : 0 ≤ kappa) (hKupper : K ≤ kappa * N)
    (hNM : N ^ 2 ≤ M) :
    (K + N) * Real.sqrt (N * K) / (2 * M)
      ≤ ((kappa + 1) * Real.sqrt kappa / 2) *
          (N / Real.sqrt M) := by
  have hsum : K + N ≤ (kappa + 1) * N := by linarith
  have hsqrt := sqrt_NK_le_sqrt_kappa_mul_N hN hkappa hKupper
  have hkappaOne : 0 ≤ kappa + 1 := by linarith
  have hsqrt0 : 0 ≤ Real.sqrt (N * K) := Real.sqrt_nonneg _
  have hproduct :
      (K + N) * Real.sqrt (N * K)
        ≤ (kappa + 1) * Real.sqrt kappa * N ^ 2 := by
    calc
      (K + N) * Real.sqrt (N * K)
          ≤ ((kappa + 1) * N) * (Real.sqrt kappa * N) := by
              exact mul_le_mul hsum hsqrt hsqrt0
                (mul_nonneg hkappaOne hN)
      _ = (kappa + 1) * Real.sqrt kappa * N ^ 2 := by ring
  have hden : 0 < 2 * M := mul_pos (by norm_num) hM
  calc
    (K + N) * Real.sqrt (N * K) / (2 * M)
        ≤ ((kappa + 1) * Real.sqrt kappa * N ^ 2) / (2 * M) :=
          div_le_div_of_nonneg_right hproduct hden.le
    _ = ((kappa + 1) * Real.sqrt kappa / 2) * (N ^ 2 / M) := by
          field_simp
    _ ≤ ((kappa + 1) * Real.sqrt kappa / 2) *
          (N / Real.sqrt M) := by
          apply mul_le_mul_of_nonneg_left
            (square_over_ambient_le_linear_sqrt_rate hN hM hNM)
          positivity

/-- Outside the nontrivial ambient regime, choosing `C^2 N^2 ≥ M` makes the
outer minimum equal to one. -/
theorem min_one_unified_rate_eq_one_of_small_ambient
    {C N M : ℝ} (hC : 0 ≤ C) (hN : 0 ≤ N) (hM : 0 < M)
    (hsmall : M ≤ C ^ 2 * N ^ 2) :
    min 1 (C * N / Real.sqrt M) = 1 := by
  have hsqrtM : 0 < Real.sqrt M := Real.sqrt_pos.2 hM
  have hCN0 : 0 ≤ C * N := mul_nonneg hC hN
  have hsquare : (Real.sqrt M) ^ 2 ≤ (C * N) ^ 2 := by
    rw [Real.sq_sqrt hM.le]
    nlinarith
  have hsqrt_le : Real.sqrt M ≤ C * N :=
    (sq_le_sq₀ (Real.sqrt_nonneg M) hCN0).mp hsquare
  have hone : 1 ≤ C * N / Real.sqrt M := by
    rw [le_div_iff₀ hsqrtM]
    simpa using hsqrt_le
  exact min_eq_left hone

end LogdetLean.GramHafnian.UltimateHiding.Sparse
