import LogdetLean.GramHafnian.UltimateHiding.Sparse.RegimeStitch
import Mathlib.Tactic

/-!
# Squared-rate conversion for the raw Jiang-density route

This file is purely elementary real algebra.  It converts the coarser
rectangular rate produced by the raw-density argument,

`(K + N) * sqrt (K * N) / M`,

to the squared hiding rate `N^2 / M` when `K <= kappa * N`.  In particular,
it imports none of the historical pointwise-likelihood or Jacobi-product
interfaces.
-/

namespace LogdetLean.GramHafnian.UltimateHiding.Sparse

noncomputable section

/-- The sparse squared-rate coefficient for the raw Jiang-density bound. -/
def rawDensitySparseSquaredCoefficient (kappa : ℕ) : ℝ :=
  ((kappa : ℝ) + 1) * Real.sqrt (kappa : ℝ)

theorem rawDensitySparseSquaredCoefficient_nonneg (kappa : ℕ) :
    0 <= rawDensitySparseSquaredCoefficient kappa := by
  unfold rawDensitySparseSquaredCoefficient
  positivity

/-- The coarser raw-density rectangular rate is `O(N^2/M)` throughout a
fixed-aspect sparse regime.  No probabilistic or large-ambient input is used. -/
theorem rawDensity_sparse_rate_le_squared_rate
    {N K M kappa : ℝ}
    (hN : 0 <= N) (hM : 0 < M)
    (hkappa : 0 <= kappa) (hKupper : K <= kappa * N) :
    (K + N) * Real.sqrt (K * N) / M <=
      ((kappa + 1) * Real.sqrt kappa) * (N ^ 2 / M) := by
  have hsum : K + N <= (kappa + 1) * N := by
    linarith
  have hsqrt : Real.sqrt (K * N) <= Real.sqrt kappa * N := by
    simpa [mul_comm] using
      (sqrt_NK_le_sqrt_kappa_mul_N hN hkappa hKupper)
  have hsum0 : 0 <= (kappa + 1) * N := by
    positivity
  have hsqrt0 : 0 <= Real.sqrt (K * N) := Real.sqrt_nonneg _
  have hproduct :
      (K + N) * Real.sqrt (K * N) <=
        (kappa + 1) * Real.sqrt kappa * N ^ 2 := by
    calc
      (K + N) * Real.sqrt (K * N) <=
          ((kappa + 1) * N) * (Real.sqrt kappa * N) := by
            exact mul_le_mul hsum hsqrt hsqrt0 hsum0
      _ = (kappa + 1) * Real.sqrt kappa * N ^ 2 := by ring
  calc
    (K + N) * Real.sqrt (K * N) / M <=
        ((kappa + 1) * Real.sqrt kappa * N ^ 2) / M :=
      div_le_div_of_nonneg_right hproduct hM.le
    _ = ((kappa + 1) * Real.sqrt kappa) * (N ^ 2 / M) := by
      field_simp

/-- Natural-number aspect-ratio wrapper matching the sparse branch API. -/
theorem rawDensity_sparse_rate_le_squared_rate_nat
    {N K M : ℝ} {kappa : ℕ}
    (hN : 0 <= N) (hM : 0 < M)
    (hKupper : K <= (kappa : ℝ) * N) :
    (K + N) * Real.sqrt (K * N) / M <=
      rawDensitySparseSquaredCoefficient kappa * (N ^ 2 / M) := by
  simpa [rawDensitySparseSquaredCoefficient] using
    (rawDensity_sparse_rate_le_squared_rate
      (N := N) (K := K) (M := M) (kappa := (kappa : ℝ))
      hN hM (Nat.cast_nonneg kappa) hKupper)

/-- At the canonical cutoff `K < 16 N`, the raw-density coefficient is `68`. -/
theorem rawDensitySparseSquaredCoefficient_sixteen :
    rawDensitySparseSquaredCoefficient 16 = 68 := by
  norm_num [rawDensitySparseSquaredCoefficient]

end

end LogdetLean.GramHafnian.UltimateHiding.Sparse
