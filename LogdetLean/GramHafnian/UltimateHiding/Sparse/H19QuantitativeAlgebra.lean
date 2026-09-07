import LogdetLean.GramHafnian.UltimateHiding.Sparse.RectangularIndices
import Mathlib.Tactic

/-!
# Elementary finite-dimensional algebra for the quantitative H19 route

The lemmas in this file contain no probability or random-matrix input.  They
turn the exact second Haar-Gram moment into the coarse bound needed by the
raw Jiang-density argument, and then perform the cancellation in the expected
log likelihood.
-/

namespace LogdetLean.GramHafnian.UltimateHiding.Sparse

noncomputable section

/-- For positive rectangular dimensions, `NK + 1` is at most half the square
of `N + K`. -/
theorem rectangular_product_add_one_le_half_sum_sq_h19
    {N K : ℝ} (hN : 1 ≤ N) (hK : 1 ≤ K) :
    N * K + 1 ≤ (N + K) ^ 2 / 2 := by
  nlinarith [sq_nonneg (N - 1), sq_nonneg (K - 1)]

/-- The closed form of the scaled Haar-Gram second moment dominates its
first two terms in `1/M`. -/
theorem haar_gram_second_moment_closedForm_lower_h19
    {M N K : ℝ} (hM : 0 < M) (hMone : 1 < M)
    (hN : 1 ≤ N) (hK : 1 ≤ K) (hs : N + K ≤ M) :
    N * K * M * (M * (N + K) - N * K - 1) / (M ^ 2 - 1) ≥
      N * K * ((N + K) - (N * K + 1) / M) := by
  have hden : 0 < M ^ 2 - 1 := by nlinarith
  have hcore : 0 ≤ M * (N + K) - N * K - 1 := by
    have hsquare : N * K + 1 ≤ (N + K) ^ 2 := by
      nlinarith [rectangular_product_add_one_le_half_sum_sq_h19 hN hK]
    nlinarith [mul_le_mul_of_nonneg_right hs (by positivity : 0 ≤ N + K)]
  have hNK : 0 ≤ N * K := mul_nonneg (by linarith) (by linarith)
  rw [ge_iff_le]
  have hMne : M ≠ 0 := ne_of_gt hM
  apply (le_div_iff₀ hden).2
  have hprod : 0 ≤ N * K * (M * (N + K) - N * K - 1) :=
    mul_nonneg hNK hcore
  have heq :
      N * K * (N + K - (N * K + 1) / M) * (M ^ 2 - 1) =
        N * K * (M * (N + K) - N * K - 1) * M -
          (N * K * (M * (N + K) - N * K - 1)) / M := by
    field_simp [hMne]
    ring
  rw [heq]
  have hsub := sub_le_self
    (N * K * (M * (N + K) - N * K - 1) * M)
    (div_nonneg hprod hM.le)
  nlinarith

/-- A convenient coarser form of the preceding moment lower bound. -/
theorem haar_gram_second_moment_coarse_lower_h19
    {M N K : ℝ} (hM : 0 < M) (hMone : 1 < M)
    (hN : 1 ≤ N) (hK : 1 ≤ K) (hs : N + K ≤ M) :
    N * K * M * (M * (N + K) - N * K - 1) / (M ^ 2 - 1) ≥
      N * K * ((N + K) - (N + K) ^ 2 / (2 * M)) := by
  have hbase := haar_gram_second_moment_closedForm_lower_h19
    hM hMone hN hK hs
  have hhalf := rectangular_product_add_one_le_half_sum_sq_h19 hN hK
  have hdiv : (N * K + 1) / M ≤ (N + K) ^ 2 / (2 * M) := by
    calc
      (N * K + 1) / M ≤ ((N + K) ^ 2 / 2) / M :=
        div_le_div_of_nonneg_right hhalf hM.le
      _ = (N + K) ^ 2 / (2 * M) := by ring
  have hNK : 0 ≤ N * K := mul_nonneg (by linarith) (by linarith)
  have hinside :
      (N + K) - (N + K) ^ 2 / (2 * M) ≤
        (N + K) - (N * K + 1) / M := by
    linarith
  exact (mul_le_mul_of_nonneg_left hinside hNK).trans hbase

/-- The first-order normalizer term and the Haar-Gram second moment cancel,
leaving a uniform `3/4 * NK(N+K)^2/M^2` bound. -/
theorem expected_logLikelihood_cancellation_h19
    {M d s E logR : ℝ}
    (hM : 0 < M) (hd : 0 ≤ d) (hs0 : 0 ≤ s) (hsM : s ≤ M)
    (hlogR : logR ≤ -(d * s) / (2 * M))
    (hE : d * (s - s ^ 2 / (2 * M)) ≤ E) :
    logR + (M - s) * (-d / M - E / (2 * M ^ 2)) + d ≤
      3 * d * s ^ 2 / (4 * M ^ 2) := by
  have hcoef : 0 ≤ M - s := sub_nonneg.mpr hsM
  have hEterm :
      -(M - s) * E / (2 * M ^ 2) ≤
        -(M - s) * (d * (s - s ^ 2 / (2 * M))) /
          (2 * M ^ 2) := by
    have hden : 0 < 2 * M ^ 2 := by positivity
    apply div_le_div_of_nonneg_right _ hden.le
    exact mul_le_mul_of_nonpos_left hE (neg_nonpos.mpr hcoef)
  calc
    logR + (M - s) * (-d / M - E / (2 * M ^ 2)) + d ≤
        -(d * s) / (2 * M) +
          (M - s) * (-d / M - E / (2 * M ^ 2)) + d := by
      gcongr
    _ = -(d * s) / (2 * M) +
          (M - s) * (-d / M) +
          (-(M - s) * E / (2 * M ^ 2)) + d := by ring
    _ ≤ -(d * s) / (2 * M) +
          (M - s) * (-d / M) +
          (-(M - s) * (d * (s - s ^ 2 / (2 * M))) /
            (2 * M ^ 2)) + d := by
      gcongr
    _ ≤ 3 * d * s ^ 2 / (4 * M ^ 2) := by
      have hMne : M ≠ 0 := ne_of_gt hM
      have hratio0 : 0 ≤ (M - s) / M :=
        div_nonneg hcoef hM.le
      have hratio1 : (M - s) / M ≤ 1 := by
        rw [div_le_one hM]
        linarith
      have hbase0 : 0 ≤ d * s ^ 2 / (4 * M ^ 2) := by positivity
      calc
        -(d * s) / (2 * M) +
              (M - s) * (-d / M) +
              (-(M - s) * (d * (s - s ^ 2 / (2 * M))) /
                (2 * M ^ 2)) + d =
            d * s ^ 2 / (2 * M ^ 2) +
              (d * s ^ 2 / (4 * M ^ 2)) * ((M - s) / M) := by
          field_simp [hMne]
          ring
        _ ≤ d * s ^ 2 / (2 * M ^ 2) +
              (d * s ^ 2 / (4 * M ^ 2)) * 1 := by
          gcongr
        _ = 3 * d * s ^ 2 / (4 * M ^ 2) := by ring

end

end LogdetLean.GramHafnian.UltimateHiding.Sparse
