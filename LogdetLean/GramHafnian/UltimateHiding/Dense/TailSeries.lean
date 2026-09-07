import LogdetLean.GramHafnian.UltimateHiding.Dense.Telescoping
import Mathlib.Analysis.PSeries

/-!
# The dense bad-tail series

Deterministic finite and infinite summation estimates for the exceptional
probabilities in the dense one-column comparison.
-/

open scoped BigOperators
open Finset

namespace LogdetLean.GramHafnian.UltimateHiding.Dense

noncomputable section

/-- A deliberately elementary exponential domination, valid also at zero.
It is the only arithmetic input needed to make the final constant uniform in
`N`. -/
theorem nat_sq_le_four_pow (N : ℕ) : N ^ 2 ≤ 4 ^ N := by
  have hN : N ≤ 2 ^ N := by
    calc
      N ≤ 2 * N := by omega
      _ ≤ 2 ^ N := Nat.mul_le_pow (by decide) N
  calc
    N ^ 2 ≤ (2 ^ N) ^ 2 := Nat.pow_le_pow_left hN 2
    _ = 4 ^ N := by simp [pow_two, ← mul_pow]

/-- The reciprocal-square tail is dominated by twice the elementary
telescoping reciprocal-product tail. -/
theorem one_div_sq_le_two_div_mul_succ (m : ℕ) (hm : 1 ≤ m) :
    (1 : ℝ) / (m : ℝ) ^ 2 ≤
      2 * ((1 : ℝ) / ((m : ℝ) * ((m + 1 : ℕ) : ℝ))) := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hm)
  have hmOne : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hsuccR : 0 < ((m + 1 : ℕ) : ℝ) := by positivity
  rw [show 2 * ((1 : ℝ) / ((m : ℝ) * ((m + 1 : ℕ) : ℝ))) =
      2 / ((m : ℝ) * ((m + 1 : ℕ) : ℝ)) by ring]
  apply (div_le_div_iff₀ (sq_pos_of_pos hmR) (mul_pos hmR hsuccR)).2
  norm_num [Nat.cast_add]
  nlinarith

/-- Every finite initial segment of the shifted reciprocal-square series is
bounded by `2 / M`. -/
theorem sum_shifted_one_div_sq_le (M L : ℕ) (hM : 1 ≤ M) :
    (∑ j ∈ Finset.range L,
      (1 : ℝ) / (((M + j : ℕ) : ℝ) ^ 2)) ≤ 2 / (M : ℝ) := by
  calc
    (∑ j ∈ Finset.range L,
        (1 : ℝ) / (((M + j : ℕ) : ℝ) ^ 2))
        ≤ ∑ j ∈ Finset.range L,
            2 * ((1 : ℝ) /
              (((M + j : ℕ) : ℝ) * ((M + j + 1 : ℕ) : ℝ))) := by
          exact Finset.sum_le_sum fun j _ ↦
            one_div_sq_le_two_div_mul_succ (M + j) (by omega)
    _ = 2 * (1 / (M : ℝ) - 1 / ((M + L : ℕ) : ℝ)) := by
          rw [← Finset.mul_sum,
            sum_reciprocal_mul_succ M L hM]
    _ ≤ 2 / (M : ℝ) := by
          have htail : 0 ≤ (1 : ℝ) / ((M + L : ℕ) : ℝ) := by positivity
          have hsub :
              1 / (M : ℝ) - 1 / ((M + L : ℕ) : ℝ) ≤ 1 / (M : ℝ) :=
            sub_le_self _ htail
          simpa [div_eq_mul_inv] using
            mul_le_mul_of_nonneg_left hsub (show (0 : ℝ) ≤ 2 by norm_num)

/-- The exceptional-probability majorant at ambient index `M + j`. -/
def denseBadTailTerm (A : ℝ) (N M j : ℕ) : ℝ :=
  (A * (N : ℝ) ^ 2 / ((M + j : ℕ) : ℝ)) ^ (N + 2)

/-- A reciprocal-square majorant after spending the remaining `N` powers at
the dense threshold `A N² / M ≤ 1/4`. -/
def denseBadTailMajorant (A : ℝ) (N M j : ℕ) : ℝ :=
  ((A * (N : ℝ) ^ 2) ^ 2 * ((1 : ℝ) / 4) ^ N) *
    ((1 : ℝ) / (((M + j : ℕ) : ℝ) ^ 2))

theorem denseBadTailTerm_nonneg
    {A : ℝ} (hA : 0 ≤ A) (N M j : ℕ) :
    0 ≤ denseBadTailTerm A N M j := by
  unfold denseBadTailTerm
  positivity

/-- Pointwise dense-tail domination.  The hypothesis is the explicit choice
`C₀ = 4 A` in `M ≥ C₀ N²`. -/
theorem denseBadTailTerm_le_majorant
    {A : ℝ} (hA : 0 ≤ A) {N M : ℕ} (hM : 1 ≤ M)
    (hthreshold : 4 * A * (N : ℝ) ^ 2 ≤ (M : ℝ)) (j : ℕ) :
    denseBadTailTerm A N M j ≤ denseBadTailMajorant A N M j := by
  let r : ℝ := A * (N : ℝ) ^ 2 / ((M + j : ℕ) : ℝ)
  have hx : 0 < ((M + j : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < M + j by omega)
  have hr0 : 0 ≤ r := by
    dsimp [r]
    positivity
  have hMx : (M : ℝ) ≤ ((M + j : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_add_right M j
  have hr4 : r ≤ (1 : ℝ) / 4 := by
    apply (div_le_iff₀ hx).2
    nlinarith [hthreshold.trans hMx]
  have hpow : r ^ N ≤ ((1 : ℝ) / 4) ^ N :=
    pow_le_pow_left₀ hr0 hr4 N
  rw [denseBadTailTerm, show
      A * (N : ℝ) ^ 2 / ((M + j : ℕ) : ℝ) = r by rfl,
    Nat.add_comm N 2, pow_add]
  calc
    r ^ 2 * r ^ N ≤ r ^ 2 * ((1 : ℝ) / 4) ^ N :=
      mul_le_mul_of_nonneg_left hpow (sq_nonneg r)
    _ = denseBadTailMajorant A N M j := by
      simp only [denseBadTailMajorant, r, div_pow, one_pow]
      ring

/-- The coefficient left after the reciprocal-square factor is at most
`A² N²`.  This is where `N² ≤ 4ᴺ` makes the estimate uniform, including
`N = 1`. -/
theorem denseBadTailMajorantCoefficient_le
    (A : ℝ) (N : ℕ) :
    (A * (N : ℝ) ^ 2) ^ 2 * ((1 : ℝ) / 4) ^ N ≤
      A ^ 2 * (N : ℝ) ^ 2 := by
  have hfour : 0 < (4 : ℝ) ^ N := by positivity
  have hNfour : (N : ℝ) ^ 2 ≤ (4 : ℝ) ^ N := by
    exact_mod_cast nat_sq_le_four_pow N
  have hN2 : 0 ≤ (N : ℝ) ^ 2 := sq_nonneg _
  have hcore : ((N : ℝ) ^ 2) ^ 2 / (4 : ℝ) ^ N ≤ (N : ℝ) ^ 2 := by
    apply (div_le_iff₀ hfour).2
    simpa [pow_two] using mul_le_mul_of_nonneg_left hNfour hN2
  calc
    (A * (N : ℝ) ^ 2) ^ 2 * ((1 : ℝ) / 4) ^ N =
        A ^ 2 * (((N : ℝ) ^ 2) ^ 2 / (4 : ℝ) ^ N) := by
          simp only [one_div_pow]
          ring
    _ ≤ A ^ 2 * (N : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left hcore (sq_nonneg A)

/-- Explicit finite dense bad-tail estimate.  Under the concrete threshold
`M ≥ 4 A N²`, every finite partial tail is at most
`2 A² N² / M`. -/
theorem sum_denseBadTailTerm_le
    {A : ℝ} (hA : 0 ≤ A) {N M : ℕ}
    (_hN : 1 ≤ N) (hM : 1 ≤ M)
    (hthreshold : 4 * A * (N : ℝ) ^ 2 ≤ (M : ℝ)) (L : ℕ) :
    (∑ j ∈ Finset.range L, denseBadTailTerm A N M j) ≤
      2 * A ^ 2 * (N : ℝ) ^ 2 / (M : ℝ) := by
  let coeff : ℝ :=
    (A * (N : ℝ) ^ 2) ^ 2 * ((1 : ℝ) / 4) ^ N
  have hcoeff0 : 0 ≤ coeff := by
    dsimp [coeff]
    positivity
  have hcoeff : coeff ≤ A ^ 2 * (N : ℝ) ^ 2 := by
    exact denseBadTailMajorantCoefficient_le A N
  have hrecip := sum_shifted_one_div_sq_le M L hM
  calc
    (∑ j ∈ Finset.range L, denseBadTailTerm A N M j)
        ≤ ∑ j ∈ Finset.range L, denseBadTailMajorant A N M j := by
          exact Finset.sum_le_sum fun j _ ↦
            denseBadTailTerm_le_majorant hA hM hthreshold j
    _ = coeff *
        (∑ j ∈ Finset.range L,
          (1 : ℝ) / (((M + j : ℕ) : ℝ) ^ 2)) := by
          simp only [denseBadTailMajorant]
          rw [← Finset.mul_sum]
    _ ≤ coeff * (2 / (M : ℝ)) :=
      mul_le_mul_of_nonneg_left hrecip hcoeff0
    _ ≤ (A ^ 2 * (N : ℝ) ^ 2) * (2 / (M : ℝ)) := by
      exact mul_le_mul_of_nonneg_right hcoeff (by positivity)
    _ = 2 * A ^ 2 * (N : ℝ) ^ 2 / (M : ℝ) := by ring

/-- Pointwise form in the reciprocal-product normalization used by the dense
one-column telescope.  This is deliberately a little looser than the summed
estimate: it turns the exceptional event at ambient index `M` into the same
`C N² / (M(M+1))` budget as the analytic good-event contribution. -/
theorem denseBadTailTerm_zero_le_telescopingRate
    {A : ℝ} (hA : 0 ≤ A) {N M : ℕ}
    (_hN : 1 ≤ N) (hM : 1 ≤ M)
    (hthreshold : 4 * A * (N : ℝ) ^ 2 ≤ (M : ℝ)) :
    denseBadTailTerm A N M 0 ≤
      denseTelescopingRate (2 * A ^ 2) N M := by
  have hpoint := denseBadTailTerm_le_majorant hA hM hthreshold 0
  have hcoeff := denseBadTailMajorantCoefficient_le A N
  have hrecip := one_div_sq_le_two_div_mul_succ M hM
  have hmajorant :
      denseBadTailMajorant A N M 0 ≤
        2 * A ^ 2 * (N : ℝ) ^ 2 /
          ((M : ℝ) * ((M + 1 : ℕ) : ℝ)) := by
    unfold denseBadTailMajorant
    simp only [Nat.add_zero]
    calc
      ((A * (N : ℝ) ^ 2) ^ 2 * ((1 : ℝ) / 4) ^ N) *
          (1 / (M : ℝ) ^ 2)
          ≤ (A ^ 2 * (N : ℝ) ^ 2) * (1 / (M : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_right hcoeff (by positivity)
      _ ≤ (A ^ 2 * (N : ℝ) ^ 2) *
          (2 * (1 / ((M : ℝ) * ((M + 1 : ℕ) : ℝ)))) :=
            mul_le_mul_of_nonneg_left hrecip (by positivity)
      _ = 2 * A ^ 2 * (N : ℝ) ^ 2 /
          ((M : ℝ) * ((M + 1 : ℕ) : ℝ)) := by ring
  exact hpoint.trans <| by
    simpa [denseTelescopingRate] using hmajorant

/-- Infinite version of `sum_denseBadTailTerm_le`.  The index `j` represents
the ambient dimension `m = M + j`, so this is literally
`∑_{m=M}^∞ (A N² / m)^(N+2)`. -/
theorem tsum_denseBadTailTerm_le
    {A : ℝ} (hA : 0 ≤ A) {N M : ℕ}
    (hN : 1 ≤ N) (hM : 1 ≤ M)
    (hthreshold : 4 * A * (N : ℝ) ^ 2 ≤ (M : ℝ)) :
    (∑' j : ℕ, denseBadTailTerm A N M j) ≤
      2 * A ^ 2 * (N : ℝ) ^ 2 / (M : ℝ) := by
  apply Real.tsum_le_of_sum_range_le
  · exact fun j ↦ denseBadTailTerm_nonneg hA N M j
  · exact fun L ↦ sum_denseBadTailTerm_le hA hN hM hthreshold L

end

end LogdetLean.GramHafnian.UltimateHiding.Dense
