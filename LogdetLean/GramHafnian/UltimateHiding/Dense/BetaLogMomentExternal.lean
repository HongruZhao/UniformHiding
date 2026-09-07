import LogdetLean.GramHafnian.UltimateHiding.Dense.BetaTailConcrete
import Mathlib.Tactic

/-!
# Harmonic-window bounds for the one-column beta variable

The one-column Taylor argument uses finite reciprocal-power windows associated
with `q ~ Beta(m-N+1,N)`. This legacy-named module now contains only their
definition and elementary bounds. The former beta-calculus axiom has been
removed; the exact logarithmic moments are proved internally in
`BetaLogMomentsInternal.lean` from the beta Mellin transform and the project's
digamma/polygamma series.

For integer shapes it follows by differentiating

`E[q^t] = B(m-N+1+t,N) / B(m-N+1,N)`

three times at zero and using the digamma/polygamma recurrences.  Equivalently,
if `X=-log q`, its first three cumulants are `H₁,H₂,2H₃`, where

`H_r = sum_{j=m-N+1}^m j^{-r}`.

Source ledger: NIST Digital Library of Mathematical Functions, sections 5.12
(beta function) and 5.15 (polygamma recurrences),
https://dlmf.nist.gov/5.12 and https://dlmf.nist.gov/5.15.
-/

open MeasureTheory Finset

namespace LogdetLean.GramHafnian.UltimateHiding.Dense

noncomputable section

/-- The finite reciprocal-power sum from `m-N+1` through `m`. -/
def oneColumnLogHarmonic (m N r : ℕ) : ℝ :=
  ∑ j ∈ Finset.range N,
    (1 : ℝ) / (((m + 1 - N + j : ℕ) : ℝ) ^ r)

theorem oneColumnLogHarmonic_nonneg (m N r : ℕ) :
    0 ≤ oneColumnLogHarmonic m N r := by
  unfold oneColumnLogHarmonic
  exact Finset.sum_nonneg fun _ _ ↦ by positivity

/-- Every denominator in the harmonic window is at least `m/2` in the
large-ambient range `2N≤m`. -/
theorem oneColumn_harmonic_denominator_half
    {m N j : ℕ} (hN : 1 ≤ N) (h2Nm : 2 * N ≤ m)
    (hj : j ∈ Finset.range N) :
    (m : ℝ) ≤ 2 * ((m + 1 - N + j : ℕ) : ℝ) := by
  have hjN : j < N := Finset.mem_range.mp hj
  have hnat : m ≤ 2 * (m + 1 - N + j) := by omega
  exact_mod_cast hnat

/-- Uniform harmonic-window estimate. -/
theorem oneColumnLogHarmonic_le
    {m N r : ℕ} (hN : 1 ≤ N) (h2Nm : 2 * N ≤ m) :
    oneColumnLogHarmonic m N r ≤
      (N : ℝ) * ((2 : ℝ) / (m : ℝ)) ^ r := by
  have hm : 0 < (m : ℝ) := by
    have : 0 < m := by omega
    exact_mod_cast this
  unfold oneColumnLogHarmonic
  calc
    (∑ j ∈ Finset.range N,
        (1 : ℝ) / (((m + 1 - N + j : ℕ) : ℝ) ^ r)) ≤
        ∑ j ∈ Finset.range N, ((2 : ℝ) / (m : ℝ)) ^ r := by
      apply Finset.sum_le_sum
      intro j hj
      have hdNat : 1 ≤ m + 1 - N + j := by omega
      have hd : 0 < ((m + 1 - N + j : ℕ) : ℝ) := by exact_mod_cast hdNat
      have hbase :
          (1 : ℝ) / ((m + 1 - N + j : ℕ) : ℝ) ≤ 2 / (m : ℝ) := by
        apply (div_le_div_iff₀ hd hm).2
        simpa using oneColumn_harmonic_denominator_half hN h2Nm hj
      simpa [one_div_pow] using
        (pow_le_pow_left₀ (by positivity) hbase r)
    _ = (N : ℝ) * ((2 : ℝ) / (m : ℝ)) ^ r := by simp

theorem oneColumnLogHarmonic_one_le
    {m N : ℕ} (hN : 1 ≤ N) (h2Nm : 2 * N ≤ m) :
    oneColumnLogHarmonic m N 1 ≤ 2 * (N : ℝ) / (m : ℝ) := by
  calc
    oneColumnLogHarmonic m N 1 ≤
        (N : ℝ) * ((2 : ℝ) / (m : ℝ)) :=
      by simpa only [pow_one] using
        (oneColumnLogHarmonic_le (r := 1) hN h2Nm)
    _ = 2 * (N : ℝ) / (m : ℝ) := by ring

theorem oneColumnLogHarmonic_two_le
    {m N : ℕ} (hN : 1 ≤ N) (h2Nm : 2 * N ≤ m) :
    oneColumnLogHarmonic m N 2 ≤ 4 * (N : ℝ) / (m : ℝ) ^ 2 := by
  calc
    oneColumnLogHarmonic m N 2 ≤
        (N : ℝ) * ((2 : ℝ) / (m : ℝ)) ^ 2 :=
      oneColumnLogHarmonic_le (r := 2) hN h2Nm
    _ = 4 * (N : ℝ) / (m : ℝ) ^ 2 := by ring

theorem oneColumnLogHarmonic_three_le
    {m N : ℕ} (hN : 1 ≤ N) (h2Nm : 2 * N ≤ m) :
    oneColumnLogHarmonic m N 3 ≤ 8 * (N : ℝ) / (m : ℝ) ^ 3 := by
  calc
    oneColumnLogHarmonic m N 3 ≤
        (N : ℝ) * ((2 : ℝ) / (m : ℝ)) ^ 3 :=
      oneColumnLogHarmonic_le (r := 3) hN h2Nm
    _ = 8 * (N : ℝ) / (m : ℝ) ^ 3 := by ring

end

end LogdetLean.GramHafnian.UltimateHiding.Dense
