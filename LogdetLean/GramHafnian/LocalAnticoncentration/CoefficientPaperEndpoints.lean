import LogdetLean.GramHafnian.LocalAnticoncentration.CoefficientEndpoints
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Paper facing coefficient endpoints for the current manuscript

This file records the exact product and Gamma representations and the two
finite exponential estimates displayed in the current Letter.  It contains
no probabilistic assumptions.
-/

open Filter
open scoped BigOperators Nat

namespace LogdetLean.GramHafnian.LocalAnticoncentration

noncomputable section

/-- The coefficient called `b_n` in the current manuscript. -/
abbrev paperBn (n : ℕ) : ℝ := limitingAnticoncentrationConstant n

/-- The coefficient called `B_{k,n}` in the current manuscript. -/
abbrev paperBkn (k n : ℕ) : ℝ := shiftedAnticoncentrationConstant k n

/-- The displayed Gamma definition of `b_n`. -/
theorem paperBn_eq_gamma (n : ℕ) :
    paperBn n =
      2 * Real.Gamma ((n : ℝ) + 1 / 2) /
        (Real.sqrt Real.pi * Real.Gamma (n : ℝ)) := by
  rfl

/-- The universal Wallis upper bound for the coefficient `b_n`. -/
theorem paperBn_le_two_div_sqrt_pi_mul_sqrt (n : ℕ) (hn : 1 ≤ n) :
    paperBn n ≤ (2 / Real.sqrt Real.pi) * Real.sqrt (n : ℝ) :=
  limitingAnticoncentrationConstant_le_two_div_sqrt_pi_mul_sqrt n hn

/-- The coefficient normalization converges to one. -/
theorem paperBn_ratio_tendsto_one :
    Filter.Tendsto
      (fun n : ℕ ↦ paperBn n /
        (2 * Real.sqrt ((n : ℝ) / Real.pi)))
      Filter.atTop (nhds 1) := by
  have hfun :
      (fun n : ℕ ↦ paperBn n /
        (2 * Real.sqrt ((n : ℝ) / Real.pi))) =
      (fun n : ℕ ↦ paperBn n /
        (2 * Real.sqrt (n : ℝ) / Real.sqrt Real.pi)) := by
    funext n
    rw [Real.sqrt_div (Nat.cast_nonneg n)]
    ring
  rw [hfun]
  exact limitingAnticoncentrationConstant_ratio_tendsto_one

/-- The exact product formula in Eq. `Bproduct`. -/
theorem paperBkn_eq_product
    (k n : ℕ) (hn : 1 ≤ n) :
    paperBkn k n =
      paperBn n * ((k : ℝ) / ((k : ℝ) - 1)) *
        ∏ r ∈ Finset.Icc 2 n,
          (((k : ℝ) + 2 * (r : ℝ) - 2) /
            ((k : ℝ) - 4 * (r : ℝ) + 1)) := by
  rw [paperBkn, shiftedAnticoncentrationConstant]
  rw [← limitingAnticoncentrationConstant_eq_centralBinomial n hn]

/-- The exact Gamma formula in Eq. `Bexact`, first in a factorized form that
is definitionally identical to the manuscript formula. -/
theorem paperBkn_eq_gamma
    (k n : ℕ) (hn : 1 ≤ n) (hk : 4 * n ≤ k) :
    paperBkn k n =
      paperBn n *
        ((k : ℝ) / ((k : ℝ) - 1)) *
        ((2 : ℝ) ^ (n - 1) / (4 : ℝ) ^ (n - 1)) *
        (Real.Gamma ((k : ℝ) / 2 + (n : ℝ)) /
          Real.Gamma ((k : ℝ) / 2 + 1)) *
        (Real.Gamma (((k : ℝ) - 4 * (n : ℝ) + 1) / 4) /
          Real.Gamma (((k : ℝ) - 3) / 4)) := by
  exact shiftedAnticoncentrationConstant_eq_gamma k n hn hk

/-- The sharper exponential estimate Eq. `Bsharper`. -/
theorem paperBkn_le_sharper
    (k n : ℕ) (hn : 1 ≤ n) (hk : 4 * n ≤ k) :
    paperBkn k n ≤ paperBn n * Real.exp
      ((3 * (n : ℝ) ^ 2 - 2) / (k : ℝ) +
        9 * (n : ℝ) ^ 3 /
          ((k : ℝ) * ((k : ℝ) - 4 * (n : ℝ) + 1))) := by
  simpa [sharpAnticoncentrationExponent] using
    shiftedAnticoncentrationConstant_le_gamma_sharp hn hk

/-- In the region `k ≥ 8n`, the exponent from the elementary product estimate
is at most `8 n²/k` and hence at most the manuscript's `32 n²/k`. -/
theorem simplifiedExponent_le_thirtyTwo
    {k n : ℕ} (hn : 1 ≤ n) (hk : 8 * n ≤ k) :
    1 / ((k : ℝ) - 1) +
        (3 * (n : ℝ) ^ 2 - 3) /
          ((k : ℝ) - 4 * (n : ℝ) + 1) ≤
      32 * (n : ℝ) ^ 2 / (k : ℝ) := by
  have hkpos : 0 < (k : ℝ) := by
    exact_mod_cast (show 0 < k by omega)
  have hkm1 : 0 < (k : ℝ) - 1 := by
    have : (8 : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast (show 8 ≤ k by omega)
    linarith
  have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hhead :
      1 / ((k : ℝ) - 1) ≤ 2 * (n : ℝ) ^ 2 / (k : ℝ) := by
    rw [div_le_div_iff₀ hkm1 hkpos]
    have hnSq : 1 ≤ (n : ℝ) ^ 2 := by nlinarith
    have hkEight : 8 ≤ (k : ℝ) := by
      exact_mod_cast (show 8 ≤ k by omega)
    nlinarith
  have htail :
      (3 * (n : ℝ) ^ 2 - 3) /
          ((k : ℝ) - 4 * (n : ℝ) + 1) ≤
        6 * (n : ℝ) ^ 2 / (k : ℝ) := by
    have hkR : 8 * (n : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hnum0 : 0 ≤ 3 * (n : ℝ) ^ 2 := by positivity
    have hnum : 3 * (n : ℝ) ^ 2 - 3 ≤ 3 * (n : ℝ) ^ 2 := by linarith
    have hkhalf : 0 < (k : ℝ) / 2 := by positivity
    have hden : (k : ℝ) / 2 ≤ (k : ℝ) - 4 * (n : ℝ) + 1 := by
      nlinarith
    calc
      (3 * (n : ℝ) ^ 2 - 3) /
            ((k : ℝ) - 4 * (n : ℝ) + 1) ≤
          (3 * (n : ℝ) ^ 2) / ((k : ℝ) / 2) :=
        div_le_div₀ hnum0 hnum hkhalf hden
      _ = 6 * (n : ℝ) ^ 2 / (k : ℝ) := by
        field_simp [hkpos.ne']
        ring
  have hx : 0 ≤ (n : ℝ) ^ 2 / (k : ℝ) := by positivity
  calc
    1 / ((k : ℝ) - 1) +
          (3 * (n : ℝ) ^ 2 - 3) /
            ((k : ℝ) - 4 * (n : ℝ) + 1) ≤
        2 * (n : ℝ) ^ 2 / (k : ℝ) +
          6 * (n : ℝ) ^ 2 / (k : ℝ) := add_le_add hhead htail
    _ = 8 * ((n : ℝ) ^ 2 / (k : ℝ)) := by ring
    _ ≤ 32 * ((n : ℝ) ^ 2 / (k : ℝ)) := by nlinarith
    _ = 32 * (n : ℝ) ^ 2 / (k : ℝ) := by ring

/-- The large dimension half of the uniform coefficient estimate. -/
theorem paperBkn_le_uniform_of_eight_mul_le
    (k n : ℕ) (hn : 1 ≤ n) (hk : 8 * n ≤ k) :
    paperBkn k n ≤
      4 * Real.sqrt (n : ℝ) *
        Real.exp (32 * (n : ℝ) ^ 2 / (k : ℝ)) := by
  have hk4 : 4 * n ≤ k := by omega
  have hbase := shiftedAnticoncentrationConstant_le_simplified hn hk4
  have hexp := simplifiedExponent_le_thirtyTwo hn hk
  have hsqrt : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  calc
    paperBkn k n ≤
        2 * Real.sqrt (n : ℝ) *
          Real.exp
            (1 / ((k : ℝ) - 1) +
              (3 * (n : ℝ) ^ 2 - 3) /
                ((k : ℝ) - 4 * (n : ℝ) + 1)) := hbase
    _ ≤ 2 * Real.sqrt (n : ℝ) *
          Real.exp (32 * (n : ℝ) ^ 2 / (k : ℝ)) := by
      gcongr
    _ ≤ 4 * Real.sqrt (n : ℝ) *
          Real.exp (32 * (n : ℝ) ^ 2 / (k : ℝ)) := by
      have hnonneg :
          0 ≤ Real.sqrt (n : ℝ) *
            Real.exp (32 * (n : ℝ) ^ 2 / (k : ℝ)) := by positivity
      nlinarith

/-- At the endpoint `k=4n`, each shifted ratio is bounded by the
corresponding reversed factorial factor. -/
theorem endpoint_shiftedRatio_le_factorialFactor
    {n r : ℕ} (hr : r ∈ Finset.Icc 2 n) :
    (((4 * n : ℕ) : ℝ) + 2 * (r : ℝ) - 2) /
        (((4 * n : ℕ) : ℝ) - 4 * (r : ℝ) + 1) ≤
      (6 * (n : ℝ)) / ((n - r + 1 : ℕ) : ℝ) := by
  have hrn : r ≤ n := (Finset.mem_Icc.mp hr).2
  have hrnR : (r : ℝ) ≤ (n : ℝ) := by exact_mod_cast hrn
  have hden : 0 < ((4 * n : ℕ) : ℝ) - 4 * (r : ℝ) + 1 := by
    push_cast
    linarith
  have hnsub : 1 ≤ n - r + 1 := by omega
  have hrev : 0 < ((n - r + 1 : ℕ) : ℝ) := by exact_mod_cast hnsub
  have hnum0 :
      0 ≤ (((4 * n : ℕ) : ℝ) + 2 * (r : ℝ) - 2) := by
    have hr2R : (2 : ℝ) ≤ (r : ℝ) := by
      exact_mod_cast (Finset.mem_Icc.mp hr).1
    push_cast
    linarith
  have hnum :
      (((4 * n : ℕ) : ℝ) + 2 * (r : ℝ) - 2) ≤
        6 * (n : ℝ) := by
    push_cast
    linarith
  have hdenOrder :
      ((n - r + 1 : ℕ) : ℝ) ≤
        ((4 * n : ℕ) : ℝ) - 4 * (r : ℝ) + 1 := by
    rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub hrn]
    push_cast
    linarith
  exact div_le_div₀ (by positivity) hnum hrev hdenOrder

/-- Reversing the interval `2,...,n` identifies its denominator product with
`(n-1)!`. -/
theorem prod_Icc_reversed_add_one_eq_factorial (n : ℕ) :
    (∏ r ∈ Finset.Icc 2 n, ((n - r + 1 : ℕ) : ℝ)) =
      (((n - 1).factorial : ℕ) : ℝ) := by
  have hnat :
      (∏ r ∈ Finset.Icc 2 n, (n - r + 1)) = (n - 1).factorial := by
    rw [← Finset.prod_range_add_one_eq_factorial]
    apply Finset.prod_bij (fun r _hr ↦ n - r)
    · intro r hr
      simp only [Finset.mem_range]
      have hr2 : 2 ≤ r := (Finset.mem_Icc.mp hr).1
      have hrn : r ≤ n := (Finset.mem_Icc.mp hr).2
      omega
    · intro r₁ hr₁ r₂ hr₂ heq
      have h1 : r₁ ≤ n := (Finset.mem_Icc.mp hr₁).2
      have h2 : r₂ ≤ n := (Finset.mem_Icc.mp hr₂).2
      omega
    · intro j hj
      simp only [Finset.mem_range] at hj
      refine ⟨n - j, ?_, ?_⟩
      · exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      · omega
    · intro r hr
      omega
  exact_mod_cast hnat

/-- The head ratio decreases with the Gram dimension. -/
theorem shiftedHeadRatio_le_endpoint
    {k n : ℕ} (hn : 1 ≤ n) (hk : 4 * n ≤ k) :
    (k : ℝ) / ((k : ℝ) - 1) ≤
      ((4 * n : ℕ) : ℝ) / (((4 * n : ℕ) : ℝ) - 1) := by
  have hkR : ((4 * n : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkden : 0 < (k : ℝ) - 1 := by
    have : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 4 ≤ k by omega)
    linarith
  have henden : 0 < ((4 * n : ℕ) : ℝ) - 1 := by
    have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hn
    push_cast
    linarith
  rw [div_le_div_iff₀ hkden henden]
  push_cast at hkR ⊢
  nlinarith

/-- Every shifted ratio decreases with `k`, so its maximum on `k≥4n` is at
the endpoint. -/
theorem shiftedRatio_le_endpoint
    {k n r : ℕ} (hk : 4 * n ≤ k) (hr : r ∈ Finset.Icc 2 n) :
    ((k : ℝ) + 2 * (r : ℝ) - 2) /
        ((k : ℝ) - 4 * (r : ℝ) + 1) ≤
      (((4 * n : ℕ) : ℝ) + 2 * (r : ℝ) - 2) /
        (((4 * n : ℕ) : ℝ) - 4 * (r : ℝ) + 1) := by
  have hrn : r ≤ n := (Finset.mem_Icc.mp hr).2
  have hr2R : (2 : ℝ) ≤ (r : ℝ) := by
    exact_mod_cast (Finset.mem_Icc.mp hr).1
  have hkR : ((4 * n : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hden : 0 < (k : ℝ) - 4 * (r : ℝ) + 1 := by
    push_cast at hkR
    have hrnR : (r : ℝ) ≤ (n : ℝ) := by exact_mod_cast hrn
    linarith
  have henden :
      0 < ((4 * n : ℕ) : ℝ) - 4 * (r : ℝ) + 1 := by
    push_cast
    have hrnR : (r : ℝ) ≤ (n : ℝ) := by exact_mod_cast hrn
    linarith
  rw [div_le_div_iff₀ hden henden]
  push_cast at hkR ⊢
  have hprod :
      0 ≤ ((k : ℝ) - 4 * (n : ℝ)) * (6 * (r : ℝ) - 3) := by
    have hleft : 0 ≤ (k : ℝ) - 4 * (n : ℝ) := by
      push_cast at hkR
      linarith
    have hright : 0 ≤ 6 * (r : ℝ) - 3 := by linarith
    exact mul_nonneg hleft hright
  nlinarith

/-- The complete rational correction is maximal at `k=4n`. -/
theorem shiftedCorrection_le_endpoint
    {k n : ℕ} (hn : 1 ≤ n) (hk : 4 * n ≤ k) :
    ((k : ℝ) / ((k : ℝ) - 1)) *
        (∏ r ∈ Finset.Icc 2 n,
          (((k : ℝ) + 2 * (r : ℝ) - 2) /
            ((k : ℝ) - 4 * (r : ℝ) + 1))) ≤
      (((4 * n : ℕ) : ℝ) / (((4 * n : ℕ) : ℝ) - 1)) *
        (∏ r ∈ Finset.Icc 2 n,
          ((((4 * n : ℕ) : ℝ) + 2 * (r : ℝ) - 2) /
            (((4 * n : ℕ) : ℝ) - 4 * (r : ℝ) + 1))) := by
  have hhead := shiftedHeadRatio_le_endpoint hn hk
  have hprod :
      (∏ r ∈ Finset.Icc 2 n,
          (((k : ℝ) + 2 * (r : ℝ) - 2) /
            ((k : ℝ) - 4 * (r : ℝ) + 1))) ≤
        (∏ r ∈ Finset.Icc 2 n,
          ((((4 * n : ℕ) : ℝ) + 2 * (r : ℝ) - 2) /
            (((4 * n : ℕ) : ℝ) - 4 * (r : ℝ) + 1))) := by
    apply Finset.prod_le_prod
    · intro r hr
      have hrn : r ≤ n := (Finset.mem_Icc.mp hr).2
      have hden := shiftedDenominator_pos hk hrn
      have hnum : 0 ≤ (k : ℝ) + 2 * (r : ℝ) - 2 := by
        have hr2R : (2 : ℝ) ≤ (r : ℝ) := by
          exact_mod_cast (Finset.mem_Icc.mp hr).1
        have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
        linarith
      exact div_nonneg hnum hden.le
    · intro r hr
      exact shiftedRatio_le_endpoint hk hr
  have hhead0 : 0 ≤ (k : ℝ) / ((k : ℝ) - 1) := by
    have hden : 0 < (k : ℝ) - 1 := by
      have : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 4 ≤ k by omega)
      linarith
    positivity
  have htargetHead0 :
      0 ≤ ((4 * n : ℕ) : ℝ) / (((4 * n : ℕ) : ℝ) - 1) := by
    have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hn
    have hden : 0 ≤ (((4 * n : ℕ) : ℝ) - 1) := by
      push_cast
      linarith
    exact div_nonneg (Nat.cast_nonneg _) hden
  have hsourceProd0 : 0 ≤
      (∏ r ∈ Finset.Icc 2 n,
        (((k : ℝ) + 2 * (r : ℝ) - 2) /
          ((k : ℝ) - 4 * (r : ℝ) + 1))) := by
    apply Finset.prod_nonneg
    intro r hr
    have hrn : r ≤ n := (Finset.mem_Icc.mp hr).2
    have hden := shiftedDenominator_pos hk hrn
    have hr2R : (2 : ℝ) ≤ (r : ℝ) := by
      exact_mod_cast (Finset.mem_Icc.mp hr).1
    have hnum : 0 ≤ (k : ℝ) + 2 * (r : ℝ) - 2 := by
      have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    exact div_nonneg hnum hden.le
  exact mul_le_mul hhead hprod hsourceProd0 htargetHead0

/-- The endpoint product is controlled by a single factorial ratio. -/
theorem endpointCorrection_le_factorialRatio
    (n : ℕ) (hn : 1 ≤ n) :
    (((4 * n : ℕ) : ℝ) / (((4 * n : ℕ) : ℝ) - 1)) *
        (∏ r ∈ Finset.Icc 2 n,
          ((((4 * n : ℕ) : ℝ) + 2 * (r : ℝ) - 2) /
            (((4 * n : ℕ) : ℝ) - 4 * (r : ℝ) + 1))) ≤
      2 * (6 * (n : ℝ)) ^ (n - 1) /
        (((n - 1).factorial : ℕ) : ℝ) := by
  have hhead :
      ((4 * n : ℕ) : ℝ) / (((4 * n : ℕ) : ℝ) - 1) ≤ 2 := by
    have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hn
    have hden : 0 < ((4 * n : ℕ) : ℝ) - 1 := by
      push_cast
      linarith
    rw [div_le_iff₀ hden]
    push_cast
    linarith
  have hprod :
      (∏ r ∈ Finset.Icc 2 n,
          ((((4 * n : ℕ) : ℝ) + 2 * (r : ℝ) - 2) /
            (((4 * n : ℕ) : ℝ) - 4 * (r : ℝ) + 1))) ≤
        (6 * (n : ℝ)) ^ (n - 1) /
          (((n - 1).factorial : ℕ) : ℝ) := by
    calc
      (∏ r ∈ Finset.Icc 2 n,
          ((((4 * n : ℕ) : ℝ) + 2 * (r : ℝ) - 2) /
            (((4 * n : ℕ) : ℝ) - 4 * (r : ℝ) + 1))) ≤
          ∏ r ∈ Finset.Icc 2 n,
            ((6 * (n : ℝ)) / ((n - r + 1 : ℕ) : ℝ)) := by
        apply Finset.prod_le_prod
        · intro r hr
          have hrn : r ≤ n := (Finset.mem_Icc.mp hr).2
          have hden :
              0 < ((4 * n : ℕ) : ℝ) - 4 * (r : ℝ) + 1 := by
            push_cast
            have hrnR : (r : ℝ) ≤ (n : ℝ) := by exact_mod_cast hrn
            linarith
          have hr2R : (2 : ℝ) ≤ (r : ℝ) := by
            exact_mod_cast (Finset.mem_Icc.mp hr).1
          have hnR : (r : ℝ) ≤ (n : ℝ) := by exact_mod_cast hrn
          have hnum :
              0 ≤ ((4 * n : ℕ) : ℝ) + 2 * (r : ℝ) - 2 := by
            push_cast
            linarith
          exact div_nonneg hnum hden.le
        · intro r hr
          exact endpoint_shiftedRatio_le_factorialFactor hr
      _ = (6 * (n : ℝ)) ^ (n - 1) /
          (((n - 1).factorial : ℕ) : ℝ) := by
        rw [Finset.prod_div_distrib]
        rw [prod_Icc_reversed_add_one_eq_factorial n]
        congr 1
        rw [Finset.prod_const]
        simp [Nat.card_Icc, hn]
  have hprod0 : 0 ≤
      (∏ r ∈ Finset.Icc 2 n,
        ((((4 * n : ℕ) : ℝ) + 2 * (r : ℝ) - 2) /
          (((4 * n : ℕ) : ℝ) - 4 * (r : ℝ) + 1))) := by
    apply Finset.prod_nonneg
    intro r hr
    have hrn : r ≤ n := (Finset.mem_Icc.mp hr).2
    have hden : 0 < ((4 * n : ℕ) : ℝ) - 4 * (r : ℝ) + 1 := by
      push_cast
      have hrnR : (r : ℝ) ≤ (n : ℝ) := by exact_mod_cast hrn
      linarith
    have hr2R : (2 : ℝ) ≤ (r : ℝ) := by
      exact_mod_cast (Finset.mem_Icc.mp hr).1
    have hnum :
        0 ≤ ((4 * n : ℕ) : ℝ) + 2 * (r : ℝ) - 2 := by
      push_cast
      linarith
    exact div_nonneg hnum hden.le
  calc
    (((4 * n : ℕ) : ℝ) / (((4 * n : ℕ) : ℝ) - 1)) *
          (∏ r ∈ Finset.Icc 2 n,
            ((((4 * n : ℕ) : ℝ) + 2 * (r : ℝ) - 2) /
              (((4 * n : ℕ) : ℝ) - 4 * (r : ℝ) + 1))) ≤
        2 * ((6 * (n : ℝ)) ^ (n - 1) /
          (((n - 1).factorial : ℕ) : ℝ)) :=
      mul_le_mul hhead hprod hprod0 (by norm_num)
    _ = 2 * (6 * (n : ℝ)) ^ (n - 1) /
        (((n - 1).factorial : ℕ) : ℝ) := by ring

/-- A coarse Stirling estimate sufficient for the endpoint half of the
uniform `exp(4n)` bound. -/
theorem factorialRatio_le_exp_four_mul_of_two_le
    (n : ℕ) (hn : 2 ≤ n) :
    2 * (6 * (n : ℝ)) ^ (n - 1) /
        (((n - 1).factorial : ℕ) : ℝ) ≤
      Real.exp (4 * (n : ℝ)) := by
  let m : ℕ := n - 1
  have hm : 1 ≤ m := by omega
  have hmR : 1 ≤ (m : ℝ) := by exact_mod_cast hm
  have hnR : (n : ℝ) ≤ 2 * (m : ℝ) := by
    dsimp [m]
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    push_cast
    have hnTwo : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hsqrt : 1 ≤ Real.sqrt (2 * Real.pi * (m : ℝ)) := by
    rw [← Real.sqrt_one]
    apply Real.sqrt_le_sqrt
    have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
    nlinarith
  have hstirling := Stirling.le_factorial_stirling m
  have hfac :
      ((m : ℝ) / Real.exp 1) ^ m ≤ ((m.factorial : ℕ) : ℝ) := by
    have hpow0 : 0 ≤ ((m : ℝ) / Real.exp 1) ^ m := by positivity
    calc
      ((m : ℝ) / Real.exp 1) ^ m ≤
          Real.sqrt (2 * Real.pi * (m : ℝ)) *
            ((m : ℝ) / Real.exp 1) ^ m := by
        nlinarith
      _ ≤ ((m.factorial : ℕ) : ℝ) := hstirling
  have hfacpos : 0 < ((m.factorial : ℕ) : ℝ) := by positivity
  have hbasepos : 0 < ((m : ℝ) / Real.exp 1) ^ m := by positivity
  have hratio :
      (6 * (n : ℝ)) ^ m / ((m.factorial : ℕ) : ℝ) ≤
        (12 * Real.exp 1) ^ m := by
    calc
      (6 * (n : ℝ)) ^ m / ((m.factorial : ℕ) : ℝ) ≤
          (6 * (n : ℝ)) ^ m /
            (((m : ℝ) / Real.exp 1) ^ m) :=
        div_le_div_of_nonneg_left (by positivity) hbasepos hfac
      _ = ((6 * (n : ℝ)) / ((m : ℝ) / Real.exp 1)) ^ m := by
        exact (div_pow _ _ m).symm
      _ = (6 * (n : ℝ) * Real.exp 1 / (m : ℝ)) ^ m := by
        congr 1
        field_simp [show (m : ℝ) ≠ 0 by positivity,
          Real.exp_ne_zero 1]
      _ ≤ (12 * Real.exp 1) ^ m := by
        apply pow_le_pow_left₀ (by positivity)
        have he : 0 < Real.exp 1 := Real.exp_pos 1
        calc
          6 * (n : ℝ) * Real.exp 1 / (m : ℝ) ≤
              6 * (2 * (m : ℝ)) * Real.exp 1 / (m : ℝ) := by
            gcongr
          _ = 12 * Real.exp 1 := by
            field_simp [show (m : ℝ) ≠ 0 by positivity]
            ring
  have hbase : 12 * Real.exp 1 ≤ Real.exp 4 := by
    have he : (5 / 2 : ℝ) ≤ Real.exp 1 := by
      exact (show (5 / 2 : ℝ) < 2.7182818283 by norm_num).trans
        Real.exp_one_gt_d9 |>.le
    have hecube : (12 : ℝ) ≤ (Real.exp 1) ^ 3 := by
      calc
        (12 : ℝ) ≤ (5 / 2 : ℝ) ^ 3 := by norm_num
        _ ≤ (Real.exp 1) ^ 3 := by gcongr
    calc
      12 * Real.exp 1 ≤ (Real.exp 1) ^ 3 * Real.exp 1 := by
        gcongr
      _ = (Real.exp 1) ^ 4 := by ring
      _ = Real.exp 4 := by
        rw [← Real.exp_nat_mul]
        norm_num
  have hpow : (12 * Real.exp 1) ^ m ≤ Real.exp (4 * (m : ℝ)) := by
    calc
      (12 * Real.exp 1) ^ m ≤ (Real.exp 4) ^ m := by
        exact (pow_le_pow_left₀ (by positivity) hbase) m
      _ = Real.exp (4 * (m : ℝ)) := by
        rw [← Real.exp_nat_mul]
        push_cast
        ring
  have htwo : (2 : ℝ) ≤ Real.exp 4 := by
    have := Real.exp_one_gt_two
    calc
      (2 : ℝ) ≤ Real.exp 1 := this.le
      _ ≤ Real.exp 4 := Real.exp_le_exp.mpr (by norm_num)
  calc
    2 * (6 * (n : ℝ)) ^ (n - 1) /
          (((n - 1).factorial : ℕ) : ℝ) =
        2 * ((6 * (n : ℝ)) ^ m / ((m.factorial : ℕ) : ℝ)) := by
      dsimp [m]
      ring
    _ ≤ 2 * (12 * Real.exp 1) ^ m := by gcongr
    _ ≤ Real.exp 4 * Real.exp (4 * (m : ℝ)) := by
      exact mul_le_mul htwo hpow (by positivity) (Real.exp_nonneg _)
    _ = Real.exp (4 * (n : ℝ)) := by
      rw [← Real.exp_add]
      dsimp [m]
      rw [Nat.cast_sub (by omega : 1 ≤ n)]
      push_cast
      congr 1
      ring

/-- The endpoint factorial ratio estimate, including the one degree base
case. -/
theorem factorialRatio_le_exp_four_mul
    (n : ℕ) (hn : 1 ≤ n) :
    2 * (6 * (n : ℝ)) ^ (n - 1) /
        (((n - 1).factorial : ℕ) : ℝ) ≤
      Real.exp (4 * (n : ℝ)) := by
  by_cases htwo : 2 ≤ n
  · exact factorialRatio_le_exp_four_mul_of_two_le n htwo
  · have hn1 : n = 1 := by omega
    subst n
    norm_num
    exact (Real.exp_one_gt_two.le.trans
      (Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 4)))

/-- manuscript Eq. (20) as one literal endpoint.  The manuscript invokes this in
the branch `4n ≤ k < 8n` and states `n ≥ 4`; the inequality itself is valid
on the stronger range `n ≥ 1`, `4n ≤ k`. -/
theorem eq20_endpoint_product
    (k n : ℕ) (hn : 1 ≤ n) (hk : 4 * n ≤ k) :
    (((k : ℝ) / ((k : ℝ) - 1)) *
          (∏ r ∈ Finset.Icc 2 n,
            (((k : ℝ) + 2 * (r : ℝ) - 2) /
              ((k : ℝ) - 4 * (r : ℝ) + 1))) ≤
        2 * (6 * (n : ℝ)) ^ (n - 1) /
          (((n - 1).factorial : ℕ) : ℝ)) ∧
      (2 * (6 * (n : ℝ)) ^ (n - 1) /
          (((n - 1).factorial : ℕ) : ℝ) ≤
        Real.exp (4 * (n : ℝ))) := by
  constructor
  · exact (shiftedCorrection_le_endpoint hn hk).trans
      (endpointCorrection_le_factorialRatio n hn)
  · exact factorialRatio_le_exp_four_mul n hn

/-- The endpoint half of the uniform coefficient estimate. -/
theorem paperBkn_le_uniform_of_lt_eight_mul
    (k n : ℕ) (hn : 1 ≤ n) (hk : 4 * n ≤ k) (hk8 : k < 8 * n) :
    paperBkn k n ≤
      4 * Real.sqrt (n : ℝ) *
        Real.exp (32 * (n : ℝ) ^ 2 / (k : ℝ)) := by
  have hcorrEndpoint := shiftedCorrection_le_endpoint hn hk
  have hendpointFactorial := endpointCorrection_le_factorialRatio n hn
  have hfactorialExp := factorialRatio_le_exp_four_mul n hn
  have hcorr :
      ((k : ℝ) / ((k : ℝ) - 1)) *
          (∏ r ∈ Finset.Icc 2 n,
            (((k : ℝ) + 2 * (r : ℝ) - 2) /
              ((k : ℝ) - 4 * (r : ℝ) + 1))) ≤
        Real.exp (4 * (n : ℝ)) :=
    hcorrEndpoint.trans (hendpointFactorial.trans hfactorialExp)
  have hcorr0 : 0 ≤
      ((k : ℝ) / ((k : ℝ) - 1)) *
        (∏ r ∈ Finset.Icc 2 n,
          (((k : ℝ) + 2 * (r : ℝ) - 2) /
            ((k : ℝ) - 4 * (r : ℝ) + 1))) := by
    have hheadDen : 0 < (k : ℝ) - 1 := by
      have : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 4 ≤ k by omega)
      linarith
    apply mul_nonneg (div_nonneg (Nat.cast_nonneg k) hheadDen.le)
    apply Finset.prod_nonneg
    intro r hr
    have hrn : r ≤ n := (Finset.mem_Icc.mp hr).2
    have hden := shiftedDenominator_pos hk hrn
    have hr2R : (2 : ℝ) ≤ (r : ℝ) := by
      exact_mod_cast (Finset.mem_Icc.mp hr).1
    have hnum : 0 ≤ (k : ℝ) + 2 * (r : ℝ) - 2 := by
      have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    exact div_nonneg hnum hden.le
  have hb := limitingAnticoncentrationConstant_le_two_sqrt n hn
  have hsqrt : 0 ≤ 2 * Real.sqrt (n : ℝ) := by positivity
  have hpre :
      paperBkn k n ≤
        2 * Real.sqrt (n : ℝ) * Real.exp (4 * (n : ℝ)) := by
    rw [paperBkn_eq_product k n hn]
    rw [mul_assoc]
    exact mul_le_mul hb hcorr hcorr0 hsqrt
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hnpos : 0 < (n : ℝ) := by positivity
  have hk8R : (k : ℝ) < 8 * (n : ℝ) := by exact_mod_cast hk8
  have hexponent :
      4 * (n : ℝ) ≤ 32 * (n : ℝ) ^ 2 / (k : ℝ) := by
    rw [le_div_iff₀ hkpos]
    nlinarith
  calc
    paperBkn k n ≤
        2 * Real.sqrt (n : ℝ) * Real.exp (4 * (n : ℝ)) := hpre
    _ ≤ 2 * Real.sqrt (n : ℝ) *
          Real.exp (32 * (n : ℝ) ^ 2 / (k : ℝ)) := by
      gcongr
    _ ≤ 4 * Real.sqrt (n : ℝ) *
          Real.exp (32 * (n : ℝ) ^ 2 / (k : ℝ)) := by
      have hnonneg :
          0 ≤ Real.sqrt (n : ℝ) *
            Real.exp (32 * (n : ℝ) ^ 2 / (k : ℝ)) := by positivity
      nlinarith

/-- The uniform bound in Eq. `Bproduct`, valid on the full theorem range. -/
theorem paperBkn_le_uniform
    (k n : ℕ) (hn : 1 ≤ n) (hk : 4 * n ≤ k) :
    paperBkn k n ≤
      4 * Real.sqrt (n : ℝ) *
        Real.exp (32 * (n : ℝ) ^ 2 / (k : ℝ)) := by
  by_cases hk8 : 8 * n ≤ k
  · exact paperBkn_le_uniform_of_eight_mul_le k n hn hk8
  · exact paperBkn_le_uniform_of_lt_eight_mul k n hn hk (by omega)

/-- The logarithmic product estimate used in the `k≥8n` branch of the End
Matter. -/
theorem log_shiftedRatioProduct_le
    (k n : ℕ) (hn : 1 ≤ n) (hk : 8 * n ≤ k) :
    Real.log
        (∏ r ∈ Finset.Icc 2 n,
          (((k : ℝ) + 2 * (r : ℝ) - 2) /
            ((k : ℝ) - 4 * (r : ℝ) + 1))) ≤
      (6 * (n : ℝ) ^ 2 - 6) / (k : ℝ) := by
  have hk4 : 4 * n ≤ k := by omega
  have hprod := shiftedRatioProduct_le_exp hn hk4
  have hkR : 8 * (n : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hden : 0 < (k : ℝ) - 4 * (n : ℝ) + 1 := by nlinarith
  have hnum : 0 ≤ 3 * (n : ℝ) ^ 2 - 3 := by
    have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith [sq_nonneg ((n : ℝ) - 1)]
  have hexponent :
      (3 * (n : ℝ) ^ 2 - 3) /
          ((k : ℝ) - 4 * (n : ℝ) + 1) ≤
        (6 * (n : ℝ) ^ 2 - 6) / (k : ℝ) := by
    have hdenOrder : (k : ℝ) / 2 ≤
        (k : ℝ) - 4 * (n : ℝ) + 1 := by nlinarith
    calc
      (3 * (n : ℝ) ^ 2 - 3) /
            ((k : ℝ) - 4 * (n : ℝ) + 1) ≤
          (3 * (n : ℝ) ^ 2 - 3) / ((k : ℝ) / 2) :=
        div_le_div_of_nonneg_left hnum (by positivity) hdenOrder
      _ = (6 * (n : ℝ) ^ 2 - 6) / (k : ℝ) := by
        field_simp [hkpos.ne']
        ring
  have hprodpos : 0 <
      (∏ r ∈ Finset.Icc 2 n,
        (((k : ℝ) + 2 * (r : ℝ) - 2) /
          ((k : ℝ) - 4 * (r : ℝ) + 1))) := by
    apply Finset.prod_pos
    intro r hr
    have hrn : r ≤ n := (Finset.mem_Icc.mp hr).2
    have hfactorDen := shiftedDenominator_pos hk4 hrn
    have hr2R : (2 : ℝ) ≤ (r : ℝ) := by
      exact_mod_cast (Finset.mem_Icc.mp hr).1
    have hfactorNum : 0 < (k : ℝ) + 2 * (r : ℝ) - 2 := by
      have hk0 : 0 < (k : ℝ) := hkpos
      linarith
    exact div_pos hfactorNum hfactorDen
  rw [Real.log_le_iff_le_exp hprodpos]
  exact hprod.trans (Real.exp_le_exp.mpr hexponent)

/-- The explicit polynomial coefficient estimate stated after Eq.
`Bsharper`. -/
theorem paperBkn_polynomial_regime
    (kseq : ℕ → ℕ) {D : ℝ} (hD : 0 < D)
    (hk4 : ∀ᶠ n : ℕ in atTop, 4 * n ≤ kseq n)
    (hscale : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ 2 / (kseq n : ℝ) ≤ D * Real.log (n : ℝ)) :
    ∀ᶠ n : ℕ in atTop,
      paperBkn (kseq n) n ≤
        2 * Real.exp 1 * (n : ℝ) ^ (3 * D + (1 / 2 : ℝ)) := by
  have hkpos : ∀ᶠ n : ℕ in atTop, 0 < kseq n := by
    filter_upwards [hk4, eventually_ge_atTop 1] with n hk hn
    omega
  have hremT := tendsto_finiteCoefficientLogRemainder_of_log_scale
    kseq hD hkpos hscale
  have hrem : ∀ᶠ n : ℕ in atTop,
      finiteCoefficientLogRemainder (kseq n) n ≤ 1 :=
    hremT.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hk4, hscale, hrem, eventually_ge_atTop 1]
    with n hkn hs hr hn
  have hnpos : 0 < (n : ℝ) := by positivity
  have hexponent :
      3 * (n : ℝ) ^ 2 / (kseq n : ℝ) +
          finiteCoefficientLogRemainder (kseq n) n ≤
        3 * D * Real.log (n : ℝ) + 1 := by
    have hthree := mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 3)
    calc
      3 * (n : ℝ) ^ 2 / (kseq n : ℝ) +
            finiteCoefficientLogRemainder (kseq n) n =
          3 * ((n : ℝ) ^ 2 / (kseq n : ℝ)) +
            finiteCoefficientLogRemainder (kseq n) n := by ring
      _ ≤ 3 * (D * Real.log (n : ℝ)) + 1 := add_le_add hthree hr
      _ = 3 * D * Real.log (n : ℝ) + 1 := by ring
  have hb := limitingAnticoncentrationConstant_le_two_sqrt n hn
  calc
    paperBkn (kseq n) n =
        paperBn n * Real.exp
          (3 * (n : ℝ) ^ 2 / (kseq n : ℝ) +
            finiteCoefficientLogRemainder (kseq n) n) := by
      exact shiftedAnticoncentrationConstant_eq_limit_mul_exp hn hkn
    _ ≤ 2 * Real.sqrt (n : ℝ) *
          Real.exp (3 * D * Real.log (n : ℝ) + 1) := by
      exact mul_le_mul hb (Real.exp_le_exp.mpr hexponent)
        (Real.exp_nonneg _) (by positivity)
    _ = 2 * Real.exp 1 *
          (n : ℝ) ^ (3 * D + (1 / 2 : ℝ)) := by
      rw [Real.sqrt_eq_rpow, Real.exp_add]
      rw [show Real.exp (3 * D * Real.log (n : ℝ)) =
          (n : ℝ) ^ (3 * D) by
        rw [Real.rpow_def_of_pos hnpos]
        congr 1
        ring]
      calc
        2 * (n : ℝ) ^ (1 / 2 : ℝ) *
              ((n : ℝ) ^ (3 * D) * Real.exp 1) =
            2 * Real.exp 1 *
              ((n : ℝ) ^ (3 * D) * (n : ℝ) ^ (1 / 2 : ℝ)) := by ring
        _ = 2 * Real.exp 1 *
            (n : ℝ) ^ (3 * D + (1 / 2 : ℝ)) := by
          rw [Real.rpow_add hnpos]

end

end LogdetLean.GramHafnian.LocalAnticoncentration
