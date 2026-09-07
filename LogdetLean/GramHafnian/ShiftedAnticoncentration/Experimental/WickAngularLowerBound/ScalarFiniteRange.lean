import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Data.Nat.Choose.Central

/-!
# Scalar certificate for the finite Wick angular range

This file contains no probability theory.  It reduces the scalar Wick
expression at integral and half-integral Gamma arguments to exact rational
arithmetic and proves its finite one-third-range lower bound.
-/

open scoped BigOperators
open Finset

namespace LogdetLean.GramHafnian.WickAngularLowerBound

/-- The exact rational form of `1 / (k * mu_k^2)`. -/
def angularBaseQ (k : ℕ) : ℚ :=
  4 * k * (Nat.centralBinom k : ℚ) ^ 2 / 16 ^ k

/-- The exact rational Gamma-ratio factor in the Wick lower bound. -/
def oddDimensionRatioQ (k n : ℕ) : ℚ :=
  ∏ q ∈ range n, ((2 * q + 1 : ℕ) : ℚ) / (k + 2 * q : ℕ)

/-- The exact discrete scalar Wick ratio. -/
def wickScalarRatioQ (k n : ℕ) : ℚ :=
  oddDimensionRatioQ k n * angularBaseQ k ^ (2 * n - 1)

def expStepQ : ℚ := 500 / 499

/-! The following natural-number numerators and denominators let the closed
finite certificates be checked by Lean's kernel evaluator without expanding
large rational-normalization proof terms. -/

private def angularNumN (k : ℕ) : ℕ :=
  4 * k * Nat.centralBinom k ^ 2

private def angularDenN (k : ℕ) : ℕ :=
  16 ^ k

private def oddNumN (n : ℕ) : ℕ :=
  ∏ q ∈ range n, (2 * q + 1)

private def dimensionDenN (k n : ℕ) : ℕ :=
  ∏ q ∈ range n, (k + 2 * q)

private def scalarNumN (k n : ℕ) : ℕ :=
  oddNumN n * angularNumN k ^ (2 * n - 1)

private def scalarDenN (k n : ℕ) : ℕ :=
  dimensionDenN k n * angularDenN k ^ (2 * n - 1)

private def expNumN (n : ℕ) : ℕ := 500 ^ n

private def expDenN (n : ℕ) : ℕ := 499 ^ n

private lemma angularBaseQ_eq_num_div (k : ℕ) :
    angularBaseQ k = (angularNumN k : ℚ) / angularDenN k := by
  simp [angularBaseQ, angularNumN, angularDenN]

private lemma oddDimensionRatioQ_eq_nat_div (k n : ℕ) :
    oddDimensionRatioQ k n =
      (oddNumN n : ℚ) / dimensionDenN k n := by
  simp [oddDimensionRatioQ, oddNumN, dimensionDenN,
    Finset.prod_div_distrib]

private lemma expStepQ_pow_eq_nat_div (n : ℕ) :
    expStepQ ^ n = (expNumN n : ℚ) / expDenN n := by
  simp [expStepQ, expNumN, expDenN, div_pow]

private lemma mixedRatioQ_eq_nat_div (kDim kAng n : ℕ) :
    oddDimensionRatioQ kDim n * angularBaseQ kAng ^ (2 * n - 1) =
      ((oddNumN n * angularNumN kAng ^ (2 * n - 1) : ℕ) : ℚ) /
        (dimensionDenN kDim n * angularDenN kAng ^ (2 * n - 1)) := by
  rw [oddDimensionRatioQ_eq_nat_div, angularBaseQ_eq_num_div, div_pow]
  push_cast
  ring

private lemma expStepQ_pow_le_mixed_of_nat {kDim kAng n : ℕ}
    (hkDim : 0 < kDim)
    (hcert : expNumN n *
        (dimensionDenN kDim n * angularDenN kAng ^ (2 * n - 1)) ≤
      expDenN n *
        (oddNumN n * angularNumN kAng ^ (2 * n - 1))) :
    expStepQ ^ n ≤
      oddDimensionRatioQ kDim n * angularBaseQ kAng ^ (2 * n - 1) := by
  rw [expStepQ_pow_eq_nat_div, mixedRatioQ_eq_nat_div]
  have hExpDenNat : 0 < expDenN n := by
    simp [expDenN]
  have hDimDenNat : 0 < dimensionDenN kDim n := by
    simp [dimensionDenN]
    intro i hi
    omega
  have hAngDenNat : 0 < angularDenN kAng := by
    simp [angularDenN]
  have hleft : (0 : ℚ) < expDenN n := by exact_mod_cast hExpDenNat
  have hright : (0 : ℚ) <
      dimensionDenN kDim n * angularDenN kAng ^ (2 * n - 1) := by
    exact_mod_cast Nat.mul_pos hDimDenNat (pow_pos hAngDenNat _)
  apply (div_le_div_iff₀ hleft hright).2
  have hcert' : expNumN n *
        (dimensionDenN kDim n * angularDenN kAng ^ (2 * n - 1)) ≤
      (oddNumN n * angularNumN kAng ^ (2 * n - 1)) * expDenN n := by
    simpa [mul_comm] using hcert
  exact_mod_cast hcert'

lemma angularBaseQ_pos {k : ℕ} (hk : 0 < k) : 0 < angularBaseQ k := by
  unfold angularBaseQ
  have hkQ : (0 : ℚ) < k := by exact_mod_cast hk
  have hcbQ : (0 : ℚ) < Nat.centralBinom k := by
    exact_mod_cast Nat.centralBinom_pos k
  exact div_pos (mul_pos (mul_pos (by norm_num) hkQ) (sq_pos_of_pos hcbQ))
    (pow_pos (by norm_num) _)

lemma oddDimensionRatioQ_pos {k n : ℕ} (hk : 0 < k) :
    0 < oddDimensionRatioQ k n := by
  unfold oddDimensionRatioQ
  apply Finset.prod_pos
  intro q hq
  apply div_pos
  · positivity
  · exact_mod_cast Nat.add_pos_left hk (2 * q)

lemma wickScalarRatioQ_pos {k n : ℕ} (hk : 0 < k) :
    0 < wickScalarRatioQ k n := by
  unfold wickScalarRatioQ
  exact mul_pos (oddDimensionRatioQ_pos hk) (pow_pos (angularBaseQ_pos hk) _)

lemma angularBaseQ_succ (k : ℕ) (hk : 0 < k) :
    angularBaseQ (k + 1) = angularBaseQ k *
      (((2 * k + 1 : ℕ) : ℚ) ^ 2 / (4 * k * (k + 1) : ℕ)) := by
  have hcb := congrArg (↑· : ℕ → ℚ) (Nat.succ_mul_centralBinom_succ k)
  push_cast at hcb
  have hkQ : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  have hksQ : ((k + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hcent : ((Nat.centralBinom (k + 1) : ℕ) : ℚ) =
      (2 * (2 * (k : ℚ) + 1) * Nat.centralBinom k) / ((k : ℚ) + 1) := by
    apply (eq_div_iff (by positivity : (k : ℚ) + 1 ≠ 0)).2
    simpa [mul_comm] using hcb
  rw [angularBaseQ, angularBaseQ, hcent]
  rw [pow_succ]
  field_simp [hkQ, hksQ]
  push_cast
  ring

lemma one_le_angularBaseQ_step (k : ℕ) (hk : 0 < k) :
    (1 : ℚ) ≤ (((2 * k + 1 : ℕ) : ℚ) ^ 2 /
      (4 * k * (k + 1) : ℕ)) := by
  have hden : (0 : ℚ) < (4 * k * (k + 1) : ℕ) := by positivity
  apply (le_div_iff₀ hden).2
  push_cast
  nlinarith

lemma angularBaseQ_mono : Monotone angularBaseQ := by
  apply monotone_nat_of_le_succ
  intro k
  rcases k with _ | k
  · norm_num [angularBaseQ, Nat.centralBinom, Nat.choose]
  · rw [angularBaseQ_succ (k + 1) (by omega)]
    exact le_mul_of_one_le_right (le_of_lt (angularBaseQ_pos (by omega)))
      (one_le_angularBaseQ_step (k + 1) (by omega))

lemma nine_eighths_le_angularBaseQ {k : ℕ} (hk : 2 ≤ k) :
    (9 / 8 : ℚ) ≤ angularBaseQ k := by
  calc
    (9 / 8 : ℚ) = angularBaseQ 2 := by
      norm_num [angularBaseQ, Nat.centralBinom, Nat.choose]
    _ ≤ angularBaseQ k := angularBaseQ_mono hk

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma angular_base_334_nat_certificate :
    159 * angularDenN 334 ≤ 125 * angularNumN 334 := by
  decide

set_option maxRecDepth 100000 in
lemma one_two_seven_two_le_angularBaseQ {k : ℕ} (hk : 334 ≤ k) :
    (159 / 125 : ℚ) ≤ angularBaseQ k := by
  calc
    (159 / 125 : ℚ) ≤ angularBaseQ 334 := by
      rw [angularBaseQ_eq_num_div]
      have hdenNat : 0 < angularDenN 334 := by
        simp [angularDenN]
      have hden : (0 : ℚ) < angularDenN 334 := by
        exact_mod_cast hdenNat
      apply (div_le_div_iff₀ (by norm_num : (0 : ℚ) < 125) hden).2
      exact_mod_cast angular_base_334_nat_certificate
    _ ≤ angularBaseQ k := angularBaseQ_mono hk

lemma oddDimensionRatioQ_succ (k n : ℕ) (hk : 0 < k) :
    oddDimensionRatioQ k (n + 1) = oddDimensionRatioQ k n *
      (((2 * n + 1 : ℕ) : ℚ) / (k + 2 * n : ℕ)) := by
  unfold oddDimensionRatioQ
  rw [prod_range_succ]

lemma wickScalarRatioQ_succ_n {k n : ℕ} (hk : 0 < k) (hn : 1 ≤ n) :
    wickScalarRatioQ k (n + 1) = wickScalarRatioQ k n *
      ((((2 * n + 1 : ℕ) : ℚ) / (k + 2 * n : ℕ)) *
        angularBaseQ k ^ 2) := by
  rw [wickScalarRatioQ, wickScalarRatioQ, oddDimensionRatioQ_succ k n hk]
  have hpow : 2 * (n + 1) - 1 = (2 * n - 1) + 2 := by omega
  rw [hpow, pow_add]
  ring

lemma six_sevenths_le_dimension_step {k n : ℕ} (hk : 0 < k)
    (hkn : 3 * k ≤ n) :
    (6 / 7 : ℚ) ≤ ((2 * n + 1 : ℕ) : ℚ) / (k + 2 * n : ℕ) := by
  have hden : (0 : ℚ) < (k + 2 * n : ℕ) := by positivity
  apply (le_div_iff₀ hden).2
  push_cast
  have hknQ : (3 : ℚ) * k ≤ n := by exact_mod_cast hkn
  nlinarith

lemma expStepQ_le_growth_step {k n : ℕ} (hk : 2 ≤ k)
    (hkn : 3 * k ≤ n) :
    expStepQ ≤ (((2 * n + 1 : ℕ) : ℚ) / (k + 2 * n : ℕ)) *
      angularBaseQ k ^ 2 := by
  have hd := six_sevenths_le_dimension_step (show 0 < k by omega) hkn
  have hb := nine_eighths_le_angularBaseQ hk
  have hbsq : (9 / 8 : ℚ) ^ 2 ≤ angularBaseQ k ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hb 2
  calc
    expStepQ ≤ (6 / 7 : ℚ) * (9 / 8 : ℚ) ^ 2 := by norm_num [expStepQ]
    _ ≤ (((2 * n + 1 : ℕ) : ℚ) / (k + 2 * n : ℕ)) *
        angularBaseQ k ^ 2 := mul_le_mul hd hbsq (by positivity) (by positivity)

lemma expStepQ_mul_wickScalarRatioQ_le_succ {k n : ℕ}
    (hk : 2 ≤ k) (hn : 1 ≤ n) (hkn : 3 * k ≤ n) :
    expStepQ * wickScalarRatioQ k n ≤ wickScalarRatioQ k (n + 1) := by
  rw [wickScalarRatioQ_succ_n (by omega) hn]
  rw [mul_comm (wickScalarRatioQ k n)]
  exact mul_le_mul_of_nonneg_right (expStepQ_le_growth_step hk hkn)
    (le_of_lt (wickScalarRatioQ_pos (by omega)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private lemma small_k_base_2_5_nat_certificate :
    expNumN 1000 *
        (dimensionDenN 5 1000 * angularDenN 2 ^ 1999) ≤
      expDenN 1000 * (oddNumN 1000 * angularNumN 2 ^ 1999) := by
  decide

/-- Exact worst-case certificate for the first elementary dimension range. -/
lemma small_k_base_certificate_2_5 :
    expStepQ ^ 1000 ≤
      oddDimensionRatioQ 5 1000 * angularBaseQ 2 ^ 1999 := by
  exact expStepQ_pow_le_mixed_of_nat (by omega) (by
    simpa using small_k_base_2_5_nat_certificate)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private lemma small_k_base_6_250_nat_certificate :
    expNumN 1000 *
        (dimensionDenN 250 1000 * angularDenN 6 ^ 1999) ≤
      expDenN 1000 * (oddNumN 1000 * angularNumN 6 ^ 1999) := by
  decide

lemma small_k_base_certificate_6_250 :
    expStepQ ^ 1000 ≤
      oddDimensionRatioQ 250 1000 * angularBaseQ 6 ^ 1999 := by
  exact expStepQ_pow_le_mixed_of_nat (by omega) (by
    simpa using small_k_base_6_250_nat_certificate)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private lemma small_k_base_251_333_nat_certificate :
    expNumN 1000 *
        (dimensionDenN 333 1000 * angularDenN 251 ^ 1999) ≤
      expDenN 1000 * (oddNumN 1000 * angularNumN 251 ^ 1999) := by
  decide

lemma small_k_base_certificate_251_333 :
    expStepQ ^ 1000 ≤
      oddDimensionRatioQ 333 1000 * angularBaseQ 251 ^ 1999 := by
  exact expStepQ_pow_le_mixed_of_nat (by omega) (by
    simpa using small_k_base_251_333_nat_certificate)

lemma oddDimensionRatioQ_antitone_k {n k l : ℕ}
    (hk : 0 < k) (hkl : k ≤ l) :
    oddDimensionRatioQ l n ≤ oddDimensionRatioQ k n := by
  unfold oddDimensionRatioQ
  apply Finset.prod_le_prod
  · intro i hi
    positivity
  · intro i hi
    have hkden : (0 : ℚ) < (k + 2 * i : ℕ) := by positivity
    have hl : 0 < l := lt_of_lt_of_le hk hkl
    have hlden : (0 : ℚ) < (l + 2 * i : ℕ) := by exact_mod_cast Nat.add_pos_left hl _
    apply div_le_div_of_nonneg_left (by positivity) hkden
    exact_mod_cast Nat.add_le_add_right hkl (2 * i)

lemma expStepQ_pow_1000_le_wickScalarRatioQ {k : ℕ}
    (hklo : 2 ≤ k) (hkhi : k ≤ 333) :
    expStepQ ^ 1000 ≤ wickScalarRatioQ k 1000 := by
  rw [wickScalarRatioQ]
  by_cases hk5 : k ≤ 5
  · calc
      expStepQ ^ 1000 ≤ oddDimensionRatioQ 5 1000 * angularBaseQ 2 ^ 1999 :=
        small_k_base_certificate_2_5
      _ ≤ oddDimensionRatioQ k 1000 * angularBaseQ k ^ 1999 := by
        exact mul_le_mul
          (oddDimensionRatioQ_antitone_k (by omega) hk5)
          (pow_le_pow_left₀ (angularBaseQ_pos (by omega)).le
            (angularBaseQ_mono hklo) 1999)
          (pow_nonneg (angularBaseQ_pos (k := 2) (by omega)).le _)
          (oddDimensionRatioQ_pos (k := k) (n := 1000) (by omega)).le
  · by_cases hk250 : k ≤ 250
    · calc
        expStepQ ^ 1000 ≤ oddDimensionRatioQ 250 1000 * angularBaseQ 6 ^ 1999 :=
          small_k_base_certificate_6_250
        _ ≤ oddDimensionRatioQ k 1000 * angularBaseQ k ^ 1999 := by
          exact mul_le_mul
            (oddDimensionRatioQ_antitone_k (by omega) hk250)
            (pow_le_pow_left₀ (angularBaseQ_pos (by omega)).le
              (angularBaseQ_mono (by omega)) 1999)
            (pow_nonneg (angularBaseQ_pos (k := 6) (by omega)).le _)
            (oddDimensionRatioQ_pos (k := k) (n := 1000) (by omega)).le
    · calc
        expStepQ ^ 1000 ≤ oddDimensionRatioQ 333 1000 * angularBaseQ 251 ^ 1999 :=
          small_k_base_certificate_251_333
        _ ≤ oddDimensionRatioQ k 1000 * angularBaseQ k ^ 1999 := by
          exact mul_le_mul
            (oddDimensionRatioQ_antitone_k (by omega) hkhi)
            (pow_le_pow_left₀ (angularBaseQ_pos (by omega)).le
              (angularBaseQ_mono (by omega)) 1999)
            (pow_nonneg (angularBaseQ_pos (k := 251) (by omega)).le _)
            (oddDimensionRatioQ_pos (k := k) (n := 1000) (by omega)).le

/-- The exact rational factor by which the boundary dimension ratio changes
from `(k,3k)` to `(k+2,3(k+2))`. -/
def boundaryDimensionStepQ (k : ℕ) : ℚ :=
  (k : ℚ) * (∏ i ∈ range 6, ((6 * k + 2 * i + 1 : ℕ) : ℚ)) /
    (∏ i ∈ range 7, ((7 * k + 2 * i : ℕ) : ℚ))

/-- Uniform exact-rational lower bound for the boundary dimension step. -/
lemma boundaryDimensionStepQ_lower {k : ℕ} (hk : 334 ≤ k) :
    (1416 / 25000 : ℚ) ≤ boundaryDimensionStepQ k := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hk
  unfold boundaryDimensionStepQ
  norm_num [prod_range_succ]
  field_simp
  ring_nf
  nlinarith [pow_nonneg (show (0 : ℚ) ≤ t by positivity) 2,
    pow_nonneg (show (0 : ℚ) ≤ t by positivity) 3,
    pow_nonneg (show (0 : ℚ) ≤ t by positivity) 4,
    pow_nonneg (show (0 : ℚ) ≤ t by positivity) 5,
    pow_nonneg (show (0 : ℚ) ≤ t by positivity) 6]

private def oddProductQ (n : ℕ) : ℚ :=
  ∏ q ∈ range n, ((2 * q + 1 : ℕ) : ℚ)

private def dimensionProductQ (k n : ℕ) : ℚ :=
  ∏ q ∈ range n, ((k + 2 * q : ℕ) : ℚ)

private lemma oddDimensionRatioQ_eq_quotient (k n : ℕ) :
    oddDimensionRatioQ k n = oddProductQ n / dimensionProductQ k n := by
  simp [oddDimensionRatioQ, oddProductQ, dimensionProductQ,
    Finset.prod_div_distrib]

private lemma dimensionProductQ_shift (k m : ℕ) :
    (k : ℚ) * dimensionProductQ (k + 2) m = dimensionProductQ k (m + 1) := by
  induction m with
  | zero => simp [dimensionProductQ]
  | succ m ih =>
      simp only [dimensionProductQ, prod_range_succ] at ih ⊢
      push_cast at ih ⊢
      rw [← ih]
      ring

private lemma oddProductQ_boundary_add_six (k : ℕ) :
    oddProductQ (3 * k + 6) = oddProductQ (3 * k) *
      (∏ i ∈ range 6, ((6 * k + 2 * i + 1 : ℕ) : ℚ)) := by
  rw [oddProductQ, oddProductQ, prod_range_add]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  push_cast
  ring

private lemma dimensionProductQ_boundary_add_seven (k : ℕ) :
    dimensionProductQ k (3 * k + 7) = dimensionProductQ k (3 * k) *
      (∏ i ∈ range 7, ((7 * k + 2 * i : ℕ) : ℚ)) := by
  rw [dimensionProductQ, dimensionProductQ, prod_range_add]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  push_cast
  ring

lemma oddDimensionRatioQ_boundary_add_two (k : ℕ) (hk : 0 < k) :
    oddDimensionRatioQ (k + 2) (3 * (k + 2)) =
      oddDimensionRatioQ k (3 * k) * boundaryDimensionStepQ k := by
  rw [show 3 * (k + 2) = 3 * k + 6 by omega,
    oddDimensionRatioQ_eq_quotient, oddDimensionRatioQ_eq_quotient,
    oddProductQ_boundary_add_six]
  have hdim := dimensionProductQ_shift k (3 * k + 6)
  rw [dimensionProductQ_boundary_add_seven] at hdim
  unfold boundaryDimensionStepQ
  have hkQ : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  have hdo : oddProductQ (3 * k) ≠ 0 := by
    unfold oddProductQ
    positivity
  have hdk : dimensionProductQ k (3 * k) ≠ 0 := by
    unfold dimensionProductQ
    apply Finset.prod_ne_zero_iff.mpr
    intro q hq
    positivity
  have hdnew : dimensionProductQ (k + 2) (3 * k + 6) ≠ 0 := by
    unfold dimensionProductQ
    apply Finset.prod_ne_zero_iff.mpr
    intro q hq
    positivity
  have heven : (∏ i ∈ range 7, ((7 * k + 2 * i : ℕ) : ℚ)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro q hq
    positivity
  field_simp [hkQ, hdk, hdnew, heven]
  nlinarith

lemma angularBaseQ_le_add_two (k : ℕ) :
    angularBaseQ k ≤ angularBaseQ (k + 2) := angularBaseQ_mono (by omega)

lemma boundary_two_step_growth {k : ℕ} (hk : 334 ≤ k) :
    expStepQ ^ 6 * wickScalarRatioQ k (3 * k) ≤
      wickScalarRatioQ (k + 2) (3 * (k + 2)) := by
  have hkpos : 0 < k := by omega
  rw [wickScalarRatioQ, wickScalarRatioQ,
    oddDimensionRatioQ_boundary_add_two k hkpos]
  have hpow : 2 * (3 * (k + 2)) - 1 = (2 * (3 * k) - 1) + 12 := by omega
  rw [hpow, pow_add]
  have hb : (159 / 125 : ℚ) ≤ angularBaseQ (k + 2) :=
    one_two_seven_two_le_angularBaseQ (by omega)
  have hstep := boundaryDimensionStepQ_lower hk
  have hnum : expStepQ ^ 6 ≤
      (1416 / 25000 : ℚ) * (159 / 125 : ℚ) ^ 12 := by
    norm_num [expStepQ]
  have hpowMono : angularBaseQ k ^ (2 * (3 * k) - 1) ≤
      angularBaseQ (k + 2) ^ (2 * (3 * k) - 1) :=
    pow_le_pow_left₀ (angularBaseQ_pos hkpos).le (angularBaseQ_le_add_two k) _
  have hoddpos := oddDimensionRatioQ_pos (n := 3*k) hkpos
  have hangpos := angularBaseQ_pos (k := k+2) (by omega)
  calc
    expStepQ ^ 6 *
        (oddDimensionRatioQ k (3 * k) * angularBaseQ k ^ (2 * (3 * k) - 1)) ≤
      ((1416 / 25000 : ℚ) * (159 / 125 : ℚ) ^ 12) *
        (oddDimensionRatioQ k (3 * k) *
          angularBaseQ (k + 2) ^ (2 * (3 * k) - 1)) := by
      exact mul_le_mul hnum
        (mul_le_mul_of_nonneg_left hpowMono hoddpos.le)
        (mul_nonneg hoddpos.le (pow_nonneg (angularBaseQ_pos hkpos).le _))
        (mul_nonneg (by norm_num) (pow_nonneg (by norm_num) 12))
    _ ≤ (oddDimensionRatioQ k (3 * k) * boundaryDimensionStepQ k) *
        (angularBaseQ (k + 2) ^ (2 * (3 * k) - 1) *
          angularBaseQ (k + 2) ^ 12) := by
      have hp12 := pow_le_pow_left₀ (by norm_num : (0 : ℚ) ≤ 159 / 125) hb 12
      have hA := pow_nonneg hangpos.le (2 * (3 * k) - 1)
      have hcoeff : (1416 / 25000 : ℚ) * (159 / 125 : ℚ) ^ 12 ≤
          boundaryDimensionStepQ k * angularBaseQ (k + 2) ^ 12 :=
        mul_le_mul hstep hp12 (by positivity) (by positivity)
      calc
        ((1416 / 25000 : ℚ) * (159 / 125 : ℚ) ^ 12) *
            (oddDimensionRatioQ k (3 * k) *
              angularBaseQ (k + 2) ^ (2 * (3 * k) - 1)) ≤
          (boundaryDimensionStepQ k * angularBaseQ (k + 2) ^ 12) *
            (oddDimensionRatioQ k (3 * k) *
              angularBaseQ (k + 2) ^ (2 * (3 * k) - 1)) :=
          mul_le_mul_of_nonneg_right hcoeff (mul_nonneg hoddpos.le hA)
        _ = (oddDimensionRatioQ k (3 * k) * boundaryDimensionStepQ k) *
            (angularBaseQ (k + 2) ^ (2 * (3 * k) - 1) *
              angularBaseQ (k + 2) ^ 12) := by ring

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private lemma boundary_base_334_nat_certificate :
    expNumN (3 * 334) * scalarDenN 334 (3 * 334) ≤
      expDenN (3 * 334) * scalarNumN 334 (3 * 334) := by
  decide

lemma boundary_base_334 :
    expStepQ ^ (3 * 334) ≤ wickScalarRatioQ 334 (3 * 334) := by
  rw [wickScalarRatioQ]
  exact expStepQ_pow_le_mixed_of_nat (by omega) (by
    simpa [scalarDenN, scalarNumN] using boundary_base_334_nat_certificate)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private lemma boundary_base_335_nat_certificate :
    expNumN (3 * 335) * scalarDenN 335 (3 * 335) ≤
      expDenN (3 * 335) * scalarNumN 335 (3 * 335) := by
  decide

lemma boundary_base_335 :
    expStepQ ^ (3 * 335) ≤ wickScalarRatioQ 335 (3 * 335) := by
  rw [wickScalarRatioQ]
  exact expStepQ_pow_le_mixed_of_nat (by omega) (by
    simpa [scalarDenN, scalarNumN] using boundary_base_335_nat_certificate)

lemma boundary_certificate {k : ℕ} (hk : 334 ≤ k) :
    expStepQ ^ (3 * k) ≤ wickScalarRatioQ k (3 * k) := by
  obtain ⟨j, hEven | hOdd⟩ := Nat.even_or_odd' k
  · subst k
    have hjlo : 167 ≤ j := by omega
    induction j, hjlo using Nat.le_induction with
    | base => simpa using boundary_base_334
    | succ j hjlo ih =>
        have hs := boundary_two_step_growth (k := 2 * j) (by omega)
        calc
          expStepQ ^ (3 * (2 * (j + 1))) =
              expStepQ ^ 6 * expStepQ ^ (3 * (2 * j)) := by
                rw [← pow_add]
                congr 1
                omega
          _ ≤ expStepQ ^ 6 * wickScalarRatioQ (2 * j) (3 * (2 * j)) :=
              mul_le_mul_of_nonneg_left (ih (by omega)) (by positivity)
          _ ≤ wickScalarRatioQ (2 * (j + 1)) (3 * (2 * (j + 1))) := by
              simpa only [Nat.mul_add, Nat.mul_one, Nat.add_comm,
                Nat.add_left_comm, Nat.add_assoc] using hs
  · subst k
    have hjlo : 167 ≤ j := by omega
    induction j, hjlo using Nat.le_induction with
    | base => simpa using boundary_base_335
    | succ j hjlo ih =>
        have hs := boundary_two_step_growth (k := 2 * j + 1) (by omega)
        calc
          expStepQ ^ (3 * (2 * (j + 1) + 1)) =
              expStepQ ^ 6 * expStepQ ^ (3 * (2 * j + 1)) := by
                rw [← pow_add]
                congr 1
                omega
          _ ≤ expStepQ ^ 6 * wickScalarRatioQ (2 * j + 1) (3 * (2 * j + 1)) :=
              mul_le_mul_of_nonneg_left (ih (by omega)) (by positivity)
          _ ≤ wickScalarRatioQ (2 * (j + 1) + 1) (3 * (2 * (j + 1) + 1)) := by
              simpa only [Nat.mul_add, Nat.mul_one, Nat.add_comm,
                Nat.add_left_comm, Nat.add_assoc] using hs

lemma expStepQ_pow_le_wickScalarRatioQ {k n : ℕ}
    (hn : 1000 ≤ n) (hklo : 2 ≤ k) (hkhi : 3 * k ≤ n) :
    expStepQ ^ n ≤ wickScalarRatioQ k n := by
  by_cases hk : k ≤ 333
  · have hbase := expStepQ_pow_1000_le_wickScalarRatioQ hklo hk
    induction n, hn using Nat.le_induction with
    | base => exact hbase
    | succ n hn ih =>
        have h3k : 3 * k ≤ n := by omega
        have hs := expStepQ_mul_wickScalarRatioQ_le_succ hklo (by omega) h3k
        calc
          expStepQ ^ (n + 1) = expStepQ * expStepQ ^ n := by rw [pow_succ]; ring
          _ ≤ expStepQ * wickScalarRatioQ k n :=
            mul_le_mul_of_nonneg_left (ih h3k) (by norm_num [expStepQ])
          _ ≤ wickScalarRatioQ k (n + 1) := hs
  · have hk334 : 334 ≤ k := by omega
    have hbase := boundary_certificate hk334
    induction n, hkhi using Nat.le_induction with
    | base => exact hbase
    | succ n hkn ih =>
        have hs := expStepQ_mul_wickScalarRatioQ_le_succ hklo (by omega) hkn
        calc
          expStepQ ^ (n + 1) = expStepQ * expStepQ ^ n := by rw [pow_succ]; ring
          _ ≤ expStepQ * wickScalarRatioQ k n :=
            mul_le_mul_of_nonneg_left (ih (by omega)) (by norm_num [expStepQ])
          _ ≤ wickScalarRatioQ k (n + 1) := hs

lemma exp_one_div_500_le_expStepQ :
    Real.exp (1 / 500 : ℝ) ≤ (expStepQ : ℝ) := by
  have h := Real.exp_bound_div_one_sub_of_interval
    (show (0 : ℝ) ≤ 1 / 500 by norm_num)
    (show (1 / 500 : ℝ) < 1 by norm_num)
  norm_num [expStepQ] at h ⊢
  exact h

/-- Fully kernel-checked finite scalar consequence. -/
theorem exp_n_div_500_le_wickScalarRatioQ
    {k n : ℕ} (hn : 1000 ≤ n) (hklo : 2 ≤ k) (hkhi : 3 * k ≤ n) :
    Real.exp ((n : ℝ) / 500) ≤ (wickScalarRatioQ k n : ℝ) := by
  have hpow := expStepQ_pow_le_wickScalarRatioQ hn hklo hkhi
  have hstepPow : Real.exp (1 / 500 : ℝ) ^ n ≤ ((expStepQ : ℝ) ^ n) :=
    pow_le_pow_left₀ (Real.exp_pos _).le exp_one_div_500_le_expStepQ n
  have hcast : ((expStepQ : ℝ) ^ n) ≤ (wickScalarRatioQ k n : ℝ) := by
    exact_mod_cast hpow
  calc
    Real.exp ((n : ℝ) / 500) = Real.exp (1 / 500 : ℝ) ^ n := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ ((expStepQ : ℝ) ^ n) := hstepPow
    _ ≤ (wickScalarRatioQ k n : ℝ) := hcast

end LogdetLean.GramHafnian.WickAngularLowerBound
