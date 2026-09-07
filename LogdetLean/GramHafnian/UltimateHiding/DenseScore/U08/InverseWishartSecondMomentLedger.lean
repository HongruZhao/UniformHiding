import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ClassicalMomentBoundsExternal
import Mathlib.Tactic

/-!
# Axiom-free algebra for the order-two inverse-Wishart entry ledger

This file contains only the finite contractions and rational inequalities that
follow after the classical inverse-Wishart second-entry formula has been
supplied.  It does **not** assert that formula as a new axiom.

For denominator dimension `p`, degrees of freedom `nu`, and
`c = nu - p - 1`, put `C = c B⁻¹`.  The classical entry formula is

`E[Cᵢⱼ Cₖₗ] = a δᵢⱼδₖₗ + b(δᵢₖδⱼₗ + δᵢₗδⱼₖ)`,

where `a = c(c-1)/((c+1)(c-2))` and
`b = c/((c+1)(c-2))`.  Contracting it and then performing the finite
Gaussian Wishart contraction gives the two ledgers below.
-/

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

/-- The denominator in the inverse-Wishart second-entry formula. -/
def inverseWishartSecondMomentDenominator (c : ℝ) : ℝ :=
  (c + 1) * (c - 2)

/-- `E tr(C²)` after contracting the inverse-Wishart second-entry formula. -/
def scaledInverseWishartTraceTwoMeanLedger (p c : ℝ) : ℝ :=
  p * c * (c + p) / inverseWishartSecondMomentDenominator c

/-- `E (tr C)²` after contracting the same entry formula. -/
def scaledInverseWishartTraceOneSquareMeanLedger (p c : ℝ) : ℝ :=
  (p ^ 2 * c * (c - 1) + 2 * p * c) /
    inverseWishartSecondMomentDenominator c

/-- Exact formal value of `E tr(Y²)` for `Y = C A`, where
`A = GᵀG` has `p+1` independent standard-Gaussian rows. -/
def betaPrimeYTraceTwoMeanLedger (p c : ℝ) : ℝ :=
  p * (p + 1) * c *
      (2 * (p + 1) * c + p ^ 2 + p + 2) /
    inverseWishartSecondMomentDenominator c

/-- Exact formal value of
`E[tr(Y²) - (tr Y)²/p]` in the same model. -/
def betaPrimeTracelessQuadraticMeanLedger (p c : ℝ) : ℝ :=
  (p + 1) * c * (p + 2) * (p - 1) * (c + p + 1) /
    inverseWishartSecondMomentDenominator c

/-- The finite numerator-Wishart contraction reduces to the displayed raw
trace-two ledger.  This theorem is pure field algebra. -/
theorem betaPrimeYTraceTwoMeanLedger_contraction (p c : ℝ) :
    (p + 1) * (p + 2) * scaledInverseWishartTraceTwoMeanLedger p c +
        (p + 1) * scaledInverseWishartTraceOneSquareMeanLedger p c =
      betaPrimeYTraceTwoMeanLedger p c := by
  unfold scaledInverseWishartTraceTwoMeanLedger
    scaledInverseWishartTraceOneSquareMeanLedger
    betaPrimeYTraceTwoMeanLedger
  ring

/-- Subtracting `p⁻¹ E(tr Y)²` from the raw trace-two contraction gives the
traceless quadratic ledger. -/
theorem betaPrimeTracelessQuadraticMeanLedger_contraction
    (p c : ℝ) (hp : p ≠ 0) :
    (p + 1) * (p + 2) * scaledInverseWishartTraceTwoMeanLedger p c +
        (p + 1) * scaledInverseWishartTraceOneSquareMeanLedger p c -
        p⁻¹ *
          ((p + 1) ^ 2 * scaledInverseWishartTraceOneSquareMeanLedger p c +
            2 * (p + 1) * scaledInverseWishartTraceTwoMeanLedger p c) =
      betaPrimeTracelessQuadraticMeanLedger p c := by
  unfold scaledInverseWishartTraceTwoMeanLedger
    scaledInverseWishartTraceOneSquareMeanLedger
    betaPrimeTracelessQuadraticMeanLedger
  field_simp [hp]
  ring

/-- The raw trace-two ledger is strictly larger than `p(p+1)²` throughout
its moment range.  In particular it is genuinely order `p³`. -/
theorem betaPrimeYTraceTwoMeanLedger_gt_cube
    {p c : ℝ} (hp : 0 < p) (hc : 2 < c) :
    p * (p + 1) ^ 2 < betaPrimeYTraceTwoMeanLedger p c := by
  have hd : 0 < inverseWishartSecondMomentDenominator c := by
    unfold inverseWishartSecondMomentDenominator
    exact mul_pos (by linarith) (by linarith)
  apply (lt_div_iff₀ hd).2
  have hidentity :
      p * (p + 1) * c *
          (2 * (p + 1) * c + p ^ 2 + p + 2) -
          p * (p + 1) ^ 2 * inverseWishartSecondMomentDenominator c =
        p * (p + 1) *
          ((p + 1) * c ^ 2 + c * (p ^ 2 + 2 * p + 3) +
            2 * (p + 1)) := by
    unfold inverseWishartSecondMomentDenominator
    ring
  have hpositive :
      0 < p * (p + 1) *
          ((p + 1) * c ^ 2 + c * (p ^ 2 + 2 * p + 3) +
            2 * (p + 1)) := by
    positivity
  apply sub_pos.mp
  rw [hidentity]
  exact hpositive

/-- Under the dense relation `c ≥ 13p`, the traceless formal mean has the
requested `O(p³)` size, with a small numerical coefficient. -/
theorem abs_betaPrimeTracelessQuadraticMeanLedger_le_twentyFour_cube
    {p c : ℝ} (hp : 1 ≤ p) (hc : 13 * p ≤ c) :
    |betaPrimeTracelessQuadraticMeanLedger p c| ≤ 24 * p ^ 3 := by
  have hp0 : 0 ≤ p := le_trans (by norm_num) hp
  have hpminus : 0 ≤ p - 1 := by linarith
  have hc13 : 13 ≤ c := by nlinarith
  have hc0 : 0 ≤ c := by linarith
  have hcp0 : 0 ≤ c + p + 1 := by positivity
  have hd : 0 < inverseWishartSecondMomentDenominator c := by
    unfold inverseWishartSecondMomentDenominator
    exact mul_pos (by linarith) (by linarith)
  have hbaseNonneg : 0 ≤ (p + 1) * (p + 2) * (p - 1) := by
    positivity
  have hpSqStep : p ^ 2 ≤ p ^ 3 := by
    nlinarith [mul_nonneg hpminus (sq_nonneg p)]
  have hpStep : p ≤ p ^ 2 := by
    nlinarith [mul_nonneg hpminus hp0]
  have hbase : (p + 1) * (p + 2) * (p - 1) ≤ 6 * p ^ 3 := by
    nlinarith
  have hcp : p + 1 ≤ c := by nlinarith
  have hratioOne : c * (c + p + 1) ≤ 2 * c ^ 2 := by
    nlinarith
  have hratioTwo : 2 * c ^ 2 ≤
      4 * inverseWishartSecondMomentDenominator c := by
    unfold inverseWishartSecondMomentDenominator
    nlinarith [sq_nonneg (c - 3)]
  have hratio : c * (c + p + 1) ≤
      4 * inverseWishartSecondMomentDenominator c :=
    hratioOne.trans hratioTwo
  have hnumNonneg :
      0 ≤ (p + 1) * c * (p + 2) * (p - 1) * (c + p + 1) := by
    positivity
  have hnum :
      (p + 1) * c * (p + 2) * (p - 1) * (c + p + 1) ≤
        24 * p ^ 3 * inverseWishartSecondMomentDenominator c := by
    calc
      (p + 1) * c * (p + 2) * (p - 1) * (c + p + 1) =
          ((p + 1) * (p + 2) * (p - 1)) *
            (c * (c + p + 1)) := by ring
      _ ≤ (6 * p ^ 3) * (c * (c + p + 1)) := by
        exact mul_le_mul_of_nonneg_right hbase (mul_nonneg hc0 hcp0)
      _ ≤ (6 * p ^ 3) *
          (4 * inverseWishartSecondMomentDenominator c) := by
        exact mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = 24 * p ^ 3 * inverseWishartSecondMomentDenominator c := by ring
  unfold betaPrimeTracelessQuadraticMeanLedger
  rw [abs_of_nonneg (div_nonneg hnumNonneg (le_of_lt hd))]
  exact (div_le_iff₀ hd).2 hnum

/-- The U10 traceless-formal-mean constant follows immediately from the same
ledger; `denseClassicalMomentConstant = 2^40` is far larger than `24`. -/
theorem abs_betaPrimeTracelessQuadraticMeanLedger_le_denseConstant
    {p c : ℝ} (hp : 1 ≤ p) (hc : 13 * p ≤ c) :
    |betaPrimeTracelessQuadraticMeanLedger p c| ≤
      denseClassicalMomentConstant * p ^ 3 := by
  calc
    |betaPrimeTracelessQuadraticMeanLedger p c| ≤ 24 * p ^ 3 :=
      abs_betaPrimeTracelessQuadraticMeanLedger_le_twentyFour_cube hp hc
    _ ≤ denseClassicalMomentConstant * p ^ 3 := by
      have hp3 : 0 ≤ p ^ 3 := by positivity
      gcongr
      norm_num [denseClassicalMomentConstant]

/-- A concrete dimension in which the requested U10 raw trace-two `O(N²)`
bound is contradicted by the exact second-moment ledger. -/
def u10TraceTwoCounterexampleDimension : ℕ := 1099511627776

/-- The matching dense parameter `K = 16N`. -/
def u10TraceTwoCounterexampleK : ℕ :=
  16 * u10TraceTwoCounterexampleDimension

theorem u10TraceTwoCounterexample_dense :
    16 * u10TraceTwoCounterexampleDimension ≤ u10TraceTwoCounterexampleK := by
  rfl

/-- Kernel-checked arithmetic counterexample for the exact ledger.  The
analytic identification of the actual beta-prime integral with this ledger
is deliberately kept as a separate scientific theorem obligation. -/
theorem u10TraceTwoMeanLedger_counterexample :
    denseClassicalMomentConstant *
        (u10TraceTwoCounterexampleDimension : ℝ) ^ 2 <
      betaPrimeYTraceTwoMeanLedger
        (u10TraceTwoCounterexampleDimension : ℝ)
        ((u10TraceTwoCounterexampleK : ℝ) -
          2 * (u10TraceTwoCounterexampleDimension : ℝ) - 1) := by
  let p : ℝ := (u10TraceTwoCounterexampleDimension : ℝ)
  have hp : 0 < p := by
    norm_num [p, u10TraceTwoCounterexampleDimension]
  have hc : 2 < (u10TraceTwoCounterexampleK : ℝ) - 2 * p - 1 := by
    norm_num [p, u10TraceTwoCounterexampleK,
      u10TraceTwoCounterexampleDimension]
  have hledger := betaPrimeYTraceTwoMeanLedger_gt_cube hp hc
  have hconstant :
      denseClassicalMomentConstant * p ^ 2 < p * (p + 1) ^ 2 := by
    norm_num [p, u10TraceTwoCounterexampleDimension,
      denseClassicalMomentConstant]
  exact hconstant.trans hledger

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
