import LogdetLean.GramHafnian.ThreePaper.RelativeAccuracyApplicationEndpoints
import LogdetLean.GramHafnian.LocalAnticoncentration.CoefficientPaperEndpoints

/-!
# Exact algebra for the two-reference manuscript comparison

This module compares the two Gaussian reference normalizations discussed in
the Letter:

* Method 1 uses the normalized transpose-Gram reference
  `K^{-1/2} G Gᵀ` and the finite coefficient `B_{K,n}`;
* Method 2 uses an independent complex-symmetric Gaussian reference and the
  limiting coefficient `b_n`.

The module is deliberately distribution-free on the Method 2 side.  Its
`deltaSym` argument is a supplied nonnegative error budget; no symmetric
Gaussian hiding theorem is assumed or postulated here.  Thus every result
below is exact ordered-field or finite-product algebra, and the existing
Method 1 scientific axiom boundary is not enlarged.
-/

open Filter
open scoped BigOperators

namespace LogdetLean.GramHafnian.ThreePaper.TwoMethodComparison

noncomputable section

open LocalAnticoncentration UniformMatrixHiding UltimateHiding

/-- The exact variance ratio between the normalized finite-`K` Gram hafnian
and its independent-symmetric limiting variance.  The empty product at
`n = 1` is one. -/
def gramToSymmetricVarianceRatio (K n : ℕ) : ℝ :=
  ∏ r ∈ Finset.Icc 2 n,
    (((K : ℝ) + 2 * (r : ℝ) - 2) / (K : ℝ))

/-- The exact independent-symmetric hafnian variance `(2n-1)!!`. -/
def symmetricHafnianVariance (n : ℕ) : ℝ :=
  (oddPairingNat n : ℝ)

/-- The companion theorem range `K ≥ 4n` is exactly the Letter's physical
range `K ≥ 2N` after substituting `N = 2n`. -/
theorem four_mul_pairCount_iff_two_mul_ambient (K n : ℕ) :
    4 * n ≤ K ↔ 2 * (2 * n) ≤ K := by
  omega

/-- The Method 2 physical reference probability.  It uses the same optical
prefactor as Method 1, the scaling `(sqrt K / M)^(2n) = K^n/M^(2n)`, and
the independent-symmetric variance `(2n-1)!!`. -/
def symmetricGaussianReferenceProbability
    (r : ℝ) (M K n : ℕ) : ℝ :=
  equalSqueezingOpticalPrefactor r (2 * n) K *
    ((K : ℝ) ^ n / (M : ℝ) ^ (2 * n)) *
      symmetricHafnianVariance n

/-- The extra finite-`K` factor in `B_{K,n}/(b_n R_{K,n})`. -/
def coefficientComparisonPenalty (K n : ℕ) : ℝ :=
  ((K : ℝ) / ((K : ℝ) - 1)) *
    ∏ r ∈ Finset.Icc 2 n,
      ((K : ℝ) / ((K : ℝ) - 4 * (r : ℝ) + 1))

/-- The exact row-dimension product is `K^n R_{K,n}`. -/
theorem dimensionProduct_eq_pow_mul_varianceRatio
    (K n : ℕ) (hK : 0 < K) (hn : 1 ≤ n) :
    dimensionProduct K n =
      (K : ℝ) ^ n * gramToSymmetricVarianceRatio K n := by
  induction n, hn using Nat.le_induction with
  | base =>
      simp [dimensionProduct, gramToSymmetricVarianceRatio]
  | succ n hn ih =>
      have hdim :
          dimensionProduct K (n + 1) =
            dimensionProduct K n * ((K + 2 * n : ℕ) : ℝ) := by
        simp [dimensionProduct, Finset.prod_range_succ]
      have hratio :
          gramToSymmetricVarianceRatio K (n + 1) =
            gramToSymmetricVarianceRatio K n *
              (((K : ℝ) + 2 * (n : ℝ)) / (K : ℝ)) := by
        unfold gramToSymmetricVarianceRatio
        rw [Finset.prod_Icc_succ_top (by omega)]
        congr 1
        push_cast
        ring
      rw [hdim, ih, hratio, pow_succ]
      have hKR : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
      field_simp [hKR]
      <;> push_cast
      <;> ring

/-- The finite Gram hafnian variance divided by the normalized symmetric
variance is exactly the product `R_{K,n}` displayed in the Letter. -/
theorem gramVariance_div_pow_symmetricVariance_eq_ratio
    (K n : ℕ) (hK : 0 < K) (hn : 1 ≤ n) :
    gramHafnianSigma K n ^ 2 /
        ((K : ℝ) ^ n * symmetricHafnianVariance n) =
      gramToSymmetricVarianceRatio K n := by
  rw [gramHafnianSigma_sq K n hK, closedFirstMoment,
    dimensionProduct_eq_pow_mul_varianceRatio K n hK hn]
  unfold symmetricHafnianVariance
  have hpow : (K : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by exact_mod_cast hK.ne')
  have hodd : (oddPairingNat n : ℝ) ≠ 0 := by
    exact_mod_cast (oddPairingNat_pos n).ne'
  field_simp [hpow, hodd]

/-- The finite Gram reference probability is exactly `R_{K,n}` times the
independent-symmetric reference probability. -/
theorem gramReferenceProbability_eq_ratio_mul_symmetricReference
    (r : ℝ) (M K n : ℕ) (hK : 0 < K) (hn : 1 ≤ n) :
    gbsGaussianReferenceProbability r M K n =
      gramToSymmetricVarianceRatio K n *
        symmetricGaussianReferenceProbability r M K n := by
  rw [gbsGaussianReferenceProbability, gramHafnianSigma_sq K n hK,
    closedFirstMoment,
    dimensionProduct_eq_pow_mul_varianceRatio K n hK hn]
  unfold scaledGBSOpticalFactor symmetricGaussianReferenceProbability
    symmetricHafnianVariance
  ring

/-- The exact coefficient factorization
`B_{K,n} = b_n R_{K,n} P_{K,n}`. -/
theorem finiteCoefficient_eq_limit_mul_ratio_mul_penalty
    (K n : ℕ) (hn : 1 ≤ n) (hK : 4 * n ≤ K) :
    paperBkn K n =
      paperBn n * gramToSymmetricVarianceRatio K n *
        coefficientComparisonPenalty K n := by
  have hKnat : 0 < K := by omega
  have hKR : (K : ℝ) ≠ 0 := by exact_mod_cast hKnat.ne'
  rw [paperBkn_eq_product K n hn]
  unfold gramToSymmetricVarianceRatio coefficientComparisonPenalty
  have hfactor : ∀ r ∈ Finset.Icc 2 n,
      ((K : ℝ) + 2 * (r : ℝ) - 2) /
          ((K : ℝ) - 4 * (r : ℝ) + 1) =
        (((K : ℝ) + 2 * (r : ℝ) - 2) / (K : ℝ)) *
          ((K : ℝ) / ((K : ℝ) - 4 * (r : ℝ) + 1)) := by
    intro r hr
    have hrn : r ≤ n := (Finset.mem_Icc.mp hr).2
    have hden : 0 < (K : ℝ) - 4 * (r : ℝ) + 1 := by
      have hfour : (4 : ℝ) * (r : ℝ) ≤ (K : ℝ) := by
        exact_mod_cast (show 4 * r ≤ K by omega)
      linarith
    field_simp [hKR, hden.ne']
  rw [show
      (∏ r ∈ Finset.Icc 2 n,
          ((K : ℝ) + 2 * (r : ℝ) - 2) /
            ((K : ℝ) - 4 * (r : ℝ) + 1)) =
        (∏ r ∈ Finset.Icc 2 n,
          (((K : ℝ) + 2 * (r : ℝ) - 2) / (K : ℝ))) *
        (∏ r ∈ Finset.Icc 2 n,
          ((K : ℝ) / ((K : ℝ) - 4 * (r : ℝ) + 1))) by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl hfactor]
  ring

/-- Every factor in the comparison penalty is at least one, and its leading
factor is strictly larger than one. -/
theorem one_lt_coefficientComparisonPenalty
    (K n : ℕ) (hn : 1 ≤ n) (hK : 4 * n ≤ K) :
    1 < coefficientComparisonPenalty K n := by
  have hKnat : 1 < K := by omega
  have hKR : (1 : ℝ) < (K : ℝ) := by exact_mod_cast hKnat
  have hKm1 : 0 < (K : ℝ) - 1 := by linarith
  have hhead :
      1 < (K : ℝ) / ((K : ℝ) - 1) := by
    exact (lt_div_iff₀ hKm1).2 (by linarith)
  have htail :
      1 ≤ ∏ r ∈ Finset.Icc 2 n,
        ((K : ℝ) / ((K : ℝ) - 4 * (r : ℝ) + 1)) := by
    apply Finset.one_le_prod
    intro r hr
    have hrn : r ≤ n := (Finset.mem_Icc.mp hr).2
    have hden : 0 < (K : ℝ) - 4 * (r : ℝ) + 1 := by
      have hfour : (4 : ℝ) * (r : ℝ) ≤ (K : ℝ) := by
        exact_mod_cast (show 4 * r ≤ K by omega)
      linarith
    apply (le_div_iff₀ hden).2
    have hr2 : (2 : ℝ) ≤ (r : ℝ) := by
      exact_mod_cast (Finset.mem_Icc.mp hr).1
    linarith
  unfold coefficientComparisonPenalty
  have hmono :
      (K : ℝ) / ((K : ℝ) - 1) ≤
        ((K : ℝ) / ((K : ℝ) - 1)) *
          ∏ r ∈ Finset.Icc 2 n,
            ((K : ℝ) / ((K : ℝ) - 4 * (r : ℝ) + 1)) := by
    nlinarith [mul_nonneg (zero_le_one.trans hhead.le)
      (sub_nonneg.mpr htail)]
  exact hhead.trans_le hmono

/-- `b_n` is positive on the physical range `n >= 1`. -/
theorem paperBn_pos (n : ℕ) (hn : 1 ≤ n) : 0 < paperBn n := by
  change 0 < limitingAnticoncentrationConstant n
  rw [limitingAnticoncentrationConstant_eq_centralBinomial n hn]
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hchoose : 0 < ((Nat.choose (2 * n) n : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega : n ≤ 2 * n)
  exact div_pos (mul_pos (mul_pos (by norm_num) hnR) hchoose)
    (pow_pos (by norm_num) n)

/-- `R_{K,n}` is positive when `K > 0`. -/
theorem gramToSymmetricVarianceRatio_pos
    (K n : ℕ) (hK : 0 < K) :
    0 < gramToSymmetricVarianceRatio K n := by
  unfold gramToSymmetricVarianceRatio
  apply Finset.prod_pos
  intro r hr
  have hKR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hr2 : (2 : ℝ) ≤ (r : ℝ) := by
    exact_mod_cast (Finset.mem_Icc.mp hr).1
  exact div_pos (by linarith) hKR

/-- Exact quotient form of the coefficient comparison. -/
theorem finiteCoefficient_div_limit_mul_ratio
    (K n : ℕ) (hn : 1 ≤ n) (hK : 4 * n ≤ K) :
    paperBkn K n /
        (paperBn n * gramToSymmetricVarianceRatio K n) =
      coefficientComparisonPenalty K n := by
  have hKnat : 0 < K := by omega
  have hpos : 0 < paperBn n * gramToSymmetricVarianceRatio K n :=
    mul_pos (paperBn_pos n hn)
      (gramToSymmetricVarianceRatio_pos K n hKnat)
  rw [finiteCoefficient_eq_limit_mul_ratio_mul_penalty K n hn hK]
  exact mul_div_cancel_left₀ _ hpos.ne'

/-- At a common physical additive scale, Method 2 has the strictly smaller
small-denominator coefficient. -/
theorem limit_mul_ratio_lt_finiteCoefficient
    (K n : ℕ) (hn : 1 ≤ n) (hK : 4 * n ≤ K) :
    paperBn n * gramToSymmetricVarianceRatio K n < paperBkn K n := by
  have hKnat : 0 < K := by omega
  have hbase : 0 < paperBn n * gramToSymmetricVarianceRatio K n :=
    mul_pos (paperBn_pos n hn)
      (gramToSymmetricVarianceRatio_pos K n hKnat)
  rw [finiteCoefficient_eq_limit_mul_ratio_mul_penalty K n hn hK]
  have hpen := one_lt_coefficientComparisonPenalty K n hn hK
  nlinarith [mul_pos hbase (sub_pos.mpr hpen)]

/-! ## Exact finite error-budget algebra -/

/-- The explicit Route-2 hiding envelope `C' d / sqrt K` used in the Letter.
This is only a scalar definition.  The assertion that the independent
complex-symmetric matrix law satisfies this envelope is the cited external
input from Shou et al.; it is not asserted or axiomatized here. -/
def symmetricHidingEnvelope (Cprime : ℝ) (K d : ℕ) : ℝ :=
  Cprime * (d : ℝ) / Real.sqrt (K : ℝ)

/-- The explicit envelope is the constant multiple of the existing raw
linear-square-root rate. -/
theorem symmetricHidingEnvelope_eq_const_mul_ultimateHidingRate
    (Cprime : ℝ) (K d : ℕ) :
    symmetricHidingEnvelope Cprime K d =
      Cprime * ultimateHidingRate K d := by
  unfold symmetricHidingEnvelope ultimateHidingRate
  ring

/-- A nonnegative constant gives a nonnegative explicit Route-2 envelope. -/
theorem symmetricHidingEnvelope_nonneg
    (Cprime : ℝ) (hCprime : 0 ≤ Cprime) (K d : ℕ) :
    0 ≤ symmetricHidingEnvelope Cprime K d := by
  unfold symmetricHidingEnvelope
  exact div_nonneg (mul_nonneg hCprime (Nat.cast_nonneg d))
    (Real.sqrt_nonneg _)

/-- Method 1 remainder at its natural Gram reference scale. -/
def methodOneRelativeRemainder
    (M K n : ℕ) (eta rho : ℝ) : ℝ :=
  paperBkn K n * (eta / rho) + hidingRemainder M (2 * n)

/-- Method 2 remainder at its own independent-symmetric reference scale. -/
def methodTwoNaturalRelativeRemainder
    (n : ℕ) (eta rho deltaSym : ℝ) : ℝ :=
  paperBn n * (eta / rho) + deltaSym

/-- Method 2 remainder expressed at the common Method 1 physical reference
scale. -/
def methodTwoCommonRelativeRemainder
    (K n : ℕ) (eta rho deltaSym : ℝ) : ℝ :=
  paperBn n * gramToSymmetricVarianceRatio K n * (eta / rho) + deltaSym

/-- Literal substitution of `C' d / sqrt K` into the natural-scale
Route-2 remainder. -/
theorem methodTwoNaturalRelativeRemainder_explicit
    (Cprime eta rho : ℝ) (K d n : ℕ) :
    methodTwoNaturalRelativeRemainder n eta rho
        (symmetricHidingEnvelope Cprime K d) =
      paperBn n * (eta / rho) +
        Cprime * (d : ℝ) / Real.sqrt (K : ℝ) := by
  rfl

/-- Literal substitution of `C' d / sqrt K` into the common-scale
Route-2 remainder. -/
theorem methodTwoCommonRelativeRemainder_explicit
    (Cprime eta rho : ℝ) (K d n : ℕ) :
    methodTwoCommonRelativeRemainder K n eta rho
        (symmetricHidingEnvelope Cprime K d) =
      paperBn n * gramToSymmetricVarianceRatio K n * (eta / rho) +
        Cprime * (d : ℝ) / Real.sqrt (K : ℝ) := by
  rfl

/-- Before the probability cap is active, Method 2 has the smaller complete
remainder exactly when its hiding-cost excess is smaller than its
anticoncentration gain.  This is the literal crossover criterion displayed
in the Letter. -/
theorem methodTwoCommonRemainder_lt_methodOne_iff_crossover
    (M K n : ℕ) (eta rho deltaSym : ℝ) :
    methodTwoCommonRelativeRemainder K n eta rho deltaSym <
        methodOneRelativeRemainder M K n eta rho ↔
      deltaSym - hidingRemainder M (2 * n) <
        (paperBkn K n -
          paperBn n * gramToSymmetricVarianceRatio K n) * (eta / rho) := by
  unfold methodTwoCommonRelativeRemainder methodOneRelativeRemainder
  constructor <;> intro h <;> nlinarith

/-- Scaling Method 2's normalized additive tolerance by `R_{K,n}` gives its
common-scale remainder exactly. -/
theorem methodTwoNatural_rescaled_eq_common
    (K n : ℕ) (eta rho deltaSym : ℝ) :
    methodTwoNaturalRelativeRemainder n
        (gramToSymmetricVarianceRatio K n * eta) rho deltaSym =
      methodTwoCommonRelativeRemainder K n eta rho deltaSym := by
  unfold methodTwoNaturalRelativeRemainder methodTwoCommonRelativeRemainder
  ring

/-- Capped Method 1 relative-failure budget. -/
def methodOneRelativeBudget
    (gamma : ℝ) (M K n : ℕ) (eta rho : ℝ) : ℝ :=
  min 1 (gamma + methodOneRelativeRemainder M K n eta rho)

/-- Capped Method 2 budget on the common physical scale. -/
def methodTwoCommonRelativeBudget
    (gamma : ℝ) (K n : ℕ) (eta rho deltaSym : ℝ) : ℝ :=
  min 1 (gamma +
    methodTwoCommonRelativeRemainder K n eta rho deltaSym)

/-- The best certified common-scale budget when both routes are available. -/
def dualMethodCommonRelativeBudget
    (gamma : ℝ) (M K n : ℕ)
    (eta rho deltaSym : ℝ) : ℝ :=
  min 1 (gamma + min
    (methodOneRelativeRemainder M K n eta rho)
    (methodTwoCommonRelativeRemainder K n eta rho deltaSym))

/-- The displayed dual budget is exactly the minimum of the two separately
capped route budgets. -/
theorem dualMethodCommonRelativeBudget_eq_min
    (gamma : ℝ) (M K n : ℕ) (eta rho deltaSym : ℝ) :
    dualMethodCommonRelativeBudget gamma M K n eta rho deltaSym =
      min (methodOneRelativeBudget gamma M K n eta rho)
        (methodTwoCommonRelativeBudget gamma K n eta rho deltaSym) := by
  unfold dualMethodCommonRelativeBudget methodOneRelativeBudget
    methodTwoCommonRelativeBudget
  rcases le_total
      (methodOneRelativeRemainder M K n eta rho)
      (methodTwoCommonRelativeRemainder K n eta rho deltaSym) with h | h
  · rw [min_eq_left h]
    have hbudget :
        min 1 (gamma + methodOneRelativeRemainder M K n eta rho) ≤
          min 1 (gamma +
            methodTwoCommonRelativeRemainder K n eta rho deltaSym) :=
      min_le_min le_rfl (by linarith)
    exact (min_eq_left hbudget).symm
  · rw [min_eq_right h]
    have hbudget :
        min 1 (gamma +
            methodTwoCommonRelativeRemainder K n eta rho deltaSym) ≤
          min 1 (gamma + methodOneRelativeRemainder M K n eta rho) :=
      min_le_min le_rfl (by linarith)
    exact (min_eq_right hbudget).symm

/-- Pure min-of-two inference: if a failure probability satisfies both
route bounds, it satisfies the displayed dual bound. -/
theorem failure_le_dualMethodCommonRelativeBudget
    {failure gamma eta rho deltaSym : ℝ} {M K n : ℕ}
    (hMethodOne :
      failure ≤ methodOneRelativeBudget gamma M K n eta rho)
    (hMethodTwo :
      failure ≤ methodTwoCommonRelativeBudget
        gamma K n eta rho deltaSym) :
    failure ≤
      dualMethodCommonRelativeBudget gamma M K n eta rho deltaSym := by
  rw [dualMethodCommonRelativeBudget_eq_min]
  exact le_min hMethodOne hMethodTwo

/-! ## Abstract prescribed-panel comparison

The following wrappers contain no random-matrix assumptions.  The functions
`h₁` and `h₂` are arbitrary supplied hiding-error ledgers.  The corresponding
theorems require each joint-transfer or one-coordinate-transfer estimate as
an explicit premise and perform only the final minimum algebra.
-/

/-- One route's arbitrary-overlap prescribed-panel budget:
`min {1, q c t + min (h L) (q h N)}`. -/
def arbitraryOverlapPanelRouteBudget
    (q : ℕ) (c t : ℝ) (h : ℕ → ℝ) (L N : ℕ) : ℝ :=
  min 1 ((q : ℝ) * c * t + min (h L) ((q : ℝ) * h N))

/-- Literal arbitrary-overlap panel budget after substituting the explicit
Route-2 envelope at the union size `L` and at one-pattern size `N`. -/
theorem arbitraryOverlapPanelRouteBudget_explicit
    (Cprime c t : ℝ) (K q L N : ℕ) :
    arbitraryOverlapPanelRouteBudget q c t
        (symmetricHidingEnvelope Cprime K) L N =
      min 1 ((q : ℝ) * c * t +
        min (Cprime * (L : ℝ) / Real.sqrt (K : ℝ))
          ((q : ℝ) *
            (Cprime * (N : ℝ) / Real.sqrt (K : ℝ)))) := by
  rfl

/-- A probability cap and the joint union-block estimate give the exact
Route-2 panel display with the explicit `C' L / sqrt K` contribution.  The
joint probability estimate itself remains an input. -/
theorem failure_le_arbitraryOverlapPanelExplicitJointBudget
    {failure Cprime c t : ℝ} {K q L : ℕ}
    (hprob : failure ≤ 1)
    (hjoint : failure ≤ (q : ℝ) * c * t +
      symmetricHidingEnvelope Cprime K L) :
    failure ≤ min 1 ((q : ℝ) * c * t +
      Cprime * (L : ℝ) / Real.sqrt (K : ℝ)) := by
  simpa [symmetricHidingEnvelope] using le_min hprob hjoint

/-- The two-route arbitrary-overlap bound is the better of the two complete
route budgets. -/
def twoRouteArbitraryOverlapPanelBudget
    (q : ℕ) (t c₁ c₂ : ℝ) (h₁ h₂ : ℕ → ℝ) (L N : ℕ) : ℝ :=
  min (arbitraryOverlapPanelRouteBudget q c₁ t h₁ L N)
    (arbitraryOverlapPanelRouteBudget q c₂ t h₂ L N)

/-- A probability cap, a joint transfer at union size `L`, and `q`
one-coordinate transfers imply the exact arbitrary-overlap route budget. -/
theorem failure_le_arbitraryOverlapPanelRouteBudget
    {failure c t : ℝ} {q L N : ℕ} {h : ℕ → ℝ}
    (hprob : failure ≤ 1)
    (hjoint : failure ≤ (q : ℝ) * c * t + h L)
    (hsingle : failure ≤
      (q : ℝ) * c * t + (q : ℝ) * h N) :
    failure ≤ arbitraryOverlapPanelRouteBudget q c t h L N := by
  unfold arbitraryOverlapPanelRouteBudget
  apply le_min hprob
  rcases le_total (h L) ((q : ℝ) * h N) with hmin | hmin
  · rw [min_eq_left hmin]
    exact hjoint
  · rw [min_eq_right hmin]
    exact hsingle

/-- If both abstract arbitrary-overlap routes are valid for the same event,
their minimum is valid. -/
theorem failure_le_twoRouteArbitraryOverlapPanelBudget
    {failure t c₁ c₂ : ℝ} {q L N : ℕ} {h₁ h₂ : ℕ → ℝ}
    (hroute₁ : failure ≤
      arbitraryOverlapPanelRouteBudget q c₁ t h₁ L N)
    (hroute₂ : failure ≤
      arbitraryOverlapPanelRouteBudget q c₂ t h₂ L N) :
    failure ≤
      twoRouteArbitraryOverlapPanelBudget q t c₁ c₂ h₁ h₂ L N := by
  exact le_min hroute₁ hroute₂

/-- Direct two-route arbitrary-overlap transfer from the six supplied
probability, joint-transfer, and single-transfer premises. -/
theorem failure_le_twoRouteArbitraryOverlapPanelBudget_of_components
    {failure t c₁ c₂ : ℝ} {q L N : ℕ} {h₁ h₂ : ℕ → ℝ}
    (hprob₁ : failure ≤ 1)
    (hjoint₁ : failure ≤ (q : ℝ) * c₁ * t + h₁ L)
    (hsingle₁ : failure ≤
      (q : ℝ) * c₁ * t + (q : ℝ) * h₁ N)
    (hprob₂ : failure ≤ 1)
    (hjoint₂ : failure ≤ (q : ℝ) * c₂ * t + h₂ L)
    (hsingle₂ : failure ≤
      (q : ℝ) * c₂ * t + (q : ℝ) * h₂ N) :
    failure ≤
      twoRouteArbitraryOverlapPanelBudget q t c₁ c₂ h₁ h₂ L N := by
  apply failure_le_twoRouteArbitraryOverlapPanelBudget
  · exact failure_le_arbitraryOverlapPanelRouteBudget
      hprob₁ hjoint₁ hsingle₁
  · exact failure_le_arbitraryOverlapPanelRouteBudget
      hprob₂ hjoint₂ hsingle₂

/-- One route's pairwise-disjoint prescribed-panel budget:
`min {1, 1-(1-min(1,c t))^q+h(qN), q(min(1,c t)+h(N))}`. -/
def disjointPanelRouteBudget
    (q : ℕ) (c t : ℝ) (h : ℕ → ℝ) (N : ℕ) : ℝ :=
  min 1 (min
    (1 - (1 - min 1 (c * t)) ^ q + h (q * N))
    ((q : ℝ) * (min 1 (c * t) + h N)))

/-- Literal disjoint-panel budget after substituting the explicit Route-2
envelope.  This theorem is only algebra; the sharp product-law and matrix-law
inputs remain separate premises of the generic transfer theorem. -/
theorem disjointPanelRouteBudget_explicit
    (Cprime c t : ℝ) (K q N : ℕ) :
    disjointPanelRouteBudget q c t
        (symmetricHidingEnvelope Cprime K) N =
      min 1 (min
        (1 - (1 - min 1 (c * t)) ^ q +
          Cprime * ((q * N : ℕ) : ℝ) / Real.sqrt (K : ℝ))
        ((q : ℝ) * (min 1 (c * t) +
          Cprime * (N : ℝ) / Real.sqrt (K : ℝ)))) := by
  rfl

/-- A probability cap and the sharp independent-reference joint estimate give
the exact Route-2 disjoint-panel display with `C' qN / sqrt K`.  Independence
and the finite-Haar transfer are not asserted by this algebraic wrapper. -/
theorem failure_le_disjointPanelExplicitJointBudget
    {failure Cprime c t : ℝ} {K q N : ℕ}
    (hprob : failure ≤ 1)
    (hjoint : failure ≤
      1 - (1 - min 1 (c * t)) ^ q +
        symmetricHidingEnvelope Cprime K (q * N)) :
    failure ≤ min 1
      (1 - (1 - min 1 (c * t)) ^ q +
        Cprime * ((q * N : ℕ) : ℝ) / Real.sqrt (K : ℝ)) := by
  simpa [symmetricHidingEnvelope] using le_min hprob hjoint

/-- The two-route disjoint-panel bound is the better complete route. -/
def twoRouteDisjointPanelBudget
    (q : ℕ) (t c₁ c₂ : ℝ) (h₁ h₂ : ℕ → ℝ) (N : ℕ) : ℝ :=
  min (disjointPanelRouteBudget q c₁ t h₁ N)
    (disjointPanelRouteBudget q c₂ t h₂ N)

/-- Supplied sharp-product and coordinatewise-union estimates imply the
exact three-way minimum for one disjoint-panel route. -/
theorem failure_le_disjointPanelRouteBudget
    {failure c t : ℝ} {q N : ℕ} {h : ℕ → ℝ}
    (hprob : failure ≤ 1)
    (hjoint : failure ≤
      1 - (1 - min 1 (c * t)) ^ q + h (q * N))
    (hsingle : failure ≤
      (q : ℝ) * (min 1 (c * t) + h N)) :
    failure ≤ disjointPanelRouteBudget q c t h N := by
  exact le_min hprob (le_min hjoint hsingle)

/-- If both abstract disjoint-panel routes bound the same event, their
minimum also bounds it. -/
theorem failure_le_twoRouteDisjointPanelBudget
    {failure t c₁ c₂ : ℝ} {q N : ℕ} {h₁ h₂ : ℕ → ℝ}
    (hroute₁ : failure ≤ disjointPanelRouteBudget q c₁ t h₁ N)
    (hroute₂ : failure ≤ disjointPanelRouteBudget q c₂ t h₂ N) :
    failure ≤ twoRouteDisjointPanelBudget q t c₁ c₂ h₁ h₂ N := by
  exact le_min hroute₁ hroute₂

/-- Direct two-route disjoint-panel transfer from the six supplied route
premises. -/
theorem failure_le_twoRouteDisjointPanelBudget_of_components
    {failure t c₁ c₂ : ℝ} {q N : ℕ} {h₁ h₂ : ℕ → ℝ}
    (hprob₁ : failure ≤ 1)
    (hjoint₁ : failure ≤
      1 - (1 - min 1 (c₁ * t)) ^ q + h₁ (q * N))
    (hsingle₁ : failure ≤
      (q : ℝ) * (min 1 (c₁ * t) + h₁ N))
    (hprob₂ : failure ≤ 1)
    (hjoint₂ : failure ≤
      1 - (1 - min 1 (c₂ * t)) ^ q + h₂ (q * N))
    (hsingle₂ : failure ≤
      (q : ℝ) * (min 1 (c₂ * t) + h₂ N)) :
    failure ≤ twoRouteDisjointPanelBudget q t c₁ c₂ h₁ h₂ N := by
  apply failure_le_twoRouteDisjointPanelBudget
  · exact failure_le_disjointPanelRouteBudget hprob₁ hjoint₁ hsingle₁
  · exact failure_le_disjointPanelRouteBudget hprob₂ hjoint₂ hsingle₂

/-! ## Abstract sampler comparison -/

/-- For a route with small-ball coefficient `c` and physical reference
probability `p`, this is the exact sampler constant
`2 c eps / (rho D p)`. -/
def samplerRouteConstant
    (c eps rho D p : ℝ) : ℝ :=
  2 * c * eps / (rho * D * p)

/-- One route's sampler budget before choosing the Markov parameter
`zeta`. -/
def samplerRouteBudget
    (zeta c eps rho D p : ℝ) (h : ℕ → ℝ) (N : ℕ) : ℝ :=
  min 1 (zeta + samplerRouteConstant c eps rho D p / zeta + h N)

/-- Literal pre-optimization sampler budget after substituting the explicit
Route-2 hiding envelope. -/
theorem samplerRouteBudget_explicit
    (Cprime zeta c eps rho D p : ℝ) (K N : ℕ) :
    samplerRouteBudget zeta c eps rho D p
        (symmetricHidingEnvelope Cprime K) N =
      min 1 (zeta + samplerRouteConstant c eps rho D p / zeta +
        Cprime * (N : ℝ) / Real.sqrt (K : ℝ)) := by
  rfl

/-- One route's sampler budget after the square-root choice. -/
def optimizedSamplerRouteBudget
    (c eps rho D p : ℝ) (h : ℕ → ℝ) (N : ℕ) : ℝ :=
  min 1 (2 * Real.sqrt (samplerRouteConstant c eps rho D p) + h N)

/-- Literal optimized sampler budget after substituting the explicit
Route-2 hiding envelope. -/
theorem optimizedSamplerRouteBudget_explicit
    (Cprime c eps rho D p : ℝ) (K N : ℕ) :
    optimizedSamplerRouteBudget c eps rho D p
        (symmetricHidingEnvelope Cprime K) N =
      min 1 (2 * Real.sqrt (samplerRouteConstant c eps rho D p) +
        Cprime * (N : ℝ) / Real.sqrt (K : ℝ)) := by
  rfl

/-- The two-route optimized sampler budget is the better complete route. -/
def twoRouteOptimizedSamplerBudget
    (c₁ c₂ eps rho D p₁ p₂ : ℝ)
    (h₁ h₂ : ℕ → ℝ) (N : ℕ) : ℝ :=
  min (optimizedSamplerRouteBudget c₁ eps rho D p₁ h₁ N)
    (optimizedSamplerRouteBudget c₂ eps rho D p₂ h₂ N)

/-- Substitution of `zeta = sqrt(2 c eps/(rho D p))` gives exactly the
optimized one-route budget. -/
theorem samplerRouteBudget_sqrt_eq_optimized
    (c eps rho D p : ℝ) (h : ℕ → ℝ) (N : ℕ)
    (hconstant : 0 < samplerRouteConstant c eps rho D p) :
    samplerRouteBudget
        (Real.sqrt (samplerRouteConstant c eps rho D p))
        c eps rho D p h N =
      optimizedSamplerRouteBudget c eps rho D p h N := by
  unfold samplerRouteBudget optimizedSamplerRouteBudget
  rw [RelativeAccuracy.samplerSqrtChoice_exact hconstant]

/-- Abstract one-route sampler inference at the optimal square-root
choice. -/
theorem failure_le_optimizedSamplerRouteBudget
    {failure c eps rho D p : ℝ} {h : ℕ → ℝ} {N : ℕ}
    (hconstant : 0 < samplerRouteConstant c eps rho D p)
    (hfailure : failure ≤ samplerRouteBudget
      (Real.sqrt (samplerRouteConstant c eps rho D p))
      c eps rho D p h N) :
    failure ≤ optimizedSamplerRouteBudget c eps rho D p h N := by
  rw [samplerRouteBudget_sqrt_eq_optimized
    c eps rho D p h N hconstant] at hfailure
  exact hfailure

/-- If both optimized sampler routes bound the same failure probability,
their minimum also does. -/
theorem failure_le_twoRouteOptimizedSamplerBudget
    {failure c₁ c₂ eps rho D p₁ p₂ : ℝ}
    {h₁ h₂ : ℕ → ℝ} {N : ℕ}
    (hroute₁ : failure ≤
      optimizedSamplerRouteBudget c₁ eps rho D p₁ h₁ N)
    (hroute₂ : failure ≤
      optimizedSamplerRouteBudget c₂ eps rho D p₂ h₂ N) :
    failure ≤ twoRouteOptimizedSamplerBudget
      c₁ c₂ eps rho D p₁ p₂ h₁ h₂ N := by
  exact le_min hroute₁ hroute₂

/-- Direct two-route sampler transfer from the supplied square-root-route
bounds and positivity of the two route constants. -/
theorem failure_le_twoRouteOptimizedSamplerBudget_of_sqrt_bounds
    {failure c₁ c₂ eps rho D p₁ p₂ : ℝ}
    {h₁ h₂ : ℕ → ℝ} {N : ℕ}
    (hconstant₁ : 0 < samplerRouteConstant c₁ eps rho D p₁)
    (hconstant₂ : 0 < samplerRouteConstant c₂ eps rho D p₂)
    (hroute₁ : failure ≤ samplerRouteBudget
      (Real.sqrt (samplerRouteConstant c₁ eps rho D p₁))
      c₁ eps rho D p₁ h₁ N)
    (hroute₂ : failure ≤ samplerRouteBudget
      (Real.sqrt (samplerRouteConstant c₂ eps rho D p₂))
      c₂ eps rho D p₂ h₂ N) :
    failure ≤ twoRouteOptimizedSamplerBudget
      c₁ c₂ eps rho D p₁ p₂ h₁ h₂ N := by
  apply failure_le_twoRouteOptimizedSamplerBudget
  · exact failure_le_optimizedSamplerRouteBudget hconstant₁ hroute₁
  · exact failure_le_optimizedSamplerRouteBudget hconstant₂ hroute₂

/-! ## Elementary algebra for the displayed asymptotic regimes -/

/-- On the exact real-valued scale `K = c N² / log N` and `n = N/2`,
the coefficient-regime parameter is `n²/K = log N/(4c)`.  The identity is
valid with Lean's totalized division even at the exceptional zero values. -/
theorem methodOnePolynomialScale_identity (N c : ℝ) :
    (N / 2) ^ 2 / (c * N ^ 2 / Real.log N) =
      Real.log N / (4 * c) := by
  by_cases hN : N = 0
  · simp [hN]
  by_cases hc : c = 0
  · simp [hc]
  by_cases hlog : Real.log N = 0
  · simp [hlog]
  field_simp [hN, hc, hlog]
  <;> ring

/-- The strict exponent window in the Letter leaves a positive choice of the
coefficient-envelope exponent `D` between `1/(4c)` and `(a-1/2)/3`. -/
theorem methodOnePolynomialWindow_margin
    {c a : ℝ} (hc : 0 < c)
    (ha : 1 / 2 + 3 / (4 * c) < a) :
    ∃ D : ℝ, 0 < D ∧ 1 / (4 * c) < D ∧
      3 * D + 1 / 2 < a := by
  let x : ℝ := 1 / (4 * c)
  let y : ℝ := (a - 1 / 2) / 3
  have hx : 0 < x := by
    dsimp [x]
    positivity
  have hxy : x < y := by
    dsimp [x, y]
    have hrewrite : 3 / (4 * c) = 3 * (1 / (4 * c)) := by ring
    rw [hrewrite] at ha
    have hmain : 3 * (1 / (4 * c)) < a - 1 / 2 := by
      linarith [ha]
    linarith
  refine ⟨(x + y) / 2, by linarith, by linarith, ?_⟩
  dsimp [y] at *
  linarith

/-- If the additive tolerance is `N^{-a}` and the coefficient envelope has
power `N^{3D+1/2}`, the residual exponent tends to zero whenever
`a > 3D+1/2`. -/
theorem methodOnePolynomialWindow_power_tendsto_zero
    {D a : ℝ} (ha : 3 * D + 1 / 2 < a) :
    Tendsto
      (fun N : ℕ ↦
        (N : ℝ) ^ (3 * D + 1 / 2 - a))
      atTop (nhds 0) := by
  have hpos : 0 < a - (3 * D + 1 / 2) := by linarith
  have hlim :=
    (tendsto_rpow_neg_atTop hpos).comp tendsto_natCast_atTop_atTop
  convert hlim using 1
  funext N
  congr 1
  ring

/-- The explicit constant multiplying the polynomial envelope does not
change the preceding convergence. -/
theorem methodOnePolynomialWindow_envelope_tendsto_zero
    {D a : ℝ} (ha : 3 * D + 1 / 2 < a) :
    Tendsto
      (fun N : ℕ ↦
        2 * Real.exp 1 *
          (N : ℝ) ^ (3 * D + 1 / 2 - a))
      atTop (nhds 0) := by
  simpa using
    tendsto_const_nhds.mul
      (methodOnePolynomialWindow_power_tendsto_zero ha)

/-- If `N²/K → 0`, then the squared hiding order `N²/K` is little-o of
the linear-square-root order `N/√K`.  This is the literal order comparison
used when `K = M ≫ N²`. -/
theorem hidingOrderComparison_isLittleO
    (N K : ℕ → ℕ)
    (hscale : Tendsto
      (fun j ↦ (N j : ℝ) ^ 2 / (K j : ℝ))
      atTop (nhds 0)) :
    (fun j ↦ (N j : ℝ) ^ 2 / (K j : ℝ)) =o[atTop]
      (fun j ↦ (N j : ℝ) / Real.sqrt (K j : ℝ)) := by
  let f : ℕ → ℝ := fun j ↦ (N j : ℝ) ^ 2 / (K j : ℝ)
  let g : ℕ → ℝ := fun j ↦
    (N j : ℝ) / Real.sqrt (K j : ℝ)
  change f =o[atTop] g
  have hfg : ∀ j, f j = (g j) ^ 2 := by
    intro j
    dsimp [f, g]
    rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg (K j))]
  have hsqrt : (fun j ↦ Real.sqrt (f j)) = g := by
    funext j
    dsimp [f, g]
    rw [Real.sqrt_div (sq_nonneg (N j : ℝ))]
    rw [Real.sqrt_sq_eq_abs,
      abs_of_nonneg (show (0 : ℝ) ≤ (N j : ℝ) by positivity)]
  have hg : Tendsto g atTop (nhds 0) := by
    have hs : Tendsto (fun j ↦ Real.sqrt (f j)) atTop (nhds 0) := by
      simpa [f] using hscale.sqrt
    rw [hsqrt] at hs
    exact hs
  apply (Asymptotics.isLittleO_iff_tendsto ?_).2
  · have hquot : (fun j ↦ f j / g j) = g := by
      funext j
      rw [hfg j]
      by_cases hj : g j = 0
      · simp [hj]
      · field_simp [hj]
    rw [hquot]
    exact hg
  · intro j hj
    rw [hfg j, hj]
    norm_num

/-- Multiplying a vanishing `d / sqrt K` scale by the fixed explicit constant
`C'` preserves convergence to zero. -/
theorem symmetricHidingEnvelope_tendsto_zero
    {ι : Type*} {l : Filter ι}
    (Cprime : ℝ) (K d : ι → ℕ)
    (hscale : Tendsto
      (fun i ↦ (d i : ℝ) / Real.sqrt (K i : ℝ))
      l (nhds 0)) :
    Tendsto
      (fun i ↦ symmetricHidingEnvelope Cprime (K i) (d i))
      l (nhds 0) := by
  have hconstant : Tendsto (fun _ : ι ↦ Cprime) l (nhds Cprime) :=
    tendsto_const_nhds
  simpa [symmetricHidingEnvelope, mul_div_assoc] using
    hconstant.mul hscale

/-- The explicit Route-2 envelope vanishes under the paper's sufficient
condition `d^2 / K → 0`.  This is deterministic scalar algebra; the claim
that it bounds the symmetric matrix-law distance remains external. -/
theorem symmetricHidingEnvelope_tendsto_zero_of_squaredRate
    (Cprime : ℝ) (d K : ℕ → ℕ)
    (hscale : Tendsto
      (fun j ↦ (d j : ℝ) ^ 2 / (K j : ℝ))
      atTop (nhds 0)) :
    Tendsto
      (fun j ↦ symmetricHidingEnvelope Cprime (K j) (d j))
      atTop (nhds 0) := by
  have hroot :
      (fun j ↦ Real.sqrt ((d j : ℝ) ^ 2 / (K j : ℝ))) =
        (fun j ↦ (d j : ℝ) / Real.sqrt (K j : ℝ)) := by
    funext j
    rw [Real.sqrt_div (sq_nonneg (d j : ℝ))]
    rw [Real.sqrt_sq_eq_abs,
      abs_of_nonneg (show (0 : ℝ) ≤ (d j : ℝ) by positivity)]
  have hlinear : Tendsto
      (fun j ↦ (d j : ℝ) / Real.sqrt (K j : ℝ))
      atTop (nhds 0) := by
    rw [← hroot]
    simpa using hscale.sqrt
  exact symmetricHidingEnvelope_tendsto_zero
    Cprime K d hlinear

/-- The raw Method-1 prescribed-panel hiding scale displayed in the Letter. -/
def methodOnePanelHidingScale (M q L N : ℕ) : ℝ :=
  min ((L : ℝ) ^ 2 / (M : ℝ))
    ((q : ℝ) * (N : ℝ) ^ 2 / (M : ℝ))

/-- The raw Method-2 prescribed-panel hiding scale displayed in the Letter. -/
def methodTwoPanelHidingScale (K q L N : ℕ) : ℝ :=
  min ((L : ℝ) / Real.sqrt (K : ℝ))
    ((q : ℝ) * (N : ℝ) / Real.sqrt (K : ℝ))

/-- Literal substitution of the certified squared hiding rate into the
Method-1 panel minimum. -/
theorem methodOnePanelHidingScale_eq_rateMinimum
    (M q L N : ℕ) :
    methodOnePanelHidingScale M q L N =
      min (ultimateSquaredHidingRate M L)
        ((q : ℝ) * ultimateSquaredHidingRate M N) := by
  unfold methodOnePanelHidingScale ultimateSquaredHidingRate
  congr 1
  ring

/-- Literal substitution of a linear-square-root hiding rate into the
Method-2 panel minimum.  Supplying this rate for the independent-symmetric
matrix law remains the cited external input. -/
theorem methodTwoPanelHidingScale_eq_rateMinimum
    (K q L N : ℕ) :
    methodTwoPanelHidingScale K q L N =
      min (ultimateHidingRate K L)
        ((q : ℝ) * ultimateHidingRate K N) := by
  unfold methodTwoPanelHidingScale ultimateHidingRate
  congr 1
  ring

/-- The certified, capped Method-1 hiding minimum is bounded by `615172`
times its displayed raw panel scale. -/
theorem methodOnePanelHidingMinimum_le_scale
    (M q L N : ℕ) :
    min (hidingRemainder M L)
        ((q : ℝ) * hidingRemainder M N) ≤
      615172 * methodOnePanelHidingScale M q L N := by
  have hL : hidingRemainder M L ≤
      615172 * ultimateSquaredHidingRate M L := by
    unfold hidingRemainder
    exact min_le_right _ _
  have hN : hidingRemainder M N ≤
      615172 * ultimateSquaredHidingRate M N := by
    unfold hidingRemainder
    exact min_le_right _ _
  have hqN : (q : ℝ) * hidingRemainder M N ≤
      (q : ℝ) * (615172 * ultimateSquaredHidingRate M N) :=
    mul_le_mul_of_nonneg_left hN (Nat.cast_nonneg q)
  calc
    min (hidingRemainder M L)
        ((q : ℝ) * hidingRemainder M N) ≤
        min (615172 * ultimateSquaredHidingRate M L)
          ((q : ℝ) *
            (615172 * ultimateSquaredHidingRate M N)) :=
      min_le_min hL hqN
    _ = 615172 * methodOnePanelHidingScale M q L N := by
      rw [methodOnePanelHidingScale_eq_rateMinimum,
        mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 615172)]
      congr 1
      ring

/-- Any supplied linear-square-root hiding ledger obeys the Method-2 panel
scale bound.  The scientific matrix-law estimate is an explicit premise. -/
theorem linearPanelHidingMinimum_le_methodTwoScale
    (C : ℝ) (hC : 0 ≤ C) (h : ℕ → ℝ)
    (K q L N : ℕ)
    (hbound : ∀ d, h d ≤ C * ultimateHidingRate K d) :
    min (h L) ((q : ℝ) * h N) ≤
      C * methodTwoPanelHidingScale K q L N := by
  have hL := hbound L
  have hN := hbound N
  have hqN : (q : ℝ) * h N ≤
      (q : ℝ) * (C * ultimateHidingRate K N) :=
    mul_le_mul_of_nonneg_left hN (Nat.cast_nonneg q)
  calc
    min (h L) ((q : ℝ) * h N) ≤
        min (C * ultimateHidingRate K L)
          ((q : ℝ) * (C * ultimateHidingRate K N)) :=
      min_le_min hL hqN
    _ = C * methodTwoPanelHidingScale K q L N := by
      rw [methodTwoPanelHidingScale_eq_rateMinimum,
        mul_min_of_nonneg _ _ hC]
      congr 1
      ring

/-- The Method-1 panel hiding minimum vanishes whenever its displayed raw
panel scale vanishes. -/
theorem methodOnePanelHidingMinimum_tendsto_zero
    {ι : Type*} {l : Filter ι}
    (M q L N : ι → ℕ)
    (hscale : Tendsto
      (fun i ↦ methodOnePanelHidingScale
        (M i) (q i) (L i) (N i)) l (nhds 0)) :
    Tendsto
      (fun i ↦ min (hidingRemainder (M i) (L i))
        ((q i : ℝ) * hidingRemainder (M i) (N i)))
      l (nhds 0) := by
  apply squeeze_zero
  · intro i
    apply le_min
    · unfold hidingRemainder
      exact le_min zero_le_one
        (mul_nonneg (by norm_num)
          (ultimateSquaredHidingRate_nonneg (M i) (L i)))
    · exact mul_nonneg (Nat.cast_nonneg (q i)) (by
        unfold hidingRemainder
        exact le_min zero_le_one
          (mul_nonneg (by norm_num)
            (ultimateSquaredHidingRate_nonneg (M i) (N i))))
  · intro i
    exact methodOnePanelHidingMinimum_le_scale
      (M i) (q i) (L i) (N i)
  · simpa using tendsto_const_nhds.mul hscale

/-- The one-coordinate Method-1 hiding remainder vanishes under the literal
rate hypothesis `N²/M → 0`, i.e. the formal content of `M ≫ N²`. -/
theorem hidingRemainder_tendsto_zero_of_squaredRate
    {ι : Type*} {l : Filter ι} (M N : ι → ℕ)
    (hscale : Tendsto
      (fun i ↦ ultimateSquaredHidingRate (M i) (N i))
      l (nhds 0)) :
    Tendsto (fun i ↦ hidingRemainder (M i) (N i))
      l (nhds 0) := by
  have hmul : Tendsto
      (fun i ↦ 615172 * ultimateSquaredHidingRate (M i) (N i))
      l (nhds 0) := by
    simpa using tendsto_const_nhds.mul hscale
  have hmin : Tendsto
      (fun i ↦ min (1 : ℝ)
        (615172 * ultimateSquaredHidingRate (M i) (N i)))
      l (nhds (min (1 : ℝ) 0)) :=
    Tendsto.min tendsto_const_nhds hmul
  simpa [hidingRemainder] using hmin

/-- Under an explicitly supplied `C d/√K` ledger bound, the Method-2 panel
hiding minimum vanishes whenever the displayed raw Method-2 panel scale does.
No independent-symmetric matrix-law estimate is asserted by this theorem. -/
theorem linearPanelHidingMinimum_tendsto_zero
    {ι : Type*} {l : Filter ι}
    (C : ℝ) (hC : 0 ≤ C)
    (h : ι → ℕ → ℝ) (K q L N : ι → ℕ)
    (hnonneg : ∀ i d, 0 ≤ h i d)
    (hbound : ∀ᶠ i in l, ∀ d : ℕ,
      h i d ≤ C * ultimateHidingRate (K i) d)
    (hscale : Tendsto
      (fun i ↦ methodTwoPanelHidingScale
        (K i) (q i) (L i) (N i)) l (nhds 0)) :
    Tendsto
      (fun i ↦ min (h i (L i)) ((q i : ℝ) * h i (N i)))
      l (nhds 0) := by
  apply squeeze_zero'
  · filter_upwards [] with i
    exact le_min (hnonneg i (L i))
      (mul_nonneg (Nat.cast_nonneg (q i)) (hnonneg i (N i)))
  · filter_upwards [hbound] with i hi
    exact linearPanelHidingMinimum_le_methodTwoScale
      C hC (h i) (K i) (q i) (L i) (N i) hi
  · simpa using tendsto_const_nhds.mul hscale

/-! ## Scoped asymptotic wrappers

These lemmas make no random-matrix assertion.  They say only that once the
three displayed error terms of a route tend to zero, the capped total budget
tends to zero as well.
-/

theorem capped_three_term_budget_tendsto_zero
    {ι : Type*} {l : Filter ι} (a b c : ι → ℝ)
    (ha : Tendsto a l (nhds 0))
    (hb : Tendsto b l (nhds 0))
    (hc : Tendsto c l (nhds 0)) :
    Tendsto (fun i ↦ min 1 (a i + b i + c i)) l (nhds 0) := by
  have hsum : Tendsto (fun i ↦ a i + b i + c i) l (nhds 0) := by
    convert (ha.add hb).add hc using 1 <;> norm_num
  have hmin :
      Tendsto (fun i ↦ min (1 : ℝ) (a i + b i + c i)) l
        (nhds (min (1 : ℝ) 0)) :=
    Tendsto.min tendsto_const_nhds hsum
  simpa using hmin

/-- Method 1's capped budget vanishes whenever its additive-failure,
anticoncentration, and hiding terms vanish. -/
theorem methodOneRelativeBudget_tendsto_zero
    {ι : Type*} {l : Filter ι}
    (gamma eta rho : ι → ℝ) (M K n : ι → ℕ)
    (hgamma : Tendsto gamma l (nhds 0))
    (hanti : Tendsto
      (fun i ↦ paperBkn (K i) (n i) * (eta i / rho i))
      l (nhds 0))
    (hhide : Tendsto
      (fun i ↦ hidingRemainder (M i) (2 * n i))
      l (nhds 0)) :
    Tendsto
      (fun i ↦ methodOneRelativeBudget
        (gamma i) (M i) (K i) (n i) (eta i) (rho i))
      l (nhds 0) := by
  simpa [methodOneRelativeBudget, methodOneRelativeRemainder,
    add_assoc] using
    capped_three_term_budget_tendsto_zero gamma
      (fun i ↦ paperBkn (K i) (n i) * (eta i / rho i))
      (fun i ↦ hidingRemainder (M i) (2 * n i))
      hgamma hanti hhide

/-- Method 2's common-scale capped budget vanishes whenever its
additive-failure, symmetric small-denominator, and supplied hiding terms
vanish. -/
theorem methodTwoCommonRelativeBudget_tendsto_zero
    {ι : Type*} {l : Filter ι}
    (gamma eta rho deltaSym : ι → ℝ) (K n : ι → ℕ)
    (hgamma : Tendsto gamma l (nhds 0))
    (hanti : Tendsto
      (fun i ↦ paperBn (n i) *
        gramToSymmetricVarianceRatio (K i) (n i) *
          (eta i / rho i)) l (nhds 0))
    (hhide : Tendsto deltaSym l (nhds 0)) :
    Tendsto
      (fun i ↦ methodTwoCommonRelativeBudget
        (gamma i) (K i) (n i) (eta i) (rho i) (deltaSym i))
      l (nhds 0) := by
  simpa [methodTwoCommonRelativeBudget,
    methodTwoCommonRelativeRemainder, add_assoc] using
    capped_three_term_budget_tendsto_zero gamma
      (fun i ↦ paperBn (n i) *
        gramToSymmetricVarianceRatio (K i) (n i) *
          (eta i / rho i)) deltaSym hgamma hanti hhide

end

end LogdetLean.GramHafnian.ThreePaper.TwoMethodComparison
