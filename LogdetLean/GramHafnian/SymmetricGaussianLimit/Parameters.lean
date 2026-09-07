import LogdetLean.GramHafnian.CurrentPRL.CoefficientPaperEndpoints
import LogdetLean.GramHafnian.ShiftedAnticoncentration.Normalization
import LogdetLean.GramHafnian.RankTwoCentralBinomial

/-!
# Exact parameters for the independent complex-symmetric Gaussian limit

This file contains only deterministic identities.  The limiting variance is
`(2n-1)!!`, and the limiting small-ball coefficient is the same `b_n` that
appears as the fixed-degree limit of the finite Gram coefficient `B_{k,n}`.
-/

open Filter
open scoped BigOperators Nat

namespace LogdetLean.GramHafnian.SymmetricGaussianLimit

noncomputable section

open CurrentPRL

/-- The squared reference scale `sigma_{infinity,n}^2 = (2n-1)!!`. -/
def symmetricGaussianSigmaSq (n : ℕ) : ℝ :=
  (oddPairingNat n : ℝ)

/-- The reference scale `sigma_{infinity,n}`. -/
def symmetricGaussianSigma (n : ℕ) : ℝ :=
  Real.sqrt (symmetricGaussianSigmaSq n)

/-- The limiting coefficient `b_n`. -/
abbrev symmetricGaussianCoefficient (n : ℕ) : ℝ :=
  paperBn n

theorem symmetricGaussianSigma_nonneg (n : ℕ) :
    0 ≤ symmetricGaussianSigma n :=
  Real.sqrt_nonneg _

theorem symmetricGaussianSigma_pos (n : ℕ) :
    0 < symmetricGaussianSigma n := by
  unfold symmetricGaussianSigma symmetricGaussianSigmaSq
  exact Real.sqrt_pos.2 (by exact_mod_cast oddPairingNat_pos n)

theorem symmetricGaussianSigma_sq (n : ℕ) :
    symmetricGaussianSigma n ^ 2 = symmetricGaussianSigmaSq n := by
  exact Real.sq_sqrt (by
    unfold symmetricGaussianSigmaSq
    exact_mod_cast (oddPairingNat_pos n).le)

theorem symmetricGaussianSigmaSq_eq_doubleFactorial (n : ℕ) :
    symmetricGaussianSigmaSq n = ((2 * n - 1)‼ : ℕ) := by
  simp [symmetricGaussianSigmaSq, oddPairingNat_eq_doubleFactorial]

theorem symmetricGaussianCoefficient_eq_centralBinomial
    (n : ℕ) (hn : 1 ≤ n) :
    symmetricGaussianCoefficient n =
      (2 * (n : ℝ)) * (Nat.choose (2 * n) n : ℝ) / (4 : ℝ) ^ n :=
  limitingAnticoncentrationConstant_eq_centralBinomial n hn

theorem symmetricGaussianCoefficient_pos (n : ℕ) (hn : 1 ≤ n) :
    0 < symmetricGaussianCoefficient n := by
  rw [symmetricGaussianCoefficient_eq_centralBinomial n hn]
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hchooseNat : 0 < Nat.choose (2 * n) n :=
    Nat.choose_pos (by omega)
  have hchoose : (0 : ℝ) < (Nat.choose (2 * n) n : ℝ) := by
    exact_mod_cast hchooseNat
  exact div_pos (mul_pos (mul_pos (by norm_num) hnR) hchoose) (by positivity)

/-- The exact raw-radius coefficient `b_n / sigma_{infinity,n}^2`. -/
theorem symmetricGaussianCoefficient_div_sigmaSq
    (n : ℕ) (hn : 1 ≤ n) :
    symmetricGaussianCoefficient n / symmetricGaussianSigmaSq n =
      1 / ((((2 * n - 2)‼ : ℕ) : ℝ)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [symmetricGaussianCoefficient_eq_centralBinomial (1 + m) (by omega)]
  rw [symmetricGaussianSigmaSq, oddPairingNat_eq_doubleFactorial]
  rw [odd_doubleFactorial_cast_eq_factorial_div]
  rw [Nat.cast_choose ℝ (show 1 + m ≤ 2 * (1 + m) by omega)]
  rw [show 2 * (1 + m) - 2 = 2 * m by omega,
    Nat.doubleFactorial_two_mul]
  rw [show 2 * (1 + m) - (1 + m) = 1 + m by omega]
  rw [show (1 + m).factorial = (m + 1) * m.factorial by
    rw [add_comm, Nat.factorial_succ]]
  push_cast
  field_simp
  have hfour : (4 : ℝ) ^ (1 + m) = (2 : ℝ) ^ (2 * (1 + m)) := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, pow_mul]
  rw [hfour, show 2 * (1 + m) = 2 + m + m by omega]
  simp only [pow_add, pow_succ]
  ring

/-- The fixed-degree finite coefficient converges to the symmetric-Gaussian
coefficient. -/
theorem tendsto_finiteCoefficient (n : ℕ) (hn : 1 ≤ n) :
    Tendsto (fun k : ℕ ↦ paperBkn k n) atTop
      (nhds (symmetricGaussianCoefficient n)) :=
  tendsto_shiftedAnticoncentrationConstant_fixed_degree n hn

/-- The row-dimension correction after dividing the finite variance by
`k^n`.  It is written as a finite product so its limit is transparent. -/
def varianceCorrection (k n : ℕ) : ℝ :=
  ∏ q ∈ Finset.range n,
    (((k + 2 * q : ℕ) : ℝ) / (k : ℝ))

theorem closedFirstMoment_div_pow_eq
    (k n : ℕ) :
    closedFirstMoment k n / (k : ℝ) ^ n =
      symmetricGaussianSigmaSq n * varianceCorrection k n := by
  rw [closedFirstMoment, symmetricGaussianSigmaSq]
  rw [dimensionProduct, varianceCorrection, Finset.prod_div_distrib]
  simp [Finset.prod_const]
  ring

theorem tendsto_varianceCorrection (n : ℕ) :
    Tendsto (fun k : ℕ ↦ varianceCorrection k n) atTop (nhds 1) := by
  unfold varianceCorrection
  convert tendsto_finsetProd (Finset.range n) (fun q _ ↦
      tendsto_add_mul_div_add_mul_atTop_nhds
        (2 * (q : ℝ)) 0 1 one_ne_zero) using 1
  · ext k
    congr 1
    ext q
    push_cast
    ring
  · simp

/-- The finite Gram-hafnian variance, divided by `k^n`, converges to
`(2n-1)!!`. -/
theorem tendsto_closedFirstMoment_div_pow (n : ℕ) :
    Tendsto (fun k : ℕ ↦ closedFirstMoment k n / (k : ℝ) ^ n)
      atTop (nhds (symmetricGaussianSigmaSq n)) := by
  have hcorr := (tendsto_varianceCorrection n).const_mul
    (symmetricGaussianSigmaSq n)
  simpa using hcorr.congr' (by
    filter_upwards [] with k
    exact (closedFirstMoment_div_pow_eq k n).symm)

/-- Square-root version of the normalized finite scale. -/
theorem tendsto_sqrt_closedFirstMoment_div_pow (n : ℕ) :
    Tendsto
      (fun k : ℕ ↦ Real.sqrt (closedFirstMoment k n / (k : ℝ) ^ n))
      atTop (nhds (symmetricGaussianSigma n)) := by
  change Tendsto
    ((fun x : ℝ ↦ Real.sqrt x) ∘
      (fun k : ℕ ↦ closedFirstMoment k n / (k : ℝ) ^ n))
    atTop (nhds (Real.sqrt (symmetricGaussianSigmaSq n)))
  exact (Real.continuous_sqrt.tendsto _).comp
    (tendsto_closedFirstMoment_div_pow n)

end

end LogdetLean.GramHafnian.SymmetricGaussianLimit
