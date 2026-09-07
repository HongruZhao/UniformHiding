import LogdetLean.GramHafnian.ShiftedAnticoncentration.Experimental.WickAngularLowerBound.MomentReduction
import LogdetLean.GramHafnian.ShiftedAnticoncentration.Experimental.WickAngularLowerBound.ScalarFiniteRange
import LogdetLean.GramHafnian.RankTwoCentralBinomial

/-!
# Exact bridge from the scalar certificate to the moment reduction

The companion scalar file proves an exponential lower bound for an exact
rational expression.  This module proves that expression is precisely the
`wickAngularRatio` used by the literal angular moment reduction.  Thus there
is no floating-point or unverified Gamma simplification between the two.
-/

open scoped BigOperators
open Finset

namespace LogdetLean.GramHafnian.WickAngularLowerBound

noncomputable section

private lemma centralBinom_mul_factorial_eq_pow_mul_oddPairing (k : ℕ) :
    ((Nat.centralBinom k : ℕ) : ℝ) * (k.factorial : ℝ) =
      (2 : ℝ) ^ k * (oddPairingNat k : ℝ) := by
  have hchooseNat := Nat.choose_mul_factorial_mul_factorial
    (show k ≤ 2 * k by omega)
  have hsub : 2 * k - k = k := by omega
  rw [hsub] at hchooseNat
  have hchoose := congrArg (fun z : ℕ ↦ (z : ℝ)) hchooseNat
  push_cast at hchoose
  have hsplitNat := factorial_two_mul_eq_even_mul_odd k
  have hsplit : ((2 * k).factorial : ℝ) =
      (2 : ℝ) ^ k * (k.factorial : ℝ) * (oddPairingNat k : ℝ) := by
    exact_mod_cast hsplitNat
  have hfac : (k.factorial : ℝ) ≠ 0 := by positivity
  apply mul_right_cancel₀ hfac
  calc
    ((Nat.centralBinom k : ℝ) * (k.factorial : ℝ)) * (k.factorial : ℝ) =
        ((2 * k).factorial : ℝ) := by
          simpa [Nat.centralBinom_eq_two_mul_choose, mul_assoc] using hchoose
    _ = (2 : ℝ) ^ k * (k.factorial : ℝ) * (oddPairingNat k : ℝ) := hsplit
    _ = ((2 : ℝ) ^ k * (oddPairingNat k : ℝ)) * (k.factorial : ℝ) := by ring

/-- Exact integer form of the complex-sphere absolute-coordinate mean. -/
lemma sphereCoordinateAbsMean_eq_centralBinom
    (k : ℕ) (hk : 0 < k) :
    sphereCoordinateAbsMean k =
      (2 : ℝ) ^ (2 * k - 1) / ((k : ℝ) * Nat.centralBinom k) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  have hsqrt : Real.sqrt Real.pi ≠ 0 := Real.sqrt_ne_zero'.mpr Real.pi_pos
  have hfacm : (m.factorial : ℝ) ≠ 0 := by positivity
  have hodd : (oddPairingNat (m + 1) : ℝ) ≠ 0 := by
    exact_mod_cast oddPairingNat_pos (m + 1) |>.ne'
  have hcb : (Nat.centralBinom (m + 1) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.centralBinom_ne_zero (m + 1)
  have hrel := centralBinom_mul_factorial_eq_pow_mul_oddPairing (m + 1)
  have hgamma32 : Real.Gamma (3 / 2 : ℝ) = Real.sqrt Real.pi / 2 := by
    convert Real.Gamma_nat_add_half 1 using 1 <;>
      norm_num [Nat.doubleFactorial]
  have hgammak : Real.Gamma ((m + 1 : ℕ) : ℝ) = (m.factorial : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using Real.Gamma_nat_eq_factorial m
  have hgammakh : Real.Gamma (((m + 1 : ℕ) : ℝ) + 1 / 2) =
      (oddPairingNat (m + 1) : ℝ) * Real.sqrt Real.pi / 2 ^ (m + 1) := by
    rw [Real.Gamma_nat_add_half (m + 1)]
    rw [← oddPairingNat_eq_doubleFactorial]
  rw [sphereCoordinateAbsMean]
  simp only [Nat.one_add]
  change Real.Gamma (3 / 2 : ℝ) * Real.Gamma ((m + 1 : ℕ) : ℝ) /
      Real.Gamma (((m + 1 : ℕ) : ℝ) + 1 / 2) =
    (2 : ℝ) ^ (2 * (m + 1) - 1) /
      (((m + 1 : ℕ) : ℝ) * Nat.centralBinom (m + 1))
  rw [hgamma32, hgammak, hgammakh]
  have hfacSucc : (((m + 1).factorial : ℕ) : ℝ) =
      (m + 1 : ℝ) * (m.factorial : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  rw [hfacSucc] at hrel
  push_cast at hrel ⊢
  field_simp [hsqrt, hfacm, hodd, hcb]
  have hpow : 2 * (2 : ℝ) ^ (2 * (m + 1) - 1) =
      (2 : ℝ) ^ (2 * (m + 1)) := by
    calc
      2 * (2 : ℝ) ^ (2 * (m + 1) - 1) =
          (2 : ℝ) ^ (2 * (m + 1) - 1) * 2 := by ring
      _ = (2 : ℝ) ^ ((2 * (m + 1) - 1) + 1) := (pow_succ _ _).symm
      _ = (2 : ℝ) ^ (2 * (m + 1)) := by congr 1 <;> omega
  have hpow2 : (2 : ℝ) ^ (2 * (m + 1)) = ((2 : ℝ) ^ (m + 1)) ^ 2 := by
    rw [← pow_mul]
    congr 1
    omega
  calc
    (m.factorial : ℝ) * 2 ^ (m + 1) * (m + 1 : ℝ) *
          (Nat.centralBinom (m + 1) : ℝ) =
        2 ^ (m + 1) *
          ((Nat.centralBinom (m + 1) : ℝ) *
            ((m + 1 : ℝ) * (m.factorial : ℝ))) := by ring
    _ = 2 ^ (m + 1) * (2 ^ (m + 1) * (oddPairingNat (m + 1) : ℝ)) := by
      rw [hrel]
    _ = (oddPairingNat (m + 1) : ℝ) * (2 ^ (m + 1)) ^ 2 := by ring
    _ = (oddPairingNat (m + 1) : ℝ) * 2 ^ (2 * (m + 1)) := by rw [hpow2]
    _ = 2 * (oddPairingNat (m + 1) : ℝ) * 2 ^ (2 * (m + 1) - 1) := by
      rw [← hpow]
      ring

lemma angularBaseQ_cast_eq_inv_sphere_factor
    (k : ℕ) (hk : 0 < k) :
    (angularBaseQ k : ℝ) =
      ((k : ℝ) * sphereCoordinateAbsMean k ^ 2)⁻¹ := by
  rw [sphereCoordinateAbsMean_eq_centralBinom k hk]
  unfold angularBaseQ
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hcb : (Nat.centralBinom k : ℝ) ≠ 0 := by
    exact_mod_cast Nat.centralBinom_ne_zero k
  have hpow2 : (2 : ℝ) ^ (4 * k) = (16 : ℝ) ^ k := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, ← pow_mul]
  push_cast
  field_simp [hkR, hcb]
  calc
    4 * ((2 : ℝ) ^ (2 * k - 1)) ^ 2 = (2 : ℝ) ^ (4 * k) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add]
      congr 1
      omega
    _ = (16 : ℝ) ^ k := hpow2

lemma oddDimensionRatioQ_cast_eq_oddPairing_div_dimensionProduct
    (k n : ℕ) (hk : 0 < k) :
    (oddDimensionRatioQ k n : ℝ) =
      (oddPairingNat n : ℝ) / dimensionProduct k n := by
  unfold oddDimensionRatioQ oddPairingNat dimensionProduct
  push_cast
  rw [Finset.prod_div_distrib]

lemma wickSqrtMomentBound_eq_sphere_pow_mul_dimensionProduct
    (k n : ℕ) (hk : 0 < k) :
    wickSqrtMomentBound k n =
      sphereCoordinateAbsMean k ^ (2 * n - 1) * dimensionProduct k n := by
  rw [wickSqrtMomentBound]
  have hgamma := gammaRatio_half_eq_dimensionProduct k n hk
  have htwo : (1 / 2 : ℝ) ^ (-(n : ℝ)) = (2 : ℝ) ^ n := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
    rw [show (1 / 2 : ℝ) ^ n = ((2 : ℝ) ^ n)⁻¹ by
      rw [one_div, inv_pow]]
    simp
  rw [htwo] at hgamma
  calc
    sphereCoordinateAbsMean k ^ (2 * n - 1) * 2 ^ n *
          Real.Gamma (n + (k : ℝ) / 2) / Real.Gamma ((k : ℝ) / 2) =
        sphereCoordinateAbsMean k ^ (2 * n - 1) *
          (2 ^ n * Real.Gamma ((k : ℝ) / 2 + n) /
            Real.Gamma ((k : ℝ) / 2)) := by ring
    _ = sphereCoordinateAbsMean k ^ (2 * n - 1) * dimensionProduct k n := by
      rw [hgamma]

/-- Exact identification of the rational certificate with the multiplicative
ratio produced by the literal Wick moment argument. -/
theorem wickScalarRatioQ_cast_eq_wickAngularRatio
    (k n : ℕ) (hk : 0 < k) :
    (wickScalarRatioQ k n : ℝ) = wickAngularRatio k n := by
  rw [wickScalarRatioQ, Rat.cast_mul, Rat.cast_pow,
    oddDimensionRatioQ_cast_eq_oddPairing_div_dimensionProduct k n hk,
    angularBaseQ_cast_eq_inv_sphere_factor k hk]
  rw [wickAngularRatio, wickSqrtMomentBound_eq_sphere_pow_mul_dimensionProduct k n hk]
  rw [closedFirstMoment]
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hdim : dimensionProduct k n ≠ 0 := (dimensionProduct_pos k n hk).ne'
  have hmu : sphereCoordinateAbsMean k ≠ 0 := by
    rw [sphereCoordinateAbsMean_eq_centralBinom k hk]
    exact div_ne_zero (pow_ne_zero _ (by norm_num))
      (mul_ne_zero hkR (by exact_mod_cast Nat.centralBinom_ne_zero k))
  rw [inv_pow]
  field_simp [hkR, hdim, hmu]
  ring

/-- Paper-facing scalar endpoint, now stated for the actual moment-reduction
ratio rather than for an auxiliary rational expression. -/
theorem exp_n_div_500_le_wickAngularRatio
    {k n : ℕ} (hn : 1000 ≤ n) (hklo : 2 ≤ k) (hkhi : 3 * k ≤ n) :
    Real.exp ((n : ℝ) / 500) ≤ wickAngularRatio k n := by
  rw [← wickScalarRatioQ_cast_eq_wickAngularRatio k n (by omega)]
  exact exp_n_div_500_le_wickScalarRatioQ hn hklo hkhi

end

end LogdetLean.GramHafnian.WickAngularLowerBound
