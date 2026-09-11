import LogdetLean.ElementaryNormalization
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-! Explicit Stirling remainders at integers and half-integers.
These cover every integer input count K, including odd K. -/
open Filter Set Real
namespace GBSHiding
noncomputable section
set_option maxHeartbeats 2000000

def logGammaStirlingError (x : ℝ) : ℝ :=
  Real.log (Real.Gamma x) - (x - 1/2) * Real.log x + x - Real.log (2 * Real.pi) / 2

theorem logStirlingSeq_error_bound (n : ℕ) (hn : 0 < n) :
    |Real.log (Stirling.stirlingSeq n) - Real.log (Real.sqrt Real.pi)| ≤
      1 / (12 * (n : ℝ)) := by
  have ht := ((Stirling.tendsto_stirlingSeq_sqrt_pi.log
    (Real.sqrt_pos.mpr Real.pi_pos).ne').const_sub (Real.log (Stirling.stirlingSeq n))).abs
  apply le_of_tendsto ht
  filter_upwards [eventually_ge_atTop n] with m hm
  simpa [abs_sub_comm] using LogdetLean.abs_log_stirlingSeq_sub_le_inv_gap hn hm

theorem logGammaStirlingError_nat (n : ℕ) (hn : 0 < n) :
    logGammaStirlingError n =
      Real.log (Stirling.stirlingSeq n) - Real.log (Real.sqrt Real.pi) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hg := Real.Gamma_add_one hnR.ne'
  rw [Real.Gamma_nat_eq_factorial] at hg
  have hl := congrArg Real.log hg
  rw [Real.log_mul hnR.ne' (Real.Gamma_pos_of_pos hnR).ne'] at hl
  have hf := LogdetLean.log_factorial_eq_stirling_decomposition hn
  unfold logGammaStirlingError
  rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) Real.pi_ne_zero,
    Real.log_sqrt Real.pi_pos.le]
  linarith

theorem logGammaStirlingError_nat_bound (n : ℕ) (hn : 0 < n) :
    |logGammaStirlingError n| ≤ 1 / (12 * (n : ℝ)) := by
  rw [logGammaStirlingError_nat n hn]
  exact logStirlingSeq_error_bound n hn

theorem logGammaStirlingError_duplication {x : ℝ} (hx : 0 < x) :
    logGammaStirlingError x = logGammaStirlingError (2*x) -
      logGammaStirlingError (x+1/2) +
      (1/2 - x * Real.log (1 + 1/(2*x))) := by
  have hy : 0 < x+1/2 := by linarith
  have h2x : 0 < 2*x := by positivity
  have hd := congrArg Real.log (Real.Gamma_mul_Gamma_add_half x)
  rw [Real.log_mul (Real.Gamma_pos_of_pos hx).ne' (Real.Gamma_pos_of_pos hy).ne',
    Real.log_mul (mul_pos (Real.Gamma_pos_of_pos h2x)
      (Real.rpow_pos_of_pos (by norm_num) _)).ne' (Real.sqrt_pos.mpr Real.pi_pos).ne',
    Real.log_mul (Real.Gamma_pos_of_pos h2x).ne'
      (Real.rpow_pos_of_pos (by norm_num) _).ne',
    Real.log_rpow (by norm_num : (0:ℝ) < 2), Real.log_sqrt Real.pi_pos.le] at hd
  have hquot : 1 + 1/(2*x) = (x+1/2)/x := by field_simp
  unfold logGammaStirlingError
  rw [hquot, Real.log_div hy.ne' hx.ne',
    Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hx.ne',
    Real.log_mul (by norm_num : (2:ℝ) ≠ 0) Real.pi_ne_zero]
  linarith

theorem duplication_correction_bounds {x : ℝ} (hx : 0 < x) :
    0 ≤ 1/2 - x * Real.log (1+1/(2*x)) ∧
      1/2 - x * Real.log (1+1/(2*x)) ≤ 1/(8*x) := by
  have ht : 0 ≤ 1/(2*x) := by positivity
  have hlo := LogdetLean.sub_half_sq_le_log_one_add ht
  have hhi := Real.log_le_sub_one_of_pos (by positivity : 0 < 1+1/(2*x))
  have he : x * (1/(2*x)) = 1/2 := by field_simp
  have he2 : x * ((1/(2*x))^2/2) = 1/(8*x) := by field_simp; ring
  have hlom := mul_le_mul_of_nonneg_left hlo hx.le
  have hhim := mul_le_mul_of_nonneg_left hhi hx.le
  rw [mul_sub, he, he2] at hlom
  have hhim' : x * Real.log (1+1/(2*x)) ≤ 1/2 := by
    calc
      _ ≤ x * (1+1/(2*x)-1) := hhim
      _ = 1/2 := by nlinarith [he]
  constructor <;> linarith

theorem logGammaStirlingError_half_bound (m : ℕ) :
    |logGammaStirlingError ((m:ℝ)+1/2)| ≤ 1/(4*((m:ℝ)+1/2)) := by
  let x : ℝ := m+1/2
  have hx : 0 < x := by dsimp [x]; positivity
  have hz : 2*x = ((2*m+1 : ℕ):ℝ) := by dsimp [x]; push_cast; ring
  have hy : x+1/2 = ((m+1 : ℕ):ℝ) := by dsimp [x]; push_cast; ring
  have hb1 := logGammaStirlingError_nat_bound (2*m+1) (by omega)
  have hb2 := logGammaStirlingError_nat_bound (m+1) (by omega)
  rw [← hz] at hb1
  rw [← hy] at hb2
  have hc := duplication_correction_bounds hx
  change |logGammaStirlingError x| ≤ 1/(4*x)
  rw [logGammaStirlingError_duplication hx]
  calc
    _ ≤ |logGammaStirlingError (2*x)| + |logGammaStirlingError (x+1/2)| +
        |1/2-x*Real.log (1+1/(2*x))| :=
      (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ 1/(12*(2*x)) + 1/(12*(x+1/2)) + 1/(8*x) := by
      rw [abs_of_nonneg hc.1]
      exact add_le_add (add_le_add hb1 hb2) hc.2
    _ ≤ 1/(4*x) := by
      have hi : 1/(12*(x+1/2)) ≤ 1/(12*x) := by
        apply one_div_le_one_div_of_le (by positivity)
        linarith
      calc
        _ ≤ 1/(12*(2*x)) + 1/(12*x) + 1/(8*x) := by linarith
        _ = _ := by field_simp; ring

/-- Uniform bound at shape K/2 for every positive integer K. -/
theorem logGammaStirlingError_halfNat_bound (K : ℕ) (hK : 0 < K) :
    |logGammaStirlingError ((K:ℝ)/2)| ≤ 1/(2*(K:ℝ)) := by
  by_cases he : K % 2 = 0
  · have hnat : K = 2*(K/2) := by omega
    have hn : 0 < K/2 := by omega
    have heq : (K:ℝ)/2 = (K/2 : ℕ) := by
      have hh : (K:ℝ) = 2*((K/2:ℕ):ℝ) := by exact_mod_cast hnat
      linarith
    have h := logGammaStirlingError_nat_bound (K/2) hn
    rw [heq]
    have hkR : (0:ℝ) < K := by exact_mod_cast hK
    have hnR : ((K/2 : ℕ):ℝ) = (K:ℝ)/2 := heq.symm
    rw [hnR] at h ⊢
    calc
      _ ≤ 1/(12*((K:ℝ)/2)) := h
      _ ≤ _ := by apply one_div_le_one_div_of_le (by positivity); linarith
  · have hnat : K = 2*(K/2)+1 := by omega
    have heq : (K:ℝ)/2 = ((K/2 : ℕ):ℝ)+1/2 := by
      have hh : (K:ℝ) = 2*((K/2:ℕ):ℝ)+1 := by exact_mod_cast hnat
      linarith
    have h := logGammaStirlingError_half_bound (K/2)
    rw [← heq] at h
    convert h using 1 <;> congr 1 <;> ring

end
end GBSHiding
