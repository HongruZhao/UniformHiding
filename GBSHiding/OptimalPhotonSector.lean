import GBSHiding.PhotonSector
import GBSHiding.SectorStirling
import Mathlib.Analysis.SpecialFunctions.Arsinh

/-! The maximizing squeezing and the uniform sector estimate in Proposition 4.1. -/
open scoped BigOperators
open MeasureTheory Set Filter Real
open LogdetLean.GramHafnian
open LogdetLean.GramHafnian.LocalAnticoncentration
open LogdetLean.GramHafnian.ThreePaper.RelativeAccuracy

namespace GBSHiding
noncomputable section
set_option maxHeartbeats 2400000

def optimalPairMass (a : ℝ) (n : ℕ) : ℝ := pairMass a ((n:ℝ)/(a+n)) n

theorem optimalParameter_mem {a : ℝ} (ha : 0 < a) {n : ℕ} (hn : 0 < n) :
    (n:ℝ)/(a+n) ∈ Ioo 0 1 := by
  have hnr : (0:ℝ) < n := by exact_mod_cast hn
  constructor
  · exact div_pos hnr (add_pos ha hnr)
  · exact (div_lt_one (add_pos ha hnr)).mpr (by linarith)

theorem pairMass_pos {a x : ℝ} (ha : 0 < a) (hx : x ∈ Ioo 0 1) (n : ℕ) :
    0 < pairMass a x n := by
  unfold pairMass
  exact mul_pos (mul_pos (pairCoefficient_pos ha _) (pow_pos hx.1 _))
    (Real.rpow_pos_of_pos (sub_pos.mpr hx.2) a)

theorem log_pairMass {a x : ℝ} (ha : 0 < a) (hx : x ∈ Ioo 0 1) (n : ℕ) :
    Real.log (pairMass a x n) = Real.log (pairCoefficient a n) +
      n * Real.log x + a * Real.log (1-x) := by
  unfold pairMass
  rw [Real.log_mul (mul_pos (pairCoefficient_pos ha _) (pow_pos hx.1 _)).ne'
    (Real.rpow_pos_of_pos (sub_pos.mpr hx.2) a).ne',
    Real.log_mul (pairCoefficient_pos ha _).ne' (pow_pos hx.1 _).ne',
    Real.log_pow, Real.log_rpow (sub_pos.mpr hx.2)]

/-- Global maximum on the entire physical interval, proved using
`log u ≤ u-1` for both factors. -/
theorem pairMass_le_optimal {a x : ℝ} (ha : 0 < a)
    (hx : x ∈ Ioo 0 1) {n : ℕ} (hn : 0 < n) :
    pairMass a x n ≤ optimalPairMass a n := by
  let y : ℝ := (n:ℝ)/(a+n)
  have hy : y ∈ Ioo 0 1 := optimalParameter_mem ha hn
  have hnr : (0:ℝ) < n := by exact_mod_cast hn
  have h1 := Real.log_le_sub_one_of_pos (div_pos hx.1 hy.1)
  have h2 := Real.log_le_sub_one_of_pos
    (div_pos (sub_pos.mpr hx.2) (sub_pos.mpr hy.2))
  rw [Real.log_div hx.1.ne' hy.1.ne'] at h1
  rw [Real.log_div (sub_pos.mpr hx.2).ne' (sub_pos.mpr hy.2).ne'] at h2
  have h1' := mul_le_mul_of_nonneg_left h1 hnr.le
  have h2' := mul_le_mul_of_nonneg_left h2 ha.le
  have heq : (n:ℝ)*(x/y-1) + a*((1-x)/(1-y)-1) = 0 := by
    dsimp [y]
    field_simp [ha.ne', hnr.ne']
    <;> ring
  have hl : Real.log (pairMass a x n) ≤ Real.log (pairMass a y n) := by
    rw [log_pairMass ha hx, log_pairMass ha hy]
    nlinarith
  exact (Real.log_le_log_iff (pairMass_pos ha hx _) (pairMass_pos ha hy _)).mp hl

/-- The maximizing physical parameter is unique. -/
theorem pairMass_lt_optimal_of_ne {a x : ℝ} (ha : 0 < a)
    (hx : x ∈ Ioo 0 1) {n : ℕ} (hn : 0 < n)
    (hne : x ≠ (n:ℝ)/(a+n)) : pairMass a x n < optimalPairMass a n := by
  let y : ℝ := (n:ℝ)/(a+n)
  have hy : y ∈ Ioo 0 1 := optimalParameter_mem ha hn
  have hnr : (0:ℝ) < n := by exact_mod_cast hn
  have hne' : x/y ≠ 1 := by
    intro hh
    exact hne ((div_eq_one_iff_eq hy.1.ne').mp hh)
  have h1 := Real.log_lt_sub_one_of_pos (div_pos hx.1 hy.1) hne'
  have h2 := Real.log_le_sub_one_of_pos
    (div_pos (sub_pos.mpr hx.2) (sub_pos.mpr hy.2))
  rw [Real.log_div hx.1.ne' hy.1.ne'] at h1
  rw [Real.log_div (sub_pos.mpr hx.2).ne' (sub_pos.mpr hy.2).ne'] at h2
  have h1' := mul_lt_mul_of_pos_left h1 hnr
  have h2' := mul_le_mul_of_nonneg_left h2 ha.le
  have heq : (n:ℝ)*(x/y-1) + a*((1-x)/(1-y)-1) = 0 := by
    dsimp [y]
    field_simp [ha.ne', hnr.ne']
    ring
  have hl : Real.log (pairMass a x n) < Real.log (pairMass a y n) := by
    rw [log_pairMass ha hx, log_pairMass ha hy]
    linarith
  exact (Real.log_lt_log_iff (pairMass_pos ha hx _) (pairMass_pos ha hy _)).mp hl

theorem pairMass_eq_optimal_iff {a x : ℝ} (ha : 0 < a)
    (hx : x ∈ Ioo 0 1) {n : ℕ} (hn : 0 < n) :
    pairMass a x n = optimalPairMass a n ↔ x = (n:ℝ)/(a+n) := by
  constructor
  · intro h
    by_contra hne
    exact (pairMass_lt_optimal_of_ne ha hx hn hne).ne h
  · rintro rfl
    rfl

theorem squeezing_mean_match_iff (K n : ℕ) (hK : 0 < K) (r : ℝ) :
    Real.tanh r^2 = (2*n:ℝ)/((K:ℝ)+2*n) ↔ (K:ℝ)*Real.sinh r^2 = 2*n := by
  have hk : (0:ℝ) < K := by exact_mod_cast hK
  have hc := (Real.cosh_pos r).ne'
  have hden : (K:ℝ)+2*n ≠ 0 := by positivity
  rw [Real.tanh_eq_sinh_div_cosh, div_pow]
  rw [div_eq_div_iff (pow_ne_zero _ hc) hden]
  have h := Real.cosh_sq_sub_sinh_sq r
  constructor <;> intro hh <;> nlinarith

theorem sectorWeight_at_mean_match (K n : ℕ) (hK : 0 < K) (r : ℝ)
    (hmatch : (K:ℝ)*Real.sinh r^2 = 2*n) :
    sectorWeight K n r = optimalPairMass ((K:ℝ)/2) n := by
  rw [sectorWeight_eq_pairMass, (squeezing_mean_match_iff K n hK r).mpr hmatch]
  unfold optimalPairMass
  congr 1
  field_simp
  <;> ring

/-- The squeezing value stated in Proposition 4.1 maximizes the sector
mass over positive squeezing. -/
theorem proposition4_1_maximizer (K n : ℕ) (hK : 0 < K) (hn : 0 < n)
    (r rstar : ℝ) (hr : 0 < r)
    (hmatch : (K:ℝ)*Real.sinh rstar^2 = 2*n) :
    sectorWeight K n r ≤ sectorWeight K n rstar := by
  have htanh : 0 < Real.tanh r := by
    simpa [equalSqueezingOpticalPrefactor] using equalSqueezingOpticalPrefactor_pos hr 1 0
  rw [sectorWeight_eq_pairMass, sectorWeight_at_mean_match K n hK rstar hmatch]
  exact pairMass_le_optimal (by positivity) ⟨sq_pos_of_pos htanh, Real.tanh_sq_lt_one r⟩ hn

/-- An explicit real squeezing choice satisfying the optimum equation. -/
theorem meanMatchedSqueezing (K n : ℕ) (hK : 0 < K) :
    (K:ℝ) * Real.sinh (Real.arsinh (Real.sqrt ((2*n:ℝ)/K)))^2 = 2*n := by
  rw [Real.sinh_arsinh, Real.sq_sqrt (by positivity)]
  have hk : (K:ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  field_simp

/-- The exact logarithmic cancellation of the three Gamma factors. -/
theorem log_optimalPairMass {a : ℝ} (ha : 0 < a) {n : ℕ} (hn : 0 < n) :
    Real.log (optimalPairMass a n) =
      -(Real.log (2*Real.pi*(n:ℝ)*(1+(n:ℝ)/a)))/2 +
        (logGammaStirlingError (a+n) - logGammaStirlingError a - logGammaStirlingError n) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have han : 0 < a+n := by positivity
  have h1 : 0 < 1+(n:ℝ)/a := by positivity
  have hrem : 1 - (n:ℝ)/(a+n) = a/(a+n) := by field_simp; ring
  have hratio : 1+(n:ℝ)/a = (a+n)/a := by field_simp
  unfold optimalPairMass
  rw [log_pairMass ha (optimalParameter_mem ha hn), pairCoefficient_eq_gamma ha n,
    Real.log_div (Real.Gamma_pos_of_pos han).ne'
      (mul_pos (Real.Gamma_pos_of_pos ha) (Real.Gamma_pos_of_pos (by positivity))).ne',
    Real.log_mul (Real.Gamma_pos_of_pos ha).ne' (Real.Gamma_pos_of_pos (by positivity)).ne',
    Real.Gamma_add_one hnR.ne', Real.log_mul hnR.ne' (Real.Gamma_pos_of_pos hnR).ne',
    hrem, Real.log_div hnR.ne' han.ne', Real.log_div ha.ne' han.ne']
  unfold logGammaStirlingError
  rw [Real.log_mul (mul_pos (by positivity : 0 < 2*Real.pi) hnR).ne' h1.ne',
    Real.log_mul (by positivity : (2*Real.pi) ≠ 0) hnR.ne',
    hratio, Real.log_div han.ne' ha.ne']
  ring

/-- An explicit uniform logarithmic error for the paper's Stirling
approximation. In particular it covers every odd and even K ≥ 4n. -/
theorem proposition4_1_uniform_log_error (K n : ℕ) (hn : 0 < n) (hK : 4*n ≤ K) :
    |Real.log (optimalPairMass ((K:ℝ)/2) n) +
      Real.log (2*Real.pi*(n:ℝ)*(1+2*(n:ℝ)/K))/2| ≤ 1/(3*(n:ℝ)) := by
  have hk : 0 < K := by omega
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hkR : (0:ℝ) < K := by exact_mod_cast hk
  have hKn : 4*(n:ℝ) ≤ K := by exact_mod_cast hK
  rw [log_optimalPairMass (by positivity) hn]
  have heq : (n:ℝ)/((K:ℝ)/2) = 2*(n:ℝ)/K := by field_simp
  rw [heq]
  have h1 := logGammaStirlingError_halfNat_bound (K+2*n) (by omega)
  have h2 := logGammaStirlingError_halfNat_bound K hk
  have h3 := logGammaStirlingError_nat_bound n hn
  have hcast : ((K+2*n:ℕ):ℝ)/2 = (K:ℝ)/2+n := by push_cast; ring
  rw [hcast] at h1
  have hsum := (abs_sub (logGammaStirlingError ((K:ℝ)/2+n) - logGammaStirlingError ((K:ℝ)/2))
    (logGammaStirlingError n)).trans (add_le_add (abs_sub _ _) le_rfl)
  have hb := hsum.trans (add_le_add (add_le_add h1 h2) h3)
  have hK2 : (0:ℝ) < K+2*n := by positivity
  have hc1 : 1/(2*((K+2*n:ℕ):ℝ)) ≤ 1/(8*(n:ℝ)) := by
    apply one_div_le_one_div_of_le (by positivity)
    push_cast
    linarith
  have hc2 : 1/(2*(K:ℝ)) ≤ 1/(8*(n:ℝ)) := by
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  have hc : 1/(2*((K+2*n:ℕ):ℝ)) + 1/(2*(K:ℝ)) + 1/(12*(n:ℝ)) ≤ 1/(3*(n:ℝ)) := by
    calc
      _ ≤ 1/(8*(n:ℝ)) + 1/(8*(n:ℝ)) + 1/(12*(n:ℝ)) := by linarith
      _ = _ := by field_simp <;> ring
  convert hb.trans hc using 1 <;> congr 1 <;> ring

end
end GBSHiding
