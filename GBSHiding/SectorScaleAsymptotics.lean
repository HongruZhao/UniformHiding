import GBSHiding.OptimalPhotonSector
import Mathlib.Analysis.Asymptotics.Theta

/-! Explicit relative Stirling error and the finite-population factor. -/
open scoped BigOperators
open MeasureTheory Set Filter Real Asymptotics
open LogdetLean.GramHafnian
open LogdetLean.GramHafnian.LocalAnticoncentration
open LogdetLean.GramHafnian.ThreePaper.RelativeAccuracy

namespace GBSHiding
noncomputable section
set_option maxHeartbeats 2400000

def sectorGaussianDenominator (K n : ℕ) : ℝ :=
  Real.sqrt (2*Real.pi*(n:ℝ)*(1+2*(n:ℝ)/K))

/-- A finite-n version of the paper's uniform relative O(1/n) estimate. -/
theorem proposition4_1_uniform_relative_error (K n : ℕ) (hn : 0 < n) (hK : 4*n ≤ K) :
    |optimalPairMass ((K:ℝ)/2) n * sectorGaussianDenominator K n - 1| ≤
      2/(3*(n:ℝ)) := by
  have hk : 0 < K := by omega
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hnr : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hp : 0 < optimalPairMass ((K:ℝ)/2) n :=
    pairMass_pos (by positivity) (optimalParameter_mem (by positivity) hn) n
  have hD : 0 < 2*Real.pi*(n:ℝ)*(1+2*(n:ℝ)/K) := by positivity
  have hs : 0 < sectorGaussianDenominator K n := Real.sqrt_pos.mpr hD
  have hlog : Real.log (optimalPairMass ((K:ℝ)/2) n * sectorGaussianDenominator K n) =
      Real.log (optimalPairMass ((K:ℝ)/2) n) +
      Real.log (2*Real.pi*(n:ℝ)*(1+2*(n:ℝ)/K))/2 := by
    rw [Real.log_mul hp.ne' hs.ne']
    unfold sectorGaussianDenominator
    rw [Real.log_sqrt hD.le]
  have hb := proposition4_1_uniform_log_error K n hn hK
  rw [← hlog] at hb
  have hb1 : |Real.log (optimalPairMass ((K:ℝ)/2) n * sectorGaussianDenominator K n)| ≤ 1 := by
    apply hb.trans
    exact (div_le_one (by positivity)).mpr (by linarith)
  have hh := Real.abs_exp_sub_one_le hb1
  rw [Real.exp_log (mul_pos hp hs)] at hh
  calc
    _ ≤ 2 * |Real.log (optimalPairMass ((K:ℝ)/2) n * sectorGaussianDenominator K n)| := hh
    _ ≤ 2 * (1/(3*(n:ℝ))) := by gcongr
    _ = _ := by ring

theorem product_one_sub_bounds {ι : Type*} (s : Finset ι) (u : ι → ℝ)
    (hu : ∀ i ∈ s, u i ∈ Icc 0 1) :
    0 ≤ ∏ i ∈ s, (1-u i) ∧ (∏ i ∈ s, (1-u i)) ≤ 1 ∧
      1 - (∑ i ∈ s, u i) ≤ ∏ i ∈ s, (1-u i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s his ih =>
    have hui := hu i (Finset.mem_insert_self _ _)
    have hus := fun j hj ↦ hu j (Finset.mem_insert_of_mem hj)
    have h := ih hus
    rw [Finset.prod_insert his, Finset.sum_insert his]
    have hs : 0 ≤ ∑ j ∈ s, u j := Finset.sum_nonneg (fun j hj ↦ (hus j hj).1)
    have hm := mul_le_mul_of_nonneg_left h.2.2 (sub_nonneg.mpr hui.2)
    exact ⟨mul_nonneg (sub_nonneg.mpr hui.2) h.1, by nlinarith [hui.1],
      by nlinarith [mul_nonneg hui.1 hs]⟩

/-- The finite-population error used in the Theta conclusion. -/
theorem finitePopulationFactor_bounds (M N : ℕ) (hM : 0 < M) (hNM : N ≤ M) :
    0 ≤ finitePopulationFactor M N ∧ finitePopulationFactor M N ≤ 1 ∧
      1 - (N:ℝ)^2/M ≤ finitePopulationFactor M N := by
  have hm : (0:ℝ) < M := by exact_mod_cast hM
  have hu : ∀ j ∈ Finset.range N, (j:ℝ)/(M:ℝ) ∈ Icc 0 1 := by
    intro j hj
    have hjM : j ≤ M := by have := Finset.mem_range.mp hj; omega
    exact ⟨by positivity, (div_le_one hm).mpr (by exact_mod_cast hjM)⟩
  have h := product_one_sub_bounds (Finset.range N) (fun j ↦ (j:ℝ)/M) hu
  have hsum : (∑ j ∈ Finset.range N, (j:ℝ)/M) ≤ (N:ℝ)^2/M := by
    calc
      _ ≤ ∑ _j ∈ Finset.range N, (N:ℝ)/M := by
        apply Finset.sum_le_sum
        intro j hj
        apply div_le_div_of_nonneg_right _ hm.le
        exact_mod_cast (Finset.mem_range.mp hj).le
      _ = _ := by simp; ring
  exact ⟨h.1, h.2.1, (sub_le_sub_left hsum 1).trans h.2.2⟩

theorem finitePopulationFactor_tendsto_one (M N : ℕ → ℕ)
    (hM : ∀ᶠ j in atTop, 0 < M j) (hNM : ∀ᶠ j in atTop, N j ≤ M j)
    (hscale : Tendsto (fun j ↦ (N j:ℝ)^2/(M j:ℝ)) atTop (nhds 0)) :
    Tendsto (fun j ↦ finitePopulationFactor (M j) (N j)) atTop (nhds 1) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (g := fun j ↦ 1-(N j:ℝ)^2/(M j:ℝ)) (h := fun _j ↦ (1:ℝ))
  · simpa using (tendsto_const_nhds (x := (1:ℝ))).sub hscale
  · exact tendsto_const_nhds
  · filter_upwards [hM,hNM] with j hm hn
    exact (finitePopulationFactor_bounds _ _ hm hn).2.2
  · filter_upwards [hM,hNM] with j hm hn
    exact (finitePopulationFactor_bounds _ _ hm hn).2.1

/-- Uniform relative Stirling error along every admissible K(n). -/
theorem proposition4_1_stirling_isBigO (K : ℕ → ℕ)
    (hK : ∀ᶠ n in atTop, 4*n ≤ K n) :
    (fun n ↦ optimalPairMass ((K n:ℝ)/2) n * sectorGaussianDenominator (K n) n - 1)
      =O[atTop] (fun n ↦ 1/(n:ℝ)) := by
  apply IsBigO.of_bound (2/3 : ℝ)
  filter_upwards [hK,eventually_ge_atTop 1] with n hKn hn
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 1/(n:ℝ))]
  convert proposition4_1_uniform_relative_error (K n) n hn hKn using 1 <;> ring

theorem sectorGaussianDenominator_bounds (K n : ℕ) (hn : 0 < n) (hK : 4*n ≤ K) :
    Real.sqrt (2*(n:ℝ)) ≤ sectorGaussianDenominator K n ∧
      sectorGaussianDenominator K n ≤ 4*Real.sqrt (2*(n:ℝ)) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hk : (0:ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hkr : 4*(n:ℝ) ≤ K := by exact_mod_cast hK
  have hr0 : 0 ≤ 2*(n:ℝ)/K := by positivity
  have hr1 : 2*(n:ℝ)/K ≤ 1 := (div_le_one hk).mpr (by linarith)
  have hs := Real.sq_sqrt (by positivity : 0 ≤ 2*(n:ℝ))
  have hd := Real.sq_sqrt (by positivity : 0 ≤ 2*Real.pi*(n:ℝ)*(1+2*(n:ℝ)/K))
  have hlo : 2*(n:ℝ) ≤ 2*Real.pi*(n:ℝ)*(1+2*(n:ℝ)/K) := by
    calc
      _ ≤ 2*Real.pi*(n:ℝ) := by nlinarith [Real.pi_gt_three]
      _ ≤ _ := by nlinarith [mul_nonneg (by positivity : 0 ≤ 2*Real.pi*(n:ℝ)) hr0]
  have hhi : 2*Real.pi*(n:ℝ)*(1+2*(n:ℝ)/K) ≤ 16*(n:ℝ) := by
    calc
      _ ≤ 2*Real.pi*(n:ℝ)*2 := by gcongr; linarith
      _ ≤ _ := by nlinarith [Real.pi_lt_four]
  unfold sectorGaussianDenominator
  constructor
  · nlinarith [Real.sqrt_nonneg (2*(n:ℝ)),
      Real.sqrt_nonneg (2*Real.pi*(n:ℝ)*(1+2*(n:ℝ)/K))]
  · nlinarith [Real.sqrt_nonneg (2*(n:ℝ)),
      Real.sqrt_nonneg (2*Real.pi*(n:ℝ)*(1+2*(n:ℝ)/K))]

theorem optimalPairMass_isTheta (K : ℕ → ℕ)
    (hK : ∀ᶠ n in atTop, 4*n ≤ K n) :
    (fun n ↦ optimalPairMass ((K n:ℝ)/2) n) =Θ[atTop]
      (fun n ↦ 1 / Real.sqrt (2*(n:ℝ))) := by
  let W := fun n ↦ optimalPairMass ((K n:ℝ)/2) n
  let D := fun n ↦ sectorGaussianDenominator (K n) n
  have hq : (fun n ↦ W n * D n) =Θ[atTop] (fun _n ↦ (1:ℝ)) := by
    have hb : ∀ᶠ n in atTop, (1:ℝ)/3 ≤ W n * D n ∧ W n * D n ≤ 2 := by
      filter_upwards [hK,eventually_ge_atTop 1] with n hk hn
      have h := proposition4_1_uniform_relative_error (K n) n hn hk
      have hnr : (1:ℝ) ≤ n := by exact_mod_cast hn
      have he : 2/(3*(n:ℝ)) ≤ 2/3 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
        linarith
      have hh := abs_le.mp (h.trans he)
      change (1:ℝ)/3 ≤ optimalPairMass ((K n:ℝ)/2) n * sectorGaussianDenominator (K n) n ∧ _
      constructor <;> linarith [hh.1,hh.2]
    constructor
    · apply IsBigO.of_bound 2
      filter_upwards [hb] with n hn
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_one,
        abs_of_nonneg (by linarith [hn.1] : 0 ≤ W n*D n), mul_one]
      exact hn.2
    · apply IsBigO.of_bound 3
      filter_upwards [hb] with n hn
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_one,
        abs_of_nonneg (by linarith [hn.1] : 0 ≤ W n*D n)]
      linarith [hn.1]
  have hd : D =Θ[atTop] (fun n ↦ Real.sqrt (2*(n:ℝ))) := by
    constructor
    · apply IsBigO.of_bound 4
      filter_upwards [hK,eventually_ge_atTop 1] with n hk hn
      simpa [D, sectorGaussianDenominator, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _)] using (sectorGaussianDenominator_bounds (K n) n hn hk).2
    · apply IsBigO.of_bound 1
      filter_upwards [hK,eventually_ge_atTop 1] with n hk hn
      simpa [D, sectorGaussianDenominator, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _)] using (sectorGaussianDenominator_bounds (K n) n hn hk).1
  have h := hq.div hd
  apply Filter.EventuallyEq.trans_isTheta _ h
  filter_upwards [hK,eventually_ge_atTop 1] with n hk hn
  have hp : 0 < D n := by
    have := (sectorGaussianDenominator_bounds (K n) n hn hk).1
    have hs : 0 < Real.sqrt (2*(n:ℝ)) := Real.sqrt_pos.mpr (by positivity)
    exact hs.trans_le this
  exact (mul_div_cancel_right₀ (W n) hp.ne').symm

/-- Final conclusion of Proposition 4.1, with the literal photon count N=2n.
Only the reference probability is used; no collision-suppression claim is made. -/
theorem proposition4_1_reference_scale_isTheta
    (M K : ℕ → ℕ) (r : ℕ → ℝ)
    (hK : ∀ᶠ n in atTop, 4*n ≤ K n)
    (hNM : ∀ᶠ n in atTop, 2*n ≤ M n)
    (hmatch : ∀ᶠ n in atTop, (K n:ℝ)*Real.sinh (r n)^2 = 2*(n:ℝ))
    (hscale : Tendsto (fun n : ℕ ↦ (2*(n:ℝ))^2/(M n:ℝ)) atTop (nhds 0)) :
    (fun n ↦ (Nat.choose (M n) (2*n):ℝ) * gbsGaussianReferenceProbability (r n) (M n) (K n) n)
      =Θ[atTop] (fun n ↦ 1 / Real.sqrt (2*(n:ℝ))) := by
  have hM : ∀ᶠ n in atTop, 0 < M n := by
    filter_upwards [hNM,eventually_ge_atTop 1] with n hnm hn
    omega
  have hf := finitePopulationFactor_tendsto_one M (fun n ↦ 2*n) hM hNM
    (by simpa using hscale)
  have ht : (fun n ↦ finitePopulationFactor (M n) (2*n)) =Θ[atTop] (fun _n ↦ (1:ℝ)) :=
    (isTheta_of_div_tendsto_nhds_ne_zero
      (f := fun _n ↦ (1:ℝ)) (g := fun n ↦ finitePopulationFactor (M n) (2*n))
      (by simpa using hf) one_ne_zero).symm
  have h := (optimalPairMass_isTheta K hK).mul ht
  have he : (fun n ↦ (Nat.choose (M n) (2*n):ℝ) *
      gbsGaussianReferenceProbability (r n) (M n) (K n) n) =ᶠ[atTop]
      (fun n ↦ optimalPairMass ((K n:ℝ)/2) n * finitePopulationFactor (M n) (2*n)) := by
    filter_upwards [hK,hNM,hmatch,hM,eventually_ge_atTop 1] with n hk hnm hr hm hn
    rw [proposition4_1_reference_scale _ _ _ hm hnm (by omega),
      sectorWeight_at_mean_match _ _ (by omega) _ hr]
  simpa using he.trans_isTheta h

end
end GBSHiding
