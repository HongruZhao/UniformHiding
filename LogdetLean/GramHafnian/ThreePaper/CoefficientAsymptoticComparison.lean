import LogdetLean.GramHafnian.ThreePaper.TwoMethodComparison

/-!
# Sequence-level coefficient asymptotics for the manuscript comparison

This module supplies literal sequence-level endpoints for the three
coefficient estimates used in the Route-1/Route-2 comparison.  The ambient
matrix size is `N_j = 2 n_j`.  No random-matrix assertion is introduced.
-/

open Filter
open scoped BigOperators Topology

namespace LogdetLean.GramHafnian.ThreePaper.TwoMethodComparison

noncomputable section

open LocalAnticoncentration

/-- Exact arithmetic sum in the exponential envelope for `R_{K,n}`. -/
theorem sum_Icc_two_two_mul_sub_two
    (n : ℕ) (hn : 1 ≤ n) :
    (∑ r ∈ Finset.Icc 2 n, (2 * (r : ℝ) - 2)) =
      (n : ℝ) ^ 2 - (n : ℝ) := by
  let P : ∀ j : ℕ, 1 ≤ j → Prop := fun j _ ↦
    (∑ r ∈ Finset.Icc 2 j, (2 * (r : ℝ) - 2)) =
      (j : ℝ) ^ 2 - (j : ℝ)
  apply Nat.le_induction (m := 1) (P := P) (n := n) (hmn := hn)
  · norm_num [P]
  · intro j hj ih
    dsimp [P] at ih ⊢
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    push_cast
    ring

/-- The exact Gram-to-symmetric variance ratio is at least one. -/
theorem one_le_gramToSymmetricVarianceRatio
    (K n : ℕ) (hK : 0 < K) :
    1 ≤ gramToSymmetricVarianceRatio K n := by
  unfold gramToSymmetricVarianceRatio
  apply Finset.one_le_prod
  intro r hr
  have hKR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  apply (le_div_iff₀ hKR).2
  have hr2 : (2 : ℝ) ≤ (r : ℝ) := by
    exact_mod_cast (Finset.mem_Icc.mp hr).1
  linarith

/-- Elementary exponential envelope for the exact variance ratio. -/
theorem gramToSymmetricVarianceRatio_le_exp_pairScale
    (K n : ℕ) (hn : 1 ≤ n) (hK : 0 < K) :
    gramToSymmetricVarianceRatio K n ≤
      Real.exp (((n : ℝ) ^ 2 - (n : ℝ)) / (K : ℝ)) := by
  have hKR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  unfold gramToSymmetricVarianceRatio
  calc
    (∏ r ∈ Finset.Icc 2 n,
        (((K : ℝ) + 2 * (r : ℝ) - 2) / (K : ℝ))) ≤
        ∏ r ∈ Finset.Icc 2 n,
          Real.exp ((2 * (r : ℝ) - 2) / (K : ℝ)) := by
      apply Finset.prod_le_prod
      · intro r hr
        have hr2 : (2 : ℝ) ≤ (r : ℝ) := by
          exact_mod_cast (Finset.mem_Icc.mp hr).1
        exact div_nonneg (by linarith) hKR.le
      · intro r hr
        have hsplit :
            ((K : ℝ) + 2 * (r : ℝ) - 2) / (K : ℝ) =
              1 + (2 * (r : ℝ) - 2) / (K : ℝ) := by
          field_simp [hKR.ne']
          ring
        rw [hsplit]
        simpa [add_comm] using
          Real.add_one_le_exp ((2 * (r : ℝ) - 2) / (K : ℝ))
    _ = Real.exp
        (∑ r ∈ Finset.Icc 2 n,
          ((2 * (r : ℝ) - 2) / (K : ℝ))) := by
      rw [Real.exp_sum]
    _ = Real.exp (((n : ℝ) ^ 2 - (n : ℝ)) / (K : ℝ)) := by
      congr 1
      rw [← Finset.sum_div, sum_Icc_two_two_mul_sub_two n hn]

/-- The two finite logarithmic coefficient bounds displayed in the manuscript End
Matter.  They are direct consequences of the exact product envelopes and add
no scientific assumption. -/
theorem coefficientLogBounds
    (K n : ℕ) (hn : 1 ≤ n) (hK : 4 * n ≤ K) :
    Real.log (gramToSymmetricVarianceRatio K n) ≤
        (n : ℝ) * ((n : ℝ) - 1) / (K : ℝ) ∧
      Real.log (paperBkn K n / paperBn n) ≤
        (3 * (n : ℝ) ^ 2 - 2) / (K : ℝ) +
          9 * (n : ℝ) ^ 3 /
            ((K : ℝ) * ((K : ℝ) - 4 * (n : ℝ) + 1)) := by
  have hKpos : 0 < K := by omega
  constructor
  · have hratioPos := gramToSymmetricVarianceRatio_pos K n hKpos
    rw [Real.log_le_iff_le_exp hratioPos]
    simpa [pow_two, mul_sub] using
      (gramToSymmetricVarianceRatio_le_exp_pairScale K n hn hKpos)
  · have hbPos := paperBn_pos n hn
    have hBPos : 0 < paperBkn K n :=
      GaussianAnticoncentration.shiftedAnticoncentrationConstant_pos n K hn hK
    have hquotPos : 0 < paperBkn K n / paperBn n := div_pos hBPos hbPos
    rw [Real.log_le_iff_le_exp hquotPos]
    apply (div_le_iff₀ hbPos).2
    simpa [mul_comm] using paperBkn_le_sharper K n hn hK

/-- The ambient dimension in the Letter is `N = 2n`, and hence tends to
infinity when the pair count is used as the sequence index. -/
theorem tendsto_evenAmbientDimension_atTop :
    Tendsto (fun n : ℕ ↦ 2 * n) atTop atTop := by
  rw [tendsto_atTop]
  intro b
  filter_upwards [eventually_ge_atTop b] with n hn
  omega

/-- In the physical scale `N = 2n`, the logarithmic hypothesis gives the
pointwise power envelope for the exact variance ratio. -/
theorem gramToSymmetricVarianceRatio_le_ambientPower
    (K n : ℕ) (kappa : ℝ) (hn : 1 ≤ n) (hK : 0 < K)
    (hscale :
      (((2 * n : ℕ) : ℝ) ^ 2 / (K : ℝ)) ≤
        kappa * Real.log (((2 * n : ℕ) : ℝ))) :
    gramToSymmetricVarianceRatio K n ≤
      (((2 * n : ℕ) : ℝ) ^ (kappa / 4)) := by
  have hKR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hnR : (0 : ℝ) < (n : ℝ) := by positivity
  have hNR : (0 : ℝ) < (((2 * n : ℕ) : ℝ)) := by positivity
  have hscale' :
      4 * (n : ℝ) ^ 2 / (K : ℝ) ≤
        kappa * Real.log (((2 * n : ℕ) : ℝ)) := by
    convert hscale using 1 <;> push_cast <;> ring
  have hpair :
      (((n : ℝ) ^ 2 - (n : ℝ)) / (K : ℝ)) ≤
        (kappa / 4) * Real.log (((2 * n : ℕ) : ℝ)) := by
    have hnum : (n : ℝ) ^ 2 - (n : ℝ) ≤ (n : ℝ) ^ 2 := by
      linarith
    have hdiv :
        ((n : ℝ) ^ 2 - (n : ℝ)) / (K : ℝ) ≤
          (n : ℝ) ^ 2 / (K : ℝ) :=
      div_le_div_of_nonneg_right hnum hKR.le
    exact hdiv.trans (by
      calc
        (n : ℝ) ^ 2 / (K : ℝ) =
            (4 * (n : ℝ) ^ 2 / (K : ℝ)) / 4 := by ring
        _ ≤ (kappa * Real.log (((2 * n : ℕ) : ℝ))) / 4 := by
          gcongr
        _ = (kappa / 4) * Real.log (((2 * n : ℕ) : ℝ)) := by ring)
  calc
    gramToSymmetricVarianceRatio K n ≤
        Real.exp (((n : ℝ) ^ 2 - (n : ℝ)) / (K : ℝ)) :=
      gramToSymmetricVarianceRatio_le_exp_pairScale K n hn hK
    _ ≤ Real.exp
        ((kappa / 4) * Real.log (((2 * n : ℕ) : ℝ))) :=
      Real.exp_le_exp.mpr hpair
    _ = (((2 * n : ℕ) : ℝ) ^ (kappa / 4)) := by
      rw [Real.rpow_def_of_pos hNR]
      congr 1
      ring

/-- The limiting small-ball coefficient times the reference-scale ratio has
the pointwise power envelope used for the third line of the manuscript display. -/
theorem paperBn_mul_ratio_le_ambientPower
    (K n : ℕ) (kappa : ℝ) (hn : 1 ≤ n) (hK : 0 < K)
    (hscale :
      (((2 * n : ℕ) : ℝ) ^ 2 / (K : ℝ)) ≤
        kappa * Real.log (((2 * n : ℕ) : ℝ))) :
    paperBn n * gramToSymmetricVarianceRatio K n ≤
      2 * (((2 * n : ℕ) : ℝ) ^ (1 / 2 + kappa / 4)) := by
  have hNpos : (0 : ℝ) < (((2 * n : ℕ) : ℝ)) := by positivity
  have hratio := gramToSymmetricVarianceRatio_le_ambientPower
    K n kappa hn hK hscale
  have hratioNonneg : 0 ≤ gramToSymmetricVarianceRatio K n :=
    (gramToSymmetricVarianceRatio_pos K n hK).le
  have hpowerNonneg :
      0 ≤ (((2 * n : ℕ) : ℝ) ^ (kappa / 4)) :=
    (Real.rpow_pos_of_pos hNpos _).le
  have hb := limitingAnticoncentrationConstant_le_two_sqrt n hn
  have hsqrt :
      Real.sqrt (n : ℝ) ≤
        (((2 * n : ℕ) : ℝ) ^ (1 / 2 : ℝ)) := by
    rw [← Real.sqrt_eq_rpow]
    apply Real.sqrt_le_sqrt
    push_cast
    linarith
  calc
    paperBn n * gramToSymmetricVarianceRatio K n ≤
        (2 * Real.sqrt (n : ℝ)) *
          (((2 * n : ℕ) : ℝ) ^ (kappa / 4)) := by
      exact mul_le_mul hb hratio hratioNonneg (by positivity)
    _ ≤ 2 * (((2 * n : ℕ) : ℝ) ^ (1 / 2 : ℝ)) *
          (((2 * n : ℕ) : ℝ) ^ (kappa / 4)) := by
      gcongr
    _ = 2 * (((2 * n : ℕ) : ℝ) ^ (1 / 2 + kappa / 4)) := by
      rw [Real.rpow_add hNpos]
      ring

/-- The pair-count logarithmic hypothesis implies its ambient-dimension
version exactly when `N = 2n`. -/
theorem pairCountLogScale_implies_ambientLogScale
    (K n : ℕ) (C : ℝ) (hn : 1 ≤ n) (hC : 0 ≤ C)
    (hscale :
      (n : ℝ) ^ 2 / (K : ℝ) ≤ C * Real.log (n : ℝ)) :
    (((2 * n : ℕ) : ℝ) ^ 2 / (K : ℝ)) ≤
      4 * C * Real.log (((2 * n : ℕ) : ℝ)) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by positivity
  have hNpos : (0 : ℝ) < (((2 * n : ℕ) : ℝ)) := by positivity
  have hnleN : (n : ℝ) ≤ (((2 * n : ℕ) : ℝ)) := by
    push_cast
    linarith
  have hlog : Real.log (n : ℝ) ≤
      Real.log (((2 * n : ℕ) : ℝ)) :=
    Real.strictMonoOn_log.monotoneOn hnR hNpos hnleN
  have hClog := mul_le_mul_of_nonneg_left hlog hC
  calc
    (((2 * n : ℕ) : ℝ) ^ 2 / (K : ℝ)) =
        4 * ((n : ℝ) ^ 2 / (K : ℝ)) := by
      push_cast
      ring
    _ ≤ 4 * (C * Real.log (n : ℝ)) := by gcongr
    _ ≤ 4 * (C * Real.log (((2 * n : ℕ) : ℝ))) := by gcongr
    _ = 4 * C * Real.log (((2 * n : ℕ) : ℝ)) := by ring

/-- Substituting `kappa = 4C` gives exactly the two specialized exponents
printed after the coefficient display. -/
theorem four_mul_pairScale_exponents (C : ℝ) :
    1 / 2 + 3 * (4 * C) / 4 = 1 / 2 + 3 * C ∧
    1 / 2 + (4 * C) / 4 = 1 / 2 + C := by
  constructor <;> ring

/-- The ambient logarithmic scale implies a slightly weaker pair-count
scale, used only to control the `o(1)` logarithmic remainder.  The original
ambient inequality is retained for the sharp leading exponent. -/
theorem eventually_pairLogScale_of_ambientLogScale
    (K : ℕ → ℕ) {kappa : ℝ} (hkappa : 0 < kappa)
    (hscale : ∀ᶠ n : ℕ in atTop,
      (((2 * n : ℕ) : ℝ) ^ 2 / (K n : ℝ)) ≤
        kappa * Real.log (((2 * n : ℕ) : ℝ))) :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ 2 / (K n : ℝ) ≤
        (kappa / 2) * Real.log (n : ℝ) := by
  filter_upwards [hscale, eventually_ge_atTop 2] with n hs hn
  have hnR : (0 : ℝ) < (n : ℝ) := by positivity
  have htwoR : (0 : ℝ) < (2 : ℝ) := by norm_num
  have htwoLe : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlogTwoLe : Real.log (2 : ℝ) ≤ Real.log (n : ℝ) :=
    Real.strictMonoOn_log.monotoneOn htwoR hnR htwoLe
  have hlogEq :
      Real.log (((2 * n : ℕ) : ℝ)) =
        Real.log 2 + Real.log (n : ℝ) := by
    push_cast
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hnR.ne']
  have hlog :
      Real.log (((2 * n : ℕ) : ℝ)) ≤
        2 * Real.log (n : ℝ) := by
    rw [hlogEq]
    linarith
  have hscale' :
      4 * (n : ℝ) ^ 2 / (K n : ℝ) ≤
        kappa * Real.log (((2 * n : ℕ) : ℝ)) := by
    convert hs using 1 <;> push_cast <;> ring
  have hlogMul := mul_le_mul_of_nonneg_left hlog hkappa.le
  calc
    (n : ℝ) ^ 2 / (K n : ℝ) =
        (4 * (n : ℝ) ^ 2 / (K n : ℝ)) / 4 := by ring
    _ ≤ (kappa * Real.log (((2 * n : ℕ) : ℝ))) / 4 := by
      gcongr
    _ ≤ (kappa * (2 * Real.log (n : ℝ))) / 4 := by
      gcongr
    _ = (kappa / 2) * Real.log (n : ℝ) := by ring

/-- A finite pointwise coefficient bound retaining the ambient-scale leading
exponent.  The remainder premise is supplied eventually by the preceding
logarithmic-scale theorem. -/
theorem paperBkn_le_ambientPower_of_logRemainder
    (K n : ℕ) (kappa : ℝ) (hn : 1 ≤ n) (hK : 4 * n ≤ K)
    (hscale :
      (((2 * n : ℕ) : ℝ) ^ 2 / (K : ℝ)) ≤
        kappa * Real.log (((2 * n : ℕ) : ℝ)))
    (hrem : finiteCoefficientLogRemainder K n ≤ 1) :
    paperBkn K n ≤
      2 * Real.exp 1 *
        (((2 * n : ℕ) : ℝ) ^ (1 / 2 + 3 * kappa / 4)) := by
  have hKpos : 0 < K := by omega
  have hNpos : (0 : ℝ) < (((2 * n : ℕ) : ℝ)) := by positivity
  have hscale' :
      4 * (n : ℝ) ^ 2 / (K : ℝ) ≤
        kappa * Real.log (((2 * n : ℕ) : ℝ)) := by
    convert hscale using 1 <;> push_cast <;> ring
  have hlead :
      3 * (n : ℝ) ^ 2 / (K : ℝ) +
          finiteCoefficientLogRemainder K n ≤
        (3 * kappa / 4) *
            Real.log (((2 * n : ℕ) : ℝ)) + 1 := by
    have hquarter :
        3 * (n : ℝ) ^ 2 / (K : ℝ) ≤
          (3 * kappa / 4) *
            Real.log (((2 * n : ℕ) : ℝ)) := by
      calc
        3 * (n : ℝ) ^ 2 / (K : ℝ) =
            (3 / 4) * (4 * (n : ℝ) ^ 2 / (K : ℝ)) := by ring
        _ ≤ (3 / 4) *
            (kappa * Real.log (((2 * n : ℕ) : ℝ))) := by
          gcongr
        _ = (3 * kappa / 4) *
            Real.log (((2 * n : ℕ) : ℝ)) := by ring
    linarith
  have hb := limitingAnticoncentrationConstant_le_two_sqrt n hn
  have hsqrt :
      Real.sqrt (n : ℝ) ≤
        (((2 * n : ℕ) : ℝ) ^ (1 / 2 : ℝ)) := by
    rw [← Real.sqrt_eq_rpow]
    apply Real.sqrt_le_sqrt
    push_cast
    linarith
  change shiftedAnticoncentrationConstant K n ≤ _
  rw [shiftedAnticoncentrationConstant_eq_limit_mul_exp hn hK]
  calc
    paperBn n * Real.exp
        (3 * (n : ℝ) ^ 2 / (K : ℝ) +
          finiteCoefficientLogRemainder K n) ≤
        (2 * Real.sqrt (n : ℝ)) *
          Real.exp ((3 * kappa / 4) *
            Real.log (((2 * n : ℕ) : ℝ)) + 1) := by
      exact mul_le_mul hb (Real.exp_le_exp.mpr hlead)
        (Real.exp_nonneg _) (by positivity)
    _ ≤ 2 * (((2 * n : ℕ) : ℝ) ^ (1 / 2 : ℝ)) *
          Real.exp ((3 * kappa / 4) *
            Real.log (((2 * n : ℕ) : ℝ)) + 1) := by
      gcongr
    _ = 2 * Real.exp 1 *
        (((2 * n : ℕ) : ℝ) ^ (1 / 2 + 3 * kappa / 4)) := by
      have hexpPower :
          Real.exp ((3 * kappa / 4) *
              Real.log (((2 * n : ℕ) : ℝ))) =
            (((2 * n : ℕ) : ℝ) ^ (3 * kappa / 4)) := by
        rw [Real.rpow_def_of_pos hNpos]
        congr 1
        ring
      rw [Real.exp_add, hexpPower, Real.rpow_add hNpos]
      ring

/-- The first line of the manuscript coefficient display, with the physical ambient
dimension `N_n = 2n` and explicit eventual hypotheses. -/
theorem paperBkn_isBigO_ambientLogScale
    (K : ℕ → ℕ) {kappa : ℝ} (hkappa : 0 < kappa)
    (hK4 : ∀ᶠ n : ℕ in atTop, 4 * n ≤ K n)
    (hscale : ∀ᶠ n : ℕ in atTop,
      (((2 * n : ℕ) : ℝ) ^ 2 / (K n : ℝ)) ≤
        kappa * Real.log (((2 * n : ℕ) : ℝ))) :
    (fun n : ℕ ↦ paperBkn (K n) n) =O[atTop]
      (fun n : ℕ ↦
        (((2 * n : ℕ) : ℝ) ^ (1 / 2 + 3 * kappa / 4))) := by
  have hkpos : ∀ᶠ n : ℕ in atTop, 0 < K n := by
    filter_upwards [hK4, eventually_ge_atTop 1] with n hkn hn
    omega
  have hpair := eventually_pairLogScale_of_ambientLogScale
    K hkappa hscale
  have hremT := tendsto_finiteCoefficientLogRemainder_of_log_scale
    K (D := kappa / 2) (by positivity) hkpos hpair
  have hrem : ∀ᶠ n : ℕ in atTop,
      finiteCoefficientLogRemainder (K n) n ≤ 1 :=
    hremT.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1))
  apply Asymptotics.IsBigO.of_bound (2 * Real.exp 1)
  filter_upwards [hK4, hscale, hrem, eventually_ge_atTop 1]
    with n hkn hs hr hn
  have hbound := paperBkn_le_ambientPower_of_logRemainder
    (K n) n kappa hn hkn hs hr
  have hBnonneg : 0 ≤ paperBkn (K n) n := by
    change 0 ≤ shiftedAnticoncentrationConstant (K n) n
    rw [shiftedAnticoncentrationConstant_eq_limit_mul_exp hn hkn]
    exact mul_nonneg (paperBn_pos n hn).le (Real.exp_nonneg _)
  have hpowerNonneg :
      0 ≤ (((2 * n : ℕ) : ℝ) ^ (1 / 2 + 3 * kappa / 4)) :=
    Real.rpow_nonneg (by positivity) _
  simpa only [Real.norm_eq_abs, abs_of_nonneg hBnonneg,
    abs_of_nonneg hpowerNonneg] using hbound

/-- The second line of the manuscript coefficient display. -/
theorem gramToSymmetricVarianceRatio_isBigO_ambientLogScale
    (K : ℕ → ℕ) {kappa : ℝ}
    (hK4 : ∀ᶠ n : ℕ in atTop, 4 * n ≤ K n)
    (hscale : ∀ᶠ n : ℕ in atTop,
      (((2 * n : ℕ) : ℝ) ^ 2 / (K n : ℝ)) ≤
        kappa * Real.log (((2 * n : ℕ) : ℝ))) :
    (fun n : ℕ ↦ gramToSymmetricVarianceRatio (K n) n) =O[atTop]
      (fun n : ℕ ↦ (((2 * n : ℕ) : ℝ) ^ (kappa / 4))) := by
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [hK4, hscale, eventually_ge_atTop 1]
    with n hkn hs hn
  have hKpos : 0 < K n := by omega
  have hbound := gramToSymmetricVarianceRatio_le_ambientPower
    (K n) n kappa hn hKpos hs
  have hratioNonneg : 0 ≤ gramToSymmetricVarianceRatio (K n) n :=
    (gramToSymmetricVarianceRatio_pos (K n) n hKpos).le
  have hpowerNonneg :
      0 ≤ (((2 * n : ℕ) : ℝ) ^ (kappa / 4)) :=
    Real.rpow_nonneg (by positivity) _
  simpa only [Real.norm_eq_abs, abs_of_nonneg hratioNonneg,
    abs_of_nonneg hpowerNonneg, one_mul] using hbound

/-- The third line of the manuscript coefficient display. -/
theorem paperBn_mul_ratio_isBigO_ambientLogScale
    (K : ℕ → ℕ) {kappa : ℝ}
    (hK4 : ∀ᶠ n : ℕ in atTop, 4 * n ≤ K n)
    (hscale : ∀ᶠ n : ℕ in atTop,
      (((2 * n : ℕ) : ℝ) ^ 2 / (K n : ℝ)) ≤
        kappa * Real.log (((2 * n : ℕ) : ℝ))) :
    (fun n : ℕ ↦
      paperBn n * gramToSymmetricVarianceRatio (K n) n) =O[atTop]
      (fun n : ℕ ↦
        (((2 * n : ℕ) : ℝ) ^ (1 / 2 + kappa / 4))) := by
  apply Asymptotics.IsBigO.of_bound 2
  filter_upwards [hK4, hscale, eventually_ge_atTop 1]
    with n hkn hs hn
  have hKpos : 0 < K n := by omega
  have hbound := paperBn_mul_ratio_le_ambientPower
    (K n) n kappa hn hKpos hs
  have hleftNonneg :
      0 ≤ paperBn n * gramToSymmetricVarianceRatio (K n) n :=
    mul_nonneg (paperBn_pos n hn).le
      (gramToSymmetricVarianceRatio_pos (K n) n hKpos).le
  have hpowerNonneg :
      0 ≤ (((2 * n : ℕ) : ℝ) ^ (1 / 2 + kappa / 4)) :=
    Real.rpow_nonneg (by positivity) _
  simpa only [Real.norm_eq_abs, abs_of_nonneg hleftNonneg,
    abs_of_nonneg hpowerNonneg] using hbound

/-- Bundled literal endpoint for all three lines of the manuscript coefficient
display. -/
theorem coefficientTriple_isBigO_ambientLogScale
    (K : ℕ → ℕ) {kappa : ℝ} (hkappa : 0 < kappa)
    (hK4 : ∀ᶠ n : ℕ in atTop, 4 * n ≤ K n)
    (hscale : ∀ᶠ n : ℕ in atTop,
      (((2 * n : ℕ) : ℝ) ^ 2 / (K n : ℝ)) ≤
        kappa * Real.log (((2 * n : ℕ) : ℝ))) :
    ((fun n : ℕ ↦ paperBkn (K n) n) =O[atTop]
      (fun n : ℕ ↦
        (((2 * n : ℕ) : ℝ) ^ (1 / 2 + 3 * kappa / 4)))) ∧
    ((fun n : ℕ ↦ gramToSymmetricVarianceRatio (K n) n) =O[atTop]
      (fun n : ℕ ↦ (((2 * n : ℕ) : ℝ) ^ (kappa / 4)))) ∧
    ((fun n : ℕ ↦
      paperBn n * gramToSymmetricVarianceRatio (K n) n) =O[atTop]
      (fun n : ℕ ↦
        (((2 * n : ℕ) : ℝ) ^ (1 / 2 + kappa / 4)))) := by
  exact ⟨paperBkn_isBigO_ambientLogScale K hkappa hK4 hscale,
    gramToSymmetricVarianceRatio_isBigO_ambientLogScale K hK4 hscale,
    paperBn_mul_ratio_isBigO_ambientLogScale K hK4 hscale⟩

/-- If the physical squared ratio `N_n^2 / K_n`, with `N_n = 2n`, tends
to zero, then the exact reference-scale ratio tends to one. -/
theorem gramToSymmetricVarianceRatio_tendsto_one_of_ambientSquaredRate
    (K : ℕ → ℕ)
    (hK4 : ∀ᶠ n : ℕ in atTop, 4 * n ≤ K n)
    (hscale : Tendsto
      (fun n : ℕ ↦ (((2 * n : ℕ) : ℝ) ^ 2 / (K n : ℝ)))
      atTop (nhds 0)) :
    Tendsto
      (fun n : ℕ ↦ gramToSymmetricVarianceRatio (K n) n)
      atTop (nhds 1) := by
  have hpair : Tendsto
      (fun n : ℕ ↦ (n : ℝ) ^ 2 / (K n : ℝ))
      atTop (nhds 0) := by
    have hmul :=
      (tendsto_const_nhds.mul hscale : Tendsto
        (fun n : ℕ ↦ (1 / 4 : ℝ) *
          (((2 * n : ℕ) : ℝ) ^ 2 / (K n : ℝ)))
        atTop (nhds ((1 / 4 : ℝ) * 0)))
    convert hmul using 1
    · funext n
      push_cast
      ring
    · norm_num
  have hexponent : Tendsto
      (fun n : ℕ ↦
        ((n : ℝ) ^ 2 - (n : ℝ)) / (K n : ℝ))
      atTop (nhds 0) := by
    refine squeeze_zero' ?_ ?_ hpair
    · filter_upwards [hK4, eventually_ge_atTop 1] with n hkn hn
      have hKpos : (0 : ℝ) < (K n : ℝ) := by
        exact_mod_cast (show 0 < K n by omega)
      have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      exact div_nonneg (by nlinarith) hKpos.le
    · filter_upwards [hK4, eventually_ge_atTop 1] with n hkn hn
      have hKpos : (0 : ℝ) < (K n : ℝ) := by
        exact_mod_cast (show 0 < K n by omega)
      apply (div_le_div_iff_of_pos_right hKpos).2
      linarith
  have hexp : Tendsto
      (fun n : ℕ ↦ Real.exp
        (((n : ℝ) ^ 2 - (n : ℝ)) / (K n : ℝ)))
      atTop (nhds 1) := by
    change Tendsto
      (Real.exp ∘ (fun n : ℕ ↦
        ((n : ℝ) ^ 2 - (n : ℝ)) / (K n : ℝ)))
      atTop (nhds 1)
    simpa only [Real.exp_zero] using
      Real.continuous_exp.continuousAt.tendsto.comp hexponent
  have hdiffUpper : Tendsto
      (fun n : ℕ ↦ Real.exp
        (((n : ℝ) ^ 2 - (n : ℝ)) / (K n : ℝ)) - 1)
      atTop (nhds 0) := by
    convert hexp.sub tendsto_const_nhds using 1 <;> norm_num
  have hdiff : Tendsto
      (fun n : ℕ ↦ gramToSymmetricVarianceRatio (K n) n - 1)
      atTop (nhds 0) := by
    refine squeeze_zero' ?_ ?_ hdiffUpper
    · filter_upwards [hK4, eventually_ge_atTop 1] with n hkn hn
      have hKpos : 0 < K n := by omega
      linarith [one_le_gramToSymmetricVarianceRatio (K n) n hKpos]
    · filter_upwards [hK4, eventually_ge_atTop 1] with n hkn hn
      have hKpos : 0 < K n := by omega
      linarith [gramToSymmetricVarianceRatio_le_exp_pairScale
        (K n) n hn hKpos]
  have hadd := hdiff.add
    (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1))
  convert hadd using 1 <;> norm_num

/-- The specialized form in the original pair-count notation.  From
`n^2/K_n ≤ C log n` one obtains the three ambient-dimension exponents
`1/2+3C`, `C`, and `1/2+C` exactly. -/
theorem coefficientTriple_isBigO_pairLogScale
    (K : ℕ → ℕ) {C : ℝ} (hC : 0 < C)
    (hK4 : ∀ᶠ n : ℕ in atTop, 4 * n ≤ K n)
    (hscale : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ 2 / (K n : ℝ) ≤ C * Real.log (n : ℝ)) :
    ((fun n : ℕ ↦ paperBkn (K n) n) =O[atTop]
      (fun n : ℕ ↦
        (((2 * n : ℕ) : ℝ) ^ (1 / 2 + 3 * C)))) ∧
    ((fun n : ℕ ↦ gramToSymmetricVarianceRatio (K n) n) =O[atTop]
      (fun n : ℕ ↦ (((2 * n : ℕ) : ℝ) ^ C))) ∧
    ((fun n : ℕ ↦
      paperBn n * gramToSymmetricVarianceRatio (K n) n) =O[atTop]
      (fun n : ℕ ↦
        (((2 * n : ℕ) : ℝ) ^ (1 / 2 + C)))) := by
  have hambient : ∀ᶠ n : ℕ in atTop,
      (((2 * n : ℕ) : ℝ) ^ 2 / (K n : ℝ)) ≤
        (4 * C) * Real.log (((2 * n : ℕ) : ℝ)) := by
    filter_upwards [hscale, eventually_ge_atTop 1] with n hs hn
    exact pairCountLogScale_implies_ambientLogScale
      (K n) n C hn hC.le hs
  have htriple := coefficientTriple_isBigO_ambientLogScale
    K (kappa := 4 * C) (by positivity) hK4 hambient
  have hBexp : 1 / 2 + 3 * (4 * C) / 4 = 1 / 2 + 3 * C := by ring
  have hRexp : (4 * C) / 4 = C := by ring
  have hbRexp : 1 / 2 + (4 * C) / 4 = 1 / 2 + C := by ring
  simpa only [hBexp, hRexp, hbRexp] using htriple

/-- Multiplying the finite coefficient by the common polynomial threshold
still tends to zero under the exact ambient logarithmic scale and exponent
gap used in the Letter. -/
theorem paperBkn_mul_polynomialThreshold_tendsto_zero_of_ambientLogScale
    (K : ℕ → ℕ) {kappa a : ℝ} (hkappa : 0 < kappa)
    (ha : 1 / 2 + 3 * kappa / 4 < a)
    (hK4 : ∀ᶠ n : ℕ in atTop, 4 * n ≤ K n)
    (hscale : ∀ᶠ n : ℕ in atTop,
      (((2 * n : ℕ) : ℝ) ^ 2 / (K n : ℝ)) ≤
        kappa * Real.log (((2 * n : ℕ) : ℝ))) :
    Tendsto
      (fun n : ℕ ↦ paperBkn (K n) n *
        (((2 * n : ℕ) : ℝ) ^ (-a)))
      atTop (nhds 0) := by
  have hB := paperBkn_isBigO_ambientLogScale K hkappa hK4 hscale
  rcases hB.exists_pos with ⟨C, hC, hCB⟩
  have hpower : Tendsto
      (fun n : ℕ ↦
        (((2 * n : ℕ) : ℝ) ^
          (3 * (kappa / 4) + 1 / 2 - a)))
      atTop (nhds 0) :=
    (methodOnePolynomialWindow_power_tendsto_zero
      (D := kappa / 4) (a := a) (by linarith)).comp
        tendsto_evenAmbientDimension_atTop
  have hright : Tendsto
      (fun n : ℕ ↦ C *
        (((2 * n : ℕ) : ℝ) ^
          (3 * (kappa / 4) + 1 / 2 - a)))
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hpower
  refine squeeze_zero' ?_ ?_ hright
  · filter_upwards [hK4, eventually_ge_atTop 1] with n hKn hn
    have hBnonneg : 0 ≤ paperBkn (K n) n := by
      change 0 ≤ shiftedAnticoncentrationConstant (K n) n
      rw [shiftedAnticoncentrationConstant_eq_limit_mul_exp hn hKn]
      exact mul_nonneg (paperBn_pos n hn).le (Real.exp_nonneg _)
    exact mul_nonneg hBnonneg (Real.rpow_nonneg (by positivity) _)
  · filter_upwards [hCB.bound, hK4, eventually_ge_atTop 1]
      with n hbound hKn hn
    have hBnonneg : 0 ≤ paperBkn (K n) n := by
      change 0 ≤ shiftedAnticoncentrationConstant (K n) n
      rw [shiftedAnticoncentrationConstant_eq_limit_mul_exp hn hKn]
      exact mul_nonneg (paperBn_pos n hn).le (Real.exp_nonneg _)
    have hNpos : (0 : ℝ) < (((2 * n : ℕ) : ℝ)) := by positivity
    have hbaseNonneg :
        0 ≤ (((2 * n : ℕ) : ℝ) ^ (1 / 2 + 3 * kappa / 4)) :=
      Real.rpow_nonneg hNpos.le _
    have hbound' :
        paperBkn (K n) n ≤
          C * (((2 * n : ℕ) : ℝ) ^ (1 / 2 + 3 * kappa / 4)) := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg hBnonneg,
        abs_of_nonneg hbaseNonneg] using hbound
    calc
      paperBkn (K n) n * (((2 * n : ℕ) : ℝ) ^ (-a)) ≤
          (C * (((2 * n : ℕ) : ℝ) ^ (1 / 2 + 3 * kappa / 4))) *
            (((2 * n : ℕ) : ℝ) ^ (-a)) :=
        mul_le_mul_of_nonneg_right hbound'
          (Real.rpow_nonneg hNpos.le _)
      _ = C * (((2 * n : ℕ) : ℝ) ^
          (3 * (kappa / 4) + 1 / 2 - a)) := by
        rw [mul_assoc, ← Real.rpow_add hNpos]
        congr 2
        ring

/-- The lower edge `c N²/log N ≤ K` of the decisive window implies the
ambient logarithmic coefficient hypothesis with `kappa = 1/c`. -/
theorem decisiveWindow_lowerBound_implies_ambientLogScale
    (K : ℕ → ℕ) {c : ℝ} (hc : 0 < c)
    (hlower : ∀ᶠ n : ℕ in atTop,
      c * (((2 * n : ℕ) : ℝ) ^ 2) /
          Real.log (((2 * n : ℕ) : ℝ)) ≤ (K n : ℝ)) :
    ∀ᶠ n : ℕ in atTop,
      (((2 * n : ℕ) : ℝ) ^ 2 / (K n : ℝ)) ≤
        (1 / c) * Real.log (((2 * n : ℕ) : ℝ)) := by
  filter_upwards [hlower, eventually_ge_atTop 1] with n hlowern hn
  have hN : (1 : ℝ) < (((2 * n : ℕ) : ℝ)) := by
    exact_mod_cast (show 1 < 2 * n by omega)
  have hlog : 0 < Real.log (((2 * n : ℕ) : ℝ)) := Real.log_pos hN
  have hleft : 0 <
      c * (((2 * n : ℕ) : ℝ) ^ 2) /
        Real.log (((2 * n : ℕ) : ℝ)) := by positivity
  have hK : (0 : ℝ) < (K n : ℝ) := lt_of_lt_of_le hleft hlowern
  apply (div_le_iff₀ hK).2
  rw [one_div]
  have hscaled := (div_le_iff₀ hlog).1 hlowern
  calc
    (((2 * n : ℕ) : ℝ) ^ 2) = c⁻¹ *
        (c * (((2 * n : ℕ) : ℝ) ^ 2)) := by
      field_simp [hc.ne']
    _ ≤ c⁻¹ *
        ((K n : ℝ) * Real.log (((2 * n : ℕ) : ℝ))) :=
      mul_le_mul_of_nonneg_left hscaled (inv_nonneg.2 hc.le)
    _ = c⁻¹ * Real.log (((2 * n : ℕ) : ℝ)) * (K n : ℝ) := by
      ring

/-- The uncapped Route 1 hiding term tends to zero under the manuscript's
literal condition `N²/M → 0`. -/
theorem routeOneExplicitHidingTerm_tendsto_zero_of_squaredRate
    (M : ℕ → ℕ)
    (hscale : Tendsto
      (fun n : ℕ ↦
        (((2 * n : ℕ) : ℝ) ^ 2 / (M n : ℝ)))
      atTop (nhds 0)) :
    Tendsto
      (fun n : ℕ ↦ (615172 : ℝ) *
        (((2 * n : ℕ) : ℝ) ^ 2 / (M n : ℝ)))
      atTop (nhds 0) := by
  simpa using tendsto_const_nhds.mul hscale

/-- If `K/N² → 0` with positive dimensions, then `N/sqrt K → ∞`. -/
theorem linearOverSqrt_tendsto_atTop_of_subquadratic
    (N K : ℕ → ℕ)
    (hNpos : ∀ᶠ j in atTop, 0 < N j)
    (hKpos : ∀ᶠ j in atTop, 0 < K j)
    (hscale : Tendsto
      (fun j ↦ (K j : ℝ) / (N j : ℝ) ^ 2)
      atTop (nhds 0)) :
    Tendsto
      (fun j ↦ (N j : ℝ) / Real.sqrt (K j : ℝ))
      atTop atTop := by
  let f : ℕ → ℝ := fun j ↦
    Real.sqrt ((K j : ℝ) / (N j : ℝ) ^ 2)
  have hf : Tendsto f atTop (nhds 0) := by
    simpa [f] using hscale.sqrt
  have hfpos : ∀ᶠ j in atTop, f j ∈ Set.Ioi (0 : ℝ) := by
    filter_upwards [hNpos, hKpos] with j hNj hKj
    dsimp [f]
    apply Real.sqrt_pos.2
    positivity
  have hwithin : Tendsto f atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.2 ⟨hf, hfpos⟩
  have hinv : Tendsto (fun j ↦ (f j)⁻¹) atTop atTop :=
    hwithin.inv_tendsto_nhdsGT_zero
  apply hinv.congr'
  filter_upwards [hNpos, hKpos] with j hNj hKj
  dsimp [f]
  rw [Real.sqrt_div (Nat.cast_nonneg (K j)), Real.sqrt_sq_eq_abs,
    abs_of_pos (by exact_mod_cast hNj)]
  have hsqrt : Real.sqrt (K j : ℝ) ≠ 0 :=
    Real.sqrt_ne_zero'.2 (by exact_mod_cast hKj)
  field_simp [hsqrt]

/-- The displayed Route 2 hiding envelope diverges throughout the strict
subquadratic `K` part of the decisive window when its constant is positive. -/
theorem symmetricHidingEnvelope_tendsto_atTop_of_subquadratic
    (Cprime : ℝ) (hCprime : 0 < Cprime)
    (N K : ℕ → ℕ)
    (hNpos : ∀ᶠ j in atTop, 0 < N j)
    (hKpos : ∀ᶠ j in atTop, 0 < K j)
    (hscale : Tendsto
      (fun j ↦ (K j : ℝ) / (N j : ℝ) ^ 2)
      atTop (nhds 0)) :
    Tendsto
      (fun j ↦ symmetricHidingEnvelope Cprime (K j) (N j))
      atTop atTop := by
  have hlinear := linearOverSqrt_tendsto_atTop_of_subquadratic
    N K hNpos hKpos hscale
  simpa [symmetricHidingEnvelope, mul_div_assoc] using
    hlinear.const_mul_atTop hCprime

/-- In particular, the displayed Route 2 envelope cannot converge to zero
in the strict subquadratic `K` window. -/
theorem symmetricHidingEnvelope_not_tendsto_zero_of_subquadratic
    (Cprime : ℝ) (hCprime : 0 < Cprime)
    (N K : ℕ → ℕ)
    (hNpos : ∀ᶠ j in atTop, 0 < N j)
    (hKpos : ∀ᶠ j in atTop, 0 < K j)
    (hscale : Tendsto
      (fun j ↦ (K j : ℝ) / (N j : ℝ) ^ 2)
      atTop (nhds 0)) :
    ¬ Tendsto
      (fun j ↦ symmetricHidingEnvelope Cprime (K j) (N j))
      atTop (nhds 0) :=
  not_tendsto_nhds_of_tendsto_atTop
    (symmetricHidingEnvelope_tendsto_atTop_of_subquadratic
      Cprime hCprime N K hNpos hKpos hscale) 0

/-- Exact sequence level certificate for the decisive simultaneous window.
The Route 1 fair bound tends to zero, while the published Route 2 scalar
envelope diverges.  This theorem compares envelopes and makes no assertion
that the underlying Route 2 distance is bounded away from zero. -/
theorem decisiveWindow_certificate
    (gamma : ℕ → ℝ) (K M : ℕ → ℕ)
    {c a Cprime : ℝ}
    (hc : 0 < c) (hCprime : 0 < Cprime)
    (ha : 1 / 2 + 3 / (4 * c) < a)
    (hgamma : Tendsto gamma atTop (nhds 0))
    (hK4 : ∀ᶠ n : ℕ in atTop, 4 * n ≤ K n)
    (hlower : ∀ᶠ n : ℕ in atTop,
      c * (((2 * n : ℕ) : ℝ) ^ 2) /
          Real.log (((2 * n : ℕ) : ℝ)) ≤ (K n : ℝ))
    (hKsubquadratic : Tendsto
      (fun n : ℕ ↦
        (K n : ℝ) / (((2 * n : ℕ) : ℝ) ^ 2))
      atTop (nhds 0))
    (hMsquared : Tendsto
      (fun n : ℕ ↦
        (((2 * n : ℕ) : ℝ) ^ 2 / (M n : ℝ)))
      atTop (nhds 0)) :
    Tendsto
      (fun n : ℕ ↦ min 1
        (gamma n +
          paperBkn (K n) n * (((2 * n : ℕ) : ℝ) ^ (-a)) +
          (615172 : ℝ) *
            (((2 * n : ℕ) : ℝ) ^ 2 / (M n : ℝ))))
      atTop (nhds 0) ∧
    Tendsto
      (fun n : ℕ ↦
        symmetricHidingEnvelope Cprime (K n) (2 * n))
      atTop atTop := by
  have hkappa : 0 < (1 / c : ℝ) := by positivity
  have hscale := decisiveWindow_lowerBound_implies_ambientLogScale
    K hc hlower
  have ha' : 1 / 2 + 3 * (1 / c) / 4 < a := by
    have heq : 3 / (4 * c) = 3 * (1 / c) / 4 := by
      field_simp [hc.ne']
    rw [← heq]
    exact ha
  have hanti :=
    paperBkn_mul_polynomialThreshold_tendsto_zero_of_ambientLogScale
      K hkappa ha' hK4 hscale
  have hhide :=
    routeOneExplicitHidingTerm_tendsto_zero_of_squaredRate M hMsquared
  constructor
  · exact capped_three_term_budget_tendsto_zero gamma
      (fun n : ℕ ↦
        paperBkn (K n) n * (((2 * n : ℕ) : ℝ) ^ (-a)))
      (fun n : ℕ ↦ (615172 : ℝ) *
        (((2 * n : ℕ) : ℝ) ^ 2 / (M n : ℝ)))
      hgamma hanti hhide
  · apply symmetricHidingEnvelope_tendsto_atTop_of_subquadratic
      Cprime hCprime (fun n : ℕ ↦ 2 * n) K
    · filter_upwards [eventually_ge_atTop 1] with n hn
      omega
    · filter_upwards [hK4, eventually_ge_atTop 1] with n hKn hn
      omega
    · exact hKsubquadratic

end

end LogdetLean.GramHafnian.ThreePaper.TwoMethodComparison
