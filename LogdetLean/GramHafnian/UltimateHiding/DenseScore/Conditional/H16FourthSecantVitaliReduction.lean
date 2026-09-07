import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16DirectFourthPointwiseDerivative
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16DirectLowerL1DerivativeChain
import Mathlib.MeasureTheory.Function.UnifTight
import Mathlib.Tactic

/-!
# The exact Vitali reduction for the sharp H16 fourth slot

The pointwise `3 -> 4` derivative is already known almost everywhere, but the
endpoint fourth jet has only the sharp integrable determinant singularity.
This file packages the genuinely remaining statement as uniform integrability
of the local normalized secants.  Everything else needed for the Vitali lift
is proved here:

* every secant is in `L1`;
* the family is uniformly tight because all local supports lie in one compact
  carrier;
* the secants converge almost everywhere to zero;
* uniform integrability therefore implies convergence in `L1` and the exact
  Banach derivative `3 -> 4`.

No scientific axiom, finite-perimeter bridge, or new endpoint assumption is
introduced.  The named proposition below is the single analytic obligation
still to be discharged for the direct H16 route.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- The normalized fourth-order remainder, localized to the fixed time
interval on which all moving supports have one compact carrier. -/
def h16CenteredFourthLocalSecantRemainder
    (N K : ℕ) (v : ComplexUnitSphere N) (t : ℝ)
    (x : ComplexSymmetricCoordinates N) : ℝ :=
  if t ∈ Icc (-1 : ℝ) 1 then
    ‖t‖⁻¹ *
      ‖h16CenteredTransportJet N K 3 v t x -
        h16CenteredTransportJet N K 3 v 0 x -
          t * h16CenteredTransportJet N K 4 v 0 x‖
  else 0

theorem h16CenteredFourthLocalSecantRemainder_nonnegative
    {N K : ℕ} (v : ComplexUnitSphere N) (t : ℝ)
    (x : ComplexSymmetricCoordinates N) :
    0 ≤ h16CenteredFourthLocalSecantRemainder N K v t x := by
  unfold h16CenteredFourthLocalSecantRemainder
  split_ifs
  · exact mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _)
  · exact le_rfl

/-- Each local normalized secant is integrable.  This uses exact H5 only
through the already proved integrability of all literal time-slice jets. -/
theorem integrable_h16CenteredFourthLocalSecantRemainder_exactH5
    (hH5 : H16ExactH5Family)
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (v : ComplexUnitSphere N) (t : ℝ) :
    Integrable (h16CenteredFourthLocalSecantRemainder N K v t)
      (complexSymmetricCoordinateVolume N) := by
  by_cases ht : t ∈ Icc (-1 : ℝ) 1
  · have hJt := integrable_h16CenteredTransportJet_direct_exactH5
      hH5 hN hboundary (3 : Fin 5) v t
    have hJzero := integrable_h16CenteredTransportJet_direct_exactH5
      hH5 hN hboundary (3 : Fin 5) v 0
    have hJfour := integrable_h16CenteredTransportJet_direct_exactH5
      hH5 hN hboundary (4 : Fin 5) v 0
    have hraw : Integrable (fun x : ComplexSymmetricCoordinates N ↦
        h16CenteredTransportJet N K 3 v t x -
          h16CenteredTransportJet N K 3 v 0 x -
            t * h16CenteredTransportJet N K 4 v 0 x)
        (complexSymmetricCoordinateVolume N) :=
      (hJt.sub hJzero).sub (hJfour.const_mul t)
    rw [show h16CenteredFourthLocalSecantRemainder N K v t =
        fun x : ComplexSymmetricCoordinates N ↦
          ‖t‖⁻¹ *
            ‖h16CenteredTransportJet N K 3 v t x -
              h16CenteredTransportJet N K 3 v 0 x -
                t * h16CenteredTransportJet N K 4 v 0 x‖ by
      funext x
      simp only [h16CenteredFourthLocalSecantRemainder, if_pos ht]]
    change Integrable (fun x : ComplexSymmetricCoordinates N ↦
      ‖t‖⁻¹ *
        ‖h16CenteredTransportJet N K 3 v t x -
          h16CenteredTransportJet N K 3 v 0 x -
            t * h16CenteredTransportJet N K 4 v 0 x‖)
      (complexSymmetricCoordinateVolume N)
    exact hraw.norm.const_mul ‖t‖⁻¹
  · rw [show h16CenteredFourthLocalSecantRemainder N K v t =
        fun _ : ComplexSymmetricCoordinates N ↦ (0 : ℝ) by
      funext x
      simp only [h16CenteredFourthLocalSecantRemainder, if_neg ht]]
    exact integrable_const_iff.mpr (Or.inl rfl)

/-- The local remainder vanishes off the common compact flow carrier. -/
theorem h16CenteredFourthLocalSecantRemainder_eq_zero_off_carrier
    {N K : ℕ} (v : ComplexUnitSphere N) (t : ℝ)
    (x : ComplexSymmetricCoordinates N)
    (hx : x ∉ h16CenteredLocalFlowCarrier N) :
    h16CenteredFourthLocalSecantRemainder N K v t x = 0 := by
  by_cases ht : t ∈ Icc (-1 : ℝ) 1
  · have hnot_t : x ∉ h16CenteredTransportSupport v t := by
      intro hxt
      exact hx (h16CenteredTransportSupport_subset_localFlowCarrier v ht hxt)
    have hzero_mem : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := by norm_num
    have hnot_zero : x ∉ h16CenteredTransportSupport v 0 := by
      intro hxzero
      exact hx
        (h16CenteredTransportSupport_subset_localFlowCarrier v hzero_mem hxzero)
    rw [h16CenteredFourthLocalSecantRemainder, if_pos ht]
    rw [h16CenteredTransportJet_zero_off_support
      (K := K) (3 : Fin 5) v t x hnot_t]
    rw [h16CenteredTransportJet_zero_off_support
      (K := K) (3 : Fin 5) v 0 x hnot_zero]
    rw [h16CenteredTransportJet_zero_off_support
      (K := K) (4 : Fin 5) v 0 x hnot_zero]
    simp
  · simp [h16CenteredFourthLocalSecantRemainder, ht]

/-- Compact support supplies the tightness half of the non-finite-measure
Vitali theorem without any additional analytic hypothesis. -/
theorem unifTight_h16CenteredFourthLocalSecantRemainder
    {N K : ℕ} (hN : 1 ≤ N) (v : ComplexUnitSphere N) :
    UnifTight
      (fun t : ℝ ↦ h16CenteredFourthLocalSecantRemainder N K v t)
      1 (complexSymmetricCoordinateVolume N) := by
  intro ε hε
  let carrier := h16CenteredLocalFlowCarrier N
  have hcarrier :
      (complexSymmetricCoordinateVolume N) carrier ≠ ∞ :=
    by
      have hvol : complexSymmetricCoordinateVolume N =
          (volume : Measure (ComplexSymmetricCoordinates N)) := by
        unfold complexSymmetricCoordinateVolume
        exact MeasureTheory.volume_pi.symm
      rw [hvol]
      exact (isCompact_h16CenteredLocalFlowCarrier hN).measure_ne_top
  refine ⟨carrier, hcarrier, ?_⟩
  intro t
  have hzero : carrierᶜ.indicator
      (h16CenteredFourthLocalSecantRemainder N K v t) = 0 := by
    funext x
    by_cases hx : x ∈ carrier
    · simp [hx]
    · have hxcompl : x ∈ carrierᶜ := by simpa using hx
      rw [indicator_of_mem hxcompl]
      exact h16CenteredFourthLocalSecantRemainder_eq_zero_off_carrier
        v t x hx
  rw [hzero, eLpNorm_zero]
  exact bot_le

/-- Almost-everywhere convergence of the localized normalized secants is the
already proved pointwise derivative, with no domination argument. -/
theorem h16CenteredFourthLocalSecantRemainder_tendsto_zero_ae
    {N K : ℕ} (hN : 1 ≤ N) (v : ComplexUnitSphere N) :
    ∀ᵐ x ∂complexSymmetricCoordinateVolume N,
      Tendsto
        (fun t : ℝ ↦ h16CenteredFourthLocalSecantRemainder N K v t x)
        (𝓝 0) (𝓝 0) := by
  filter_upwards
      [h16CenteredTransportJet_three_hasDerivAt_zero_ae
        (N := N) (K := K) hN v] with x hx
  have hraw := hasDerivAt_iff_tendsto.mp hx
  apply hraw.congr'
  filter_upwards
      [Icc_mem_nhds (by norm_num : (-1 : ℝ) < 0)
        (by norm_num : (0 : ℝ) < 1)] with t ht
  simp [h16CenteredFourthLocalSecantRemainder, ht, sub_zero,
    smul_eq_mul]

/-- The one remaining direct H16 condition: uniform integrability of the
localized normalized fourth secants.  Per-time `L1`, tightness, and a.e.
convergence are theorems and are deliberately absent from this proposition. -/
def H16CenteredFourthLocalSecantsUnifIntegrable (N K : ℕ) : Prop :=
  ∀ v : ComplexUnitSphere N,
    UnifIntegrable
      (fun t : ℝ ↦ h16CenteredFourthLocalSecantRemainder N K v t)
      1 (complexSymmetricCoordinateVolume N)

/-- Vitali convergence closes the sharp Banach derivative once the single
uniform-integrability condition is supplied. -/
theorem h16CenteredDirectFourthL1DerivativeAtZero_of_unifIntegrable_exactH5
    (hH5 : H16ExactH5Family)
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (hui : H16CenteredFourthLocalSecantsUnifIntegrable N K) :
    H16CenteredDirectFourthL1DerivativeAtZero hH5 hN hboundary := by
  intro v
  let μ := complexSymmetricCoordinateVolume N
  let R : ℝ → ComplexSymmetricCoordinates N → ℝ := fun t ↦
    h16CenteredFourthLocalSecantRemainder N K v t
  let L : ℝ → H16CenteredCoordinateL1 N := fun t ↦
    h16CenteredDirectJetLp hH5 hN hboundary (3 : Fin 5) v t
  let L' : H16CenteredCoordinateL1 N :=
    h16CenteredDirectJetLp hH5 hN hboundary (4 : Fin 5) v 0
  have hRint (t : ℝ) : Integrable (R t) μ := by
    simpa only [R, μ] using
      integrable_h16CenteredFourthLocalSecantRemainder_exactH5
        hH5 hN hboundary v t
  have hRmem (t : ℝ) : MemLp (R t) 1 μ :=
    memLp_one_iff_integrable.mpr (hRint t)
  have hRlim : ∀ᵐ x ∂μ,
      Tendsto (fun t : ℝ ↦ R t x) (𝓝 0) (𝓝 0) := by
    simpa only [R, μ] using
      h16CenteredFourthLocalSecantRemainder_tendsto_zero_ae
        (N := N) (K := K) hN v
  have hELp : Tendsto (fun t : ℝ ↦ eLpNorm (R t) 1 μ)
      (𝓝 0) (𝓝 0) := by
    rw [tendsto_iff_seq_tendsto]
    intro ts hts
    have hseqUI : UnifIntegrable (fun n : ℕ ↦ R (ts n)) 1 μ := by
      intro ε hε
      obtain ⟨δ, hδ, hbound⟩ := hui v hε
      exact ⟨δ, hδ, fun n s hs hμs ↦ hbound (ts n) s hs hμs⟩
    have hseqTight : UnifTight (fun n : ℕ ↦ R (ts n)) 1 μ := by
      obtain hfull := unifTight_h16CenteredFourthLocalSecantRemainder
        (N := N) (K := K) hN v
      intro ε hε
      obtain ⟨s, hs, hbound⟩ := hfull hε
      exact ⟨s, hs, fun n ↦ hbound (ts n)⟩
    have hseqLim : ∀ᵐ x ∂μ,
        Tendsto (fun n : ℕ ↦ R (ts n) x) atTop (𝓝 0) := by
      filter_upwards [hRlim] with x hx
      exact hx.comp hts
    have hv := tendsto_Lp_of_tendsto_ae
      (μ := μ) (p := (1 : ℝ≥0∞))
      le_rfl ENNReal.one_ne_top
      (fun n ↦ (hRmem (ts n)).aestronglyMeasurable)
      (MemLp.zero' : MemLp
        (fun _ : ComplexSymmetricCoordinates N ↦ (0 : ℝ)) 1 μ)
      hseqUI hseqTight hseqLim
    have hsubzero : ∀ n : ℕ,
        R (ts n) - (fun _ : ComplexSymmetricCoordinates N ↦ (0 : ℝ)) =
          R (ts n) := by
      intro n
      exact sub_zero _
    change Tendsto (fun n : ℕ ↦ eLpNorm (R (ts n)) 1 μ)
      atTop (𝓝 0)
    simpa only [hsubzero] using hv
  have hIntegralNorm : Tendsto (fun t : ℝ ↦ ∫ x, ‖R t x‖ ∂μ)
      (𝓝 0) (𝓝 0) := by
    have hreal : Tendsto
        (fun t : ℝ ↦ (eLpNorm (R t) 1 μ).toReal)
        (𝓝 0) (𝓝 0) := by
      have hcomp := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hELp
      change Tendsto (fun t : ℝ ↦ (eLpNorm (R t) 1 μ).toReal)
        (𝓝 0) (𝓝 (ENNReal.toReal 0)) at hcomp
      simpa only [ENNReal.toReal_zero] using hcomp
    apply hreal.congr'
    filter_upwards with t
    rw [toReal_eLpNorm (hRmem t).aestronglyMeasurable]
    exact lpNorm_one_eq_integral_norm (hRmem t).aestronglyMeasurable
  have hIntegral : Tendsto (fun t : ℝ ↦ ∫ x, R t x ∂μ)
      (𝓝 0) (𝓝 0) := by
    apply hIntegralNorm.congr'
    filter_upwards with t
    apply integral_congr_ae
    exact ae_of_all μ fun x ↦ by
      change ‖R t x‖ = R t x
      rw [Real.norm_eq_abs,
        abs_of_nonneg
          (h16CenteredFourthLocalSecantRemainder_nonnegative v t x)]
  rw [hasDerivAt_iff_tendsto]
  apply hIntegral.congr'
  filter_upwards
      [Icc_mem_nhds (by norm_num : (-1 : ℝ) < 0)
        (by norm_num : (0 : ℝ) < 1)] with t ht
  symm
  change ‖t - 0‖⁻¹ * ‖L t - L 0 - (t - 0) • L'‖ =
    ∫ x, R t x ∂μ
  rw [sub_zero]
  rw [L1.norm_eq_integral_norm]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards
      [Lp.coeFn_sub (L t) (L 0),
        Lp.coeFn_smul t L',
        Lp.coeFn_sub (L t - L 0) (t • L'),
        h16CenteredDirectJetLp_coeFn_ae hH5 hN hboundary
          (3 : Fin 5) v t,
        h16CenteredDirectJetLp_coeFn_ae hH5 hN hboundary
          (3 : Fin 5) v 0,
        h16CenteredDirectJetLp_coeFn_ae hH5 hN hboundary
          (4 : Fin 5) v 0] with
      x hsub hsmul hsub' hJt hJzero hJfour
  simp only [Pi.sub_apply, Pi.smul_apply] at hsub hsmul hsub'
  rw [hsub', hsub, hsmul, hJt, hJzero, hJfour]
  simp [R, h16CenteredFourthLocalSecantRemainder, ht, smul_eq_mul]

/-- Combining the already proved lower chain with the Vitali top slot gives
the full direct H16 derivative chain. -/
theorem h16CenteredDirectL1DerivativeAtZeroChain_of_unifIntegrable_exactH5
    (hH5 : H16ExactH5Family)
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (hui : H16CenteredFourthLocalSecantsUnifIntegrable N K) :
    H16CenteredDirectL1DerivativeAtZeroChain hH5 hN hboundary :=
  h16CenteredDirectL1DerivativeAtZeroChain_of_lower_of_fourth
    hH5 hN hboundary
    (h16CenteredDirectLowerL1DerivativeAtZeroChain_proved_exactH5
      hH5 hN hboundary)
    (h16CenteredDirectFourthL1DerivativeAtZero_of_unifIntegrable_exactH5
      hH5 hN hboundary hui)

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
