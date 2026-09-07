import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16DirectLowerPointwiseDerivativeChain
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16DirectL1WeakGenerator
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16LowerJetLocalEnvelope
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-!
# The complete direct lower `L1` derivative chain for H16

The all-points lower-jet derivative is lifted to the canonical `L1` classes.
For each of the three lower slots, the mean-value theorem bounds the remainder
quotient by twice the proved integrable local envelope for the successor jet.
Dominated convergence then proves the Banach derivative.
-/

open MeasureTheory Filter Set
open scoped ContDiff ENNReal Topology

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

private theorem h16CenteredTransportJet_lower_local_lipschitz
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (r : Fin 3) (v : ComplexUnitSphere N)
    (b : ComplexSymmetricCoordinates N → ℝ)
    (hb : ∀ (t : ℝ), t ∈ Icc (-1 : ℝ) 1 →
      ∀ x : ComplexSymmetricCoordinates N,
        ‖h16CenteredTransportJet N K r.succ.castSucc v t x‖ ≤ b x)
    {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1)
    (x : ComplexSymmetricCoordinates N) :
    ‖h16CenteredTransportJet N K r.castSucc.castSucc v t x -
        h16CenteredTransportJet N K r.castSucc.castSucc v 0 x‖ ≤
      b x * ‖t‖ := by
  let f : ℝ → ℝ := fun s ↦ h16CenteredTransportJet N K
    r.castSucc.castSucc v s x
  let f' : ℝ → ℝ := fun s ↦ h16CenteredTransportJet N K
    r.succ.castSucc v s x
  have hderiv : ∀ s ∈ Icc (-1 : ℝ) 1,
      HasDerivWithinAt f (f' s) (Icc (-1 : ℝ) 1) s := by
    intro s hs
    exact (h16CenteredTransportJet_lower_hasDerivAt
      (N := N) (K := K) hN hboundary r v x s).hasDerivWithinAt
  have hbound : ∀ s ∈ Icc (-1 : ℝ) 1, ‖f' s‖ ≤ b x := by
    intro s hs
    exact hb s hs x
  have hzero : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := by norm_num
  simpa [f, f', sub_zero] using
    (Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      hderiv hbound (convex_Icc (-1 : ℝ) 1) hzero ht)

private theorem measurable_h16CenteredTransportJet_slice_lower_chain
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (s : Fin 5) (v : ComplexUnitSphere N) (t : ℝ) :
    Measurable (fun x : ComplexSymmetricCoordinates N ↦
      h16CenteredTransportJet N K s v t x) := by
  have hparam : Measurable (fun x : ComplexSymmetricCoordinates N ↦
      (((v, t), x) : (ComplexUnitSphere N × ℝ) ×
        ComplexSymmetricCoordinates N)) := by
    fun_prop
  have h := (measurable_h16CenteredTransportJet_direct
    hN hboundary s).comp hparam
  convert h using 1 <;> rfl

/-- Exact direct `L1` derivative for any one of the three lower slots. -/
theorem h16CenteredDirectJetLp_lower_hasDerivAt_exactH5
    (hH5 : H16ExactH5Family)
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (r : Fin 3) (v : ComplexUnitSphere N) :
    HasDerivAt
      (fun t : ℝ ↦ h16CenteredDirectJetLp hH5 hN hboundary
        r.castSucc.castSucc v t)
      (h16CenteredDirectJetLp hH5 hN hboundary
        r.succ.castSucc v 0) 0 := by
  let μ := complexSymmetricCoordinateVolume N
  let J : ℝ → ComplexSymmetricCoordinates N → ℝ := fun t x ↦
    h16CenteredTransportJet N K r.castSucc.castSucc v t x
  let J' : ℝ → ComplexSymmetricCoordinates N → ℝ := fun t x ↦
    h16CenteredTransportJet N K r.succ.castSucc v t x
  let L : ℝ → H16CenteredCoordinateL1 N := fun t ↦
    h16CenteredDirectJetLp hH5 hN hboundary r.castSucc.castSucc v t
  let L' : H16CenteredCoordinateL1 N :=
    h16CenteredDirectJetLp hH5 hN hboundary r.succ.castSucc v 0
  obtain ⟨b, hbnonneg, hbint, hb⟩ :=
    exists_h16CenteredLocalJetLowerEnvelope
      (N := N) (K := K) hN hboundary r.succ
  let R : ℝ → ComplexSymmetricCoordinates N → ℝ := fun t x ↦
    ‖t‖⁻¹ * ‖J t x - J 0 x - t • J' 0 x‖
  have hRnonneg : ∀ t x, 0 ≤ R t x := by
    intro t x
    exact mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _)
  have hRmeas : ∀ t, AEStronglyMeasurable (R t) μ := by
    intro t
    have hJt : Measurable (J t) := by
      simpa only [J] using
        (measurable_h16CenteredTransportJet_slice_lower_chain
          hN hboundary r.castSucc.castSucc v t)
    have hJzero : Measurable (J 0) := by
      simpa only [J] using
        (measurable_h16CenteredTransportJet_slice_lower_chain
          hN hboundary r.castSucc.castSucc v 0)
    have hJ'zero : Measurable (J' 0) := by
      simpa only [J'] using
        (measurable_h16CenteredTransportJet_slice_lower_chain
          hN hboundary r.succ.castSucc v 0)
    exact (((hJt.sub hJzero).sub (hJ'zero.const_smul t)).norm.const_mul
      ‖t‖⁻¹).aestronglyMeasurable
  have hRlim : ∀ x, Tendsto (fun t ↦ R t x) (𝓝 0) (𝓝 0) := by
    intro x
    have hd := h16CenteredTransportJet_lower_hasDerivAt
      (N := N) (K := K) hN hboundary r v x 0
    simpa [R, J, J'] using (hasDerivAt_iff_tendsto.mp hd)
  have hRbound : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ᵐ x ∂μ, ‖R t x‖ ≤ 2 * b x := by
    filter_upwards [Icc_mem_nhds (by norm_num : (-1 : ℝ) < 0)
      (by norm_num : (0 : ℝ) < 1)] with t ht
    exact ae_of_all μ fun x ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (hRnonneg t x)]
      by_cases htzero : t = 0
      · simp [R, htzero, hbnonneg x]
      · have hlip := h16CenteredTransportJet_lower_local_lipschitz
          (N := N) (K := K) hN hboundary r v b
          (fun s hs y ↦ by simpa using hb v s hs y) ht x
        have hnext : ‖J' 0 x‖ ≤ b x := by
          exact hb v 0 (by norm_num) x
        calc
          R t x ≤ ‖t‖⁻¹ *
              (‖J t x - J 0 x‖ + ‖t • J' 0 x‖) := by
            unfold R
            gcongr
            exact norm_sub_le _ _
          _ ≤ ‖t‖⁻¹ * (b x * ‖t‖ + ‖t‖ * b x) := by
            apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (norm_nonneg t))
            apply add_le_add
            · simpa [J] using hlip
            · rw [norm_smul]
              exact mul_le_mul_of_nonneg_left hnext (norm_nonneg t)
          _ = 2 * b x := by
            have htpos : 0 < ‖t‖ := norm_pos_iff.mpr htzero
            field_simp
            ring
  have hRintegral : Tendsto (fun t ↦ ∫ x, R t x ∂μ) (𝓝 0) (𝓝 0) := by
    have hRbound' : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ᵐ x ∂μ,
        ‖R t x‖ ≤ (2 • b) x := by
      simpa [Pi.smul_apply, smul_eq_mul] using hRbound
    have hbint' : Integrable (2 • b) μ := by
      dsimp only [μ]
      exact (hbint.const_mul 2).congr <| ae_of_all _ fun x ↦ by
        simp [Pi.smul_apply, smul_eq_mul]
    have hraw := tendsto_integral_filter_of_dominated_convergence
      (G := ℝ) (F := R) (f := fun _ ↦ (0 : ℝ)) (2 • b)
      (Eventually.of_forall hRmeas) hRbound' hbint'
      (ae_of_all μ hRlim)
    simpa using hraw
  rw [hasDerivAt_iff_tendsto]
  apply hRintegral.congr'
  filter_upwards with t
  symm
  change ‖t - 0‖⁻¹ * ‖L t - L 0 - (t - 0) • L'‖ = ∫ x, R t x ∂μ
  rw [sub_zero]
  rw [L1.norm_eq_integral_norm]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (L t) (L 0),
    Lp.coeFn_smul t L', Lp.coeFn_sub (L t - L 0) (t • L'),
    h16CenteredDirectJetLp_coeFn_ae hH5 hN hboundary
      r.castSucc.castSucc v t,
    h16CenteredDirectJetLp_coeFn_ae hH5 hN hboundary
      r.castSucc.castSucc v 0,
    h16CenteredDirectJetLp_coeFn_ae hH5 hN hboundary
      r.succ.castSucc v 0] with
      x hsub hsmul hsub' hJt hJzero hJ'zero
  simp only [Pi.sub_apply, Pi.smul_apply] at hsub hsmul hsub'
  rw [hsub', hsub, hsmul, hJt, hJzero, hJ'zero]

/-- The full direct lower `L1` derivative premise is a theorem: all slots
`0 -> 1`, `1 -> 2`, and `2 -> 3` are discharged from exact H5 and the proved
determinant estimates. -/
theorem h16CenteredDirectLowerL1DerivativeAtZeroChain_proved_exactH5
    (hH5 : H16ExactH5Family)
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K) :
    H16CenteredDirectLowerL1DerivativeAtZeroChain
      hH5 hN hboundary := by
  intro r hr v
  let s : Fin 3 := ⟨r, hr⟩
  have hsource : s.castSucc.castSucc = r.castSucc := Fin.ext rfl
  have htarget : s.succ.castSucc = r.succ := Fin.ext rfl
  simpa only [hsource, htarget] using
    (h16CenteredDirectJetLp_lower_hasDerivAt_exactH5
      hH5 hN hboundary s v)

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
