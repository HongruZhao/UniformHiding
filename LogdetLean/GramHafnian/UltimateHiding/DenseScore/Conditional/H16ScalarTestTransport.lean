import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16FlowGeneratorCalculus

/-!
# Scalar compact-test transport for the corrected H16 jets

This module turns the determinant-superlevel weak generator identities into
ordinary time derivatives of compact-test pairings.  The proof uses only
zero-extended `L1` representatives, measure-preserving centered transport,
and a globally bounded compact-test generator.  It never asks for pointwise
fourth-boundary continuity or a global pointwise fourth-jet majorant.
-/

open MeasureTheory Filter Set
open scoped ContDiff ENNReal Topology Interval

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- Pairing an `L1` jet class with a test is the integral against its literal
zero-extended representative. -/
theorem h16TestPairCLM_centeredJet_eq_integral
    {N K : ℕ} {hN : 1 ≤ N} {hboundary : 2 * N + 8 ≤ K}
    (W : COECenteredOrderFourWeakGeneratorFacts N K hN hboundary)
    (r : Fin 5) (v : ComplexUnitSphere N) (t : ℝ)
    (phi : ComplexSymmetricCoordinates N → ℝ)
    (hphi : ContDiff ℝ ∞ phi) (hsupp : HasCompactSupport phi) :
    Conditional.h16TestPairCLM phi hphi hsupp
        (h16CenteredJetLpOfWeak W r v t) =
      ∫ x, phi x * h16CenteredTransportJet N K r v t x
        ∂(complexSymmetricCoordinateVolume N) := by
  rw [Conditional.h16TestPairCLM_apply]
  apply integral_congr_ae
  filter_upwards [h16CenteredJetLpOfWeak_coeFn_ae W r v t] with x hx
  rw [hx]

/-- Measure-preserving centered transport rewrites every moving literal-jet
pairing as a time-zero jet against a transported test. -/
theorem h16_integral_test_mul_centeredJet_eq_zero_transport
    {N K : ℕ} {hN : 1 ≤ N} {hboundary : 2 * N + 8 ≤ K}
    (W : COECenteredOrderFourWeakGeneratorFacts N K hN hboundary)
    (r : Fin 5) (v : ComplexUnitSphere N) (t : ℝ)
    (phi : ComplexSymmetricCoordinates N → ℝ) :
    (∫ x, phi x * h16CenteredTransportJet N K r v t x
        ∂(complexSymmetricCoordinateVolume N)) =
      ∫ y, phi (h16CenteredCoordinateFlow v t y) *
          h16CenteredTransportJet N K r v 0 y
        ∂(complexSymmetricCoordinateVolume N) := by
  have hEmb : MeasurableEmbedding (h16CenteredCoordinateFlow v t) := by
    change MeasurableEmbedding
      (centeredTransposeCongruenceFlowCoordinateRealCLE v t)
    exact (centeredTransposeCongruenceFlowCoordinateRealCLE v t).toHomeomorph.measurableEmbedding
  calc
    (∫ x, phi x * h16CenteredTransportJet N K r v t x
        ∂(complexSymmetricCoordinateVolume N)) =
        ∫ y, phi (h16CenteredCoordinateFlow v t y) *
          h16CenteredTransportJet N K r v t
            (h16CenteredCoordinateFlow v t y)
          ∂(complexSymmetricCoordinateVolume N) :=
      ((W.coordinate_measurePreserving v t).integral_comp hEmb
        (fun x ↦ phi x * h16CenteredTransportJet N K r v t x)).symm
    _ = ∫ y, phi (h16CenteredCoordinateFlow v t y) *
          h16CenteredTransportJet N K r v 0 y
        ∂(complexSymmetricCoordinateVolume N) := by
      apply integral_congr_ae
      exact ae_of_all _ fun y ↦ by
        change phi (h16CenteredCoordinateFlow v t y) *
            h16CenteredTransportJet N K r v t
              (h16CenteredCoordinateFlow v t y) = _
        rw [h16CenteredTransportJet_eq_zero_pullback]
        rw [h16CenteredCoordinateFlow_neg_left]

private theorem continuous_h16_testGenerator
    {N : ℕ} (hN : 1 ≤ N) (v : ComplexUnitSphere N)
    {phi : ComplexSymmetricCoordinates N → ℝ}
    (hphi : ContDiff ℝ ∞ phi) :
    Continuous (fun x ↦
      (fderiv ℝ phi x) (h16CenteredCoordinateVectorField v x)) := by
  exact ((hphi.continuous_fderiv (by simp)).clm_apply
    (continuous_h16CenteredCoordinateVectorField hN v))

private theorem hasCompactSupport_h16_testGenerator
    {N : ℕ} (v : ComplexUnitSphere N)
    {phi : ComplexSymmetricCoordinates N → ℝ}
    (hsupp : HasCompactSupport phi) :
    HasCompactSupport (fun x ↦
      (fderiv ℝ phi x) (h16CenteredCoordinateVectorField v x)) := by
  apply (hsupp.fderiv ℝ).mono'
  intro x hx
  change (fderiv ℝ phi x) (h16CenteredCoordinateVectorField v x) ≠ 0 at hx
  apply subset_tsupport (fderiv ℝ phi)
  change fderiv ℝ phi x ≠ 0
  intro hzero
  apply hx
  rw [hzero]
  exact ContinuousLinearMap.zero_apply _

/-- Differentiation under the coordinate integral for a time-zero `L1` jet
against a transported compact test.  Domination is by a constant times the
base-jet norm, never by a pointwise fourth-jet boundary majorant. -/
theorem h16_hasDerivAt_integral_zeroJet_mul_testFlow
    {N K : ℕ} {hN : 1 ≤ N} {hboundary : 2 * N + 8 ≤ K}
    (W : COECenteredOrderFourWeakGeneratorFacts N K hN hboundary)
    (r : Fin 5) (v : ComplexUnitSphere N)
    (phi : ComplexSymmetricCoordinates N → ℝ)
    (hphi : ContDiff ℝ ∞ phi) (hsupp : HasCompactSupport phi)
    (t : ℝ) :
    HasDerivAt
      (fun u : ℝ ↦ ∫ y,
        h16CenteredTransportJet N K r v 0 y *
          phi (h16CenteredCoordinateFlow v u y)
        ∂(complexSymmetricCoordinateVolume N))
      (∫ y, h16CenteredTransportJet N K r v 0 y *
        (fderiv ℝ phi (h16CenteredCoordinateFlow v t y))
          (h16CenteredCoordinateVectorField v
            (h16CenteredCoordinateFlow v t y))
        ∂(complexSymmetricCoordinateVolume N)) t := by
  let μ := complexSymmetricCoordinateVolume N
  let j : ComplexSymmetricCoordinates N → ℝ :=
    h16CenteredTransportJet N K r v 0
  let q : ComplexSymmetricCoordinates N → ℝ := fun x ↦
    (fderiv ℝ phi x) (h16CenteredCoordinateVectorField v x)
  let F : ℝ → ComplexSymmetricCoordinates N → ℝ := fun u y ↦
    j y * phi (h16CenteredCoordinateFlow v u y)
  let F' : ℝ → ComplexSymmetricCoordinates N → ℝ := fun u y ↦
    j y * q (h16CenteredCoordinateFlow v u y)
  have hqcont : Continuous q :=
    continuous_h16_testGenerator hN v hphi
  have hqsupp : HasCompactSupport q :=
    hasCompactSupport_h16_testGenerator v hsupp
  obtain ⟨C, hC⟩ := hqcont.bounded_above_of_compact_support hqsupp
  obtain ⟨D, hD⟩ :=
    hphi.continuous.bounded_above_of_compact_support hsupp
  have hflow_cont (u : ℝ) :
      Continuous (h16CenteredCoordinateFlow v u) := by
    change Continuous (centeredTransposeCongruenceFlowCoordinateRealCLE v u)
    exact (centeredTransposeCongruenceFlowCoordinateRealCLE v u).continuous
  have hFint (u : ℝ) : Integrable (F u) μ := by
    apply (W.jet_integrable r v 0).mul_bdd
    · exact (hphi.continuous.comp (hflow_cont u)).aestronglyMeasurable
    · exact ae_of_all _ fun y ↦ hD _
  have hF'int (u : ℝ) : Integrable (F' u) μ := by
    apply (W.jet_integrable r v 0).mul_bdd
    · exact (hqcont.comp (hflow_cont u)).aestronglyMeasurable
    · exact ae_of_all _ fun y ↦ hC _
  have hbound_int : Integrable (fun y ↦ C * ‖j y‖) μ :=
    (W.jet_integrable r v 0).norm.const_mul C
  have hresult := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := F) (F' := F') (bound := fun y ↦ C * ‖j y‖)
    (x₀ := t) (s := Set.univ)
    univ_mem
    (Filter.Eventually.of_forall fun u ↦ (hFint u).aestronglyMeasurable)
    (hFint t)
    (hF'int t).aestronglyMeasurable
    (ae_of_all _ fun y u hu ↦ by
      dsimp only [F', j, q]
      calc
        ‖h16CenteredTransportJet N K r v 0 y *
            (fderiv ℝ phi (h16CenteredCoordinateFlow v u y))
              (h16CenteredCoordinateVectorField v
                (h16CenteredCoordinateFlow v u y))‖ =
            ‖h16CenteredTransportJet N K r v 0 y‖ *
              ‖q (h16CenteredCoordinateFlow v u y)‖ := norm_mul _ _
        _ ≤ ‖h16CenteredTransportJet N K r v 0 y‖ * C :=
          mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
        _ = C * ‖h16CenteredTransportJet N K r v 0 y‖ := mul_comm _ _)
    hbound_int
    (ae_of_all _ fun y u hu ↦ by
      have houter : HasFDerivAt phi
          (fderiv ℝ phi (h16CenteredCoordinateFlow v u y))
          (h16CenteredCoordinateFlow v u y) :=
        ((hphi.differentiable (by simp)).differentiableAt.hasFDerivAt)
      have hcomp := houter.comp_hasDerivAt u
        (h16CenteredCoordinateFlow_hasDerivAt hN v u y)
      have hmul := hcomp.const_mul (j y)
      simpa only [F, F', j, q, Function.comp_apply] using hmul)
  simpa only [F, F', j, q, μ] using hresult.2

/-- Each compact-test pairing of the `r`th moving zero-extended jet has
derivative given by the pairing with the next jet.  The weak generator at
time zero is transported by the exact centered flow. -/
theorem h16TestPair_centeredJet_hasDerivAt
    {N K : ℕ} {hN : 1 ≤ N} {hboundary : 2 * N + 8 ≤ K}
    (W : COECenteredOrderFourWeakGeneratorFacts N K hN hboundary)
    (r : Fin 4) (v : ComplexUnitSphere N)
    (phi : ComplexSymmetricCoordinates N → ℝ)
    (hphi : ContDiff ℝ ∞ phi) (hsupp : HasCompactSupport phi)
    (t : ℝ) :
    HasDerivAt
      (fun u ↦ Conditional.h16TestPairCLM phi hphi hsupp
        (h16CenteredJetLpOfWeak W r.castSucc v u))
      (Conditional.h16TestPairCLM phi hphi hsupp
        (h16CenteredJetLpOfWeak W r.succ v t)) t := by
  let psi : ComplexSymmetricCoordinates N → ℝ := fun y ↦
    phi (h16CenteredCoordinateFlow v t y)
  have hpsi_cont : ContDiff ℝ ∞ psi :=
    h16_test_comp_centeredFlow_contDiff v t hphi
  have hpsi_supp : HasCompactSupport psi :=
    h16_test_comp_centeredFlow_hasCompactSupport v t hsupp
  have hweak := W.weak_generator_chain r v psi hpsi_supp hpsi_cont
  have hvalue :
      (∫ y, h16CenteredTransportJet N K r.castSucc v 0 y *
        (fderiv ℝ phi (h16CenteredCoordinateFlow v t y))
          (h16CenteredCoordinateVectorField v
            (h16CenteredCoordinateFlow v t y))
        ∂(complexSymmetricCoordinateVolume N)) =
      Conditional.h16TestPairCLM phi hphi hsupp
        (h16CenteredJetLpOfWeak W r.succ v t) := by
    calc
      (∫ y, h16CenteredTransportJet N K r.castSucc v 0 y *
          (fderiv ℝ phi (h16CenteredCoordinateFlow v t y))
            (h16CenteredCoordinateVectorField v
              (h16CenteredCoordinateFlow v t y))
          ∂(complexSymmetricCoordinateVolume N)) =
          ∫ y, h16CenteredTransportJet N K r.castSucc v 0 y *
            (fderiv ℝ psi y) (h16CenteredCoordinateVectorField v y)
          ∂(complexSymmetricCoordinateVolume N) := by
        apply integral_congr_ae
        exact ae_of_all _ fun y ↦ by
          change h16CenteredTransportJet N K r.castSucc v 0 y *
              (fderiv ℝ phi (h16CenteredCoordinateFlow v t y))
                (h16CenteredCoordinateVectorField v
                  (h16CenteredCoordinateFlow v t y)) =
            h16CenteredTransportJet N K r.castSucc v 0 y *
              (fderiv ℝ psi y) (h16CenteredCoordinateVectorField v y)
          rw [h16_fderiv_test_comp_centeredFlow_vectorField hN v t hphi y]
      _ = ∫ y, h16CenteredTransportJet N K r.succ v 0 y * psi y
          ∂(complexSymmetricCoordinateVolume N) := hweak.symm
      _ = ∫ y, psi y * h16CenteredTransportJet N K r.succ v 0 y
          ∂(complexSymmetricCoordinateVolume N) := by
        apply integral_congr_ae
        exact ae_of_all _ fun y ↦ mul_comm _ _
      _ = ∫ x, phi x * h16CenteredTransportJet N K r.succ v t x
          ∂(complexSymmetricCoordinateVolume N) := by
        exact (h16_integral_test_mul_centeredJet_eq_zero_transport
          W r.succ v t phi).symm
      _ = Conditional.h16TestPairCLM phi hphi hsupp
          (h16CenteredJetLpOfWeak W r.succ v t) :=
        (h16TestPairCLM_centeredJet_eq_integral
          W r.succ v t phi hphi hsupp).symm
  have hbase := h16_hasDerivAt_integral_zeroJet_mul_testFlow
    W r.castSucc v phi hphi hsupp t
  have hfun :
      (fun u ↦ Conditional.h16TestPairCLM phi hphi hsupp
        (h16CenteredJetLpOfWeak W r.castSucc v u)) =
      (fun u ↦ ∫ y, h16CenteredTransportJet N K r.castSucc v 0 y *
        phi (h16CenteredCoordinateFlow v u y)
        ∂(complexSymmetricCoordinateVolume N)) := by
    funext u
    rw [h16TestPairCLM_centeredJet_eq_integral
      W r.castSucc v u phi hphi hsupp]
    rw [h16_integral_test_mul_centeredJet_eq_zero_transport
      W r.castSucc v u phi]
    apply integral_congr_ae
    exact ae_of_all _ fun y ↦ mul_comm _ _
  rw [hfun]
  exact hbase.congr_deriv hvalue

/-- The determinant-superlevel weak-generator package therefore proves the
entire shifted scalar compact-test interval chain required by the checked
distribution-to-`L1` bridge. -/
theorem h16CenteredShiftedTestPairIntervalChain_proved
    {N K : ℕ} {hN : 1 ≤ N} {hboundary : 2 * N + 8 ≤ K}
    (W : COECenteredOrderFourWeakGeneratorFacts N K hN hboundary) :
    H16CenteredShiftedTestPairIntervalChain W := by
  intro r v a h phi hphi hsupp
  let P : ℝ → ℝ := fun t ↦ Conditional.h16TestPairCLM phi hphi hsupp
    (h16CenteredJetLpOfWeak W r.castSucc v t)
  let Q : ℝ → ℝ := fun t ↦ Conditional.h16TestPairCLM phi hphi hsupp
    (h16CenteredJetLpOfWeak W r.succ v t)
  have hQ : Continuous Q :=
    (Conditional.h16TestPairCLM phi hphi hsupp).continuous.comp
      (continuous_h16CenteredJetLpOfWeak_fixedDirection W r.succ v)
  have hderiv : ∀ s ∈ uIcc (0 : ℝ) h,
      HasDerivAt (fun u ↦ P (a + u)) (Q (a + s)) s := by
    intro s hs
    exact (h16TestPair_centeredJet_hasDerivAt W r v phi hphi hsupp
      (a + s)).comp_const_add a s
  rw [map_sub]
  change P (a + h) - P a = ∫ s in (0 : ℝ)..h, Q (a + s)
  symm
  simpa only [add_zero] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      ((hQ.comp (continuous_const.add continuous_id)).intervalIntegrable 0 h)

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
