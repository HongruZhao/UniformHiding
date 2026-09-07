import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16WeakFactsProof
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16CoordinateJacobianOne
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16DeterminantLocalLowerJetContinuity
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16FourthJetRadialBound
import Mathlib.Tactic

/-!
# A direct `L1` route to the H16 weak generator

This module constructs the literal centered jets in `L1` before any weak-facts
package has been assumed.  Exact H5, the proved coordinate Jacobian, the proved
lower-jet continuity, and the proved fourth radial estimate already give all
time-slice integrability.

The sole remaining direct analytic premise is the time-zero Banach derivative
chain for these canonical `L1` classes.  Differentiating a compact-test pairing
of that chain and differentiating the same pairing after measure-preserving
transport give the weak-generator identity by uniqueness of derivatives.  Thus
this premise replaces finite-perimeter and Gauss--Green data entirely.
-/

open MeasureTheory Filter Set
open scoped ContDiff ENNReal Topology Interval

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- Joint measurability of every literal jet, assembled from the proved
continuity through order three and the separate fourth-jet theorem. -/
theorem measurable_h16CenteredTransportJet_direct
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (r : Fin 5) :
    Measurable (fun p :
        (ComplexUnitSphere N × ℝ) × ComplexSymmetricCoordinates N ↦
      h16CenteredTransportJet N K r p.1.1 p.1.2 p.2) := by
  by_cases hr : (r : ℕ) < 4
  · let s : Fin 4 := ⟨r, hr⟩
    have hrs : s.castSucc = r := Fin.ext rfl
    simpa only [hrs] using
      (continuous_h16CenteredTransportJet_through_three
        hN hboundary s).measurable
  · have hr4 : r = (4 : Fin 5) := Fin.ext (by omega)
    simpa only [hr4] using
      measurable_h16CenteredTransportJet_four hN hboundary

private theorem h16_direct_baseJet_aestronglyMeasurable
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (r : Fin 5) (v : ComplexUnitSphere N) :
    AEStronglyMeasurable (h16CenteredTransportJet N K r v 0)
      (complexSymmetricCoordinateVolume N) := by
  have hparam : Measurable
      (fun x : ComplexSymmetricCoordinates N ↦ ((v, (0 : ℝ)), x)) :=
    measurable_const.prodMk measurable_id
  exact ((measurable_h16CenteredTransportJet_direct
    hN hboundary r).comp hparam).aestronglyMeasurable

private theorem h16_direct_baseJet_integrable
    (hH5 : H16ExactH5Family)
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (r : Fin 5) (v : ComplexUnitSphere N) :
    Integrable (h16CenteredTransportJet N K r v 0)
      (complexSymmetricCoordinateVolume N) := by
  by_cases hr : (r : ℕ) < 4
  · let s : Fin 4 := ⟨r, hr⟩
    have hrs : s.castSucc = r := Fin.ext rfl
    obtain ⟨b, hbnonneg, hbint, hbound⟩ :=
      exists_h16CenteredBaseJetLowerEnvelope_of_continuous
        (continuous_h16CenteredTransportJet_through_three hN hboundary)
        (fun q w t x hx ↦ h16CenteredTransportJet_zero_off_support
          q w t x hx)
        s
    exact hbint.mono'
      (h16_direct_baseJet_aestronglyMeasurable hN hboundary r v)
      (by
        exact ae_of_all _ fun x ↦ by
          have hx := hbound v x
          simpa only [hrs, Real.norm_eq_abs,
            abs_of_nonneg (hbnonneg x)] using hx)
  · have hr4 : r = (4 : Fin 5) := Fin.ext (by omega)
    subst r
    exact h16CenteredBaseJetFourIntegrable_of_exactH5
      hH5 hN hboundary
      (h16CenteredFourthJetRadialEstimate_proved hN hboundary) v

/-- Every literal time-slice jet is integrable, without weak-generator or
Gauss--Green input.  Integrability is transported from time zero by the proved
measure-preserving centered flow. -/
theorem integrable_h16CenteredTransportJet_direct_exactH5
    (hH5 : H16ExactH5Family)
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (r : Fin 5) (v : ComplexUnitSphere N) (t : ℝ) :
    Integrable (h16CenteredTransportJet N K r v t)
      (complexSymmetricCoordinateVolume N) := by
  have hbase := h16_direct_baseJet_integrable hH5 hN hboundary r v
  have hcomp : Integrable
      (h16CenteredTransportJet N K r v 0 ∘
        h16CenteredCoordinateFlow v (-t))
      (complexSymmetricCoordinateVolume N) :=
    (h16CenteredCoordinateFlow_measurePreserving_of_complexJacobianOne
      v (-t) ((h16CenteredCoordinateComplexJacobianFamily hN) v (-t))).integrable_comp_of_integrable
        hbase
  apply hcomp.congr
  exact ae_of_all _ fun x ↦
    (h16CenteredTransportJet_eq_zero_pullback r v t x).symm

/-- The canonical pre-weak `L1` class represented by the literal jet. -/
noncomputable def h16CenteredDirectJetLp
    (hH5 : H16ExactH5Family)
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (r : Fin 5) (v : ComplexUnitSphere N) (t : ℝ) :
    H16CenteredCoordinateL1 N :=
  (integrable_h16CenteredTransportJet_direct_exactH5
    hH5 hN hboundary r v t).toL1
      (h16CenteredTransportJet N K r v t)

theorem h16CenteredDirectJetLp_coeFn_ae
    (hH5 : H16ExactH5Family)
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (r : Fin 5) (v : ComplexUnitSphere N) (t : ℝ) :
    (fun x ↦ h16CenteredDirectJetLp hH5 hN hboundary r v t x) =ᵐ[
        complexSymmetricCoordinateVolume N]
      h16CenteredTransportJet N K r v t :=
  Integrable.coeFn_toL1
    (integrable_h16CenteredTransportJet_direct_exactH5
      hH5 hN hboundary r v t)

/-- The pre-weak time-`t` class is the measure-preserving pullback of its
time-zero class. -/
theorem h16CenteredDirectJetLp_eq_pullback_zero
    (hH5 : H16ExactH5Family)
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (r : Fin 5) (v : ComplexUnitSphere N) (t : ℝ) :
    h16CenteredDirectJetLp hH5 hN hboundary r v t =
      Lp.compMeasurePreserving
        (h16CenteredCoordinateFlow v (-t))
        (h16CenteredCoordinateFlow_measurePreserving_of_complexJacobianOne
          v (-t) ((h16CenteredCoordinateComplexJacobianFamily hN) v (-t)))
        (h16CenteredDirectJetLp hH5 hN hboundary r v 0) := by
  let hmp := h16CenteredCoordinateFlow_measurePreserving_of_complexJacobianOne
    v (-t) ((h16CenteredCoordinateComplexJacobianFamily hN) v (-t))
  apply Lp.ext
  filter_upwards [h16CenteredDirectJetLp_coeFn_ae
      hH5 hN hboundary r v t,
    Lp.coeFn_compMeasurePreserving
      (h16CenteredDirectJetLp hH5 hN hboundary r v 0) hmp,
    hmp.quasiMeasurePreserving.ae
      (h16CenteredDirectJetLp_coeFn_ae
        hH5 hN hboundary r v 0)] with x htx hpull hzero
  rw [htx, hpull]
  change h16CenteredTransportJet N K r v t x =
    h16CenteredDirectJetLp hH5 hN hboundary r v 0
      (h16CenteredCoordinateFlow v (-t) x)
  rw [hzero]
  exact h16CenteredTransportJet_eq_zero_pullback r v t x

/-- Every canonical pre-weak jet orbit is strongly continuous in `L1`.
This uses only the explicit centered matrix-exponential flow and
measure-preserving pullback, not the derivative premise. -/
theorem continuous_h16CenteredDirectJetLp_fixedDirection
    (hH5 : H16ExactH5Family)
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (r : Fin 5) (v : ComplexUnitSphere N) :
    Continuous (fun t : ℝ ↦
      h16CenteredDirectJetLp hH5 hN hboundary r v t) := by
  letI : IsLocallyFiniteMeasure (complexSymmetricCoordinateVolume N) := by
    rw [show complexSymmetricCoordinateVolume N =
        (volume : Measure (ComplexSymmetricCoordinates N)) by
      unfold complexSymmetricCoordinateVolume
      exact MeasureTheory.volume_pi.symm]
    infer_instance
  have hflow : Continuous (h16CenteredInverseCoordinateFlowCM v) :=
    continuous_h16CenteredInverseCoordinateFlowCM_of_matrixExp v
      (h16MatrixExponentialCurveContinuous_centered hN v)
  have hpull : Continuous (fun t : ℝ ↦
      Lp.compMeasurePreserving
        (h16CenteredInverseCoordinateFlowCM v t)
        (h16CenteredCoordinateFlow_measurePreserving_of_complexJacobianOne
          v (-t) ((h16CenteredCoordinateComplexJacobianFamily hN) v (-t)))
        (h16CenteredDirectJetLp hH5 hN hboundary r v 0)) := by
    exact continuous_const.compMeasurePreservingLp hflow
      (fun t ↦ h16CenteredCoordinateFlow_measurePreserving_of_complexJacobianOne
        v (-t) ((h16CenteredCoordinateComplexJacobianFamily hN) v (-t)))
      (by norm_num)
  apply hpull.congr
  intro t
  exact (h16CenteredDirectJetLp_eq_pullback_zero
    hH5 hN hboundary r v t).symm

/-- The exact pre-weak Banach-space input.  It contains only the four
time-zero `L1` derivative identities and no test function, boundary flux,
finite-perimeter datum, or Gauss--Green certificate. -/
abbrev H16CenteredDirectL1DerivativeAtZeroChain
    (hH5 : H16ExactH5Family)
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K) : Prop :=
  ∀ (r : Fin 4) (v : ComplexUnitSphere N),
    HasDerivAt
      (fun t : ℝ ↦
        h16CenteredDirectJetLp hH5 hN hboundary r.castSucc v t)
      (h16CenteredDirectJetLp hH5 hN hboundary r.succ v 0) 0

/-- The lower three slots of the direct chain.  Their successors are globally
continuous zero extensions, so these are the slots accessible to ordinary
compact domination once the pointwise boundary glue is established. -/
abbrev H16CenteredDirectLowerL1DerivativeAtZeroChain
    (hH5 : H16ExactH5Family)
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K) : Prop :=
  ∀ (r : Fin 4), (r : ℕ) < 3 → ∀ v : ComplexUnitSphere N,
    HasDerivAt
      (fun t : ℝ ↦
        h16CenteredDirectJetLp hH5 hN hboundary r.castSucc v t)
      (h16CenteredDirectJetLp hH5 hN hboundary r.succ v 0) 0

/-- The sharp top slot `3 → 4`.  At the endpoint boundary exponent its
target has the integrable `q^(-1/2)` singularity, so this is precisely where
a fixed pointwise dominated-convergence argument ceases to apply. -/
abbrev H16CenteredDirectFourthL1DerivativeAtZero
    (hH5 : H16ExactH5Family)
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K) : Prop :=
  ∀ v : ComplexUnitSphere N,
    HasDerivAt
      (fun t : ℝ ↦
        h16CenteredDirectJetLp hH5 hN hboundary (3 : Fin 5) v t)
      (h16CenteredDirectJetLp hH5 hN hboundary (4 : Fin 5) v 0) 0

/-- The lower chain and the single singular top slot reassemble the exact
four-slot direct derivative premise. -/
theorem h16CenteredDirectL1DerivativeAtZeroChain_of_lower_of_fourth
    (hH5 : H16ExactH5Family)
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (Hlower : H16CenteredDirectLowerL1DerivativeAtZeroChain
      hH5 hN hboundary)
    (Hfourth : H16CenteredDirectFourthL1DerivativeAtZero
      hH5 hN hboundary) :
    H16CenteredDirectL1DerivativeAtZeroChain hH5 hN hboundary := by
  intro r v
  by_cases hr : (r : ℕ) < 3
  · exact Hlower r hr v
  · have hr3 : r = (3 : Fin 4) := Fin.ext (by omega)
    subst r
    simpa using Hfourth v

private theorem continuous_h16_direct_testGenerator
    {N : ℕ} (hN : 1 ≤ N) (v : ComplexUnitSphere N)
    {phi : ComplexSymmetricCoordinates N → ℝ}
    (hphi : ContDiff ℝ ∞ phi) :
    Continuous (fun x ↦
      (fderiv ℝ phi x) (h16CenteredCoordinateVectorField v x)) := by
  exact ((hphi.continuous_fderiv (by simp)).clm_apply
    (continuous_h16CenteredCoordinateVectorField hN v))

private theorem hasCompactSupport_h16_direct_testGenerator
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
  exact zero_apply _

/-- Generic differentiation under the integral for an arbitrary integrable
base density against a transported compact test. -/
theorem h16_hasDerivAt_integral_mul_testFlow_of_integrable
    {N : ℕ} (hN : 1 ≤ N) (v : ComplexUnitSphere N)
    (j : ComplexSymmetricCoordinates N → ℝ)
    (hj : Integrable j (complexSymmetricCoordinateVolume N))
    (phi : ComplexSymmetricCoordinates N → ℝ)
    (hphi : ContDiff ℝ ∞ phi) (hsupp : HasCompactSupport phi)
    (t : ℝ) :
    HasDerivAt
      (fun u : ℝ ↦ ∫ y,
        j y * phi (h16CenteredCoordinateFlow v u y)
        ∂(complexSymmetricCoordinateVolume N))
      (∫ y, j y *
        (fderiv ℝ phi (h16CenteredCoordinateFlow v t y))
          (h16CenteredCoordinateVectorField v
            (h16CenteredCoordinateFlow v t y))
        ∂(complexSymmetricCoordinateVolume N)) t := by
  let μ := complexSymmetricCoordinateVolume N
  let q : ComplexSymmetricCoordinates N → ℝ := fun x ↦
    (fderiv ℝ phi x) (h16CenteredCoordinateVectorField v x)
  let F : ℝ → ComplexSymmetricCoordinates N → ℝ := fun u y ↦
    j y * phi (h16CenteredCoordinateFlow v u y)
  let F' : ℝ → ComplexSymmetricCoordinates N → ℝ := fun u y ↦
    j y * q (h16CenteredCoordinateFlow v u y)
  have hqcont : Continuous q :=
    continuous_h16_direct_testGenerator hN v hphi
  have hqsupp : HasCompactSupport q :=
    hasCompactSupport_h16_direct_testGenerator v hsupp
  obtain ⟨C, hC⟩ := hqcont.bounded_above_of_compact_support hqsupp
  obtain ⟨D, hD⟩ :=
    hphi.continuous.bounded_above_of_compact_support hsupp
  have hflow_cont (u : ℝ) :
      Continuous (h16CenteredCoordinateFlow v u) := by
    change Continuous (centeredTransposeCongruenceFlowCoordinateRealCLE v u)
    exact (centeredTransposeCongruenceFlowCoordinateRealCLE v u).continuous
  have hFint (u : ℝ) : Integrable (F u) μ := by
    apply hj.mul_bdd
    · exact (hphi.continuous.comp (hflow_cont u)).aestronglyMeasurable
    · exact ae_of_all _ fun y ↦ hD _
  have hF'int (u : ℝ) : Integrable (F' u) μ := by
    apply hj.mul_bdd
    · exact (hqcont.comp (hflow_cont u)).aestronglyMeasurable
    · exact ae_of_all _ fun y ↦ hC _
  have hbound_int : Integrable (fun y ↦ C * ‖j y‖) μ :=
    hj.norm.const_mul C
  have hresult := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := F) (F' := F') (bound := fun y ↦ C * ‖j y‖)
    (x₀ := t) (s := Set.univ)
    univ_mem
    (Filter.Eventually.of_forall fun u ↦ (hFint u).aestronglyMeasurable)
    (hFint t)
    (hF'int t).aestronglyMeasurable
    (ae_of_all _ fun y u hu ↦ by
      dsimp only [F', q]
      calc
        ‖j y *
            (fderiv ℝ phi (h16CenteredCoordinateFlow v u y))
              (h16CenteredCoordinateVectorField v
                (h16CenteredCoordinateFlow v u y))‖ =
            ‖j y‖ * ‖q (h16CenteredCoordinateFlow v u y)‖ :=
              norm_mul _ _
        _ ≤ ‖j y‖ * C :=
          mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
        _ = C * ‖j y‖ := mul_comm _ _)
    hbound_int
    (ae_of_all _ fun y u hu ↦ by
      have houter : HasFDerivAt phi
          (fderiv ℝ phi (h16CenteredCoordinateFlow v u y))
          (h16CenteredCoordinateFlow v u y) :=
        ((hphi.differentiable (by simp)).differentiableAt.hasFDerivAt)
      have hcomp := houter.comp_hasDerivAt u
        (h16CenteredCoordinateFlow_hasDerivAt hN v u y)
      have hmul := hcomp.const_mul (j y)
      simpa only [F, F', q, Function.comp_apply] using hmul)
  simpa only [F, F', q, μ] using hresult.2

private theorem h16TestPairCLM_directJet_eq_integral
    (hH5 : H16ExactH5Family)
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (r : Fin 5) (v : ComplexUnitSphere N) (t : ℝ)
    (phi : ComplexSymmetricCoordinates N → ℝ)
    (hphi : ContDiff ℝ ∞ phi) (hsupp : HasCompactSupport phi) :
    Conditional.h16TestPairCLM phi hphi hsupp
        (h16CenteredDirectJetLp hH5 hN hboundary r v t) =
      ∫ x, phi x * h16CenteredTransportJet N K r v t x
        ∂(complexSymmetricCoordinateVolume N) := by
  rw [Conditional.h16TestPairCLM_apply]
  apply integral_congr_ae
  filter_upwards [h16CenteredDirectJetLp_coeFn_ae
    hH5 hN hboundary r v t] with x hx
  rw [hx]

private theorem h16_integral_test_mul_centeredJet_eq_zero_transport_direct
    {N K : ℕ} (hN : 1 ≤ N)
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
  have hmp := h16CenteredCoordinateFlow_measurePreserving_of_complexJacobianOne
    v t ((h16CenteredCoordinateComplexJacobianFamily hN) v t)
  calc
    (∫ x, phi x * h16CenteredTransportJet N K r v t x
        ∂(complexSymmetricCoordinateVolume N)) =
        ∫ y, phi (h16CenteredCoordinateFlow v t y) *
          h16CenteredTransportJet N K r v t
            (h16CenteredCoordinateFlow v t y)
          ∂(complexSymmetricCoordinateVolume N) :=
      (hmp.integral_comp hEmb
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

/-- The direct time-zero `L1` derivative chain implies all four weak
generator identities.  This is the foundations-only bridge replacing the
sequential Gauss--Green input. -/
theorem h16CenteredWeakGeneratorChain_of_directL1Derivative
    (hH5 : H16ExactH5Family)
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (H : H16CenteredDirectL1DerivativeAtZeroChain
      hH5 hN hboundary) :
    H16CenteredWeakGeneratorChain N K := by
  intro r v phi hsupp hphi
  let P : H16CenteredCoordinateL1 N →L[ℝ] ℝ :=
    Conditional.h16TestPairCLM
      (μ := complexSymmetricCoordinateVolume N) phi hphi hsupp
  have hpair : HasDerivAt
      (fun t : ℝ ↦ P
        (h16CenteredDirectJetLp hH5 hN hboundary r.castSucc v t))
      (P (h16CenteredDirectJetLp hH5 hN hboundary r.succ v 0)) 0 :=
    P.hasFDerivAt.comp_hasDerivAt 0 (H r v)
  have hflow := h16_hasDerivAt_integral_mul_testFlow_of_integrable
    hN v (h16CenteredTransportJet N K r.castSucc v 0)
    (h16_direct_baseJet_integrable hH5 hN hboundary r.castSucc v)
    phi hphi hsupp 0
  have hfun :
      (fun t : ℝ ↦ P
        (h16CenteredDirectJetLp hH5 hN hboundary r.castSucc v t)) =
      (fun t : ℝ ↦ ∫ y,
        h16CenteredTransportJet N K r.castSucc v 0 y *
          phi (h16CenteredCoordinateFlow v t y)
        ∂(complexSymmetricCoordinateVolume N)) := by
    funext t
    rw [h16TestPairCLM_directJet_eq_integral
      hH5 hN hboundary r.castSucc v t phi hphi hsupp]
    rw [h16_integral_test_mul_centeredJet_eq_zero_transport_direct
      hN r.castSucc v t phi]
    apply integral_congr_ae
    exact ae_of_all _ fun y ↦ mul_comm _ _
  have hflow' : HasDerivAt
      (fun t : ℝ ↦ P
        (h16CenteredDirectJetLp hH5 hN hboundary r.castSucc v t))
      (∫ y, h16CenteredTransportJet N K r.castSucc v 0 y *
        (fderiv ℝ phi y) (h16CenteredCoordinateVectorField v y)
        ∂(complexSymmetricCoordinateVolume N)) 0 := by
    rw [hfun]
    simpa using hflow
  calc
    (∫ x, h16CenteredTransportJet N K r.succ v 0 x * phi x
        ∂(complexSymmetricCoordinateVolume N)) =
        ∫ x, phi x * h16CenteredTransportJet N K r.succ v 0 x
          ∂(complexSymmetricCoordinateVolume N) := by
      apply integral_congr_ae
      exact ae_of_all _ fun x ↦ mul_comm _ _
    _ = P (h16CenteredDirectJetLp
          hH5 hN hboundary r.succ v 0) :=
      (h16TestPairCLM_directJet_eq_integral
        hH5 hN hboundary r.succ v 0 phi hphi hsupp).symm
    _ = ∫ x, h16CenteredTransportJet N K r.castSucc v 0 x *
          (fderiv ℝ phi x) (h16CenteredCoordinateVectorField v x)
          ∂(complexSymmetricCoordinateVolume N) :=
      hpair.unique hflow'

private theorem h16CenteredDirectJetLp_eq_jetLpOfWeak
    (hH5 : H16ExactH5Family)
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (W : COECenteredOrderFourWeakGeneratorFacts N K hN hboundary)
    (r : Fin 5) (v : ComplexUnitSphere N) (t : ℝ) :
    h16CenteredDirectJetLp hH5 hN hboundary r v t =
      h16CenteredJetLpOfWeak W r v t := by
  apply Lp.ext
  filter_upwards [h16CenteredDirectJetLp_coeFn_ae
      hH5 hN hboundary r v t,
    h16CenteredJetLpOfWeak_coeFn_ae W r v t] with x hdirect hweak
  rw [hdirect, hweak]

/-- Conversely, a weak-generator chain gives the direct time-zero `L1`
derivative chain through the already proved scalar-to-Bochner bridge.  This
shows that, after the now-proved measurability, integrability, Jacobian, and
radial estimates, the direct `L1` premise is exactly the remaining analytic
content rather than a hidden finite-perimeter assumption. -/
theorem h16CenteredDirectL1DerivativeAtZeroChain_of_weakGenerator
    (hH5 : H16ExactH5Family)
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (G : H16CenteredWeakGeneratorChain N K) :
    H16CenteredDirectL1DerivativeAtZeroChain hH5 hN hboundary := by
  let A : H16CenteredWeakFactsAssemblyInputs N K hN hboundary :=
    { complexJacobian := h16CenteredCoordinateComplexJacobianFamily hN
      jet_joint_measurable :=
        measurable_h16CenteredTransportJet_direct hN hboundary
      continuous_through_three :=
        continuous_h16CenteredTransportJet_through_three hN hboundary
      fourthJet_radialEstimate :=
        h16CenteredFourthJetRadialEstimate_proved hN hboundary
      weakGenerator_chain := G }
  let W : COECenteredOrderFourWeakGeneratorFacts N K hN hboundary :=
    h16CenteredOrderFourWeakGeneratorFacts_of_assemblyInputs_exactH5 hH5 A
  intro r v
  have hfun :
      (fun t : ℝ ↦
        h16CenteredDirectJetLp hH5 hN hboundary r.castSucc v t) =
      (fun t : ℝ ↦ h16CenteredJetLpOfWeak W r.castSucc v t) := by
    funext t
    exact h16CenteredDirectJetLp_eq_jetLpOfWeak
      hH5 hN hboundary W r.castSucc v t
  rw [hfun, h16CenteredDirectJetLp_eq_jetLpOfWeak
    hH5 hN hboundary W r.succ v 0]
  exact h16CenteredJetLp_hasDerivAt_of_bochner W
    (h16CenteredShiftedBochnerIntervalChain_proved W) r v 0

/-- Exact equivalence between the pre-weak time-zero `L1` generator-domain
statement and the four global weak-generator identities. -/
theorem h16CenteredDirectL1DerivativeAtZeroChain_iff_weakGenerator
    (hH5 : H16ExactH5Family)
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K) :
    H16CenteredDirectL1DerivativeAtZeroChain hH5 hN hboundary ↔
      H16CenteredWeakGeneratorChain N K :=
  ⟨h16CenteredWeakGeneratorChain_of_directL1Derivative
      hH5 hN hboundary,
    h16CenteredDirectL1DerivativeAtZeroChain_of_weakGenerator
      hH5 hN hboundary⟩

/-- All other weak-facts assembly fields are the already proved analytic
theorems, so the direct `L1` premise alone inhabits the generic assembler. -/
noncomputable def h16CenteredWeakFactsAssemblyInputs_of_directL1Derivative
    (hH5 : H16ExactH5Family)
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (H : H16CenteredDirectL1DerivativeAtZeroChain
      hH5 hN hboundary) :
    H16CenteredWeakFactsAssemblyInputs N K hN hboundary where
  complexJacobian := h16CenteredCoordinateComplexJacobianFamily hN
  jet_joint_measurable :=
    measurable_h16CenteredTransportJet_direct hN hboundary
  continuous_through_three :=
    continuous_h16CenteredTransportJet_through_three hN hboundary
  fourthJet_radialEstimate :=
    h16CenteredFourthJetRadialEstimate_proved hN hboundary
  weakGenerator_chain :=
    h16CenteredWeakGeneratorChain_of_directL1Derivative
      hH5 hN hboundary H

/-- Complete corrected H16 weak facts from exact H5 and the direct time-zero
`L1` derivative chain, with no Gauss--Green input. -/
noncomputable def h16CenteredOrderFourWeakGeneratorFacts_of_directL1Derivative_exactH5
    (hH5 : H16ExactH5Family)
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (H : H16CenteredDirectL1DerivativeAtZeroChain
      hH5 hN hboundary) :
    COECenteredOrderFourWeakGeneratorFacts N K hN hboundary :=
  h16CenteredOrderFourWeakGeneratorFacts_of_assemblyInputs_exactH5
    hH5
    (h16CenteredWeakFactsAssemblyInputs_of_directL1Derivative
      hH5 hN hboundary H)

/-- Literal H16 from the direct `L1` derivative chain. -/
theorem coeCorner_centeredFixedDirection_eventPath_derivative_from_directL1_exactH5
    (hH5 : H16ExactH5Family)
    {N K r : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (hr : r ≤ 4) (v : ComplexUnitSphere N)
    (H : H16CenteredDirectL1DerivativeAtZeroChain
      hH5 hN hboundary)
    (event : Set (ConcreteMatrixState N)) (hevent : MeasurableSet event) :
    iteratedDeriv r (concreteCenteredRankOneCOEEventPath K v event) 0 =
      ∫ A, event.indicator
        (concreteCenteredDensityScore r N K v) A
        ∂(concreteScaledCOECornerLaw
          LogdetLean.GramHafnian.CurrentPRL.canonicalUnitaryHaarProbabilityFamily
            N K) :=
  coeCorner_centeredFixedDirection_eventPath_derivative_from_weakFacts_exactH5
    hH5 hN hboundary hr v
      (h16CenteredOrderFourWeakGeneratorFacts_of_directL1Derivative_exactH5
        hH5 hN hboundary H)
      event hevent

/-- Globally quantified family of direct time-zero `L1` derivative chains. -/
abbrev H16CenteredDirectL1DerivativeAtZeroFamily
    (hH5 : H16ExactH5Family) : Prop :=
  ∀ {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K),
    H16CenteredDirectL1DerivativeAtZeroChain hH5 hN hboundary

/-- Shared H16--H18 compact-`L1` handoff from the direct derivative family,
entirely bypassing finite perimeter and sequential Gauss--Green. -/
theorem h16DownstreamCompactL1ScientificInputs_of_directL1_exactH5
    (hH5 : H16ExactH5Family)
    (H : H16CenteredDirectL1DerivativeAtZeroFamily hH5) :
    H16DownstreamCompactL1ScientificInputs := by
  let W : H16CenteredWeakFactsFamily := fun hN hboundary ↦
    h16CenteredOrderFourWeakGeneratorFacts_of_directL1Derivative_exactH5
      hH5 hN hboundary (H hN hboundary)
  exact h16DownstreamCompactL1ScientificInputs_from_weakFacts_exactH5 hH5 W

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
