import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16WeakFactsAssembly
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16L1WeakBochnerBridge
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16CenteredL1OrbitDerived
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16ZeroExtensionDownstreamAssembly
import Mathlib.Tactic

/-!
# H16 scalar-test to Bochner reduction

This module isolates the exact last distributional transport statement.  A
shifted interval identity against compactly supported smooth scalar tests is
lifted, using distributional uniqueness, to the full `L1` Bochner identity.
It then proves the derivative tower, genuine fixed-direction `C^4`, the exact
H16 event derivative, and the four compact-`L1` inputs consumed downstream.

The remaining scalar-test identity is strictly below H16: it mentions no
event, totalized iterated derivative, projective integral, or compact-time
score envelope.  It is the direct target of the determinant-superlevel
Gauss--Green calculation with interior and boundary-layer cutoffs.
-/

open MeasureTheory Set
open scoped ContDiff ENNReal NNReal

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.CurrentPRL

/-- Shifted compact-test interval identities for the four successive
zero-extended coordinate jets.  This is the smallest scalar form needed by
the already proved distribution-to-`L1` bridge. -/
def H16CenteredShiftedTestPairIntervalChain
    {N K : ℕ} {hN : 1 ≤ N} {hboundary : 2 * N + 8 ≤ K}
    (W : COECenteredOrderFourWeakGeneratorFacts N K hN hboundary) : Prop :=
  ∀ (r : Fin 4) (v : ComplexUnitSphere N) (a h : ℝ)
    (phi : ComplexSymmetricCoordinates N → ℝ)
    (hphi : ContDiff ℝ ∞ phi) (hsupp : HasCompactSupport phi),
      Conditional.h16TestPairCLM phi hphi hsupp
          (h16CenteredJetLpOfWeak W r.castSucc v (a + h) -
            h16CenteredJetLpOfWeak W r.castSucc v a) =
        ∫ s in (0 : ℝ)..h,
          Conditional.h16TestPairCLM phi hphi hsupp
            (h16CenteredJetLpOfWeak W r.succ v (a + s))

/-- The exact shifted Bochner identity left after the scalar compact-test
Gauss--Green calculation.  The generic theorem
`Conditional.h16_l1_intervalIdentity_of_testPairing` proves the abstract
scalar-test-to-Bochner lift; instantiating its premise is kept logically
separate from this endpoint assembly. -/
def H16CenteredShiftedBochnerIntervalChain
    {N K : ℕ} {hN : 1 ≤ N} {hboundary : 2 * N + 8 ≤ K}
    (W : COECenteredOrderFourWeakGeneratorFacts N K hN hboundary) : Prop :=
  ∀ (r : Fin 4) (v : ComplexUnitSphere N) (a h : ℝ),
      h16CenteredJetLpOfWeak W r.castSucc v (a + h) -
          h16CenteredJetLpOfWeak W r.castSucc v a =
        ∫ s in (0 : ℝ)..h,
          h16CenteredJetLpOfWeak W r.succ v (a + s)

private theorem h16_hasDerivAt_of_shifted_fundamental_identity
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [CompleteSpace B]
    (F G : ℝ → B) (hG : Continuous G)
    (hfund : ∀ (a h : ℝ),
      F (a + h) - F a = ∫ s in (0 : ℝ)..h, G (a + s))
    (a : ℝ) : HasDerivAt F (G a) a := by
  let Gs : ℝ → B := fun s ↦ G (a + s)
  have hGs : Continuous Gs :=
    hG.comp (continuous_const.add continuous_id)
  have hint : HasDerivAt
      (fun h ↦ ∫ s in (0 : ℝ)..h, Gs s) (Gs 0) 0 :=
    intervalIntegral.integral_hasDerivAt_right
      (hGs.intervalIntegrable 0 0)
      hGs.aestronglyMeasurable.stronglyMeasurableAtFilter
      hGs.continuousAt
  have hq : HasDerivAt
      (fun t ↦ ∫ s in (0 : ℝ)..(t - a), Gs s) (G a) a := by
    have hint' : HasDerivAt
        (fun h ↦ ∫ s in (0 : ℝ)..h, Gs s) (Gs 0) (a - a) := by
      simpa using hint
    simpa only [Gs, add_zero] using hint'.comp_sub_const a a
  have heq : F = fun t ↦ F a + ∫ s in (0 : ℝ)..(t - a), Gs s := by
    funext t
    calc
      F t = F (a + (t - a)) := by congr 1 <;> ring
      _ = (F (a + (t - a)) - F a) + F a :=
        (sub_add_cancel _ _).symm
      _ = (∫ s in (0 : ℝ)..(t - a), G (a + s)) + F a := by
        rw [hfund a (t - a)]
      _ = F a + ∫ s in (0 : ℝ)..(t - a), Gs s := by
        rw [add_comm]
  rw [heq]
  exact hq.const_add (F a)

/-- The shifted Bochner chain yields every derivative in the canonical `L1`
jet tower. -/
theorem h16CenteredJetLp_hasDerivAt_of_bochner
    {N K : ℕ} {hN : 1 ≤ N} {hboundary : 2 * N + 8 ≤ K}
    (W : COECenteredOrderFourWeakGeneratorFacts N K hN hboundary)
    (B : H16CenteredShiftedBochnerIntervalChain W)
    (r : Fin 4) (v : ComplexUnitSphere N) (a : ℝ) :
    HasDerivAt
      (fun t ↦ h16CenteredJetLpOfWeak W r.castSucc v t)
      (h16CenteredJetLpOfWeak W r.succ v a) a := by
  apply h16_hasDerivAt_of_shifted_fundamental_identity
    (fun t ↦ h16CenteredJetLpOfWeak W r.castSucc v t)
    (fun t ↦ h16CenteredJetLpOfWeak W r.succ v t)
    (continuous_h16CenteredJetLpOfWeak_fixedDirection W r.succ v)
  exact fun b h ↦ B r v b h

/-- The five canonical `L1` representatives form a genuine order-four
Banach derivative tower. -/
theorem h16CenteredJetLp_fourJetTower_of_bochner
    {N K : ℕ} {hN : 1 ≤ N} {hboundary : 2 * N + 8 ≤ K}
    (W : COECenteredOrderFourWeakGeneratorFacts N K hN hboundary)
    (B : H16CenteredShiftedBochnerIntervalChain W)
    (v : ComplexUnitSphere N) :
    Conditional.H16L1FourJetTower
      (fun t ↦ h16CenteredJetLpOfWeak W 0 v t)
      (fun t ↦ h16CenteredJetLpOfWeak W 1 v t)
      (fun t ↦ h16CenteredJetLpOfWeak W 2 v t)
      (fun t ↦ h16CenteredJetLpOfWeak W 3 v t)
      (fun t ↦ h16CenteredJetLpOfWeak W 4 v t) where
  d01 := h16CenteredJetLp_hasDerivAt_of_bochner W B 0 v
  d12 := h16CenteredJetLp_hasDerivAt_of_bochner W B 1 v
  d23 := h16CenteredJetLp_hasDerivAt_of_bochner W B 2 v
  d34 := h16CenteredJetLp_hasDerivAt_of_bochner W B 3 v
  continuous_four :=
    continuous_h16CenteredJetLpOfWeak_fixedDirection W 4 v

/-- In particular, each fixed-direction density orbit is genuinely `C^4` in
`L1`; this statement is prior to applying any event functional. -/
theorem h16CenteredJetLp_contDiff_four_of_bochner
    {N K : ℕ} {hN : 1 ≤ N} {hboundary : 2 * N + 8 ≤ K}
    (W : COECenteredOrderFourWeakGeneratorFacts N K hN hboundary)
    (B : H16CenteredShiftedBochnerIntervalChain W)
    (v : ComplexUnitSphere N) :
    ContDiff ℝ 4 (fun t ↦ h16CenteredJetLpOfWeak W 0 v t) :=
  (h16CenteredJetLp_fourJetTower_of_bochner W B v).contDiff_four

/-- Every iterated derivative through order four is the corresponding
canonical zero-extended `L1` jet, so no totalization gap remains. -/
theorem h16CenteredJetLp_iteratedDeriv_of_bochner
    {N K : ℕ} {hN : 1 ≤ N} {hboundary : 2 * N + 8 ≤ K}
    (W : COECenteredOrderFourWeakGeneratorFacts N K hN hboundary)
    (B : H16CenteredShiftedBochnerIntervalChain W)
    (r : Fin 5) (v : ComplexUnitSphere N) (t : ℝ) :
    iteratedDeriv (r : ℕ)
        (fun u ↦ h16CenteredJetLpOfWeak W 0 v u) t =
      h16CenteredJetLpOfWeak W r v t := by
  have h01 : deriv (fun u ↦ h16CenteredJetLpOfWeak W 0 v u) =
      fun u ↦ h16CenteredJetLpOfWeak W 1 v u :=
    funext fun u ↦ (h16CenteredJetLp_hasDerivAt_of_bochner W B 0 v u).deriv
  have h12 : deriv (fun u ↦ h16CenteredJetLpOfWeak W 1 v u) =
      fun u ↦ h16CenteredJetLpOfWeak W 2 v u :=
    funext fun u ↦ (h16CenteredJetLp_hasDerivAt_of_bochner W B 1 v u).deriv
  have h23 : deriv (fun u ↦ h16CenteredJetLpOfWeak W 2 v u) =
      fun u ↦ h16CenteredJetLpOfWeak W 3 v u :=
    funext fun u ↦ (h16CenteredJetLp_hasDerivAt_of_bochner W B 2 v u).deriv
  have h34 : deriv (fun u ↦ h16CenteredJetLpOfWeak W 3 v u) =
      fun u ↦ h16CenteredJetLpOfWeak W 4 v u :=
    funext fun u ↦ (h16CenteredJetLp_hasDerivAt_of_bochner W B 3 v u).deriv
  fin_cases r <;>
    simp only [Fin.isValue, iteratedDeriv_zero, iteratedDeriv_succ,
      h01, h12, h23, h34] <;> rfl

/-! ## Actual event paths and the exact H16 endpoint -/

/-- The actual centered pushforward law is the moving normalized coordinate
density using only corrected weak facts. -/
theorem h16_map_scaledLaw_eq_map_coordinateMovingProbability_of_weakFacts
    (hH5 : H16ExactH5Family)
    {N K : ℕ} {hN : 1 ≤ N} {hboundary : 2 * N + 8 ≤ K}
    (W : COECenteredOrderFourWeakGeneratorFacts N K hN hboundary)
    (v : ComplexUnitSphere N) (t : ℝ) :
    Measure.map
        (transposeCongruenceFlow
          (concreteCenteredOrbitalDirection N v) t)
        (concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K) =
      Measure.map (h16ScaledSymmetricCoordinateEmbedding N K)
        ((complexSymmetricCoordinateVolume N).withDensity
          (fun x ↦
            (h16CenteredCoordinateProbabilityWeight K v t x : ℝ≥0∞))) := by
  have hmatrixFlow : Measurable
      (transposeCongruenceFlow
        (concreteCenteredOrbitalDirection N v) t) := by
    unfold transposeCongruenceFlow
    exact measurable_transposeCongruence _
  rw [h16_scaledLaw_eq_map_coordinateProbabilityDensity_of_exactH5
    hH5 hN (by omega : 2 * N ≤ K)]
  rw [Measure.map_map
    hmatrixFlow
    (measurable_h16ScaledSymmetricCoordinateEmbedding N K)]
  have hintertwine :
      transposeCongruenceFlow
          (concreteCenteredOrbitalDirection N v) t ∘
          h16ScaledSymmetricCoordinateEmbedding N K =
        h16ScaledSymmetricCoordinateEmbedding N K ∘
          h16CenteredCoordinateFlow v t := by
    funext x
    exact h16_centeredFlow_scaledCoordinateEmbedding v t x
  rw [hintertwine]
  rw [← Measure.map_map
    (measurable_h16ScaledSymmetricCoordinateEmbedding N K)
    (W.coordinate_measurePreserving v t).measurable]
  rw [h16_map_coordinateProbabilityDensity_centered_of_weakFacts W v t]

/-- Each event path is the fixed-set functional of the canonical `L1`
density orbit. -/
theorem h16_fixedDirection_eventPath_eq_coordinateSetIntegral_of_weakFacts
    (hH5 : H16ExactH5Family)
    {N K : ℕ} {hN : 1 ≤ N} {hboundary : 2 * N + 8 ≤ K}
    (W : COECenteredOrderFourWeakGeneratorFacts N K hN hboundary)
    (v : ComplexUnitSphere N) (event : Set (ConcreteMatrixState N))
    (hevent : MeasurableSet event) (t : ℝ) :
    concreteCenteredRankOneCOEEventPath K v event t =
      ∫ x in h16CenteredCoordinateEvent N K event,
        h16CenteredJetLpOfWeak W 0 v t x
        ∂(complexSymmetricCoordinateVolume N) := by
  unfold concreteCenteredRankOneCOEEventPath
  rw [h16_map_scaledLaw_eq_map_coordinateMovingProbability_of_weakFacts
    hH5 W v t]
  change
    (Measure.map (h16ScaledSymmetricCoordinateEmbedding N K)
      ((complexSymmetricCoordinateVolume N).withDensity
        (fun x ↦
          (h16CenteredCoordinateProbabilityWeight K v t x : ℝ≥0∞)))
      event).toReal = _
  rw [Measure.map_apply
    (measurable_h16ScaledSymmetricCoordinateEmbedding N K) hevent]
  change
    ((complexSymmetricCoordinateVolume N).withDensity
      (fun x ↦
        (h16CenteredCoordinateProbabilityWeight K v t x : ℝ≥0∞))).real
      (h16CenteredCoordinateEvent N K event) = _
  rw [← setIntegral_one_eq_measureReal]
  rw [setIntegral_withDensity_eq_setIntegral_smul
    (measurable_h16CenteredCoordinateProbabilityWeight W v t)
    (fun _ ↦ (1 : ℝ))
    (measurableSet_h16CenteredCoordinateEvent hevent)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae
      (h16CenteredJetLpOfWeak_coeFn_ae W 0 v t)] with x hx
  rw [hx, W.density_zero_eq_probabilityDensity v t x]
  simp only [h16CenteredCoordinateProbabilityWeight,
    NNReal.smul_def, h16COECoordinateProbabilityWeight_coe_real,
    smul_eq_mul, mul_one]

/-- The exact fixed-direction H16 endpoint follows from the scalar-test
transport chain.  All original quantifiers are preserved. -/
theorem coeCorner_centeredFixedDirection_eventPath_derivative_of_bochner
    (hH5 : H16ExactH5Family)
    {N K r : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (hr : r ≤ 4) (v : ComplexUnitSphere N)
    (W : COECenteredOrderFourWeakGeneratorFacts N K hN hboundary)
    (B : H16CenteredShiftedBochnerIntervalChain W)
    (event : Set (ConcreteMatrixState N)) (hevent : MeasurableSet event) :
    iteratedDeriv r (concreteCenteredRankOneCOEEventPath K v event) 0 =
      ∫ A, event.indicator
        (concreteCenteredDensityScore r N K v) A
        ∂(concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K) := by
  let rf : Fin 5 := ⟨r, by omega⟩
  have hpath : concreteCenteredRankOneCOEEventPath K v event =
      fun t ↦ ∫ x in h16CenteredCoordinateEvent N K event,
        h16CenteredJetLpOfWeak W 0 v t x
        ∂(complexSymmetricCoordinateVolume N) := by
    funext t
    exact h16_fixedDirection_eventPath_eq_coordinateSetIntegral_of_weakFacts
      hH5 W v event hevent t
  rw [hpath]
  calc
    iteratedDeriv r
        (fun t ↦ ∫ x in h16CenteredCoordinateEvent N K event,
          h16CenteredJetLpOfWeak W 0 v t x
          ∂(complexSymmetricCoordinateVolume N)) 0 =
      ∫ x in h16CenteredCoordinateEvent N K event,
        iteratedDeriv r
          (fun t ↦ h16CenteredJetLpOfWeak W 0 v t) 0 x
        ∂(complexSymmetricCoordinateVolume N) :=
      h16_iteratedDeriv_setIntegral_of_contDiff_L1
        (complexSymmetricCoordinateVolume N)
        (h16CenteredCoordinateEvent N K event)
        (h16CenteredJetLp_contDiff_four_of_bochner W B v) hr 0
    _ = ∫ x in h16CenteredCoordinateEvent N K event,
        h16CenteredJetLpOfWeak W rf v 0 x
        ∂(complexSymmetricCoordinateVolume N) := by
      rw [h16CenteredJetLp_iteratedDeriv_of_bochner W B rf v 0]
    _ = ∫ x in h16CenteredCoordinateEvent N K event,
        h16CenteredTransportJet N K rf v 0 x
        ∂(complexSymmetricCoordinateVolume N) := by
      exact integral_congr_ae
        (ae_restrict_of_ae
          (h16CenteredJetLpOfWeak_coeFn_ae W rf v 0))
    _ = ∫ A, event.indicator
        (concreteCenteredDensityScore r N K v) A
        ∂(concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K) := by
      simpa only [rf] using
        (h16_integral_indicator_score_scaledLaw_eq_setIntegral_centeredJet
          hH5 hN hboundary rf v event hevent).symm

/-- The same scalar-test chain gives genuine `C^4` for every measurable
fixed-direction event path. -/
theorem coeCorner_centeredFixedDirection_eventPath_contDiff_four_of_bochner
    (hH5 : H16ExactH5Family)
    {N K : ℕ} {hN : 1 ≤ N} {hboundary : 2 * N + 8 ≤ K}
    (W : COECenteredOrderFourWeakGeneratorFacts N K hN hboundary)
    (B : H16CenteredShiftedBochnerIntervalChain W)
    (v : ComplexUnitSphere N)
    (event : Set (ConcreteMatrixState N)) (hevent : MeasurableSet event) :
    ContDiff ℝ 4 (concreteCenteredRankOneCOEEventPath K v event) := by
  have hpath : concreteCenteredRankOneCOEEventPath K v event =
      fun t ↦ h16SetIntegralL1CLM
        (complexSymmetricCoordinateVolume N)
        (h16CenteredCoordinateEvent N K event)
        (h16CenteredJetLpOfWeak W 0 v t) := by
    funext t
    rw [h16_fixedDirection_eventPath_eq_coordinateSetIntegral_of_weakFacts
      hH5 W v event hevent t]
    exact (h16SetIntegralL1CLM_apply
      (complexSymmetricCoordinateVolume N)
      (h16CenteredCoordinateEvent N K event)
      (h16CenteredJetLpOfWeak W 0 v t)).symm
  rw [hpath]
  exact (h16SetIntegralL1CLM
    (complexSymmetricCoordinateVolume N)
    (h16CenteredCoordinateEvent N K event)).contDiff.fun_comp
      (h16CenteredJetLp_contDiff_four_of_bochner W B v)

/-! ## Universally quantified U07 adapter -/

abbrev H16CenteredWeakFactsFamily : Type :=
  ∀ {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K),
    COECenteredOrderFourWeakGeneratorFacts N K hN hboundary

def H16CenteredShiftedBochnerIntervalFamily
    (W : H16CenteredWeakFactsFamily) : Prop :=
  ∀ {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K),
    H16CenteredShiftedBochnerIntervalChain (W hN hboundary)

theorem h16DownstreamFixedDirectionH16_of_bochner
    (hH5 : H16ExactH5Family) (W : H16CenteredWeakFactsFamily)
    (B : H16CenteredShiftedBochnerIntervalFamily W) :
    H16DownstreamFixedDirectionH16Contract := by
  intro N K r hN hboundary hr v event hevent
  exact coeCorner_centeredFixedDirection_eventPath_derivative_of_bochner
    hH5 hN hboundary hr v (W hN hboundary) (B hN hboundary)
      event hevent

theorem h16DownstreamFixedDirectionC4_of_bochner
    (hH5 : H16ExactH5Family) (W : H16CenteredWeakFactsFamily)
    (B : H16CenteredShiftedBochnerIntervalFamily W) :
    H16DownstreamFixedDirectionC4Contract := by
  intro N K hN hboundary v event hevent
  exact coeCorner_centeredFixedDirection_eventPath_contDiff_four_of_bochner
    hH5 (W hN hboundary) (B hN hboundary) v event hevent

/-- Exact H5, the corrected weak facts, and only the shifted scalar-test
transport chain discharge exactly the four scientific inputs in U07's clean
H17/H18 compact-`L1` assembly. -/
theorem h16DownstreamCompactL1ScientificInputs_of_bochner_exactH5
    (hH5 : H16ExactH5Family) (W : H16CenteredWeakFactsFamily)
    (B : H16CenteredShiftedBochnerIntervalFamily W) :
    H16DownstreamCompactL1ScientificInputs where
  fixedDirectionH16 := h16DownstreamFixedDirectionH16_of_bochner hH5 W B
  fixedDirectionC4 := h16DownstreamFixedDirectionC4_of_bochner hH5 W B
  scaledCOESupport := h16DownstreamScaledCOESupport_of_exactH5 hH5
  compactZeroExtL1Envelope :=
    h16DownstreamCompactZeroExtL1Envelope_of_weakFacts_exactH5 hH5 W

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
