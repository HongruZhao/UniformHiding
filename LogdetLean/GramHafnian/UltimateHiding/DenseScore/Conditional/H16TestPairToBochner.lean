import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16TestPairBochnerReduction

/-!
# Specialization of compact-test uniqueness to H16 coordinates

This module isolates the tiny coordinate-specific separation step in the
already kernel-checked generic distribution-to-`L1` bridge.  Keeping that
step as an explicit foundational premise avoids unfolding the large
independent-coordinate type during the scientific reduction.
-/

open MeasureTheory
open scoped ContDiff

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

/-- Compactly supported smooth test pairings separate the concrete centered
coordinate `L1` space.  This is a purely foundational finite-dimensional
statement: it contains no determinant, jet, event, H5, or endpoint data. -/
def H16CenteredCoordinateTestPairingSeparates (N : ℕ) : Prop :=
  ∀ f g : H16CenteredCoordinateL1 N,
    (∀ (phi : ComplexSymmetricCoordinates N → ℝ)
      (hphi : ContDiff ℝ ∞ phi) (hsupp : HasCompactSupport phi),
      Conditional.h16TestPairCLM phi hphi hsupp f =
        Conditional.h16TestPairCLM phi hphi hsupp g) → f = g

set_option maxHeartbeats 2000000 in
/-- The shifted scalar compact-test identities lift to the shifted Bochner
identity once the coordinate test-separation fact is supplied.  The latter
is independent of every H16 scientific input. -/
theorem h16CenteredShiftedBochnerIntervalChain_of_testPair
    {N K : ℕ} {hN : 1 ≤ N} {hboundary : 2 * N + 8 ≤ K}
    (U : H16CenteredCoordinateTestPairingSeparates N)
    (W : COECenteredOrderFourWeakGeneratorFacts N K hN hboundary)
    (T : H16CenteredShiftedTestPairIntervalChain W) :
    H16CenteredShiftedBochnerIntervalChain W := by
  intro r v a h
  let G : ℝ → H16CenteredCoordinateL1 N := fun u ↦
    h16CenteredJetLpOfWeak W r.succ v (a + u)
  have hG : Continuous G :=
    (continuous_h16CenteredJetLpOfWeak_fixedDirection W r.succ v).comp
      (continuous_const.add continuous_id)
  apply U
  intro phi hphi hsupp
  rw [map_sub]
  rw [← (Conditional.h16TestPairCLM phi hphi hsupp).intervalIntegral_comp_comm
    (hG.intervalIntegrable 0 h)]
  simpa only [map_sub, G] using T r v a h phi hphi hsupp

/-- Universally quantified compact-test interval family corresponding to a
corrected weak-facts family. -/
def H16CenteredShiftedTestPairIntervalFamily
    (W : H16CenteredWeakFactsFamily) : Prop :=
  ∀ {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K),
    H16CenteredShiftedTestPairIntervalChain (W hN hboundary)

/-- Universally quantified foundational separation family for the concrete
centered coordinate spaces. -/
def H16CenteredCoordinateTestPairingSeparatesFamily : Prop :=
  ∀ N : ℕ, H16CenteredCoordinateTestPairingSeparates N

/-- The scalar compact-test chain, after the distributional uniqueness
specialization above, discharges exactly the four scientific inputs consumed
by U07's compact-`L1` H17/H18 assembly. -/
theorem h16DownstreamCompactL1ScientificInputs_of_testPair_exactH5
    (U : H16CenteredCoordinateTestPairingSeparatesFamily)
    (hH5 : H16ExactH5Family) (W : H16CenteredWeakFactsFamily)
    (T : H16CenteredShiftedTestPairIntervalFamily W) :
    H16DownstreamCompactL1ScientificInputs := by
  apply h16DownstreamCompactL1ScientificInputs_of_bochner_exactH5 hH5 W
  intro N K hN hboundary
  exact h16CenteredShiftedBochnerIntervalChain_of_testPair
    (U N) (W hN hboundary) (T hN hboundary)

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
