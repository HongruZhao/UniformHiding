import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16CenteredL1Orbit
import Mathlib.Tactic

/-!
# Projective compact-time `L1` envelope from the corrected weak facts

The corrected weak-generator interface supplies an integrable envelope after
pullback to the fixed base support.  Since the centered coordinate flow is
measure preserving, its pullback action on `L1` is an isometry.  Consequently
the integral of that one base envelope bounds every direction and every time.

This is stronger than compact-time control and remains valid for the fourth
jet, which is only an `L1` representative at the boundary.
-/

open MeasureTheory
open scoped ENNReal Topology

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- The integral of the pulled-back base envelope bounds the `L1` norm of
every literal jet orbit, uniformly in direction and time. -/
theorem h16CenteredJetLp_norm_le_pulledBackEnvelopeIntegral
    {N K : ℕ} {hN : 1 ≤ N} {hboundary : 2 * N + 8 ≤ K}
    (W : COECenteredOrderFourWeakGeneratorFacts N K hN hboundary)
    (b : Fin 5 → ComplexSymmetricCoordinates N → ℝ)
    (hb : ∀ r, (∀ y, 0 ≤ b r y) ∧
      Integrable (b r) (complexSymmetricCoordinateVolume N))
    (hbound : ∀ (r : Fin 5) (v : ComplexUnitSphere N) (t : ℝ),
      ∀ᵐ y ∂(complexSymmetricCoordinateVolume N),
        ‖h16CenteredTransportJet N K r v t
            (h16CenteredCoordinateFlow v t y)‖ ≤ b r y)
    (r : Fin 5) (v : ComplexUnitSphere N) (t : ℝ) :
    ‖h16CenteredJetLpOfWeak W r v t‖ ≤
      ∫ y, b r y ∂(complexSymmetricCoordinateVolume N) := by
  have hbaseBound :
      ‖h16CenteredJetLpOfWeak W r v 0‖ ≤
        ∫ y, b r y ∂(complexSymmetricCoordinateVolume N) := by
    rw [L1.norm_eq_integral_norm]
    calc
      (∫ y, ‖h16CenteredJetLpOfWeak W r v 0 y‖
          ∂(complexSymmetricCoordinateVolume N)) =
          ∫ y, ‖h16CenteredTransportJet N K r v 0 y‖
            ∂(complexSymmetricCoordinateVolume N) := by
        exact integral_congr_ae
          ((h16CenteredJetLpOfWeak_coeFn_ae W r v 0).fun_comp
            fun z : ℝ ↦ ‖z‖)
      _ ≤ ∫ y, b r y ∂(complexSymmetricCoordinateVolume N) := by
        apply integral_mono_ae (W.jet_integrable r v 0).norm (hb r).2
        filter_upwards [hbound r v 0] with y hy
        simpa only [h16CenteredCoordinateFlow_zero] using hy
  rw [h16CenteredJetLpOfWeak_eq_pullback_zero]
  simpa only [Lp.norm_compMeasurePreserving] using hbaseBound

/-- Every corrected weak-generator package supplies the exact projective
compact-time envelope required by the order-four `L1` interface.  The bound
is actually uniform over all real times. -/
theorem h16CenteredJetLp_projective_compactTime_L1_envelope_of_weakFacts
    {N K : ℕ} {hN : 1 ≤ N} {hboundary : 2 * N + 8 ≤ K}
    (W : COECenteredOrderFourWeakGeneratorFacts N K hN hboundary)
    (r : Fin 5) (R : ℝ) :
    ∃ G : ComplexUnitSphere N → ℝ,
      (∀ v, 0 ≤ G v) ∧
      Integrable G (complexUnitSphereProbabilityMeasure N) ∧
      ∀ (v : ComplexUnitSphere N) (t : ℝ),
        |t| ≤ R → ‖h16CenteredJetLpOfWeak W r v t‖ ≤ G v := by
  obtain ⟨b, hb, hbound⟩ := W.pulledBack_L1_envelope
  let B : ℝ := ∫ y, b r y ∂(complexSymmetricCoordinateVolume N)
  let G : ComplexUnitSphere N → ℝ := fun _ ↦ B
  have hB : 0 ≤ B := integral_nonneg (hb r).1
  letI : IsProbabilityMeasure (complexUnitSphereProbabilityMeasure N) :=
    complexUnitSphereProbabilityMeasure_isProbability hN
  refine ⟨G, fun _ ↦ hB, integrable_const B, ?_⟩
  intro v t ht
  exact h16CenteredJetLp_norm_le_pulledBackEnvelopeIntegral
    W b hb hbound r v t

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
