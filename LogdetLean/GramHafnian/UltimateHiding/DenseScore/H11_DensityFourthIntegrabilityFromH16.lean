import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16DirectL1WeakGenerator
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16ScaledScoreL1FromWeakFacts
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H5_FriedmanMelloA1Adapter
import Mathlib.Tactic

/-!
# Direct fixed-direction fourth-density integrability for H11

The proved H16 coordinate analysis already constructs every literal
zero-extended density jet through order four in `L¹`.  The older public
scaled-law adapter routed this fact through a weak-generator package, even
though its proof only needs the direct coordinate jet and the exact H5
coordinate law.  This file records that strictly lower direct adapter.

It is useful for the sign/normalization route to H11: integrability of the
fourth *density* score must be available before one solves the Bell identity
for the fourth *log* score.  No H11 moment statement is imported or used.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.LocalAnticoncentration

private theorem h11_h16_jet_at_zero_score_global
    {N K : ℕ} (hN : 1 ≤ N) (hK : 0 < K)
    (r : Fin 5) (v : ComplexUnitSphere N)
    (x : ComplexSymmetricCoordinates N) :
    h16CenteredTransportJet N K r v 0 x =
      h16ZeroExtendedConcreteCenteredDensityScore
          (r : ℕ) N K v
          (h16ScaledSymmetricCoordinateEmbedding N K x) *
        h16CenteredTransportJet N K 0 v 0 x := by
  by_cases hx : coeCornerSupport (complexSymmetricMatrixOfCoordinates x)
  · exact h16CenteredTransportJet_zero_eq_score_mul_density_pointwise
      hN hK r v x hx
  · have hout : x ∉ h16CenteredTransportSupport v 0 := by
      simpa [h16CenteredTransportSupport] using hx
    rw [h16CenteredTransportJet_zero_off_support r v 0 x hout]
    rw [h16CenteredTransportJet_zero_off_support (0 : Fin 5) v 0 x hout]
    simp

/-- Direct exact-H5 transfer of fixed-direction score integrability from
flat symmetric coordinates to the actual scaled COE law.  In particular,
the specialization `r = 4` is independent of every H8--H13 moment package. -/
theorem integrable_h16ZeroExtendedConcreteCenteredDensityScore_direct_exactH5
    (hH5 : H16ExactH5Family) {N K : ℕ}
    (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (r : Fin 5) (v : ComplexUnitSphere N) :
    Integrable
      (h16ZeroExtendedConcreteCenteredDensityScore (r : ℕ) N K v)
      (concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K) := by
  have hK : 0 < K := by omega
  rw [h16_scaledLaw_eq_map_coordinateProbabilityDensity_of_exactH5
    hH5 hN (by omega : 2 * N ≤ K)]
  rw [(measurableEmbedding_h16ScaledSymmetricCoordinateEmbedding hK).integrable_map_iff]
  change Integrable
    (fun x ↦ h16ZeroExtendedConcreteCenteredDensityScore
      (r : ℕ) N K v (h16ScaledSymmetricCoordinateEmbedding N K x))
    ((complexSymmetricCoordinateVolume N).withDensity
      (fun x ↦ (h16COECoordinateProbabilityWeight N K x : ℝ≥0∞)))
  rw [integrable_withDensity_iff_integrable_coe_smul
    (measurable_h16COECoordinateProbabilityWeight N K)]
  exact (integrable_h16CenteredTransportJet_direct_exactH5
    hH5 hN hboundary r v 0).congr <| by
      filter_upwards [] with x
      simp only [smul_eq_mul,
        h16COECoordinateProbabilityWeight_coe_real]
      rw [h11_h16_jet_at_zero_score_global hN hK r v x]
      rw [h16CenteredTransportJet_zero_eq_probabilityDensity]
      simp only [neg_zero, h16CenteredCoordinateFlow_zero]
      ring

/-- The concrete fourth-density section needed by the H11 Bell-sign route,
now with approved A1 as its only nonfoundational input. -/
theorem integrable_concreteCenteredDensityScore_four_fixedDirection_from_A1
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (v : ComplexUnitSphere N) :
    Integrable
      (h16ZeroExtendedConcreteCenteredDensityScore 4 N K v)
      (concreteScaledCOECornerLaw
    canonicalUnitaryHaarProbabilityFamily N K) := by
  let hH5 : H16ExactH5Family := by
    intro n k hn h2nk
    exact
      friedmanMello1985_unscaledCOECornerLaw_eq_determinantDensity_of_A1
        hn h2nk
  exact
    integrable_h16ZeroExtendedConcreteCenteredDensityScore_direct_exactH5
      hH5 hN hboundary (4 : Fin 5) v

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
