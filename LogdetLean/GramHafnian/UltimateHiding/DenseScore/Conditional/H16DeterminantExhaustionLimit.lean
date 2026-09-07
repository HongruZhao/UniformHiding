import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16DirectGaussGreenReduction
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Dominated convergence on the determinant-superlevel exhaustion

The two exhaustion-limit fields in the first direct Gauss--Green certificate
are not geometric assumptions.  For any integrable function that is zero off
the open determinant support, ordinary dominated convergence supplies the
limit.  Consequently the reduced finite-domain certificate below contains
only the actual Gauss--Green identity, the boundary-flux estimate, and bulk
integrability.
-/

open MeasureTheory Filter Set
open scoped Topology ContDiff

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- Set integrals over positive determinant superlevels converge to the
global integral of every integrable zero-extended function. -/
theorem h16_tendsto_setIntegral_determinantSuperlevel
    {N : ℕ} {f : ComplexSymmetricCoordinates N → ℝ}
    (hf : Integrable f (complexSymmetricCoordinateVolume N))
    (hzero : ∀ x, ¬coeCornerSupport
        (complexSymmetricMatrixOfCoordinates x) → f x = 0) :
    Tendsto
      (fun epsilon ↦
        ∫ x in h16COECoordinateDeterminantSuperlevel N epsilon, f x
          ∂(complexSymmetricCoordinateVolume N))
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ x, f x ∂(complexSymmetricCoordinateVolume N))) := by
  let F : ℝ → ComplexSymmetricCoordinates N → ℝ := fun epsilon ↦
    (h16COECoordinateDeterminantSuperlevel N epsilon).indicator f
  have hFmeas : ∀ᶠ epsilon : ℝ in 𝓝[>] (0 : ℝ),
      AEStronglyMeasurable (F epsilon)
        (complexSymmetricCoordinateVolume N) := by
    filter_upwards [] with epsilon
    exact hf.aestronglyMeasurable.indicator
      (measurableSet_h16COECoordinateDeterminantSuperlevel N epsilon)
  have hbound : ∀ᶠ epsilon : ℝ in 𝓝[>] (0 : ℝ),
      ∀ᵐ x ∂(complexSymmetricCoordinateVolume N),
        ‖F epsilon x‖ ≤ ‖f x‖ := by
    filter_upwards [] with epsilon
    exact ae_of_all _ fun x ↦ norm_indicator_le_norm_self _ _
  have hlim : ∀ᵐ x ∂(complexSymmetricCoordinateVolume N),
      Tendsto (fun epsilon ↦ F epsilon x)
        (𝓝[>] (0 : ℝ)) (𝓝 (f x)) := by
    apply ae_of_all
    intro x
    by_cases hx : coeCornerSupport
        (complexSymmetricMatrixOfCoordinates x)
    · have hgap : 0 < h16COECoordinateGapDeterminant N x :=
        h16COECoordinateGapDeterminant_pos hx
      have hevent : ∀ᶠ epsilon : ℝ in 𝓝[>] (0 : ℝ),
          epsilon < h16COECoordinateGapDeterminant N x := by
        rw [eventually_nhdsWithin_iff, eventually_nhds_iff]
        exact ⟨Iio (h16COECoordinateGapDeterminant N x),
          fun _ h _ ↦ h, isOpen_Iio,
          by simpa only [mem_Iio] using hgap⟩
      apply tendsto_const_nhds.congr'
      filter_upwards [hevent] with epsilon hepsilon
      simp [F, h16COECoordinateDeterminantSuperlevel, hx, hepsilon]
    · have hfx : f x = 0 := hzero x hx
      rw [hfx]
      apply tendsto_const_nhds.congr'
      filter_upwards [] with epsilon
      simp [F, h16COECoordinateDeterminantSuperlevel, hx]
  have hdom := tendsto_integral_filter_of_dominated_convergence
    (fun x ↦ ‖f x‖) hFmeas hbound hf.norm hlim
  simpa only [F, integral_indicator
    (measurableSet_h16COECoordinateDeterminantSuperlevel N _)] using hdom

/-- Finite-domain Gauss--Green data after removing the automatic exhaustion
limits.  The successor and generator bulk terms are required only to be
integrable; no pointwise boundary regularity at order four is present. -/
structure H16FiniteGaussGreenCertificate
    {N K : ℕ} (hboundary : 2 * N + 8 ≤ K)
    (r : Fin 4) (v : ComplexUnitSphere N)
    (phi : ComplexSymmetricCoordinates N → ℝ) : Type where
  boundaryFlux : ℝ → ℝ
  boundaryConstant : ℝ
  boundaryConstant_nonnegative : 0 ≤ boundaryConstant
  left_integrable : Integrable
    (fun x ↦ h16CenteredTransportJet N K r.succ v 0 x * phi x)
    (complexSymmetricCoordinateVolume N)
  right_integrable : Integrable
    (fun x ↦ h16CenteredTransportJet N K r.castSucc v 0 x *
      (fderiv ℝ phi x) (h16CenteredCoordinateVectorField v x))
    (complexSymmetricCoordinateVolume N)
  finite_domain_identity :
    ∀ᶠ epsilon : ℝ in 𝓝[>] (0 : ℝ),
      (∫ x in h16COECoordinateDeterminantSuperlevel N epsilon,
          h16CenteredTransportJet N K r.succ v 0 x * phi x
          ∂(complexSymmetricCoordinateVolume N)) =
        (∫ x in h16COECoordinateDeterminantSuperlevel N epsilon,
          h16CenteredTransportJet N K r.castSucc v 0 x *
            (fderiv ℝ phi x) (h16CenteredCoordinateVectorField v x)
          ∂(complexSymmetricCoordinateVolume N)) +
          boundaryFlux epsilon
  boundary_flux_bound :
    ∀ᶠ epsilon : ℝ in 𝓝[>] (0 : ℝ),
      ‖boundaryFlux epsilon‖ ≤ boundaryConstant * epsilon ^
        (coeCornerDensityExponent N K - ((r : ℕ) : ℝ))

private theorem h16_zero_off_base_coordinateSupport
    {N K : ℕ} (r : Fin 5) (v : ComplexUnitSphere N)
    (x : ComplexSymmetricCoordinates N)
    (hx : ¬coeCornerSupport (complexSymmetricMatrixOfCoordinates x)) :
    h16CenteredTransportJet N K r v 0 x = 0 := by
  apply h16CenteredTransportJet_zero_off_support
  simpa [h16CenteredTransportSupport] using hx

/-- The smaller finite certificate canonically supplies the earlier limit
certificate. -/
def H16FiniteGaussGreenCertificate.toLimitCertificate
    {N K : ℕ} {hboundary : 2 * N + 8 ≤ K}
    {r : Fin 4} {v : ComplexUnitSphere N}
    {phi : ComplexSymmetricCoordinates N → ℝ}
    (H : H16FiniteGaussGreenCertificate hboundary r v phi) :
    H16DirectGaussGreenLimitCertificate hboundary r v phi where
  boundaryFlux := H.boundaryFlux
  boundaryConstant := H.boundaryConstant
  boundaryConstant_nonnegative := H.boundaryConstant_nonnegative
  finite_domain_identity := H.finite_domain_identity
  boundary_flux_bound := H.boundary_flux_bound
  left_exhaustion_tendsto :=
    h16_tendsto_setIntegral_determinantSuperlevel H.left_integrable
      (fun x hx ↦ by
        rw [h16_zero_off_base_coordinateSupport r.succ v x hx]
        simp)
  right_exhaustion_tendsto :=
    h16_tendsto_setIntegral_determinantSuperlevel H.right_integrable
      (fun x hx ↦ by
        rw [h16_zero_off_base_coordinateSupport r.castSucc v x hx]
        simp)

/-- One finite-domain Gauss--Green identity and its true boundary estimate
imply the global weak-generator identity. -/
theorem h16_weakGeneratorIdentity_of_finiteGaussGreen
    {N K : ℕ} {hboundary : 2 * N + 8 ≤ K}
    {r : Fin 4} {v : ComplexUnitSphere N}
    {phi : ComplexSymmetricCoordinates N → ℝ}
    (H : H16FiniteGaussGreenCertificate hboundary r v phi) :
    (∫ x, h16CenteredTransportJet N K r.succ v 0 x * phi x
      ∂(complexSymmetricCoordinateVolume N)) =
    ∫ x, h16CenteredTransportJet N K r.castSucc v 0 x *
      (fderiv ℝ phi x) (h16CenteredCoordinateVectorField v x)
      ∂(complexSymmetricCoordinateVolume N) :=
  h16_weakGeneratorIdentity_of_directGaussGreen H.toLimitCertificate

/-- Exact smaller family now targeted by the spectral-ball Gauss--Green
proof. -/
abbrev H16CenteredFiniteGaussGreenFacts
    (N K : ℕ) (hboundary : 2 * N + 8 ≤ K) : Type :=
  ∀ (r : Fin 4) (v : ComplexUnitSphere N)
    (phi : ComplexSymmetricCoordinates N → ℝ),
    HasCompactSupport phi → ContDiff ℝ ∞ phi →
      H16FiniteGaussGreenCertificate hboundary r v phi

theorem h16CenteredWeakGeneratorChain_of_finiteGaussGreen
    {N K : ℕ} {hboundary : 2 * N + 8 ≤ K}
    (H : H16CenteredFiniteGaussGreenFacts N K hboundary) :
    H16CenteredWeakGeneratorChain N K := by
  intro r v phi hcompact hsmooth
  exact h16_weakGeneratorIdentity_of_finiteGaussGreen
    (H r v phi hcompact hsmooth)

/-- Final sharpened determinant-specific blocker after automatic exhaustion
limits have been removed.  It contains only the Weyl--Takagi radial `L1`
input, the algebraic fourth-jet radial bound, and finite-domain
Gauss--Green/bulk-integrability data. -/
structure H16CenteredFiniteGeometricInputs
    (N K : ℕ) (_hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K) : Type where
  fourthRadial_integrable : H16COEFourthRadialIntegrability N K
  fourthJet_radialEstimate : H16CenteredFourthJetRadialEstimate N K
  finiteGaussGreen : H16CenteredFiniteGaussGreenFacts N K hboundary

theorem H16CenteredFiniteGeometricInputs.toDirectIBPAnalyticCore
    {N K : ℕ} {hN : 1 ≤ N} {hboundary : 2 * N + 8 ≤ K}
    (H : H16CenteredFiniteGeometricInputs N K hN hboundary) :
    H16CenteredDirectIBPAnalyticCore N K hN hboundary where
  baseJetFour_integrable :=
    h16CenteredBaseJetFourIntegrable_of_radial
      H.fourthRadial_integrable H.fourthJet_radialEstimate
  weakGenerator_chain :=
    h16CenteredWeakGeneratorChain_of_finiteGaussGreen H.finiteGaussGreen

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
