import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16OrderFourAnalyticCore
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
# H16 determinant radial and direct Gauss--Green reduction

This module isolates the exact geometric statements still missing from the
order-four zero-extension proof.  The fourth jet is controlled only in `L1`
by the sharp radial kernel `q ^ (alpha - 4)`.  Boundary traces occur only at
orders zero through three, on the determinant-superlevel exhaustion.

Nothing in this file assumes pointwise continuity of the fourth jet at the
boundary, a time-uniform pointwise fourth-jet dominator, an event derivative,
H5, or the H16 endpoint.  The final theorem proves the previously named
direct-IBP analytic core from three strictly geometric inputs:

* integrability of the determinant radial kernel (the Weyl--Takagi layer),
* an algebraic radial estimate for the literal fourth jet, and
* finite-domain Gauss--Green identities with vanishing boundary flux.
-/

open MeasureTheory Filter Set
open scoped ENNReal Topology ContDiff

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-! ## Literal determinant geometry in independent coordinates -/

/-- The real determinant gap `det (I - Cᴴ C)` in independent symmetric
coordinates. -/
def h16COECoordinateGapDeterminant (N : ℕ)
    (x : ComplexSymmetricCoordinates N) : ℝ :=
  let C := complexSymmetricMatrixOfCoordinates x
  (Matrix.det (1 - C.conjTranspose * C)).re

theorem h16COECoordinateGapDeterminant_pos
    {N : ℕ} {x : ComplexSymmetricCoordinates N}
    (hx : coeCornerSupport (complexSymmetricMatrixOfCoordinates x)) :
    0 < h16COECoordinateGapDeterminant N x := by
  exact (RCLike.lt_iff_re_im.mp hx.det_pos).1

theorem measurable_h16COECoordinateGapDeterminant (N : ℕ) :
    Measurable (h16COECoordinateGapDeterminant N) := by
  letI : OpensMeasurableSpace (ConcreteMatrixState N) :=
    Pi.opensMeasurableSpace
  have hden : Continuous (fun C : ConcreteMatrixState N ↦
      1 - C.conjTranspose * C) :=
    continuous_const.sub
      (continuous_id.matrix_conjTranspose.matrix_mul continuous_id)
  have hdet : Measurable (fun C : ConcreteMatrixState N ↦
      Matrix.det (1 - C.conjTranspose * C)) :=
    hden.matrix_det.measurable
  exact Complex.measurable_re.comp
    (hdet.comp (measurable_complexSymmetricMatrixOfCoordinates N))

/-- The exact open superlevel exhaustion used for direct integration by
parts.  As `epsilon -> 0+`, these sets exhaust the open determinant support. -/
def h16COECoordinateDeterminantSuperlevel
    (N : ℕ) (epsilon : ℝ) : Set (ComplexSymmetricCoordinates N) :=
  {x | coeCornerSupport (complexSymmetricMatrixOfCoordinates x) ∧
    epsilon < h16COECoordinateGapDeterminant N x}

theorem measurableSet_h16COECoordinateDeterminantSuperlevel
    (N : ℕ) (epsilon : ℝ) :
    MeasurableSet (h16COECoordinateDeterminantSuperlevel N epsilon) := by
  exact ((measurableSet_coeCornerSupport N).preimage
    (measurable_complexSymmetricMatrixOfCoordinates N)).inter
      (measurableSet_lt measurable_const
        (measurable_h16COECoordinateGapDeterminant N))

/-- The sharp order-four radial kernel.  It is zero off the open support;
at the minimal exponent it behaves like `q ^ (-1/2)` near the boundary. -/
def h16COEFourthRadialKernel (N K : ℕ)
    (x : ComplexSymmetricCoordinates N) : ℝ := by
  classical
  exact if coeCornerSupport (complexSymmetricMatrixOfCoordinates x) then
    (h16COECoordinateGapDeterminant N x) ^
      (coeCornerDensityExponent N K - 4)
  else 0

theorem h16COEFourthRadialKernel_nonnegative
    (N K : ℕ) (x : ComplexSymmetricCoordinates N) :
    0 ≤ h16COEFourthRadialKernel N K x := by
  classical
  unfold h16COEFourthRadialKernel
  split_ifs with hsupport
  · exact Real.rpow_nonneg
      (h16COECoordinateGapDeterminant_pos hsupport).le _
  · exact le_rfl

theorem measurable_h16COEFourthRadialKernel (N K : ℕ) :
    Measurable (h16COEFourthRadialKernel N K) := by
  classical
  have hrpow : Measurable (fun z : ℝ ↦
      z ^ (coeCornerDensityExponent N K - 4)) := by
    refine measurable_of_continuousOn_compl_singleton 0 ?_
    exact continuousOn_id.rpow_const fun z hz ↦
      Or.inl (by simpa using hz)
  unfold h16COEFourthRadialKernel
  exact Measurable.ite
    ((measurableSet_coeCornerSupport N).preimage
      (measurable_complexSymmetricMatrixOfCoordinates N))
    (hrpow.comp (measurable_h16COECoordinateGapDeterminant N))
    measurable_const

/-- The sharp Weyl--Takagi conclusion needed at order four.  This proposition
is deliberately only radial integrability; it contains no jet, flow,
generator, event, or derivative-chain conclusion. -/
abbrev H16COEFourthRadialIntegrability (N K : ℕ) : Prop :=
  Integrable (h16COEFourthRadialKernel N K)
    (complexSymmetricCoordinateVolume N)

/-- A convenient exact target for the missing Takagi/coarea calculation:
linear volume decay of small positive determinant sublevels. -/
def H16COEGapSublevelLinearBound (N : ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ eta : ℝ, eta ∈ Ioc (0 : ℝ) 1 →
    complexSymmetricCoordinateVolume N
        {x | coeCornerSupport (complexSymmetricMatrixOfCoordinates x) ∧
          0 < h16COECoordinateGapDeterminant N x ∧
          h16COECoordinateGapDeterminant N x ≤ eta} ≤
      ENNReal.ofReal (C * eta)

/-! ## Fourth-jet algebraic radial estimate -/

/-- The determinant algebra estimate for the literal fourth base jet.  Its
constant is uniform over projective directions, while the majorant is fixed
in the base coordinate space. -/
structure H16CenteredFourthJetRadialEstimate
    (N K : ℕ) : Type where
  constant : ℝ
  constant_nonnegative : 0 ≤ constant
  jet_aestronglyMeasurable :
    ∀ v : ComplexUnitSphere N,
      AEStronglyMeasurable (h16CenteredTransportJet N K 4 v 0)
        (complexSymmetricCoordinateVolume N)
  jet_norm_le :
    ∀ v : ComplexUnitSphere N,
      ∀ᵐ x ∂(complexSymmetricCoordinateVolume N),
        ‖h16CenteredTransportJet N K 4 v 0 x‖ ≤
          constant * h16COEFourthRadialKernel N K x

/-- The radial integrability and algebraic estimate imply genuine `L1`
integrability of the fourth base jet, without assigning any boundary trace
to that jet. -/
theorem h16CenteredBaseJetFourIntegrable_of_radial
    {N K : ℕ} (hradial : H16COEFourthRadialIntegrability N K)
    (hjet : H16CenteredFourthJetRadialEstimate N K) :
    H16CenteredBaseJetFourIntegrable N K := by
  intro v
  exact (hradial.const_mul hjet.constant).mono'
    (hjet.jet_aestronglyMeasurable v) (hjet.jet_norm_le v)

/-- The same data produce the fixed integrable fourth-jet majorant required
by the corrected weak-generator interface. -/
theorem integrable_h16CenteredFourthJetRadialMajorant
    {N K : ℕ} (hradial : H16COEFourthRadialIntegrability N K)
    (hjet : H16CenteredFourthJetRadialEstimate N K) :
    Integrable
      (fun x ↦ hjet.constant * h16COEFourthRadialKernel N K x)
      (complexSymmetricCoordinateVolume N) :=
  hradial.const_mul hjet.constant

theorem h16CenteredFourthJetRadialMajorant_nonnegative
    {N K : ℕ} (hjet : H16CenteredFourthJetRadialEstimate N K)
    (x : ComplexSymmetricCoordinates N) :
    0 ≤ hjet.constant * h16COEFourthRadialKernel N K x :=
  mul_nonneg hjet.constant_nonnegative
    (h16COEFourthRadialKernel_nonnegative N K x)

/-! ## Direct Gauss--Green on determinant superlevels -/

/-- Raw finite-domain Gauss--Green data for one generator identity.  The two
bulk terms are the literal restrictions to the determinant superlevel.
Only the order-`r` boundary flux is estimated, where `r : Fin 4`; no
order-four boundary estimate appears. -/
structure H16DirectGaussGreenLimitCertificate
    {N K : ℕ} (hboundary : 2 * N + 8 ≤ K)
    (r : Fin 4) (v : ComplexUnitSphere N)
    (phi : ComplexSymmetricCoordinates N → ℝ) : Type where
  boundaryFlux : ℝ → ℝ
  boundaryConstant : ℝ
  boundaryConstant_nonnegative : 0 ≤ boundaryConstant
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
  left_exhaustion_tendsto :
    Tendsto
      (fun epsilon ↦
        ∫ x in h16COECoordinateDeterminantSuperlevel N epsilon,
          h16CenteredTransportJet N K r.succ v 0 x * phi x
          ∂(complexSymmetricCoordinateVolume N))
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ x, h16CenteredTransportJet N K r.succ v 0 x * phi x
        ∂(complexSymmetricCoordinateVolume N)))
  right_exhaustion_tendsto :
    Tendsto
      (fun epsilon ↦
        ∫ x in h16COECoordinateDeterminantSuperlevel N epsilon,
          h16CenteredTransportJet N K r.castSucc v 0 x *
            (fderiv ℝ phi x) (h16CenteredCoordinateVectorField v x)
          ∂(complexSymmetricCoordinateVolume N))
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ x, h16CenteredTransportJet N K r.castSucc v 0 x *
        (fderiv ℝ phi x) (h16CenteredCoordinateVectorField v x)
        ∂(complexSymmetricCoordinateVolume N)))

/-- Direct Gauss--Green plus the proved scalar boundary exponent yields one
global weak-generator identity. -/
theorem h16_weakGeneratorIdentity_of_directGaussGreen
    {N K : ℕ} {hboundary : 2 * N + 8 ≤ K}
    {r : Fin 4} {v : ComplexUnitSphere N}
    {phi : ComplexSymmetricCoordinates N → ℝ}
    (H : H16DirectGaussGreenLimitCertificate hboundary r v phi) :
    (∫ x, h16CenteredTransportJet N K r.succ v 0 x * phi x
      ∂(complexSymmetricCoordinateVolume N)) =
    ∫ x, h16CenteredTransportJet N K r.castSucc v 0 x *
      (fderiv ℝ phi x) (h16CenteredCoordinateVectorField v x)
      ∂(complexSymmetricCoordinateVolume N) := by
  have hflux : Tendsto H.boundaryFlux (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    h16_boundary_trace_tendsto_zero_of_bound hboundary r
      H.boundaryFlux H.boundaryConstant H.boundaryConstant_nonnegative
      H.boundary_flux_bound
  have hsum := H.right_exhaustion_tendsto.add hflux
  have hfinite :
      (fun epsilon ↦
        ∫ x in h16COECoordinateDeterminantSuperlevel N epsilon,
          h16CenteredTransportJet N K r.succ v 0 x * phi x
          ∂(complexSymmetricCoordinateVolume N)) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun epsilon ↦
        (∫ x in h16COECoordinateDeterminantSuperlevel N epsilon,
          h16CenteredTransportJet N K r.castSucc v 0 x *
            (fderiv ℝ phi x) (h16CenteredCoordinateVectorField v x)
          ∂(complexSymmetricCoordinateVolume N)) +
          H.boundaryFlux epsilon) :=
    H.finite_domain_identity
  have hleft_from_finite := hsum.congr' hfinite.symm
  have hunique := tendsto_nhds_unique H.left_exhaustion_tendsto
    hleft_from_finite
  simpa only [add_zero] using hunique

/-- The exact finite-domain Gauss--Green family needed for all four weak
generator identities. -/
abbrev H16CenteredDirectGaussGreenFacts
    (N K : ℕ) (hboundary : 2 * N + 8 ≤ K) : Type :=
  ∀ (r : Fin 4) (v : ComplexUnitSphere N)
    (phi : ComplexSymmetricCoordinates N → ℝ),
    HasCompactSupport phi → ContDiff ℝ ∞ phi →
      H16DirectGaussGreenLimitCertificate hboundary r v phi

theorem h16CenteredWeakGeneratorChain_of_directGaussGreen
    {N K : ℕ} {hboundary : 2 * N + 8 ≤ K}
    (H : H16CenteredDirectGaussGreenFacts N K hboundary) :
    H16CenteredWeakGeneratorChain N K := by
  intro r v phi hcompact hsmooth
  exact h16_weakGeneratorIdentity_of_directGaussGreen
    (H r v phi hcompact hsmooth)

/-! ## Exact determinant-specific reduced endpoint -/

/-- The strictly geometric data remaining before the generic `L1` and
Bochner machinery.  This structure is not equivalent to H16: it contains no
event, H5, time-dependent `L1` derivative, `ContDiff`, or projective sphere
integral. -/
structure H16CenteredDirectGeometricInputs
    (N K : ℕ) (_hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K) : Type where
  fourthRadial_integrable : H16COEFourthRadialIntegrability N K
  fourthJet_radialEstimate : H16CenteredFourthJetRadialEstimate N K
  directGaussGreen : H16CenteredDirectGaussGreenFacts N K hboundary

/-- All determinant and limit deductions surrounding the two genuinely
geometric inputs are now kernel-checked: the inputs imply the complete
direct-IBP analytic core. -/
theorem H16CenteredDirectGeometricInputs.toDirectIBPAnalyticCore
    {N K : ℕ} {hN : 1 ≤ N} {hboundary : 2 * N + 8 ≤ K}
    (H : H16CenteredDirectGeometricInputs N K hN hboundary) :
    H16CenteredDirectIBPAnalyticCore N K hN hboundary where
  baseJetFour_integrable :=
    h16CenteredBaseJetFourIntegrable_of_radial
      H.fourthRadial_integrable H.fourthJet_radialEstimate
  weakGenerator_chain :=
    h16CenteredWeakGeneratorChain_of_directGaussGreen H.directGaussGreen

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
