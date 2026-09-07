import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16BoundaryExponentFourInterface
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16CoordinateGeometry
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16AmbientDensity
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16BoundaryExhaustion
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# H16 centered zero extension: weak-generator interface

This module fixes the literal coordinate density, its globally zero-extended
interior jets, and the corrected geometric-measure contract.  Boundary traces
occur only for orders zero through three.  The fourth jet is required to be
measurable and `L1`, with a fixed integrable envelope after pullback by the
centered coordinate flow.

There is intentionally no pointwise order-four derivative-chain field and no
fixed ambient pointwise envelope uniform in time.  Exact H5 and events do not
occur in this interface.

This file is an uncompiled interface checkpoint.  It introduces no axiom and
does not assert that the structure below is inhabited.
-/

open MeasureTheory Filter
open scoped ENNReal Topology ContDiff

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- Total mass in the literal determinant-density normalization. -/
def h16COECoordinateRawMass (N K : ℕ) : ℝ≥0∞ :=
  coeCornerRawDeterminantDensityMeasure N K Set.univ

/-- Normalized real determinant density on independent symmetric
coordinates.  H5 is not used in this definition. -/
def h16COECoordinateProbabilityDensity (N K : ℕ)
    (x : ComplexSymmetricCoordinates N) : ℝ :=
  (h16COECoordinateRawMass N K)⁻¹.toReal *
    (coeCornerDeterminantWeight N K x).toReal

/-- Literal centered congruence flow on independent symmetric coordinates. -/
def h16CenteredCoordinateFlow {N : ℕ}
    (v : ComplexUnitSphere N) (t : ℝ)
    (x : ComplexSymmetricCoordinates N) :
    ComplexSymmetricCoordinates N :=
  transposeCongruenceFlowCoordinates
    (concreteCenteredOrbitalDirection N v) t x

/-- Moving open support, written as inverse image of the fixed matrix ball. -/
def h16CenteredTransportSupport {N : ℕ}
    (v : ComplexUnitSphere N) (t : ℝ) :
    Set (ComplexSymmetricCoordinates N) :=
  {x | coeCornerSupport <|
    complexSymmetricMatrixOfCoordinates
      (h16CenteredCoordinateFlow v (-t) x)}

/-- Real determinant of the inverse-flow gap matrix. -/
def h16CenteredTransportGapDeterminant {N : ℕ}
    (v : ComplexUnitSphere N) (t : ℝ)
    (x : ComplexSymmetricCoordinates N) : ℝ :=
  let C := complexSymmetricMatrixOfCoordinates
    (h16CenteredCoordinateFlow v (-t) x)
  (Matrix.det (1 - C.conjTranspose * C)).re

/-- Smooth interior expression before applying the moving-support indicator.
Only its values and derivatives at interior points are consumed. -/
def h16CenteredTransportInteriorDensity
    (N K : ℕ) (v : ComplexUnitSphere N) (t : ℝ)
    (x : ComplexSymmetricCoordinates N) : ℝ :=
  (h16COECoordinateRawMass N K)⁻¹.toReal *
    Real.rpow (h16CenteredTransportGapDeterminant v t x)
      (coeCornerDensityExponent N K)

/-- The literal order-`r` interior derivative, assigned zero globally away
from the moving open support.  In particular, the order-four boundary value
is zero by definition; no boundary continuity is asserted. -/
def h16CenteredTransportJet
    (N K : ℕ) (r : Fin 5) (v : ComplexUnitSphere N) (t : ℝ)
    (x : ComplexSymmetricCoordinates N) : ℝ := by
  classical
  exact if x ∈ h16CenteredTransportSupport v t then
    iteratedDeriv (r : ℕ)
      (fun u : ℝ ↦ h16CenteredTransportInteriorDensity N K v u x) t
  else 0

/-- The exact open support used for globally zero matrix-score
representatives. -/
def h16ScaledCOEOpenSupport (N K : ℕ) : Set (ConcreteMatrixState N) :=
  {A | (unscaleCOECorner K A).IsSymm ∧
    coeCornerSupport (unscaleCOECorner K A)}

/-- Literal centered density score, globally set to zero off scaled support. -/
def h16ZeroExtendedConcreteCenteredDensityScore
    (r N K : ℕ) (v : ComplexUnitSphere N) :
    ConcreteMatrixState N → ℝ :=
  (h16ScaledCOEOpenSupport N K).indicator
    (concreteCenteredDensityScore r N K v)

/-- Infinitesimal coordinate vector field of the forward centered flow.
The flow is smooth; using `deriv` here fixes the sign convention without
duplicating its matrix formula in the public interface. -/
def h16CenteredCoordinateVectorField {N : ℕ}
    (v : ComplexUnitSphere N) (x : ComplexSymmetricCoordinates N) :
    ComplexSymmetricCoordinates N :=
  deriv (fun t : ℝ ↦ h16CenteredCoordinateFlow v t x) 0

/-- Weak forward-generator identity with the inverse-pullback sign convention
used by `h16CenteredTransportJet`. -/
def COEWeakGeneratorIdentity {N : ℕ}
    (j jnext : ComplexSymmetricCoordinates N → ℝ)
    (X : ComplexSymmetricCoordinates N → ComplexSymmetricCoordinates N) :
    Prop :=
  ∀ phi : ComplexSymmetricCoordinates N → ℝ,
    HasCompactSupport phi → ContDiff ℝ ∞ phi →
      (∫ x, jnext x * phi x
        ∂(complexSymmetricCoordinateVolume N)) =
      ∫ x, j x * (fderiv ℝ phi x) (X x)
        ∂(complexSymmetricCoordinateVolume N)

/-- Corrected Gauss--Green/weak-generator facts for the literal jets.

The internal proof is expected to use the epsilon exhaustion, surface bounds,
boundary flux estimates for `Fin 4`, and an integrable fourth-jet majorant.
Only the resulting weak identities and estimates needed by the `L1` layer are
public fields. -/
structure COECenteredOrderFourWeakGeneratorFacts
    (N K : ℕ) (_hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K) : Type where
  scalar : COEBoundaryExponentFourFacts N K hboundary
  coordinate_measurePreserving :
    ∀ (v : ComplexUnitSphere N) (t : ℝ),
      MeasurePreserving
        (h16CenteredCoordinateFlow v t)
        (complexSymmetricCoordinateVolume N)
        (complexSymmetricCoordinateVolume N)
  density_zero_eq_probabilityDensity :
    ∀ (v : ComplexUnitSphere N) (t : ℝ)
      (x : ComplexSymmetricCoordinates N),
      h16CenteredTransportJet N K 0 v t x =
        h16COECoordinateProbabilityDensity N K
          (h16CenteredCoordinateFlow v (-t) x)
  jet_joint_measurable :
    ∀ r : Fin 5,
      Measurable (fun p :
          (ComplexUnitSphere N × ℝ) × ComplexSymmetricCoordinates N ↦
        h16CenteredTransportJet N K r p.1.1 p.1.2 p.2)
  jet_integrable :
    ∀ (r : Fin 5) (v : ComplexUnitSphere N) (t : ℝ),
      Integrable (h16CenteredTransportJet N K r v t)
        (complexSymmetricCoordinateVolume N)
  zero_off_support :
    ∀ (r : Fin 5) (v : ComplexUnitSphere N) (t : ℝ)
      (x : ComplexSymmetricCoordinates N),
      x ∉ h16CenteredTransportSupport v t →
        h16CenteredTransportJet N K r v t x = 0
  continuous_through_three :
    ∀ r : Fin 4,
      Continuous (fun p :
          (ComplexUnitSphere N × ℝ) × ComplexSymmetricCoordinates N ↦
        h16CenteredTransportJet N K r.castSucc p.1.1 p.1.2 p.2)
  baseJetMajorantFour : ComplexSymmetricCoordinates N → ℝ
  baseJetMajorantFour_nonnegative :
    ∀ x, 0 ≤ baseJetMajorantFour x
  baseJetMajorantFour_integrable :
    Integrable baseJetMajorantFour (complexSymmetricCoordinateVolume N)
  baseJet_four_le :
    ∀ v : ComplexUnitSphere N,
      ∀ᵐ x ∂(complexSymmetricCoordinateVolume N),
        ‖h16CenteredTransportJet N K 4 v 0 x‖ ≤
          baseJetMajorantFour x
  weak_generator_chain :
    ∀ (r : Fin 4) (v : ComplexUnitSphere N),
      COEWeakGeneratorIdentity
        (h16CenteredTransportJet N K r.castSucc v 0)
        (h16CenteredTransportJet N K r.succ v 0)
        (h16CenteredCoordinateVectorField v)
  pulledBack_L1_envelope :
    ∃ b : Fin 5 → ComplexSymmetricCoordinates N → ℝ,
      (∀ r, (∀ y, 0 ≤ b r y) ∧
        Integrable (b r) (complexSymmetricCoordinateVolume N)) ∧
      ∀ (r : Fin 5) (v : ComplexUnitSphere N) (t : ℝ),
        ∀ᵐ y ∂(complexSymmetricCoordinateVolume N),
          ‖h16CenteredTransportJet N K r v t
              (h16CenteredCoordinateFlow v t y)‖ ≤ b r y
  jet_at_zero_score :
    ∀ (r : Fin 5) (v : ComplexUnitSphere N),
      ∀ᵐ x ∂(complexSymmetricCoordinateVolume N),
        h16CenteredTransportJet N K r v 0 x =
          h16ZeroExtendedConcreteCenteredDensityScore
              (r : ℕ) N K v
              (h16ScaledSymmetricCoordinateEmbedding N K x) *
            h16CenteredTransportJet N K 0 v 0 x

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
