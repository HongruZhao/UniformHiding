import A3.HermitianWeylIntegration
import A3.HermitianSpectralNullity

open Set MeasureTheory MeasureTheory.Measure

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace A3Research

/-- The full raw Hermitian Weyl integration law. Every orbit, chart,
Jacobian, regularity and measure input is discharged on its actual carrier. -/
def hermitianWeylSymmetricIntegrationLaw (n : ℕ) (K : Type*) [RCLike K]
    [MeasureSpace K] [BorelSpace K] [PolishSpace K]
    [IsAddHaarMeasure (volume : Measure K)] : HermitianWeylSymmetricIntegrationLaw n K := by
  letI : IsAddHaarMeasure (hermitianCoordinateVolume n K) := by
    unfold hermitianCoordinateVolume
    exact prod.instIsAddHaarMeasure _ _
  apply hermitianWeylSymmetricIntegrationLaw_of_ae_regular n K
  simpa only [regularHermitianCoordinateSet, regularHermitianRadii,
    Set.mem_preimage, Set.mem_ofPred_eq] using
      (ae_injective_canonicalHermitianSpectrum (n := n) (K := K))

/-- Unconditional real-symmetric Weyl integration, with Vandermonde power one. -/
def hermitianWeylIntegration_real (n : ℕ) : HermitianWeylSymmetricIntegrationLaw n ℝ :=
  hermitianWeylSymmetricIntegrationLaw n ℝ

/-- Unconditional complex-Hermitian Weyl integration, with Vandermonde power two. -/
def hermitianWeylIntegration_complex (n : ℕ) : HermitianWeylSymmetricIntegrationLaw n ℂ :=
  hermitianWeylSymmetricIntegrationLaw n ℂ

end A3Research
