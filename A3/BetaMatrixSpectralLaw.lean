import A3.BetaMatrixPairLaw
import A3.BetaMatrixSpectralDensity

open MeasureTheory MeasureTheory.Measure Set
open LogdetLean.GramHafnian.UltimateHiding.DenseScore
open scoped BigOperators ENNReal
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace A3Research

variable {n : ℕ} {K : Type*} [RCLike K]
  [MeasureSpace K] [BorelSpace K] [PolishSpace K]
  [IsAddHaarMeasure (volume : Measure K)]

def betaMatrixProbabilityMeasure (n : ℕ) (K : Type*) [RCLike K]
    [MeasureSpace K] [BorelSpace K] (α δ : ℝ) : Measure (HermitianCoordinates n K) :=
  (betaMatrixRawMeasure n K α δ Set.univ)⁻¹ • betaMatrixRawMeasure n K α δ

theorem betaMatrixRawMeasure_mass_eq_weyl_betaJacobi (a b : ℝ) :
    betaMatrixRawMeasure n K ((Module.finrank ℝ K : ℝ) * ((n : ℝ) + a) / 2)
      ((Module.finrank ℝ K : ℝ) * ((n : ℝ) + b) / 2) Set.univ =
      ((hermitianWeylSymmetricIntegrationLaw n K).orbitConstant : ℝ≥0∞) *
        betaJacobiRawMeasure n a b (Module.finrank ℝ K) Set.univ := by
  have h := betaMatrixRawMeasure_symmetric_test_law (n := n) (K := K) a b
    (fun _ : Fin n → ℝ ↦ ()) measurable_const (fun _ _ ↦ rfl)
  have hm := congrArg (fun μ : Measure Unit ↦ μ Set.univ) h
  have hc : Measurable ((fun _ : Fin n → ℝ ↦ ()) ∘
      (canonicalHermitianSpectrum : HermitianCoordinates n K → _)) :=
    measurable_const.comp measurable_canonicalHermitianSpectrum
  rw [Measure.map_apply hc MeasurableSet.univ] at hm
  simpa only [Measure.map_apply measurable_const MeasurableSet.univ,
    Set.preimage_univ, Measure.smul_apply, smul_eq_mul] using hm

/-- Normalization cancels the actual angular constant and gives precisely the
paper's normalized beta-Jacobi law for every measurable symmetric test. -/
theorem betaMatrixProbabilityMeasure_symmetric_test_law
    (a b : ℝ) {Y : Type} [MeasurableSpace Y] (F : (Fin n → ℝ) → Y)
    (hF : Measurable F) (hperm : IsA2SymmetricTest F) :
    Measure.map (F ∘ canonicalHermitianSpectrum)
      (betaMatrixProbabilityMeasure n K ((Module.finrank ℝ K : ℝ) * ((n : ℝ) + a) / 2)
        ((Module.finrank ℝ K : ℝ) * ((n : ℝ) + b) / 2)) =
      Measure.map F (betaJacobiProbabilityMeasure n a b (Module.finrank ℝ K)) := by
  let C : ℝ≥0∞ := (hermitianWeylSymmetricIntegrationLaw n K).orbitConstant
  have hC0 : C ≠ 0 := by
    dsimp only [C]
    exact ENNReal.coe_ne_zero.mpr
      (hermitianWeylSymmetricIntegrationLaw n K).orbitConstant_pos.ne'
  have hCtop : C ≠ ∞ := ENNReal.coe_ne_top
  have hcoeff (Z : ℝ≥0∞) : (C * Z)⁻¹ * C = Z⁻¹ := by
    rw [ENNReal.mul_inv (Or.inl hC0) (Or.inl hCtop)]
    calc
      C⁻¹ * Z⁻¹ * C = (C⁻¹ * C) * Z⁻¹ := by ac_rfl
      _ = Z⁻¹ := by rw [ENNReal.inv_mul_cancel hC0 hCtop, one_mul]
  unfold betaMatrixProbabilityMeasure betaJacobiProbabilityMeasure
    H6RadialMeasureAdapters.normalizeMeasure
  rw [Measure.map_smul, betaMatrixRawMeasure_symmetric_test_law a b F hF hperm,
    betaMatrixRawMeasure_mass_eq_weyl_betaJacobi a b, smul_smul, Measure.map_smul]
  change ((C * _)⁻¹ * C) • _ = _
  rw [hcoeff]

end A3Research
