import A3.BetaMatrixStatistic
import A3.HermitianCongruenceMeasure

open scoped BigOperators Matrix.Norms.Elementwise ComplexOrder MatrixOrder ENNReal
open Matrix MeasureTheory Set
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace A3Research

variable {n : ℕ} {K : Type*} [RCLike K]
  [MeasureSpace K] [BorelSpace K] [PolishSpace K]
  [(hermitianCoordinateVolume n K).IsAddHaarMeasure]

/-- Exact linear substitution in the literal independent Hermitian volume. -/
theorem lintegral_hermitianCongruence
    {C : Matrix (Fin n) (Fin n) K} (hC : C.PosDef)
    (f : HermitianCoordinates n K → ℝ≥0∞) :
    ∫⁻ x, f x ∂(hermitianCoordinateVolume n K) =
      ∫⁻ x, ENNReal.ofReal |LinearMap.det (hermitianCoordinateConjugationLinearMap C)| *
        f (hermitianCoordinateConjugationLinearMap C x) ∂(hermitianCoordinateVolume n K) := by
  let J : ℝ := (RCLike.re C.det) ^ (2 + Module.finrank ℝ K * (n - 1))
  have hJ : 0 < J := pow_pos (re_det_pos_of_posDef hC) _
  have hmeasure : ENNReal.ofReal J •
      Measure.map (hermitianCoordinateConjugationLinearMap C)
        (hermitianCoordinateVolume n K) = hermitianCoordinateVolume n K := by
    rw [map_hermitianCongruence_volume hC, smul_smul]
    change (ENNReal.ofReal J * ENNReal.ofReal J⁻¹) • _ = _
    rw [← ENNReal.ofReal_mul hJ.le, mul_inv_cancel₀ hJ.ne', ENNReal.ofReal_one, one_smul]
  calc
    _ = ∫⁻ x, f x ∂(ENNReal.ofReal J • Measure.map
        (hermitianCoordinateConjugationLinearMap C) (hermitianCoordinateVolume n K)) := by
      rw [hmeasure]
    _ = ENNReal.ofReal J * ∫⁻ x, f (hermitianCoordinateConjugationLinearMap C x)
        ∂(hermitianCoordinateVolume n K) := by
      rw [lintegral_smul_measure, (measurableEmbedding_hermitianCongruence hC.isUnit).lintegral_map]
      rfl
    _ = _ := by
      rw [abs_det_hermitianCoordinateConjugation_posDef hC,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- Pointwise density identity, including points outside the beta cone. -/
theorem wishartAmbientDensity_pair_jacobian
    (hn : 1 ≤ n) (α δ : ℝ) {C : Matrix (Fin n) (Fin n) K} (hC : C.PosDef)
    (x : HermitianCoordinates n K) :
    ENNReal.ofReal |LinearMap.det (hermitianCoordinateConjugationLinearMap C)| *
      (wishartAmbientDensity n K α (hermitianCoordinateConjugationLinearMap C x) *
        wishartAmbientDensity n K δ (hermitianCoordinateConjugationLinearMap C
          (hermitianComplementCoordinates x))) =
      wishartAmbientDensity n K (α + δ) (hermitianCoordinateProjection (C * C)) *
        betaMatrixDensity n K α δ x := by
  classical
  have hS : (C * C).PosDef := by
    simpa only [Matrix.star_eq_conjTranspose, hC.isHermitian.eq, Matrix.mul_one] using
      hC.isUnit.posDef_star_right_conjugate_iff.mpr Matrix.PosDef.one
  have hp : (hermitianMatrixOfCoordinates (hermitianCoordinateProjection (C * C))).PosDef := by
    rwa [hermitianMatrixOfCoordinates_projection _ hS.isHermitian]
  have hAxiff : (hermitianMatrixOfCoordinates
      (hermitianCoordinateConjugationLinearMap C x)).PosDef ↔
      (hermitianMatrixOfCoordinates x).PosDef := by
    rw [hermitianCoordinateConjugation_reconstruct, ← Matrix.star_eq_conjTranspose]
    exact hC.isUnit.posDef_star_right_conjugate_iff
  have hBxiff : (hermitianMatrixOfCoordinates
      (hermitianCoordinateConjugationLinearMap C (hermitianComplementCoordinates x))).PosDef ↔
      (1 - hermitianMatrixOfCoordinates x).PosDef := by
    rw [hermitianCoordinateConjugation_reconstruct, hermitianMatrixOf_complementCoordinates,
      ← Matrix.star_eq_conjTranspose]
    exact hC.isUnit.posDef_star_right_conjugate_iff
  by_cases hx : x ∈ hermitianBetaDomain n K
  · have hAx := hAxiff.mpr hx.1
    have hBx := hBxiff.mpr hx.2
    simp only [wishartAmbientDensity, betaMatrixDensity, if_pos hAx, if_pos hBx,
      if_pos hp, if_pos hx]
    rw [← ENNReal.ofReal_mul (wishartAmbientKernel_pos α hAx).le,
      ← ENNReal.ofReal_mul (abs_nonneg _),
      ← ENNReal.ofReal_mul (wishartAmbientKernel_pos (α + δ) hp).le]
    congr 1
    rw [mul_comm |LinearMap.det _|]
    exact wishartAmbientKernel_pair_jacobian hn α δ hC hx
  · have hout : ¬ ((hermitianMatrixOfCoordinates
        (hermitianCoordinateConjugationLinearMap C x)).PosDef ∧
        (hermitianMatrixOfCoordinates (hermitianCoordinateConjugationLinearMap C
          (hermitianComplementCoordinates x))).PosDef) := by
      intro hh
      apply hx
      exact ⟨hAxiff.mp hh.1, hBxiff.mp hh.2⟩
    simp only [wishartAmbientDensity, betaMatrixDensity, if_neg hx, mul_zero]
    by_cases hA : (hermitianMatrixOfCoordinates (hermitianCoordinateConjugationLinearMap C x)).PosDef
    · have hB : ¬ (hermitianMatrixOfCoordinates (hermitianCoordinateConjugationLinearMap C
          (hermitianComplementCoordinates x))).PosDef := fun hh ↦ hout ⟨hA, hh⟩
      simp only [if_neg hB, mul_zero]
    · simp only [if_neg hA, zero_mul, mul_zero]

end A3Research
