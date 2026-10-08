import A3.BetaMatrixIntegration

open scoped BigOperators Matrix.Norms.Elementwise ComplexOrder MatrixOrder ENNReal
open Matrix MeasureTheory Set
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace A3Research

variable {n : ℕ} {K : Type*} [RCLike K]
  [MeasureSpace K] [BorelSpace K] [PolishSpace K]
  [(hermitianCoordinateVolume n K).IsAddHaarMeasure]

theorem hermitianConjugation_add_complement_coordinates
    {C : Matrix (Fin n) (Fin n) K} (hC : C.IsHermitian) (x : HermitianCoordinates n K) :
    hermitianCoordinateConjugationLinearMap C x +
      hermitianCoordinateConjugationLinearMap C (hermitianComplementCoordinates x) =
        hermitianCoordinateProjection (C * C) := by
  have hadd (A B : Matrix (Fin n) (Fin n) K) :
      hermitianCoordinateProjection (A + B) =
        hermitianCoordinateProjection A + hermitianCoordinateProjection B :=
    (hermitianCoordinateProjectionLinearMap n K).map_add A B
  have h := congrArg hermitianCoordinateProjection (hermitianConjugation_add_complement hC x)
  rw [hadd, hermitianCoordinateProjection_ofCoordinates,
    hermitianCoordinateProjection_ofCoordinates] at h
  exact h

theorem wishartAmbientDensity_ne_top (α : ℝ) (x : HermitianCoordinates n K) :
    wishartAmbientDensity n K α x ≠ ∞ := by
  classical
  unfold wishartAmbientDensity
  split_ifs <;> simp

/-- Genuine conditional-fiber integration, with no differentiability of the total square root. -/
theorem wishartJacobi_fiber_lintegral
    (hn : 1 ≤ n) (α δ : ℝ) (g : HermitianCoordinates n K → ℝ≥0∞)
    (S : HermitianCoordinates n K) :
    ∫⁻ A, (wishartAmbientDensity n K α A * wishartAmbientDensity n K δ (S - A)) *
        g (betaMatrixJacobiCoordinates (A, S - A)) ∂(hermitianCoordinateVolume n K) =
      wishartAmbientDensity n K (α + δ) S *
        ∫⁻ x, betaMatrixDensity n K α δ x * g x ∂(hermitianCoordinateVolume n K) := by
  classical
  by_cases hS : (hermitianMatrixOfCoordinates S).PosDef
  · let C := CFC.sqrt (hermitianMatrixOfCoordinates S)
    have hC : C.PosDef := posDef_cfc_sqrt hS
    have hsquare : C * C = hermitianMatrixOfCoordinates S :=
      CFC.sqrt_mul_sqrt_self _ hS.posSemidef.nonneg
    have hproj : hermitianCoordinateProjection (C * C) = S := by
      rw [hsquare, hermitianCoordinateProjection_ofCoordinates]
    have hcomp (x : HermitianCoordinates n K) :
        S - hermitianCoordinateConjugationLinearMap C x =
          hermitianCoordinateConjugationLinearMap C (hermitianComplementCoordinates x) := by
      have ha := hermitianConjugation_add_complement_coordinates hC.isHermitian x
      rw [hproj] at ha
      exact (eq_sub_of_add_eq' ha).symm
    calc
      _ = ∫⁻ x, ENNReal.ofReal |LinearMap.det (hermitianCoordinateConjugationLinearMap C)| *
          ((wishartAmbientDensity n K α (hermitianCoordinateConjugationLinearMap C x) *
            wishartAmbientDensity n K δ (S - hermitianCoordinateConjugationLinearMap C x)) *
            g (betaMatrixJacobiCoordinates
              (hermitianCoordinateConjugationLinearMap C x,
                S - hermitianCoordinateConjugationLinearMap C x)))
          ∂(hermitianCoordinateVolume n K) := lintegral_hermitianCongruence hC _
      _ = ∫⁻ x, wishartAmbientDensity n K (α + δ) S *
          (betaMatrixDensity n K α δ x * g x) ∂(hermitianCoordinateVolume n K) := by
        apply lintegral_congr
        intro x
        rw [hcomp, betaMatrixJacobiCoordinates_sum_congruence hC,
          ← mul_assoc, wishartAmbientDensity_pair_jacobian hn α δ hC,
          hproj, mul_assoc]
      _ = _ := lintegral_const_mul' _ _ (wishartAmbientDensity_ne_top (α + δ) S)
  · have hout (A : HermitianCoordinates n K) :
        ¬ ((hermitianMatrixOfCoordinates A).PosDef ∧
          (hermitianMatrixOfCoordinates (S - A)).PosDef) := by
      intro hh
      apply hS
      have h := hh.1.add hh.2
      have he : hermitianMatrixOfCoordinates A + hermitianMatrixOfCoordinates (S - A) =
          hermitianMatrixOfCoordinates S := by
        rw [show hermitianMatrixOfCoordinates (S - A) =
            hermitianMatrixOfCoordinates S - hermitianMatrixOfCoordinates A from
          (hermitianMatrixOfCoordinatesLinearMap n K).map_sub S A]
        abel
      rwa [he] at h
    have hzero (A : HermitianCoordinates n K) :
        wishartAmbientDensity n K α A * wishartAmbientDensity n K δ (S - A) = 0 := by
      unfold wishartAmbientDensity
      by_cases hA : (hermitianMatrixOfCoordinates A).PosDef
      · have hB : ¬ (hermitianMatrixOfCoordinates (S - A)).PosDef := fun hb ↦ hout A ⟨hA, hb⟩
        simp only [if_neg hB, mul_zero]
      · simp only [if_neg hA, zero_mul]
    have hI : (∫⁻ A, (wishartAmbientDensity n K α A * wishartAmbientDensity n K δ (S - A)) *
        g (betaMatrixJacobiCoordinates (A, S - A)) ∂(hermitianCoordinateVolume n K)) = 0 := by
      calc
        _ = ∫⁻ _ : HermitianCoordinates n K, (0 : ℝ≥0∞) ∂(hermitianCoordinateVolume n K) := by
          apply lintegral_congr
          intro A
          rw [hzero A, zero_mul]
        _ = 0 := lintegral_zero
    rw [hI]
    simp only [wishartAmbientDensity, if_neg hS, zero_mul]

end A3Research
