import LogdetLean.GramHafnian.ShiftedAnticoncentration.Wishart.LiteralWishartStep

/-!
# The regularized Wishart inequality in the current PRL

This module exposes the bounded cutoff inequality printed as Eq. (22) in
the End Matter of ``Quadratic Small Ball Anticoncentration for Gaussian Gram
Hafnians``.  The expectation is the ordinary real integral under the exact
iid circular complex Gaussian law of the past columns.

No external assumption is used.  The proof assembles the internally proved
coordinate score identities, transports them through the exact Gaussian
realification, and applies the deterministic matrix Cauchy--Schwarz
comparison.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.CurrentPRL

noncomputable section

open LogdetLean.GramHafnian
open LogdetLean.GramHafnian.Wishart

/-- The exact regularized score identity behind PRL Eq. (22), stated on the
literal past-column probability space.  The two integrability statements are
included because they are part of the cutoff argument, not implicit
side conditions. -/
theorem eq22_regularized_wishart_score_data
    (k r : ℕ) (hr2 : 2 ≤ r) (hk : 4 * r ≤ k)
    (δ : ℝ) (hδ : 0 < δ) :
    let hr : 1 ≤ r := by omega
    let μ := Measure.pi fun _ : OddCofactorIndex r hr ↦
      circularGaussianVector k
    Integrable (fun A ↦ pastCoupledInverseQuadratic hr A /
        (pastCofactorW hr A + δ) ^ 2) μ ∧
      Integrable (fun A ↦ pastCofactorW hr A /
        (pastCofactorW hr A + δ) ^ 2) μ ∧
      (∫ A, pastCoupledInverseQuadratic hr A /
          (pastCofactorW hr A + δ) ^ 2 ∂μ) =
        (((k : ℝ) - 4 * r + 1)⁻¹) *
          ∫ A, pastCofactorW hr A /
            (pastCofactorW hr A + δ) ^ 2 ∂μ := by
  dsimp only
  have hr : 1 ≤ r := by omega
  let I := OddCofactorIndex r hr
  have hgap : Fintype.card (I ⊕ I) + 1 < k := by
    dsimp only [I]
    rw [Fintype.card_sum, card_oddCofactorIndex]
    omega
  have hcoeff : (k : ℝ) - 2 * Fintype.card I - 1 ≠ 0 := by
    rw [show (k : ℝ) - 2 * Fintype.card I - 1 =
        (k : ℝ) - 4 * r + 1 by
      simpa only [I] using oddCofactor_realWishart_residual_eq k r hr]
    have hkR : (4 : ℝ) * r ≤ k := by exact_mod_cast hk
    linarith
  have hfull : ∀ᵐ R
      ∂halfGaussianMatrixSum k (OddCofactorIndex r hr),
      IsUnit (realWishartGram R).det := by
    apply ae_isUnit_det_realWishartGram_halfGaussianMatrixSum_generic
    rw [Fintype.card_sum, card_oddCofactorIndex]
    omega
  have hRe (i j : I) :
      Integrable (fun R : Matrix (Fin k) (I ⊕ I) ℝ ↦
        rankOneRealCoordinateWeight
            (realifiedRegularizedCofactorWeight δ)
            realifiedCofactorVector i j R *
          (inverseGramScoreCoefficient (Fin k) (I ⊕ I) *
            Matrix.trace ((realWishartGram R)⁻¹ *
              scoreDeltaM (hermitianRealCoordinateDirection i j))))
        (halfGaussianMatrixSum k I) ∧
      Integrable (fun R : Matrix (Fin k) (I ⊕ I) ℝ ↦
        rankOneRealCoordinateWeight
            (realifiedRegularizedCofactorWeight δ)
            realifiedCofactorVector i j R *
          Matrix.trace (scoreDeltaM (hermitianRealCoordinateDirection i j)))
        (halfGaussianMatrixSum k I) ∧
      ((∫ R : Matrix (Fin k) (I ⊕ I) ℝ,
          rankOneRealCoordinateWeight
              (realifiedRegularizedCofactorWeight δ)
              realifiedCofactorVector i j R *
            (inverseGramScoreCoefficient (Fin k) (I ⊕ I) *
              Matrix.trace ((realWishartGram R)⁻¹ *
                scoreDeltaM (hermitianRealCoordinateDirection i j)))
          ∂halfGaussianMatrixSum k I) =
        ∫ R : Matrix (Fin k) (I ⊕ I) ℝ,
          rankOneRealCoordinateWeight
              (realifiedRegularizedCofactorWeight δ)
              realifiedCofactorVector i j R *
            Matrix.trace
              (scoreDeltaM (hermitianRealCoordinateDirection i j))
          ∂halfGaussianMatrixSum k I) := by
    simpa only [rankOneRealCoordinateWeight_realified_fintype] using
      (bounded_preservedSWeight_fixedH_score_halfGaussianMatrixSum
        (regularizedCofactorRealCoordinateWeight δ i j)
        (measurable_regularizedCofactorRealCoordinateWeight hδ i j)
        δ⁻¹ (abs_regularizedCofactorRealCoordinateWeight_le hδ i j)
        (hermitianRealCoordinateDirection_isHermitian i j) hgap)
  have hIm (i j : I) :
      Integrable (fun R : Matrix (Fin k) (I ⊕ I) ℝ ↦
        rankOneImagCoordinateWeight
            (realifiedRegularizedCofactorWeight δ)
            realifiedCofactorVector i j R *
          (inverseGramScoreCoefficient (Fin k) (I ⊕ I) *
            Matrix.trace ((realWishartGram R)⁻¹ *
              scoreDeltaM (hermitianImagCoordinateDirection i j))))
        (halfGaussianMatrixSum k I) ∧
      Integrable (fun R : Matrix (Fin k) (I ⊕ I) ℝ ↦
        rankOneImagCoordinateWeight
            (realifiedRegularizedCofactorWeight δ)
            realifiedCofactorVector i j R *
          Matrix.trace (scoreDeltaM (hermitianImagCoordinateDirection i j)))
        (halfGaussianMatrixSum k I) ∧
      ((∫ R : Matrix (Fin k) (I ⊕ I) ℝ,
          rankOneImagCoordinateWeight
              (realifiedRegularizedCofactorWeight δ)
              realifiedCofactorVector i j R *
            (inverseGramScoreCoefficient (Fin k) (I ⊕ I) *
              Matrix.trace ((realWishartGram R)⁻¹ *
                scoreDeltaM (hermitianImagCoordinateDirection i j)))
          ∂halfGaussianMatrixSum k I) =
        ∫ R : Matrix (Fin k) (I ⊕ I) ℝ,
          rankOneImagCoordinateWeight
              (realifiedRegularizedCofactorWeight δ)
              realifiedCofactorVector i j R *
            Matrix.trace
              (scoreDeltaM (hermitianImagCoordinateDirection i j))
          ∂halfGaussianMatrixSum k I) := by
    simpa only [rankOneImagCoordinateWeight_realified_fintype] using
      (bounded_preservedSWeight_fixedH_score_halfGaussianMatrixSum
        (regularizedCofactorImagCoordinateWeight δ i j)
        (measurable_regularizedCofactorImagCoordinateWeight hδ i j)
        δ⁻¹ (abs_regularizedCofactorImagCoordinateWeight_le hδ i j)
        (hermitianImagCoordinateDirection_isHermitian i j) hgap)
  have hscore :=
    regularized_coupled_score_of_coordinate_scores_fintype
      δ hfull
      (fun i j ↦ (hRe i j).1)
      (fun i j ↦ (hIm i j).1)
      (fun i j ↦ (hRe i j).2.1)
      (fun i j ↦ (hIm i j).2.1)
      (fun i j ↦ (hRe i j).2.2)
      (fun i j ↦ (hIm i j).2.2)
  have hA :=
    integrable_regularized_realifiedCoupledCofactorQuadratic_fintype
      δ hcoeff hfull
      (fun i j ↦ (hRe i j).1)
      (fun i j ↦ (hIm i j).1)
  have hW := integrable_regularized_realifiedCofactorW_fintype
      δ (fun i j ↦ (hRe i j).2.1) (fun i j ↦ (hIm i j).2.1)
  have heq := regularized_realified_integral_identity_fintype
    δ hcoeff hscore
  have hreal :
      Integrable (fun R : Matrix (Fin k) (I ⊕ I) ℝ ↦
        realifiedCoupledCofactorQuadratic R /
          (realifiedCofactorW R + δ) ^ 2)
        (halfGaussianMatrixSum k I) ∧
      Integrable (fun R : Matrix (Fin k) (I ⊕ I) ℝ ↦
        realifiedCofactorW R / (realifiedCofactorW R + δ) ^ 2)
        (halfGaussianMatrixSum k I) ∧
      (∫ R, realifiedCoupledCofactorQuadratic R /
          (realifiedCofactorW R + δ) ^ 2
          ∂halfGaussianMatrixSum k I) =
        (((k : ℝ) - 4 * r + 1)⁻¹) *
          ∫ R, realifiedCofactorW R /
            (realifiedCofactorW R + δ) ^ 2
            ∂halfGaussianMatrixSum k I := by
    refine ⟨hA, hW, ?_⟩
    simpa only [I, oddCofactor_realWishart_residual_eq] using heq
  exact literal_regularized_score_data_of_realified hr δ
    (((k : ℝ) - 4 * r + 1)⁻¹) hreal.1 hreal.2.1 hreal.2.2

/-- PRL Eq. (22): for every positive cutoff, the exact circular Gaussian
past-column expectation obeys the regularized Wishart comparison.  The
right integrand is written with the grouped denominator used in the paper. -/
theorem eq22_regularized_wishart_inequality
    (k r : ℕ) (hr2 : 2 ≤ r) (hk : 4 * r ≤ k)
    (δ : ℝ) (hδ : 0 < δ) :
    let hr : 1 ≤ r := by omega
    let μ := Measure.pi fun _ : OddCofactorIndex r hr ↦
      circularGaussianVector k
    (∫ A, pastCofactorW hr A /
        (pastCofactorW hr A + δ) ^ 2 ∂μ) ≥
      ((k : ℝ) - 4 * r + 1) *
        ∫ A, pastCofactorW hr A ^ 2 /
          (pastCofactorV hr A * (pastCofactorW hr A + δ) ^ 2) ∂μ := by
  dsimp only
  have hr : 1 ≤ r := by omega
  let μ := Measure.pi fun _ : OddCofactorIndex r hr ↦
    circularGaussianVector k
  obtain ⟨hQint, hWint, heq⟩ :=
    eq22_regularized_wishart_score_data k r hr2 hk δ hδ
  have hc : 0 < (k : ℝ) - 4 * r + 1 := by
    have hkR : (4 : ℝ) * r ≤ k := by exact_mod_cast hk
    linarith
  have htarget_nonneg :
      ∀ᵐ A ∂μ, 0 ≤ pastCofactorW hr A ^ 2 /
        (pastCofactorV hr A * (pastCofactorW hr A + δ) ^ 2) := by
    filter_upwards [ae_pastCofactorV_pos_paperRange hr hk] with A hV
    exact div_nonneg (sq_nonneg _) (mul_nonneg hV.le (sq_nonneg _))
  have htarget_le :
      ∀ᵐ A ∂μ, pastCofactorW hr A ^ 2 /
          (pastCofactorV hr A * (pastCofactorW hr A + δ) ^ 2) ≤
        pastCoupledInverseQuadratic hr A /
          (pastCofactorW hr A + δ) ^ 2 := by
    filter_upwards [ae_pastCofactorV_pos_paperRange hr hk,
      ae_pastCofactorW_pos_paperRange hr hk,
      ae_pastCofactorW_sq_le_pastCofactorV_mul_coupledInverseQuadratic hr hk]
      with A hV hW hmatrix
    have hden : 0 < (pastCofactorW hr A + δ) ^ 2 :=
      sq_pos_of_pos (add_pos hW hδ)
    have hdiv : pastCofactorW hr A ^ 2 / pastCofactorV hr A ≤
        pastCoupledInverseQuadratic hr A := by
      apply (div_le_iff₀ hV).2
      simpa [mul_comm] using hmatrix
    calc
      pastCofactorW hr A ^ 2 /
          (pastCofactorV hr A * (pastCofactorW hr A + δ) ^ 2) =
          (pastCofactorW hr A ^ 2 / pastCofactorV hr A) /
            (pastCofactorW hr A + δ) ^ 2 := by
              field_simp [ne_of_gt hV, ne_of_gt hden]
      _ ≤ pastCoupledInverseQuadratic hr A /
          (pastCofactorW hr A + δ) ^ 2 :=
        div_le_div_of_nonneg_right hdiv hden.le
  have hintegral :
      (∫ A, pastCofactorW hr A ^ 2 /
          (pastCofactorV hr A * (pastCofactorW hr A + δ) ^ 2) ∂μ) ≤
        ∫ A, pastCoupledInverseQuadratic hr A /
          (pastCofactorW hr A + δ) ^ 2 ∂μ :=
    integral_mono_of_nonneg htarget_nonneg hQint htarget_le
  calc
    ((k : ℝ) - 4 * r + 1) *
        ∫ A, pastCofactorW hr A ^ 2 /
          (pastCofactorV hr A * (pastCofactorW hr A + δ) ^ 2) ∂μ ≤
      ((k : ℝ) - 4 * r + 1) *
        ∫ A, pastCoupledInverseQuadratic hr A /
          (pastCofactorW hr A + δ) ^ 2 ∂μ :=
      mul_le_mul_of_nonneg_left hintegral hc.le
    _ = ∫ A, pastCofactorW hr A /
          (pastCofactorW hr A + δ) ^ 2 ∂μ := by
      rw [heq, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hc), one_mul]

end

end LogdetLean.GramHafnian.CurrentPRL
