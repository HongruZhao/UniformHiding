import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.PolynomialInverseEntryIntegrability
import LogdetLean.GramHafnian.UltimateHiding.WishartCore.Wishart.MatrixSteinHaffClosure
import Mathlib.Tactic

/-!
# Stein--Haff closure for tests differentiable on the full-rank locus

The existing bounded-test closure assumes a globally differentiable scalar
test.  Inverse entries are differentiable only where the Gram matrix is
nonsingular.  Deleted-row full rank is nevertheless uniform on almost every
one-dimensional Gaussian slice, so the scalar integration-by-parts theorem
only needs the local derivative there.  This module records that sharper,
still axiom-free interface.
-/

open MeasureTheory
open scoped BigOperators Matrix.Norms.Operator

namespace LogdetLean.GramHafnian

noncomputable section

namespace Wishart

/-- Product-rule derivative of one flattened weighted Stein component from a
derivative available only at the selected base point. -/
theorem hasDerivAt_flattenedWeightedSteinComponent_insertNth_of_hasFDerivAt
    {k p n : ℕ} (hdim : n + 1 = k * p)
    (g : Matrix (Fin k) (Fin p) ℝ → ℝ)
    (g' : Matrix (Fin k) (Fin p) ℝ →
      Matrix (Fin k) (Fin p) ℝ →L[ℝ] ℝ)
    (D : Matrix (Fin p) (Fin p) ℝ)
    (i : Fin (n + 1)) (y : Fin n → ℝ) (t : ℝ)
    (hfull : IsUnit (realWishartGram
      (flatSuccMatrixMeasurableEquiv hdim (i.insertNth t y))).det)
    (hg : HasFDerivAt g
      (g' (flatSuccMatrixMeasurableEquiv hdim (i.insertNth t y)))
      (flatSuccMatrixMeasurableEquiv hdim (i.insertNth t y))) :
    HasDerivAt
      (fun s : ℝ ↦ flattenedWeightedSteinComponent
        hdim g D i (i.insertNth s y))
      (flattenedWeightedSteinComponentDerivative
        hdim g g' D i (i.insertNth t y)) t := by
  let R := flatSuccMatrixMeasurableEquiv hdim (i.insertNth t y)
  let E := flatCoordinateMatrixUnit hdim i
  let a := flatCoordinateRow hdim i
  let j := flatCoordinateColumn hdim i
  have hgline : HasDerivAt
      (fun s : ℝ ↦ g
        (flatSuccMatrixMeasurableEquiv hdim (i.insertNth s y)))
      (g' R E) t := by
    have hbase : HasDerivAt
        (fun u : ℝ ↦ g (R + u • E)) (g' R E) 0 :=
      hg.hasLineDerivAt E
    have hshift : HasDerivAt (fun s : ℝ ↦ s - t) 1 t := by
      simpa using (hasDerivAt_id t).sub_const t
    have ht : (0 : ℝ) = t - t := by ring
    rw [ht] at hbase
    have hcomp := hbase.comp (h := fun s : ℝ ↦ s - t) t hshift
    have hfun :
        (fun s : ℝ ↦ g
          (flatSuccMatrixMeasurableEquiv hdim (i.insertNth s y))) =
        (fun s : ℝ ↦ g (R + (s - t) • E)) := by
      funext s
      rw [flatSuccMatrix_insertNth_eq_matrixLine hdim i y s t]
      rfl
    rw [hfun]
    simpa [Function.comp_def] using hcomp
  have hVmat := hasDerivAt_steinVectorFieldValue_flatSucc_insertNth
    hdim i y t D hfull
  have hVa := hasDerivAt_pi.mp hVmat a
  have hVaj := hasDerivAt_pi.mp hVa j
  change HasDerivAt
    ((fun s : ℝ ↦ g
        (flatSuccMatrixMeasurableEquiv hdim (i.insertNth s y))) *
      (fun s : ℝ ↦ steinVectorFieldValue
        (flatSuccMatrixMeasurableEquiv hdim (i.insertNth s y)) D a j))
    (g' R E * steinVectorFieldValue R D a j +
      g R * steinVectorFieldLinearization R D E a j) t
  exact hgline.mul hVaj

/-- Almost-everywhere slice derivative when the scalar test is Frechet
differentiable at every full-rank matrix. -/
theorem forall_ae_hasDerivAt_flattenedWeightedSteinComponent_of_nonsingular_fderiv
    {k p n : ℕ} (hdim : n + 1 = k * p) (hp : p < k)
    (g : Matrix (Fin k) (Fin p) ℝ → ℝ)
    (g' : Matrix (Fin k) (Fin p) ℝ →
      Matrix (Fin k) (Fin p) ℝ →L[ℝ] ℝ)
    (D : Matrix (Fin p) (Fin p) ℝ)
    (hg : ∀ R, IsUnit (realWishartGram R).det →
      HasFDerivAt g (g' R) R) :
    ∀ i : Fin (n + 1),
      ∀ᵐ y : Fin n → ℝ ∂halfGaussianPi n, ∀ t : ℝ,
        HasDerivAt
          (fun s : ℝ ↦ flattenedWeightedSteinComponent
            hdim g D i (i.insertNth s y))
          (flattenedWeightedSteinComponentDerivative
            hdim g g' D i (i.insertNth t y)) t := by
  intro i
  filter_upwards [
    ae_forall_isUnit_det_realWishartGram_flatSuccMatrix_slice_of_lt
      hdim i hp] with y hy
  intro t
  exact hasDerivAt_flattenedWeightedSteinComponent_insertNth_of_hasFDerivAt
    hdim g g' D i y t (hy t) (hg _ (hy t))

/-- Gaussian divergence for a scalar Gram test differentiable only on the
full-rank locus. -/
theorem integral_flattenedWeightedSteinComponent_divergence_of_integrable_of_nonsingular_fderiv
    {k p n : ℕ} (hdim : n + 1 = k * p) (hp : p < k)
    (g : Matrix (Fin k) (Fin p) ℝ → ℝ)
    (g' : Matrix (Fin k) (Fin p) ℝ →
      Matrix (Fin k) (Fin p) ℝ →L[ℝ] ℝ)
    (D : Matrix (Fin p) (Fin p) ℝ)
    (hg : ∀ R, IsUnit (realWishartGram R).det →
      HasFDerivAt g (g' R) R)
    (hvalue : ∀ i, Integrable
      (flattenedWeightedSteinComponent hdim g D i)
      (halfGaussianPi (n + 1)))
    (hderiv : ∀ i, Integrable
      (flattenedWeightedSteinComponentDerivative hdim g g' D i)
      (halfGaussianPi (n + 1)))
    (hradial : ∀ i, Integrable
      (fun x ↦ 2 * x i * flattenedWeightedSteinComponent hdim g D i x)
      (halfGaussianPi (n + 1))) :
    (∫ x, ∑ i, flattenedWeightedSteinComponentDerivative
      hdim g g' D i x ∂halfGaussianPi (n + 1)) =
      ∫ x, ∑ i, 2 * x i * flattenedWeightedSteinComponent
        hdim g D i x ∂halfGaussianPi (n + 1) := by
  exact integral_halfGaussianPi_divergence_of_integrable
    (fun i x ↦ flattenedWeightedSteinComponent hdim g D i x)
    (fun i x ↦ flattenedWeightedSteinComponentDerivative
      hdim g g' D i x)
    (forall_ae_hasDerivAt_flattenedWeightedSteinComponent_of_nonsingular_fderiv
      hdim hp g g' D hg)
    hvalue hderiv hradial

/-- Full Stein--Haff closure from the literal coordinate-family
integrability hypotheses, allowing the test derivative to exist only on the
almost-sure full-rank locus. -/
theorem steinHaff_halfGaussianMatrix_of_nonsingular_fderiv_and_flattenedSteinFamilies
    {k p n : ℕ} (hdim : n + 1 = k * p) (hp : p < k)
    (g : Matrix (Fin k) (Fin p) ℝ → ℝ)
    (g' : Matrix (Fin k) (Fin p) ℝ →
      Matrix (Fin k) (Fin p) ℝ →L[ℝ] ℝ)
    (D : Matrix (Fin p) (Fin p) ℝ)
    (q : Matrix (Fin k) (Fin p) ℝ → ℝ)
    (hg : ∀ R, IsUnit (realWishartGram R).det →
      HasFDerivAt g (g' R) R)
    (hchain : ∀ R, IsUnit (realWishartGram R).det →
      g' R (steinVectorFieldValue R D) = q R)
    (hq : Integrable q (halfGaussianMatrix k p))
    (hvalue : ∀ i, Integrable
      (flattenedWeightedSteinComponent hdim g D i)
      (halfGaussianPi (n + 1)))
    (hderiv : ∀ i, Integrable
      (flattenedWeightedSteinComponentDerivative hdim g g' D i)
      (halfGaussianPi (n + 1)))
    (hradial : ∀ i, Integrable
      (fun x ↦ 2 * x i * flattenedWeightedSteinComponent hdim g D i x)
      (halfGaussianPi (n + 1))) :
    Integrable
        (fun R : Matrix (Fin k) (Fin p) ℝ ↦
          g R * (inverseGramScoreCoefficient (Fin k) (Fin p) *
            Matrix.trace ((realWishartGram R)⁻¹ * D)))
        (halfGaussianMatrix k p) ∧
      Integrable
        (fun R : Matrix (Fin k) (Fin p) ℝ ↦
          g R * Matrix.trace D - q R)
        (halfGaussianMatrix k p) ∧
      ((∫ R, g R *
            (inverseGramScoreCoefficient (Fin k) (Fin p) *
              Matrix.trace ((realWishartGram R)⁻¹ * D))
          ∂halfGaussianMatrix k p) =
        ∫ R, g R * Matrix.trace D - q R
          ∂halfGaussianMatrix k p) := by
  let e := flatSuccMatrixMeasurableEquiv hdim
  let μ := halfGaussianMatrix k p
  let ν := halfGaussianPi (n + 1)
  have hfull : ∀ᵐ R ∂μ, IsUnit (realWishartGram R).det :=
    ae_isUnit_det_realWishartGram_halfGaussianMatrix k p (Nat.le_of_lt hp)
  have hfullFlat : ∀ᵐ x ∂ν,
      IsUnit (realWishartGram (e x)).det :=
    (measurePreserving_flatSuccMatrixMeasurableEquiv hdim).quasiMeasurePreserving.ae
      hfull
  have hinv : MeasurePreserving e.symm μ ν :=
    (measurePreserving_flatSuccMatrixMeasurableEquiv hdim).symm e
  have hflatDeriv : Integrable
      (fun x ↦ ∑ i, flattenedWeightedSteinComponentDerivative
        hdim g g' D i x) ν :=
    integrable_sum_flattenedWeightedSteinComponentDerivative
      hdim g g' D hderiv
  have hdivComp : Integrable
      (fun x ↦ weightedSteinCoordinateDivergence g (e x) D) ν := by
    apply hflatDeriv.congr
    filter_upwards [hfullFlat] with x hx
    simpa [e] using
      (sum_flattenedWeightedSteinComponentDerivative_eq_divergence
        hdim g g' D x (hg _ hx) hx)
  have hdiv : Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        weightedSteinCoordinateDivergence g R D) μ := by
    have h := hinv.integrable_comp_of_integrable hdivComp
    simpa [Function.comp_def, e] using h
  have hscoreInt : Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        g R * (inverseGramScoreCoefficient (Fin k) (Fin p) *
          Matrix.trace ((realWishartGram R)⁻¹ * D))) μ := by
    apply (hdiv.sub hq).congr
    filter_upwards [hfull] with R hR
    change weightedSteinCoordinateDivergence g R D - q R = _
    rw [weightedSteinCoordinateDivergence_eq_fderiv_add_mul
      g (g' R) R D (hg R hR) hR, hchain R hR,
      steinVectorFieldCoordinateDivergence_eq R D hR]
    unfold inverseGramScoreCoefficient
    simp only [Fintype.card_fin]
    ring
  have hflatRadial : Integrable
      (fun x ↦ ∑ i, 2 * x i *
        flattenedWeightedSteinComponent hdim g D i x) ν :=
    integrable_sum_flattenedWeightedSteinComponent_radial
      hdim g D hradial
  have hradialComp : Integrable
      (fun x ↦ 2 * realFrobeniusInner (e x)
        (g (e x) • steinVectorFieldValue (e x) D)) ν := by
    apply hflatRadial.congr
    filter_upwards [] with x
    simpa [e] using
      (sum_flattenedWeightedSteinComponent_radial_eq hdim g D x)
  have hradialMatrix : Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        2 * realFrobeniusInner R
          (g R • steinVectorFieldValue R D)) μ := by
    have h := hinv.integrable_comp_of_integrable hradialComp
    simpa [Function.comp_def, e] using h
  have hconstantInt : Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        g R * Matrix.trace D - q R) μ := by
    apply (hradialMatrix.sub hq).congr
    filter_upwards [hfull] with R hR
    change (2 * realFrobeniusInner R
      (g R • steinVectorFieldValue R D)) - q R = _
    rw [two_mul_weighted_frobenius_steinVectorFieldValue g R D hR]
  have hIBP :=
    integral_flattenedWeightedSteinComponent_divergence_of_integrable_of_nonsingular_fderiv
      hdim hp g g' D hg hvalue hderiv hradial
  have hIBPFlatMatrix :
      (∫ x, weightedSteinCoordinateDivergence g (e x) D ∂ν) =
        ∫ x, 2 * realFrobeniusInner (e x)
          (g (e x) • steinVectorFieldValue (e x) D) ∂ν := by
    calc
      (∫ x, weightedSteinCoordinateDivergence g (e x) D ∂ν) =
          ∫ x, ∑ i, flattenedWeightedSteinComponentDerivative
            hdim g g' D i x ∂ν := by
        apply integral_congr_ae
        filter_upwards [hfullFlat] with x hx
        exact (sum_flattenedWeightedSteinComponentDerivative_eq_divergence
          hdim g g' D x (hg _ hx) hx).symm
      _ = ∫ x, ∑ i, 2 * x i *
          flattenedWeightedSteinComponent hdim g D i x ∂ν := hIBP
      _ = ∫ x, 2 * realFrobeniusInner (e x)
          (g (e x) • steinVectorFieldValue (e x) D) ∂ν := by
        apply integral_congr_ae
        filter_upwards [] with x
        exact sum_flattenedWeightedSteinComponent_radial_eq hdim g D x
  have hscore :
      (∫ R, g R *
          (inverseGramScoreCoefficient (Fin k) (Fin p) *
            Matrix.trace ((realWishartGram R)⁻¹ * D)) ∂μ) =
        ∫ R, g R * Matrix.trace D - q R ∂μ := by
    calc
      (∫ R, g R *
          (inverseGramScoreCoefficient (Fin k) (Fin p) *
            Matrix.trace ((realWishartGram R)⁻¹ * D)) ∂μ) =
          ∫ R, weightedSteinCoordinateDivergence g R D - q R ∂μ := by
        apply integral_congr_ae
        filter_upwards [hfull] with R hR
        rw [weightedSteinCoordinateDivergence_eq_fderiv_add_mul
          g (g' R) R D (hg R hR) hR, hchain R hR,
          steinVectorFieldCoordinateDivergence_eq R D hR]
        unfold inverseGramScoreCoefficient
        simp only [Fintype.card_fin]
        ring
      _ = (∫ R, weightedSteinCoordinateDivergence g R D ∂μ) -
          ∫ R, q R ∂μ := integral_sub hdiv hq
      _ = (∫ R, 2 * realFrobeniusInner R
          (g R • steinVectorFieldValue R D) ∂μ) -
          ∫ R, q R ∂μ := by
        rw [← integral_comp_flatSuccMatrixMeasurableEquiv hdim
              (fun R ↦ weightedSteinCoordinateDivergence g R D),
          ← integral_comp_flatSuccMatrixMeasurableEquiv hdim
              (fun R ↦ 2 * realFrobeniusInner R
                (g R • steinVectorFieldValue R D))]
        exact congrArg (fun x ↦ x - ∫ R, q R ∂μ) hIBPFlatMatrix
      _ = ∫ R, (2 * realFrobeniusInner R
          (g R • steinVectorFieldValue R D)) - q R ∂μ :=
        (integral_sub hradialMatrix hq).symm
      _ = ∫ R, g R * Matrix.trace D - q R ∂μ := by
        apply integral_congr_ae
        filter_upwards [hfull] with R hR
        rw [two_mul_weighted_frobenius_steinVectorFieldValue g R D hR]
  exact ⟨hscoreInt, hconstantInt, hscore⟩

end Wishart

end

end LogdetLean.GramHafnian
