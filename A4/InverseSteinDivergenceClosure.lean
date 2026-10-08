import A4.InverseSteinFlatDivergence

/-!
# Closing the matrix Gaussian divergence argument

`FlatDivergenceTransport` proves the Gaussian divergence identity from the
three genuine coordinate-family integrability hypotheses.  `IntegratedScore`
then identifies the two sides pointwise on the almost-sure full-rank locus.
This file records the missing analytic closure: those same hypotheses also
imply the two `Integrable` conclusions in the classical fixed-direction
Stein--Haff statement.

The result is deliberately stated for numeric matrix indices.  Reindexing a
finite column type is a separate measure-preserving algebraic operation and
does not belong to the singular-field cutoff argument.
-/

open MeasureTheory
open scoped BigOperators Matrix.Norms.Operator

namespace A4Research

noncomputable section

namespace InverseStein

/-- The explicit flat derivative sum is integrable whenever every coordinate
derivative is integrable. -/
theorem integrable_sum_flattenedWeightedSteinComponentDerivative
    {k p n : ℕ} (hdim : n + 1 = k * p)
    (g : Matrix (Fin k) (Fin p) ℝ → ℝ)
    (g' : Matrix (Fin k) (Fin p) ℝ →
      Matrix (Fin k) (Fin p) ℝ →L[ℝ] ℝ)
    (D : Matrix (Fin p) (Fin p) ℝ)
    (hderiv : ∀ i, Integrable
      (flattenedWeightedSteinComponentDerivative hdim g g' D i)
      (halfGaussianPi (n + 1))) :
    Integrable
      (fun x ↦ ∑ i, flattenedWeightedSteinComponentDerivative
        hdim g g' D i x)
      (halfGaussianPi (n + 1)) := by
  exact integrable_finsetSum _ (fun i _ ↦ hderiv i)

/-- The explicit flat radial sum is integrable whenever every coordinate
radial term is integrable. -/
theorem integrable_sum_flattenedWeightedSteinComponent_radial
    {k p n : ℕ} (hdim : n + 1 = k * p)
    (g : Matrix (Fin k) (Fin p) ℝ → ℝ)
    (D : Matrix (Fin p) (Fin p) ℝ)
    (hradial : ∀ i, Integrable
      (fun x ↦ 2 * x i * flattenedWeightedSteinComponent hdim g D i x)
      (halfGaussianPi (n + 1))) :
    Integrable
      (fun x ↦ ∑ i, 2 * x i *
        flattenedWeightedSteinComponent hdim g D i x)
      (halfGaussianPi (n + 1)) := by
  exact integrable_finsetSum _ (fun i _ ↦ hradial i)

/-- Product-rule form of the weighted Stein-field divergence, without the
preserved-coordinate assumption.  The first term is the differential of the
scalar weight in the lifted Gram direction. -/
theorem weightedSteinCoordinateDivergence_eq_fderiv_add_mul
    {k p : Type*} [Fintype k] [Fintype p]
    [DecidableEq k] [DecidableEq p]
    (g : Matrix k p ℝ → ℝ) (g' : Matrix k p ℝ →L[ℝ] ℝ)
    (R : Matrix k p ℝ) (D : Matrix p p ℝ)
    (hg : HasFDerivAt g g' R)
    (hM : IsUnit (realWishartGram R).det) :
    weightedSteinCoordinateDivergence g R D =
      g' (steinVectorFieldValue R D) +
        g R * steinVectorFieldCoordinateDivergence R D := by
  rw [weightedSteinCoordinateDivergence_eq_explicit g g' R D hg hM]
  rw [show (∑ a, ∑ j,
      (g' (Matrix.single a j 1) * steinVectorFieldValue R D a j +
        g R * steinVectorFieldLinearization R D
          (Matrix.single a j 1) a j)) =
      (∑ a, ∑ j,
        g' (Matrix.single a j 1) * steinVectorFieldValue R D a j) +
      g R * rectangularCoordinateTrace
        (steinVectorFieldLinearization R D) by
    simp [rectangularCoordinateTrace, Finset.sum_add_distrib,
      Finset.mul_sum]]
  have hfirst :
      (∑ a, ∑ j,
        g' (Matrix.single a j 1) * steinVectorFieldValue R D a j) =
        g' (steinVectorFieldValue R D) := by
    let V := steinVectorFieldValue R D
    calc
      (∑ a, ∑ j, g' (Matrix.single a j 1) * V a j) =
          ∑ a, ∑ j, (V a j) * g' (Matrix.single a j 1) := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = g' (∑ a, ∑ j, (V a j) • Matrix.single a j 1) := by
        simp only [map_sum]
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro j _
        simpa [smul_eq_mul] using
          (g'.map_smul (V a j) (Matrix.single a j (1 : ℝ))).symm
      _ = g' V := by rw [← matrix_eq_sum_smul_single V]
  rw [hfirst,
    ← steinVectorFieldCoordinateDivergence_eq_coordinateTrace R D hM]

end InverseStein

end

end A4Research
