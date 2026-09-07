import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.NonsingularSteinHaff
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.InverseWishartSecondEntrySteinConditional
import Mathlib.Tactic

/-!
# Direct inverse-entry Stein--Haff reduction

This module differentiates one inverse-Gram entry on the full-rank locus and
applies the nonsingular-test Gaussian divergence closure.  All matrix
calculus and the resulting second-entry recursion are internal.  The only
remaining analytic input is the three literal coordinate-family
integrability statements; a later section discharges those from the
Gaussian-polynomial inverse-entry engine.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.Elementwise

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08

noncomputable section

open LogdetLean.GramHafnian
open LogdetLean.GramHafnian.Wishart
open LogdetLean.GramHafnian.UltimateHiding.DenseScore

/-- One inverse-Gram entry as a scalar test on rectangular matrices. -/
def inverseWishartEntryTest {k p : ℕ} (l m : Fin p)
    (R : Matrix (Fin k) (Fin p) ℝ) : ℝ :=
  (realWishartGram R)⁻¹ l m

/-- Its canonical Frechet derivative.  At singular matrices `fderiv` is
zero by definition; all analytic uses below are restricted to full rank. -/
def inverseWishartEntryTestDerivative {k p : ℕ} (l m : Fin p)
    (R : Matrix (Fin k) (Fin p) ℝ) :
    Matrix (Fin k) (Fin p) ℝ →L[ℝ] ℝ :=
  fderiv ℝ (inverseWishartEntryTest l m) R

/-- Frechet differentiability of one inverse-Gram entry on the nonsingular
locus. -/
theorem hasFDerivAt_inverseWishartEntryTest
    {k p : ℕ} (l m : Fin p)
    (R : Matrix (Fin k) (Fin p) ℝ)
    (hfull : IsUnit (realWishartGram R).det) :
    HasFDerivAt (inverseWishartEntryTest l m)
      (inverseWishartEntryTestDerivative l m R) R := by
  have hinv := hasFDerivAt_matrix_nonsing_inv (realWishartGram R) hfull
  have hentry := (squareMatrixEntryCLM l m).hasFDerivAt.comp
    (realWishartGram R) hinv
  have hcomp := hentry.comp R (hasFDerivAt_realWishartGram R)
  exact hcomp.differentiableAt.hasFDerivAt

/-- The derivative in a lifted symmetric Gram direction is the standard
inverse-sandwich entry. -/
theorem inverseWishartEntryTestDerivative_steinVectorFieldValue
    {k p : ℕ} (l m : Fin p)
    (R : Matrix (Fin k) (Fin p) ℝ)
    (D : Matrix (Fin p) (Fin p) ℝ) (hD : D.IsSymm)
    (hfull : IsUnit (realWishartGram R).det) :
    inverseWishartEntryTestDerivative l m R
        (steinVectorFieldValue R D) =
      -(((realWishartGram R)⁻¹ * D * (realWishartGram R)⁻¹) l m) := by
  let V := steinVectorFieldValue R D
  have hlocal :=
    (hasFDerivAt_inverseWishartEntryTest l m R hfull).hasLineDerivAt V
  have hline :=
    hasDerivAt_inverse_realWishartGram_entry_matrixLine R V hfull l m
  have heq := hlocal.unique hline
  calc
    inverseWishartEntryTestDerivative l m R V =
        (-((realWishartGram R)⁻¹ *
          (V.transpose * R + R.transpose * V) *
          (realWishartGram R)⁻¹)) l m := heq
    _ = -(((realWishartGram R)⁻¹ * D *
          (realWishartGram R)⁻¹) l m) := by
      rw [gram_firstVariation_steinVectorFieldValue R hD hfull]
      rfl

/-- The inverse-sandwich entry is integrable at the second inverse-moment
threshold. -/
theorem integrable_inverseWishartEntrySandwich_halfGaussianMatrix
    {k p : ℕ} (hgap : p + 4 ≤ k)
    (D : Matrix (Fin p) (Fin p) ℝ) (l m : Fin p) :
    Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        -(((realWishartGram R)⁻¹ * D *
          (realWishartGram R)⁻¹) l m))
      (halfGaussianMatrix k p) := by
  have hterm (a b : Fin p) : Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        (realWishartGram R)⁻¹ l a * D a b *
          (realWishartGram R)⁻¹ b m)
      (halfGaussianMatrix k p) := by
    let indices : Fin 2 → Fin p × Fin p := ![(l, a), (b, m)]
    have hprod := integrable_inverseWishartEntryProduct_halfGaussianMatrix
      (q := 2) (by omega) indices
    have hscaled := hprod.mul_const (D a b)
    simpa [indices, inverseWishartEntryProduct, Fin.prod_univ_two,
      mul_assoc, mul_comm, mul_left_comm] using hscaled
  have hsum : Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        ∑ a : Fin p, ∑ b : Fin p,
          (realWishartGram R)⁻¹ l a * D a b *
            (realWishartGram R)⁻¹ b m)
      (halfGaussianMatrix k p) :=
    integrable_finsetSum _ (fun a _ ↦
      integrable_finsetSum _ (fun b _ ↦ hterm a b))
  apply hsum.neg.congr
  filter_upwards [] with R
  simp only [Pi.neg_apply, Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- One Gaussian coordinate times a prescribed inverse-entry product is
integrable without changing the inverse-moment threshold. -/
theorem integrable_matrixCoordinate_mul_inverseWishartEntryProduct_halfGaussianMatrix
    {k p q : ℕ} (hq : 0 < q) (hgap : p + 2 * q ≤ k)
    (a : Fin k) (i : Fin p) (indices : Fin q → Fin p × Fin p) :
    Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        R a i * inverseWishartEntryProduct indices R)
      (halfGaussianMatrix k p) := by
  have hmajor := (
    integrable_one_add_rectangularSqMass_mul_inverseWishartEntryProduct_halfGaussianMatrix
      hq hgap indices).norm
  apply hmajor.mono'
    (((measurable_pi_apply i).comp
      ((measurable_pi_apply a).comp measurable_id)).mul
        (measurable_inverseWishartEntryProduct k p q indices)).aestronglyMeasurable
  filter_upwards [] with R
  change |R a i * inverseWishartEntryProduct indices R| ≤
    ‖(1 + rectangularSqMass R) * inverseWishartEntryProduct indices R‖
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (by
    have := rectangularSqMass_nonneg R
    linarith : 0 ≤ 1 + rectangularSqMass R)]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  have hs := sq_entry_le_rectangularSqMass R a i
  rw [← sq_abs] at hs
  nlinarith [sq_nonneg (|R a i| - 1)]

/-- Two Gaussian coordinates times a prescribed inverse-entry product are
integrable at the same threshold. -/
theorem integrable_two_matrixCoordinates_mul_inverseWishartEntryProduct_halfGaussianMatrix
    {k p q : ℕ} (hq : 0 < q) (hgap : p + 2 * q ≤ k)
    (a b : Fin k) (i j : Fin p)
    (indices : Fin q → Fin p × Fin p) :
    Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        R a i * R b j * inverseWishartEntryProduct indices R)
      (halfGaussianMatrix k p) := by
  have hmajor0 :=
    integrable_one_add_rectangularSqMass_mul_inverseWishartEntryProduct_halfGaussianMatrix
      hq hgap indices
  have hmajor := (hmajor0.const_mul (2 : ℝ)).norm
  apply hmajor.mono'
    (((((measurable_pi_apply i).comp
      ((measurable_pi_apply a).comp measurable_id)).mul
        ((measurable_pi_apply j).comp
          ((measurable_pi_apply b).comp measurable_id))).mul
            (measurable_inverseWishartEntryProduct k p q indices)).aestronglyMeasurable)
  filter_upwards [] with R
  change |R a i * R b j * inverseWishartEntryProduct indices R| ≤
    ‖2 * ((1 + rectangularSqMass R) *
      inverseWishartEntryProduct indices R)‖
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
    abs_mul (1 + rectangularSqMass R)
      (inverseWishartEntryProduct indices R),
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    abs_of_nonneg (by
      have := rectangularSqMass_nonneg R
      linarith : 0 ≤ 1 + rectangularSqMass R)]
  have hai := sq_entry_le_rectangularSqMass R a i
  have hbj := sq_entry_le_rectangularSqMass R b j
  have hcoord : |R a i| * |R b j| ≤
      2 * (1 + rectangularSqMass R) := by
    calc
      |R a i| * |R b j| = |R a i * R b j| := (abs_mul _ _).symm
      _ ≤ (R a i) ^ 2 + (R b j) ^ 2 := abs_mul_le_sq_add_sq _ _
      _ ≤ 2 * rectangularSqMass R := by linarith
      _ ≤ 2 * (1 + rectangularSqMass R) := by linarith
  have hmul := mul_le_mul_of_nonneg_right hcoord
    (abs_nonneg (inverseWishartEntryProduct indices R))
  simpa only [mul_assoc] using hmul

/-- Matrix-law integrability of the value component of the inverse-entry
weighted Stein field. -/
theorem integrable_inverseWishartEntryTest_mul_steinVectorFieldValue_apply
    {k p : ℕ} (hgap : p + 8 ≤ k)
    (l m : Fin p) (D : Matrix (Fin p) (Fin p) ℝ)
    (a : Fin k) (i : Fin p) :
    Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        inverseWishartEntryTest l m R *
          steinVectorFieldValue R D a i)
      (halfGaussianMatrix k p) := by
  have hterm (x y : Fin p) : Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        (1 / 2 : ℝ) *
          (R a x *
            ((realWishartGram R)⁻¹ l m * (realWishartGram R)⁻¹ x y)) *
          D y i)
      (halfGaussianMatrix k p) := by
    let indices : Fin 2 → Fin p × Fin p := ![(l, m), (x, y)]
    have hbase :=
      integrable_matrixCoordinate_mul_inverseWishartEntryProduct_halfGaussianMatrix
        (q := 2) (by norm_num) (by omega) a x indices
    have hscaled := (hbase.const_mul (D y i)).const_mul (1 / 2 : ℝ)
    simpa [indices, inverseWishartEntryProduct, Fin.prod_univ_two,
      mul_assoc, mul_comm, mul_left_comm] using hscaled
  have hsum := integrable_finsetSum (Finset.univ : Finset (Fin p))
    (fun x _ ↦ integrable_finsetSum (Finset.univ : Finset (Fin p))
      (fun y _ ↦ hterm x y))
  apply hsum.congr
  filter_upwards [] with R
  simp only [inverseWishartEntryTest, steinVectorFieldValue,
    Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  have hdist :
      (1 / 2 : ℝ) *
          ((∑ y : Fin p, R a y * (realWishartGram R)⁻¹ y x) * D x i) =
        ∑ y : Fin p, (1 / 2 : ℝ) *
          (R a y * (realWishartGram R)⁻¹ y x) * D x i := by
    rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    ring
  rw [hdist, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

/-- Matrix-law integrability of the radial value component. -/
theorem integrable_inverseWishartEntryTest_mul_steinVectorFieldValue_radial
    {k p : ℕ} (hgap : p + 8 ≤ k)
    (l m : Fin p) (D : Matrix (Fin p) (Fin p) ℝ)
    (a : Fin k) (i : Fin p) :
    Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        2 * R a i *
          (inverseWishartEntryTest l m R *
            steinVectorFieldValue R D a i))
      (halfGaussianMatrix k p) := by
  have hterm (x y : Fin p) : Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        R a i * R a x *
          ((realWishartGram R)⁻¹ l m * (realWishartGram R)⁻¹ x y) *
          D y i)
      (halfGaussianMatrix k p) := by
    let indices : Fin 2 → Fin p × Fin p := ![(l, m), (x, y)]
    have hbase :=
      integrable_two_matrixCoordinates_mul_inverseWishartEntryProduct_halfGaussianMatrix
        (q := 2) (by norm_num) (by omega) a a i x indices
    have hscaled := hbase.mul_const (D y i)
    simpa [indices, inverseWishartEntryProduct, Fin.prod_univ_two,
      mul_assoc, mul_comm, mul_left_comm] using hscaled
  have hsum := integrable_finsetSum (Finset.univ : Finset (Fin p))
    (fun x _ ↦ integrable_finsetSum (Finset.univ : Finset (Fin p))
      (fun y _ ↦ hterm x y))
  apply hsum.congr
  filter_upwards [] with R
  simp only [inverseWishartEntryTest, steinVectorFieldValue,
    Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  have hdist :
      (1 / 2 : ℝ) *
          ((∑ y : Fin p, R a y * (realWishartGram R)⁻¹ y x) * D x i) =
        ∑ y : Fin p, (1 / 2 : ℝ) *
          (R a y * (realWishartGram R)⁻¹ y x) * D x i := by
    rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    ring
  rw [hdist, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

/-- Integrability of the product between the explicit inverse-entry
derivative in a fixed matrix direction and one Stein-field coordinate. -/
theorem integrable_inverseWishartEntryExplicitDerivative_mul_steinVectorFieldValue_apply
    {k p : ℕ} (hgap : p + 8 ≤ k)
    (l m : Fin p) (E : Matrix (Fin k) (Fin p) ℝ)
    (D : Matrix (Fin p) (Fin p) ℝ)
    (a : Fin k) (i : Fin p) :
    Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        (-((realWishartGram R)⁻¹ *
            (E.transpose * R + R.transpose * E) *
            (realWishartGram R)⁻¹)) l m *
          steinVectorFieldValue R D a i)
      (halfGaussianMatrix k p) := by
  have hmonomial (x y : Fin p) (r : Fin k) (t z : Fin p) :
      Integrable
        (fun R : Matrix (Fin k) (Fin p) ℝ ↦
          ((realWishartGram R)⁻¹ l x *
              (E r x * R r y + R r x * E r y) *
              (realWishartGram R)⁻¹ y m) *
            (R a z * (realWishartGram R)⁻¹ z t * D t i))
        (halfGaussianMatrix k p) := by
    let indices : Fin 3 → Fin p × Fin p :=
      ![(l, x), (y, m), (z, t)]
    have hfirst :=
      integrable_two_matrixCoordinates_mul_inverseWishartEntryProduct_halfGaussianMatrix
        (q := 3) (by norm_num) (by omega) r a y z indices
    have hsecond :=
      integrable_two_matrixCoordinates_mul_inverseWishartEntryProduct_halfGaussianMatrix
        (q := 3) (by norm_num) (by omega) r a x z indices
    have hfirstScaled := (hfirst.mul_const (E r x)).mul_const (D t i)
    have hsecondScaled := (hsecond.mul_const (E r y)).mul_const (D t i)
    apply (hfirstScaled.add hsecondScaled).congr
    filter_upwards [] with R
    simp [indices, inverseWishartEntryProduct, Fin.prod_univ_three]
    ring
  have hsum : Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        -(1 / 2 : ℝ) *
          (∑ t : Fin p, ∑ z : Fin p, ∑ y : Fin p,
            ∑ x : Fin p, ∑ r : Fin k,
              ((realWishartGram R)⁻¹ l x *
                  (E r x * R r y + R r x * E r y) *
                  (realWishartGram R)⁻¹ y m) *
                (R a z * (realWishartGram R)⁻¹ z t * D t i)))
      (halfGaussianMatrix k p) := by
    have hinner := integrable_finsetSum (Finset.univ : Finset (Fin p))
      (fun t _ ↦ integrable_finsetSum (Finset.univ : Finset (Fin p))
        (fun z _ ↦ integrable_finsetSum (Finset.univ : Finset (Fin p))
          (fun y _ ↦ integrable_finsetSum (Finset.univ : Finset (Fin p))
            (fun x _ ↦ integrable_finsetSum (Finset.univ : Finset (Fin k))
              (fun r _ ↦ hmonomial x y r t z)))))
    exact hinner.const_mul (-(1 / 2 : ℝ))
  apply hsum.congr
  filter_upwards [] with R
  simp only [steinVectorFieldValue, Matrix.smul_apply, smul_eq_mul,
    Matrix.mul_apply, Matrix.add_apply, Matrix.transpose_apply, Matrix.neg_apply,
    Finset.sum_add_distrib]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t _
  let S : ℝ :=
    -(∑ y : Fin p, ∑ x : Fin p,
      (realWishartGram R)⁻¹ l x *
        ((∑ r : Fin k, E r x * R r y) +
          ∑ r : Fin k, R r x * E r y) *
        (realWishartGram R)⁻¹ y m)
  let T : Fin p → ℝ := fun z ↦
    R a z * (realWishartGram R)⁻¹ z t * D t i
  change _ = S * ((1 / 2 : ℝ) * ∑ z : Fin p, T z)
  rw [← mul_assoc, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  dsimp only [S, T]
  rw [neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.sum_add_distrib]
  simp_rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r _
  ring

/-- Integrability of one inverse entry times a coordinate of the explicit
linearization of the Stein field.  The two nonlinear summands contain three
inverse entries and two Gaussian coordinates, hence the `p + 8 ≤ k`
threshold is more than sufficient. -/
theorem integrable_inverseWishartEntryTest_mul_steinVectorFieldLinearization_apply
    {k p : ℕ} (hgap : p + 8 ≤ k)
    (l m : Fin p) (D : Matrix (Fin p) (Fin p) ℝ)
    (E : Matrix (Fin k) (Fin p) ℝ)
    (a : Fin k) (i : Fin p) :
    Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        inverseWishartEntryTest l m R *
          steinVectorFieldLinearization R D E a i)
      (halfGaussianMatrix k p) := by
  have hfirstTerm (x y : Fin p) : Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        (realWishartGram R)⁻¹ l m *
          (E a x * ((realWishartGram R)⁻¹ x y * D y i)))
      (halfGaussianMatrix k p) := by
    let indices : Fin 2 → Fin p × Fin p := ![(l, m), (x, y)]
    have hbase := integrable_inverseWishartEntryProduct_halfGaussianMatrix
      (k := k) (p := p) (q := 2) (by omega) indices
    have hscaled := (hbase.mul_const (E a x)).mul_const (D y i)
    simpa [indices, inverseWishartEntryProduct, Fin.prod_univ_two,
      mul_assoc, mul_comm, mul_left_comm] using hscaled
  have hfirstSum := integrable_finsetSum (Finset.univ : Finset (Fin p))
    (fun x _ ↦ integrable_finsetSum (Finset.univ : Finset (Fin p))
      (fun y _ ↦ hfirstTerm x y))
  have hfirst : Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        inverseWishartEntryTest l m R *
          (E * ((realWishartGram R)⁻¹ * D)) a i)
      (halfGaussianMatrix k p) := by
    apply hfirstSum.congr
    filter_upwards [] with R
    simp only [inverseWishartEntryTest, Matrix.mul_apply]
    simp only [Finset.mul_sum, Finset.sum_mul]

  have hsecondTerm (b : Fin k) (x z t y : Fin p) : Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        (realWishartGram R)⁻¹ l m *
          ((R a z * (realWishartGram R)⁻¹ z x * E b x) *
            (R b y * (realWishartGram R)⁻¹ y t * D t i)))
      (halfGaussianMatrix k p) := by
    let indices : Fin 3 → Fin p × Fin p :=
      ![(l, m), (z, x), (y, t)]
    have hbase :=
      integrable_two_matrixCoordinates_mul_inverseWishartEntryProduct_halfGaussianMatrix
        (q := 3) (by norm_num) (by omega) a b z y indices
    have hscaled := (hbase.mul_const (E b x)).mul_const (D t i)
    simpa [indices, inverseWishartEntryProduct, Fin.prod_univ_three,
      mul_assoc, mul_comm, mul_left_comm] using hscaled
  have hsecondSum := integrable_finsetSum (Finset.univ : Finset (Fin k))
    (fun b _ ↦ integrable_finsetSum (Finset.univ : Finset (Fin p))
      (fun t _ ↦ integrable_finsetSum (Finset.univ : Finset (Fin p))
        (fun y _ ↦ integrable_finsetSum (Finset.univ : Finset (Fin p))
          (fun x _ ↦ integrable_finsetSum (Finset.univ : Finset (Fin p))
            (fun z _ ↦ hsecondTerm b x z t y)))))
  have hsecond : Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        inverseWishartEntryTest l m R *
          (((R * (realWishartGram R)⁻¹) * E.transpose) *
            (R * (realWishartGram R)⁻¹ * D)) a i)
      (halfGaussianMatrix k p) := by
    apply hsecondSum.congr
    filter_upwards [] with R
    simp only [inverseWishartEntryTest, Matrix.mul_apply,
      Matrix.transpose_apply]
    simp only [Finset.mul_sum, Finset.sum_mul]

  have hthirdTerm (t : Fin p) (b : Fin k) (x z y : Fin p) : Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        (realWishartGram R)⁻¹ l m *
          ((R a z * (realWishartGram R)⁻¹ z x * R b x * E b t) *
            ((realWishartGram R)⁻¹ t y * D y i)))
      (halfGaussianMatrix k p) := by
    let indices : Fin 3 → Fin p × Fin p :=
      ![(l, m), (z, x), (t, y)]
    have hbase :=
      integrable_two_matrixCoordinates_mul_inverseWishartEntryProduct_halfGaussianMatrix
        (q := 3) (by norm_num) (by omega) a b z x indices
    have hscaled := (hbase.mul_const (E b t)).mul_const (D y i)
    simpa [indices, inverseWishartEntryProduct, Fin.prod_univ_three,
      mul_assoc, mul_comm, mul_left_comm] using hscaled
  have hthirdSum := integrable_finsetSum (Finset.univ : Finset (Fin p))
    (fun t _ ↦ integrable_finsetSum (Finset.univ : Finset (Fin p))
      (fun y _ ↦ integrable_finsetSum (Finset.univ : Finset (Fin k))
        (fun b _ ↦ integrable_finsetSum (Finset.univ : Finset (Fin p))
          (fun x _ ↦ integrable_finsetSum (Finset.univ : Finset (Fin p))
            (fun z _ ↦ hthirdTerm t b x z y)))))
  have hthird : Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        inverseWishartEntryTest l m R *
          ((((R * (realWishartGram R)⁻¹) * R.transpose) * E) *
            ((realWishartGram R)⁻¹ * D)) a i)
      (halfGaussianMatrix k p) := by
    apply hthirdSum.congr
    filter_upwards [] with R
    simp only [inverseWishartEntryTest, Matrix.mul_apply,
      Matrix.transpose_apply]
    simp only [Finset.mul_sum, Finset.sum_mul]

  have hcombined := ((hfirst.sub hsecond).sub hthird).const_mul (1 / 2 : ℝ)
  apply hcombined.congr
  filter_upwards [] with R
  simp only [inverseWishartEntryTest, steinVectorFieldLinearization,
    Matrix.smul_apply, smul_eq_mul, Pi.sub_apply, Matrix.sub_apply]
  ring

/-- The derivative-defined inverse entry agrees almost everywhere with its
explicit inverse-sandwich derivative, so its product with a Stein coordinate
inherits the preceding integrability theorem. -/
theorem integrable_inverseWishartEntryTestDerivative_mul_steinVectorFieldValue_apply
    {k p : ℕ} (hgap : p + 8 ≤ k)
    (l m : Fin p) (E : Matrix (Fin k) (Fin p) ℝ)
    (D : Matrix (Fin p) (Fin p) ℝ)
    (a : Fin k) (i : Fin p) :
    Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        inverseWishartEntryTestDerivative l m R E *
          steinVectorFieldValue R D a i)
      (halfGaussianMatrix k p) := by
  have hexplicit :=
    integrable_inverseWishartEntryExplicitDerivative_mul_steinVectorFieldValue_apply
      hgap l m E D a i
  apply hexplicit.congr
  filter_upwards [
    ae_isUnit_det_realWishartGram_halfGaussianMatrix k p (by omega)]
      with R hR
  have hlocal :=
    (hasFDerivAt_inverseWishartEntryTest l m R hR).hasLineDerivAt E
  have hformula :=
    hasDerivAt_inverse_realWishartGram_entry_matrixLine R E hR l m
  have heq := hlocal.unique hformula
  exact (congrArg (fun z : ℝ ↦
    z * steinVectorFieldValue R D a i) heq).symm

/-- Matrix-law integrability of the complete product-rule derivative of one
inverse-entry weighted Stein coordinate. -/
theorem integrable_inverseWishartEntryWeightedSteinComponentDerivative_halfGaussianMatrix
    {k p : ℕ} (hgap : p + 8 ≤ k)
    (l m : Fin p) (D : Matrix (Fin p) (Fin p) ℝ)
    (E : Matrix (Fin k) (Fin p) ℝ)
    (a : Fin k) (i : Fin p) :
    Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        inverseWishartEntryTestDerivative l m R E *
            steinVectorFieldValue R D a i +
          inverseWishartEntryTest l m R *
            steinVectorFieldLinearization R D E a i)
      (halfGaussianMatrix k p) :=
  (integrable_inverseWishartEntryTestDerivative_mul_steinVectorFieldValue_apply
      hgap l m E D a i).add
    (integrable_inverseWishartEntryTest_mul_steinVectorFieldLinearization_apply
      hgap l m D E a i)

/-- Exact coordinate-family contract consumed by the nonsingular-test
Stein--Haff closure.  It contains only value, derivative, and radial
integrability, not an integral identity or any moment formula. -/
structure HalfGaussianInverseWishartEntrySteinFamilies
    {k p n : ℕ} (hdim : n + 1 = k * p)
    (l m : Fin p) (D : Matrix (Fin p) (Fin p) ℝ) : Prop where
  value : ∀ i, Integrable
    (flattenedWeightedSteinComponent hdim
      (inverseWishartEntryTest l m) D i)
    (halfGaussianPi (n + 1))
  derivative : ∀ i, Integrable
    (flattenedWeightedSteinComponentDerivative hdim
      (inverseWishartEntryTest l m)
      (inverseWishartEntryTestDerivative l m) D i)
    (halfGaussianPi (n + 1))
  radial : ∀ i, Integrable
    (fun x ↦ 2 * x i * flattenedWeightedSteinComponent hdim
      (inverseWishartEntryTest l m) D i x)
    (halfGaussianPi (n + 1))

/-- All flattened coordinate families for an inverse-entry test, transported
from the exact matrix-law polynomial/inverse-moment estimates. -/
theorem halfGaussianInverseWishartEntrySteinFamilies
    {k p n : ℕ} (hdim : n + 1 = k * p) (hgap : p + 8 ≤ k)
    (l m : Fin p) (D : Matrix (Fin p) (Fin p) ℝ) :
    HalfGaussianInverseWishartEntrySteinFamilies hdim l m D := by
  let e := flatSuccMatrixMeasurableEquiv hdim
  have hmp : MeasurePreserving e (halfGaussianPi (n + 1))
      (halfGaussianMatrix k p) :=
    measurePreserving_flatSuccMatrixMeasurableEquiv hdim
  refine ⟨?_, ?_, ?_⟩
  · intro q
    let a := flatCoordinateRow hdim q
    let i := flatCoordinateColumn hdim q
    have hm :=
      integrable_inverseWishartEntryTest_mul_steinVectorFieldValue_apply
        hgap l m D a i
    have hf := hmp.integrable_comp_of_integrable hm
    exact hf.congr (Filter.Eventually.of_forall fun x ↦ by rfl)
  · intro q
    let E := flatCoordinateMatrixUnit hdim q
    let a := flatCoordinateRow hdim q
    let i := flatCoordinateColumn hdim q
    have hm :=
      integrable_inverseWishartEntryWeightedSteinComponentDerivative_halfGaussianMatrix
        hgap l m D E a i
    have hf := hmp.integrable_comp_of_integrable hm
    exact hf.congr (Filter.Eventually.of_forall fun x ↦ by rfl)
  · intro q
    let a := flatCoordinateRow hdim q
    let i := flatCoordinateColumn hdim q
    have hm := integrable_inverseWishartEntryTest_mul_steinVectorFieldValue_radial
      hgap l m D a i
    have hf := hmp.integrable_comp_of_integrable hm
    exact hf.congr (Filter.Eventually.of_forall fun x ↦ by
      change 2 * (flatSuccMatrixMeasurableEquiv hdim x) a i *
          (inverseWishartEntryTest l m (flatSuccMatrixMeasurableEquiv hdim x) *
            steinVectorFieldValue (flatSuccMatrixMeasurableEquiv hdim x) D a i) =
        2 * x q *
          (inverseWishartEntryTest l m (flatSuccMatrixMeasurableEquiv hdim x) *
            steinVectorFieldValue (flatSuccMatrixMeasurableEquiv hdim x) D a i)
      rw [show (flatSuccMatrixMeasurableEquiv hdim x) a i = x q by
        simpa [a, i] using flatSuccMatrix_apply_flatCoordinatePair hdim x q])

/-- Stein--Haff for one inverse entry, reduced only to the literal
coordinate-family integrability contract. -/
theorem halfGaussian_inverseWishart_entry_steinHaff_of_families
    {k p n : ℕ} (hdim : n + 1 = k * p) (hp : p < k)
    (hgap : p + 4 ≤ k) (l m : Fin p)
    (D : Matrix (Fin p) (Fin p) ℝ) (hD : D.IsSymm)
    (H : HalfGaussianInverseWishartEntrySteinFamilies hdim l m D) :
    Integrable
        (fun R : Matrix (Fin k) (Fin p) ℝ ↦
          (realWishartGram R)⁻¹ l m *
            (inverseGramScoreCoefficient (Fin k) (Fin p) *
              Matrix.trace ((realWishartGram R)⁻¹ * D)))
        (halfGaussianMatrix k p) ∧
      Integrable
        (fun R : Matrix (Fin k) (Fin p) ℝ ↦
          (realWishartGram R)⁻¹ l m * Matrix.trace D +
            ((realWishartGram R)⁻¹ * D *
              (realWishartGram R)⁻¹) l m)
        (halfGaussianMatrix k p) ∧
      ((∫ R, (realWishartGram R)⁻¹ l m *
            (inverseGramScoreCoefficient (Fin k) (Fin p) *
              Matrix.trace ((realWishartGram R)⁻¹ * D))
          ∂halfGaussianMatrix k p) =
        ∫ R, (realWishartGram R)⁻¹ l m * Matrix.trace D +
            ((realWishartGram R)⁻¹ * D *
              (realWishartGram R)⁻¹) l m
          ∂halfGaussianMatrix k p) := by
  have h :=
    steinHaff_halfGaussianMatrix_of_nonsingular_fderiv_and_flattenedSteinFamilies
      hdim hp
      (inverseWishartEntryTest l m)
      (inverseWishartEntryTestDerivative l m) D
      (fun R ↦ -(((realWishartGram R)⁻¹ * D *
        (realWishartGram R)⁻¹) l m))
      (fun R hR ↦ hasFDerivAt_inverseWishartEntryTest l m R hR)
      (fun R hR ↦
        inverseWishartEntryTestDerivative_steinVectorFieldValue
          l m R D hD hR)
      (integrable_inverseWishartEntrySandwich_halfGaussianMatrix hgap D l m)
      H.value H.derivative H.radial
  simpa [inverseWishartEntryTest, sub_eq_add_neg] using h

/-- Unconditional inverse-entry Stein--Haff identity at the polynomial
inverse-moment threshold. -/
theorem halfGaussian_inverseWishart_entry_steinHaff
    {k p n : ℕ} (hdim : n + 1 = k * p) (hgap : p + 8 ≤ k)
    (l m : Fin p) (D : Matrix (Fin p) (Fin p) ℝ) (hD : D.IsSymm) :
    Integrable
        (fun R : Matrix (Fin k) (Fin p) ℝ ↦
          (realWishartGram R)⁻¹ l m *
            (inverseGramScoreCoefficient (Fin k) (Fin p) *
              Matrix.trace ((realWishartGram R)⁻¹ * D)))
        (halfGaussianMatrix k p) ∧
      Integrable
        (fun R : Matrix (Fin k) (Fin p) ℝ ↦
          (realWishartGram R)⁻¹ l m * Matrix.trace D +
            ((realWishartGram R)⁻¹ * D *
              (realWishartGram R)⁻¹) l m)
        (halfGaussianMatrix k p) ∧
      ((∫ R, (realWishartGram R)⁻¹ l m *
            (inverseGramScoreCoefficient (Fin k) (Fin p) *
              Matrix.trace ((realWishartGram R)⁻¹ * D))
          ∂halfGaussianMatrix k p) =
        ∫ R, (realWishartGram R)⁻¹ l m * Matrix.trace D +
            ((realWishartGram R)⁻¹ * D *
              (realWishartGram R)⁻¹) l m
          ∂halfGaussianMatrix k p) :=
  halfGaussian_inverseWishart_entry_steinHaff_of_families
    hdim (by omega) (by omega) l m D hD
      (halfGaussianInverseWishartEntrySteinFamilies hdim hgap l m D)

/-- Entry expansion for a symmetric two-single matrix sandwich. -/
theorem matrix_mul_symmetricSingle_mul_entry
    {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    (i j l m : Fin p) :
    (A * ((Matrix.single j i 1 + Matrix.single i j 1) :
      Matrix (Fin p) (Fin p) ℝ) * A) l m =
      A l j * A i m + A l i * A j m := by
  rw [Matrix.mul_assoc, Matrix.add_mul, Matrix.mul_add, Matrix.add_apply]
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and]

/-- The inverse-entry Stein--Haff identity gives the exact three-pair
second-entry recursion, with all coordinate-family integrability discharged
internally. -/
theorem halfGaussian_inverseWishart_secondEntry_steinRecursion
    {k p : ℕ} (hgap : p + 8 ≤ k) :
    HalfGaussianInverseWishartSecondEntrySteinRecursion k p := by
  refine ⟨?_⟩
  intro i j l m
  have hp0 : 0 < p := by
    have hi := i.isLt
    omega
  have hk0 : 0 < k := by omega
  have hkp0 : 0 < k * p := Nat.mul_pos hk0 hp0
  let n := k * p - 1
  have hdim : n + 1 = k * p := by
    dsimp only [n]
    omega
  let D : Matrix (Fin p) (Fin p) ℝ :=
    Matrix.single j i 1 + Matrix.single i j 1
  have hD : D.IsSymm := by
    dsimp only [D]
    simpa [Matrix.transpose_single] using
      Matrix.isSymm_add_transpose_self (Matrix.single j i (1 : ℝ))
  have hHaff := halfGaussian_inverseWishart_entry_steinHaff
    hdim hgap l m D hD
  have heq := hHaff.2.2
  let c := inverseWishartEntryGap k p
  have hcoeff : inverseGramScoreCoefficient (Fin k) (Fin p) = c / 2 := by
    simp [inverseGramScoreCoefficient, inverseWishartEntryGap, c]
  have htraceD : Matrix.trace D = 2 * realKroneckerDelta i j := by
    by_cases hij : i = j
    · subst j
      dsimp only [D]
      rw [Matrix.trace_add, Matrix.trace_single_eq_same]
      norm_num [realKroneckerDelta]
    · have hji : j ≠ i := fun hji ↦ hij hji.symm
      dsimp only [D]
      rw [Matrix.trace_add,
        Matrix.trace_single_eq_of_ne j i (1 : ℝ) hji,
        Matrix.trace_single_eq_of_ne i j (1 : ℝ) hij]
      simp [realKroneckerDelta, hij]
  have htraceInv :
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        Matrix.trace ((realWishartGram R)⁻¹ * D)) =
      (fun R ↦ 2 * (realWishartGram R)⁻¹ i j) := by
    funext R
    rw [show D = Matrix.single j i 1 + Matrix.single i j 1 by rfl,
      Matrix.mul_add, Matrix.trace_add,
      trace_mul_single_eq_entry, trace_mul_single_eq_entry,
      (realWishartGram_inv_isSymm R).apply i j]
    ring
  have hsandwich :
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        ((realWishartGram R)⁻¹ * D * (realWishartGram R)⁻¹) l m) =
      (fun R ↦
        (realWishartGram R)⁻¹ l j * (realWishartGram R)⁻¹ i m +
          (realWishartGram R)⁻¹ l i * (realWishartGram R)⁻¹ j m) := by
    funext R
    simpa only [D] using
      matrix_mul_symmetricSingle_mul_entry (realWishartGram R)⁻¹ i j l m
  rw [hcoeff] at heq
  have heq' :
      (∫ R : Matrix (Fin k) (Fin p) ℝ,
        (realWishartGram R)⁻¹ l m *
          (c / 2 * (2 * (realWishartGram R)⁻¹ i j))
        ∂halfGaussianMatrix k p) =
      ∫ R : Matrix (Fin k) (Fin p) ℝ,
        (realWishartGram R)⁻¹ l m * (2 * realKroneckerDelta i j) +
          ((realWishartGram R)⁻¹ l j * (realWishartGram R)⁻¹ i m +
            (realWishartGram R)⁻¹ l i * (realWishartGram R)⁻¹ j m)
        ∂halfGaussianMatrix k p := by
    calc
      (∫ R : Matrix (Fin k) (Fin p) ℝ,
        (realWishartGram R)⁻¹ l m *
          (c / 2 * (2 * (realWishartGram R)⁻¹ i j))
        ∂halfGaussianMatrix k p) =
          ∫ R, (realWishartGram R)⁻¹ l m *
            (c / 2 * Matrix.trace ((realWishartGram R)⁻¹ * D))
          ∂halfGaussianMatrix k p := by
        apply integral_congr_ae
        filter_upwards [] with R
        rw [congrFun htraceInv R]
      _ = ∫ R, (realWishartGram R)⁻¹ l m * Matrix.trace D +
            ((realWishartGram R)⁻¹ * D * (realWishartGram R)⁻¹) l m
          ∂halfGaussianMatrix k p := heq
      _ = ∫ R : Matrix (Fin k) (Fin p) ℝ,
          (realWishartGram R)⁻¹ l m * (2 * realKroneckerDelta i j) +
            ((realWishartGram R)⁻¹ l j * (realWishartGram R)⁻¹ i m +
              (realWishartGram R)⁻¹ l i * (realWishartGram R)⁻¹ j m)
          ∂halfGaussianMatrix k p := by
        apply integral_congr_ae
        filter_upwards [] with R
        rw [htraceD, congrFun hsandwich R]

  have hentry (a b : Fin p) : Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        (realWishartGram R)⁻¹ a b)
      (halfGaussianMatrix k p) := by
    let indices : Fin 1 → Fin p × Fin p := ![(a, b)]
    have hbase := integrable_inverseWishartEntryProduct_halfGaussianMatrix
      (k := k) (p := p) (q := 1) (by omega) indices
    apply hbase.congr
    filter_upwards [] with R
    simp [indices, inverseWishartEntryProduct, Fin.prod_univ_one]
  have hsecond (a b d e : Fin p) : Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        (realWishartGram R)⁻¹ a b * (realWishartGram R)⁻¹ d e)
      (halfGaussianMatrix k p) := by
    let indices : Fin 2 → Fin p × Fin p := ![(a, b), (d, e)]
    have hbase := integrable_inverseWishartEntryProduct_halfGaussianMatrix
      (k := k) (p := p) (q := 2) (by omega) indices
    apply hbase.congr
    filter_upwards [] with R
    simp [indices, inverseWishartEntryProduct, Fin.prod_univ_two]
  have hmeanTerm : Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        (realWishartGram R)⁻¹ l m * (2 * realKroneckerDelta i j))
      (halfGaussianMatrix k p) :=
    (hentry l m).mul_const (2 * realKroneckerDelta i j)
  have hfirstProduct : Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        (realWishartGram R)⁻¹ l j * (realWishartGram R)⁻¹ i m)
      (halfGaussianMatrix k p) := hsecond l j i m
  have hsecondProduct : Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        (realWishartGram R)⁻¹ l i * (realWishartGram R)⁻¹ j m)
      (halfGaussianMatrix k p) := hsecond l i j m
  have hmeanIntegral :
      (∫ R : Matrix (Fin k) (Fin p) ℝ,
        (realWishartGram R)⁻¹ l m * (2 * realKroneckerDelta i j)
          ∂halfGaussianMatrix k p) =
        2 * halfGaussianInverseWishartEntryMeanIntegral k p l m *
          realKroneckerDelta i j := by
    unfold halfGaussianInverseWishartEntryMeanIntegral
    rw [show (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        (realWishartGram R)⁻¹ l m * (2 * realKroneckerDelta i j)) =
      (fun R ↦ (2 * realKroneckerDelta i j) *
        (realWishartGram R)⁻¹ l m) by
          funext R
          ring,
      integral_const_mul]
    ring
  have hfirstIntegral :
      (∫ R : Matrix (Fin k) (Fin p) ℝ,
        (realWishartGram R)⁻¹ l j * (realWishartGram R)⁻¹ i m
          ∂halfGaussianMatrix k p) =
        halfGaussianInverseWishartSecondEntryIntegral k p i m j l := by
    unfold halfGaussianInverseWishartSecondEntryIntegral
    apply integral_congr_ae
    filter_upwards [] with R
    rw [(realWishartGram_inv_isSymm R).apply l j]
    ring
  have hsecondIntegral :
      (∫ R : Matrix (Fin k) (Fin p) ℝ,
        (realWishartGram R)⁻¹ l i * (realWishartGram R)⁻¹ j m
          ∂halfGaussianMatrix k p) =
        halfGaussianInverseWishartSecondEntryIntegral k p i l j m := by
    unfold halfGaussianInverseWishartSecondEntryIntegral
    apply integral_congr_ae
    filter_upwards [] with R
    rw [(realWishartGram_inv_isSymm R).apply l i]
  calc
    c * halfGaussianInverseWishartSecondEntryIntegral k p i j l m =
        ∫ R : Matrix (Fin k) (Fin p) ℝ,
          (realWishartGram R)⁻¹ l m *
            (c / 2 * (2 * (realWishartGram R)⁻¹ i j))
          ∂halfGaussianMatrix k p := by
      unfold halfGaussianInverseWishartSecondEntryIntegral
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with R
      ring
    _ = ∫ R : Matrix (Fin k) (Fin p) ℝ,
          (realWishartGram R)⁻¹ l m * (2 * realKroneckerDelta i j) +
            ((realWishartGram R)⁻¹ l j * (realWishartGram R)⁻¹ i m +
              (realWishartGram R)⁻¹ l i * (realWishartGram R)⁻¹ j m)
          ∂halfGaussianMatrix k p := heq'
    _ = (∫ R : Matrix (Fin k) (Fin p) ℝ,
          (realWishartGram R)⁻¹ l m * (2 * realKroneckerDelta i j)
            ∂halfGaussianMatrix k p) +
        ((∫ R : Matrix (Fin k) (Fin p) ℝ,
          (realWishartGram R)⁻¹ l j * (realWishartGram R)⁻¹ i m
            ∂halfGaussianMatrix k p) +
        (∫ R : Matrix (Fin k) (Fin p) ℝ,
          (realWishartGram R)⁻¹ l i * (realWishartGram R)⁻¹ j m
            ∂halfGaussianMatrix k p)) := by
      have houter := integral_add hmeanTerm
        (hfirstProduct.add hsecondProduct)
      have hinner := integral_add hfirstProduct hsecondProduct
      calc
        _ = (∫ R : Matrix (Fin k) (Fin p) ℝ,
              (realWishartGram R)⁻¹ l m * (2 * realKroneckerDelta i j)
                ∂halfGaussianMatrix k p) +
            ∫ R : Matrix (Fin k) (Fin p) ℝ,
              (realWishartGram R)⁻¹ l j * (realWishartGram R)⁻¹ i m +
                (realWishartGram R)⁻¹ l i * (realWishartGram R)⁻¹ j m
                ∂halfGaussianMatrix k p := by
          simpa only [Pi.add_apply] using houter
        _ = _ := congrArg
          (fun z : ℝ ↦ (∫ R : Matrix (Fin k) (Fin p) ℝ,
            (realWishartGram R)⁻¹ l m * (2 * realKroneckerDelta i j)
              ∂halfGaussianMatrix k p) + z) hinner
    _ = 2 * halfGaussianInverseWishartEntryMeanIntegral k p l m *
          realKroneckerDelta i j +
        halfGaussianInverseWishartSecondEntryIntegral k p i l j m +
        halfGaussianInverseWishartSecondEntryIntegral k p i m j l := by
      rw [hmeanIntegral, hfirstIntegral, hsecondIntegral]
      ring

/-- Exact variance-one scaled inverse-Wishart second-entry tensor at the
dimension-uniform H8/H10 threshold. -/
theorem scaledInverseWishartSecondEntryMomentFormula_internal
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K) :
    ScaledInverseWishartSecondEntryMomentFormula N K :=
  scaledInverseWishartSecondEntryMomentFormula_of_stein_conditional hgap
    (halfGaussian_inverseWishart_secondEntry_steinRecursion
      (k := K - N) (p := N) (by omega))

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08
