import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.InverseWishartSecondEntryStein
import Mathlib.Tactic

/-!
# Direct third-entry inverse-Wishart Stein recursion

This module fills the analytic order-three gap between the existing
single-entry and triple-entry Stein tests.  It differentiates a product of
two inverse-Gram entries, proves the three flattened coordinate-family
integrability obligations, and derives the exact five-term recursion for a
product of three inverse entries.

No endpoint or literature identity is assumed here.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.Elementwise

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08

noncomputable section

open LogdetLean.GramHafnian
open LogdetLean.GramHafnian.Wishart
open LogdetLean.GramHafnian.UltimateHiding.DenseScore

set_option maxHeartbeats 3600000

/-! ## Double-entry differential calculus -/

/-- Product of two prescribed inverse-Gram entries. -/
def inverseWishartDoubleEntryTest {k p : ℕ}
    (a b c d : Fin p) (R : Matrix (Fin k) (Fin p) ℝ) : ℝ :=
  (realWishartGram R)⁻¹ a b * (realWishartGram R)⁻¹ c d

/-- Its canonical Frechet derivative. -/
def inverseWishartDoubleEntryTestDerivative {k p : ℕ}
    (a b c d : Fin p) (R : Matrix (Fin k) (Fin p) ℝ) :
    Matrix (Fin k) (Fin p) ℝ →L[ℝ] ℝ :=
  fderiv ℝ (inverseWishartDoubleEntryTest a b c d) R

/-- The double product is Frechet differentiable on the full-rank locus. -/
theorem hasFDerivAt_inverseWishartDoubleEntryTest
    {k p : ℕ} (a b c d : Fin p)
    (R : Matrix (Fin k) (Fin p) ℝ)
    (hfull : IsUnit (realWishartGram R).det) :
    HasFDerivAt (inverseWishartDoubleEntryTest a b c d)
      (inverseWishartDoubleEntryTestDerivative a b c d R) R := by
  have h1 := hasFDerivAt_inverseWishartEntryTest a b R hfull
  have h2 := hasFDerivAt_inverseWishartEntryTest c d R hfull
  exact (h1.mul h2).differentiableAt.hasFDerivAt

/-- Explicit product-rule derivative in a lifted symmetric Gram direction. -/
theorem inverseWishartDoubleEntryTestDerivative_steinVectorFieldValue
    {k p : ℕ} (a b c d : Fin p)
    (R : Matrix (Fin k) (Fin p) ℝ)
    (D : Matrix (Fin p) (Fin p) ℝ) (hD : D.IsSymm)
    (hfull : IsUnit (realWishartGram R).det) :
    inverseWishartDoubleEntryTestDerivative a b c d R
        (steinVectorFieldValue R D) =
      -(((realWishartGram R)⁻¹ * D * (realWishartGram R)⁻¹) a b) *
          (realWishartGram R)⁻¹ c d -
        (realWishartGram R)⁻¹ a b *
          (((realWishartGram R)⁻¹ * D * (realWishartGram R)⁻¹) c d) := by
  let V := steinVectorFieldValue R D
  have hlocal :=
    (hasFDerivAt_inverseWishartDoubleEntryTest a b c d R hfull).hasLineDerivAt V
  have h1 :=
    (hasFDerivAt_inverseWishartEntryTest a b R hfull).hasLineDerivAt V
  have h2 :=
    (hasFDerivAt_inverseWishartEntryTest c d R hfull).hasLineDerivAt V
  have hprod := h1.mul h2
  have heq := hlocal.unique hprod
  dsimp only [V] at heq
  simp only [zero_smul, add_zero, Pi.mul_apply] at heq
  have hv1 := inverseWishartEntryTestDerivative_steinVectorFieldValue
    a b R D hD hfull
  have hv2 := inverseWishartEntryTestDerivative_steinVectorFieldValue
    c d R D hD hfull
  have halg {x y : ℝ}
      (hx : x = -(((realWishartGram R)⁻¹ * D *
        (realWishartGram R)⁻¹) a b))
      (hy : y = -(((realWishartGram R)⁻¹ * D *
        (realWishartGram R)⁻¹) c d)) :
      x * inverseWishartEntryTest c d R +
          inverseWishartEntryTest a b R * y =
        -(((realWishartGram R)⁻¹ * D * (realWishartGram R)⁻¹) a b) *
            (realWishartGram R)⁻¹ c d -
          (realWishartGram R)⁻¹ a b *
            (((realWishartGram R)⁻¹ * D * (realWishartGram R)⁻¹) c d) := by
    rw [hx, hy]
    simp only [inverseWishartEntryTest]
    ring
  exact heq.trans (halg hv1 hv2)

/-- Full product-rule derivative in an arbitrary rectangular direction. -/
theorem inverseWishartDoubleEntryTestDerivative_apply
    {k p : ℕ} (a b c d : Fin p)
    (R E : Matrix (Fin k) (Fin p) ℝ)
    (hfull : IsUnit (realWishartGram R).det) :
    inverseWishartDoubleEntryTestDerivative a b c d R E =
      (-((realWishartGram R)⁻¹ *
          (E.transpose * R + R.transpose * E) *
          (realWishartGram R)⁻¹)) a b *
          (realWishartGram R)⁻¹ c d +
        (realWishartGram R)⁻¹ a b *
          (-((realWishartGram R)⁻¹ *
            (E.transpose * R + R.transpose * E) *
            (realWishartGram R)⁻¹)) c d := by
  have hlocal :=
    (hasFDerivAt_inverseWishartDoubleEntryTest a b c d R hfull).hasLineDerivAt E
  have h1 :=
    (hasFDerivAt_inverseWishartEntryTest a b R hfull).hasLineDerivAt E
  have h2 :=
    (hasFDerivAt_inverseWishartEntryTest c d R hfull).hasLineDerivAt E
  have hprod := h1.mul h2
  have heq := hlocal.unique hprod
  simp only [zero_smul, add_zero, Pi.mul_apply] at heq
  have hv1 := h1.unique
    (hasDerivAt_inverse_realWishartGram_entry_matrixLine R E hfull a b)
  have hv2 := h2.unique
    (hasDerivAt_inverse_realWishartGram_entry_matrixLine R E hfull c d)
  have halg {x y : ℝ}
      (hx : x = (-((realWishartGram R)⁻¹ *
        (E.transpose * R + R.transpose * E) *
        (realWishartGram R)⁻¹)) a b)
      (hy : y = (-((realWishartGram R)⁻¹ *
        (E.transpose * R + R.transpose * E) *
        (realWishartGram R)⁻¹)) c d) :
      x * inverseWishartEntryTest c d R +
          inverseWishartEntryTest a b R * y =
        (-((realWishartGram R)⁻¹ *
            (E.transpose * R + R.transpose * E) *
            (realWishartGram R)⁻¹)) a b *
            (realWishartGram R)⁻¹ c d +
          (realWishartGram R)⁻¹ a b *
            (-((realWishartGram R)⁻¹ *
              (E.transpose * R + R.transpose * E) *
              (realWishartGram R)⁻¹)) c d := by
    rw [hx, hy]
    simp only [inverseWishartEntryTest]
  exact heq.trans (halg hv1 hv2)

/-! ## Matrix-law integrability for the double-entry Stein test -/

/-- The explicit Stein-direction derivative of a double entry product is
integrable once third inverse-entry products exist. -/
theorem integrable_inverseWishartDoubleEntrySteinDerivativeValue
    {k p : ℕ} (hgap : p + 6 ≤ k)
    (a b c d : Fin p) (D : Matrix (Fin p) (Fin p) ℝ) :
    Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        -(((realWishartGram R)⁻¹ * D * (realWishartGram R)⁻¹) a b) *
            (realWishartGram R)⁻¹ c d -
          (realWishartGram R)⁻¹ a b *
            (((realWishartGram R)⁻¹ * D *
              (realWishartGram R)⁻¹) c d))
      (halfGaussianMatrix k p) := by
  have hterm (u v x y : Fin p) : Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        (((realWishartGram R)⁻¹ * D * (realWishartGram R)⁻¹) u v) *
          (realWishartGram R)⁻¹ x y)
      (halfGaussianMatrix k p) := by
    have hmonomial (i j : Fin p) : Integrable
        (fun R : Matrix (Fin k) (Fin p) ℝ ↦
          (realWishartGram R)⁻¹ u i * D i j *
            (realWishartGram R)⁻¹ j v *
              (realWishartGram R)⁻¹ x y)
        (halfGaussianMatrix k p) := by
      let indices : Fin 3 → Fin p × Fin p :=
        ![(u, i), (j, v), (x, y)]
      have hbase := integrable_inverseWishartEntryProduct_halfGaussianMatrix
        (k := k) (p := p) (q := 3) (by omega) indices
      have hscaled := hbase.mul_const (D i j)
      simpa [indices, inverseWishartEntryProduct, Fin.prod_univ_three,
        mul_assoc, mul_comm, mul_left_comm] using hscaled
    have hsum := integrable_finsetSum (Finset.univ : Finset (Fin p))
      (fun i _ ↦ integrable_finsetSum (Finset.univ : Finset (Fin p))
        (fun j _ ↦ hmonomial i j))
    apply hsum.congr
    filter_upwards [] with R
    simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
  have h := (hterm a b c d).neg.sub (hterm c d a b)
  apply h.congr
  filter_upwards [] with R
  simp only [Pi.sub_apply, Pi.neg_apply]
  ring

/-- Value component of the double-entry weighted Stein field. -/
theorem integrable_inverseWishartDoubleEntryTest_mul_steinVectorFieldValue_apply
    {k p : ℕ} (hgap : p + 6 ≤ k)
    (u v x y : Fin p) (D : Matrix (Fin p) (Fin p) ℝ)
    (a : Fin k) (i : Fin p) :
    Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        inverseWishartDoubleEntryTest u v x y R *
          steinVectorFieldValue R D a i)
      (halfGaussianMatrix k p) := by
  have hterm (s t : Fin p) : Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        (1 / 2 : ℝ) *
          (R a s *
            ((realWishartGram R)⁻¹ u v *
              (realWishartGram R)⁻¹ x y *
              (realWishartGram R)⁻¹ s t)) * D t i)
      (halfGaussianMatrix k p) := by
    let indices : Fin 3 → Fin p × Fin p :=
      ![(u, v), (x, y), (s, t)]
    have hbase :=
      integrable_matrixCoordinate_mul_inverseWishartEntryProduct_halfGaussianMatrix
        (q := 3) (by norm_num) (by omega) a s indices
    have hscaled := (hbase.mul_const (D t i)).const_mul (1 / 2 : ℝ)
    simpa [indices, inverseWishartEntryProduct, Fin.prod_univ_three,
      mul_assoc, mul_comm, mul_left_comm] using hscaled
  have hsum := integrable_finsetSum (Finset.univ : Finset (Fin p))
    (fun s _ ↦ integrable_finsetSum (Finset.univ : Finset (Fin p))
      (fun t _ ↦ hterm s t))
  apply hsum.congr
  filter_upwards [] with R
  simp only [inverseWishartDoubleEntryTest, steinVectorFieldValue,
    Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  ring

/-- Radial value component; only two Gaussian coordinates and three inverse
entries occur. -/
theorem integrable_inverseWishartDoubleEntryTest_mul_steinVectorFieldValue_radial
    {k p : ℕ} (hgap : p + 6 ≤ k)
    (u v x y : Fin p) (D : Matrix (Fin p) (Fin p) ℝ)
    (a : Fin k) (i : Fin p) :
    Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        2 * R a i *
          (inverseWishartDoubleEntryTest u v x y R *
            steinVectorFieldValue R D a i))
      (halfGaussianMatrix k p) := by
  have hterm (s t : Fin p) : Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        R a i * R a s *
          ((realWishartGram R)⁻¹ u v *
            (realWishartGram R)⁻¹ x y *
            (realWishartGram R)⁻¹ s t) * D t i)
      (halfGaussianMatrix k p) := by
    let indices : Fin 3 → Fin p × Fin p :=
      ![(u, v), (x, y), (s, t)]
    have hbase :=
      integrable_two_matrixCoordinates_mul_inverseWishartEntryProduct_halfGaussianMatrix
        (q := 3) (by norm_num) (by omega) a a i s indices
    have hscaled := hbase.mul_const (D t i)
    simpa [indices, inverseWishartEntryProduct, Fin.prod_univ_three,
      mul_assoc, mul_comm, mul_left_comm] using hscaled
  have hsum := integrable_finsetSum (Finset.univ : Finset (Fin p))
    (fun s _ ↦ integrable_finsetSum (Finset.univ : Finset (Fin p))
      (fun t _ ↦ hterm s t))
  apply hsum.congr
  filter_upwards [] with R
  simp only [inverseWishartDoubleEntryTest, steinVectorFieldValue,
    Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  ring

private theorem neg_half_sum_four_product_factor
    {I J S R W : Type*}
    [Fintype I] [Fintype J] [Fintype S] [Fintype R] [Fintype W]
    (F : S → R → W → ℝ) (T : I → J → ℝ) (x : ℝ) :
    -(1 / 2 : ℝ) *
        (∑ i : I, ∑ j : J, ∑ s : S, ∑ r : R, ∑ w : W,
          F s r w * x * T i j) =
      (-(∑ s : S, ∑ r : R, ∑ w : W, F s r w)) *
        x * ((1 / 2 : ℝ) * ∑ i : I, ∑ j : J, T i j) := by
  classical
  let C : ℝ := (∑ s : S, ∑ r : R, ∑ w : W, F s r w) * x
  have hfactor (i : I) (j : J) :
      (∑ s : S, ∑ r : R, ∑ w : W, F s r w * x * T i j) =
        T i j * C := by
    calc
      (∑ s : S, ∑ r : R, ∑ w : W, F s r w * x * T i j) =
          ∑ s : S, ∑ r : R, ∑ w : W, F s r w * (x * T i j) := by
            apply Finset.sum_congr rfl
            intro s _
            apply Finset.sum_congr rfl
            intro r _
            apply Finset.sum_congr rfl
            intro w _
            ring
      _ = ∑ s : S, ∑ r : R, (∑ w : W, F s r w) * (x * T i j) := by
        apply Finset.sum_congr rfl
        intro s _
        apply Finset.sum_congr rfl
        intro r _
        exact (Finset.sum_mul Finset.univ (fun w : W ↦ F s r w)
          (x * T i j)).symm
      _ = ∑ s : S, (∑ r : R, ∑ w : W, F s r w) * (x * T i j) := by
        apply Finset.sum_congr rfl
        intro s _
        exact (Finset.sum_mul Finset.univ
          (fun r : R ↦ ∑ w : W, F s r w) (x * T i j)).symm
      _ = (∑ s : S, ∑ r : R, ∑ w : W, F s r w) * (x * T i j) :=
        (Finset.sum_mul Finset.univ
          (fun s : S ↦ ∑ r : R, ∑ w : W, F s r w) (x * T i j)).symm
      _ = T i j * C := by
        dsimp only [C]
        ring
  simp_rw [hfactor]
  have hcollapse :
      (∑ i : I, ∑ j : J, T i j * C) =
        (∑ i : I, ∑ j : J, T i j) * C := by
    calc
      (∑ i : I, ∑ j : J, T i j * C) =
          ∑ i : I, (∑ j : J, T i j) * C := by
            apply Finset.sum_congr rfl
            intro i _
            exact (Finset.sum_mul Finset.univ (fun j : J ↦ T i j) C).symm
      _ = (∑ i : I, ∑ j : J, T i j) * C :=
        (Finset.sum_mul Finset.univ (fun i : I ↦ ∑ j : J, T i j) C).symm
  rw [hcollapse]
  dsimp only [C]
  ring

/-- One explicit inverse-entry derivative, one additional inverse entry,
and a Stein-field coordinate are integrable in the order-four range. -/
theorem integrable_inverseWishartEntryExplicitDerivative_mul_oneEntry_mul_steinValue
    {k p : ℕ} (hgap : p + 8 ≤ k)
    (u v x y : Fin p) (E : Matrix (Fin k) (Fin p) ℝ)
    (D : Matrix (Fin p) (Fin p) ℝ)
    (a : Fin k) (i : Fin p) :
    Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        (-((realWishartGram R)⁻¹ *
            (E.transpose * R + R.transpose * E) *
            (realWishartGram R)⁻¹)) u v *
          (realWishartGram R)⁻¹ x y *
          steinVectorFieldValue R D a i)
      (halfGaussianMatrix k p) := by
  have hmonomial (r s : Fin p) (row : Fin k) (t q : Fin p) :
      Integrable
        (fun R : Matrix (Fin k) (Fin p) ℝ ↦
          (((realWishartGram R)⁻¹ u r *
              (E row r * R row s + R row r * E row s) *
              (realWishartGram R)⁻¹ s v) *
            (realWishartGram R)⁻¹ x y) *
            (R a q * (realWishartGram R)⁻¹ q t * D t i))
        (halfGaussianMatrix k p) := by
    let indices : Fin 4 → Fin p × Fin p :=
      ![(u, r), (s, v), (x, y), (q, t)]
    have hfirst :=
      integrable_two_matrixCoordinates_mul_inverseWishartEntryProduct_halfGaussianMatrix
        (q := 4) (by norm_num) (by omega) row a s q indices
    have hsecond :=
      integrable_two_matrixCoordinates_mul_inverseWishartEntryProduct_halfGaussianMatrix
        (q := 4) (by norm_num) (by omega) row a r q indices
    have hfirstScaled := (hfirst.mul_const (E row r)).mul_const (D t i)
    have hsecondScaled := (hsecond.mul_const (E row s)).mul_const (D t i)
    apply (hfirstScaled.add hsecondScaled).congr
    filter_upwards [] with R
    simp [indices, inverseWishartEntryProduct, Fin.prod_univ_four]
    ring
  have hsum : Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        -(1 / 2 : ℝ) *
          (∑ t : Fin p, ∑ q : Fin p, ∑ s : Fin p,
            ∑ r : Fin p, ∑ row : Fin k,
              (((realWishartGram R)⁻¹ u r *
                  (E row r * R row s + R row r * E row s) *
                  (realWishartGram R)⁻¹ s v) *
                (realWishartGram R)⁻¹ x y) *
                (R a q * (realWishartGram R)⁻¹ q t * D t i)))
      (halfGaussianMatrix k p) := by
    have hinner := integrable_finsetSum (Finset.univ : Finset (Fin p))
      (fun t _ ↦ integrable_finsetSum (Finset.univ : Finset (Fin p))
        (fun q _ ↦ integrable_finsetSum (Finset.univ : Finset (Fin p))
          (fun s _ ↦ integrable_finsetSum (Finset.univ : Finset (Fin p))
            (fun r _ ↦ integrable_finsetSum (Finset.univ : Finset (Fin k))
              (fun row _ ↦ hmonomial r s row t q)))))
    exact hinner.const_mul (-(1 / 2 : ℝ))
  apply hsum.congr
  filter_upwards [] with R
  simp only [steinVectorFieldValue, Matrix.smul_apply, smul_eq_mul,
    Matrix.mul_apply, Matrix.add_apply, Matrix.transpose_apply,
    Matrix.neg_apply, Finset.sum_add_distrib]
  let F : Fin p → Fin p → Fin k → ℝ := fun s r row ↦
    (realWishartGram R)⁻¹ u r *
      (E row r * R row s + R row r * E row s) *
      (realWishartGram R)⁻¹ s v
  let T : Fin p → Fin p → ℝ := fun t q ↦
    R a q * (realWishartGram R)⁻¹ q t * D t i
  have hrow (s r : Fin p) :
      (realWishartGram R)⁻¹ u r *
          ((∑ row : Fin k, E row r * R row s) +
            ∑ row : Fin k, R row r * E row s) *
          (realWishartGram R)⁻¹ s v =
        ∑ row : Fin k, F s r row := by
    dsimp only [F]
    conv_lhs =>
      rw [mul_add]
      rw [Finset.mul_sum, Finset.mul_sum]
      rw [add_mul]
      rw [Finset.sum_mul, Finset.sum_mul]
      rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro row _
    ring
  have hrowsum :
      (∑ s : Fin p,
        (∑ r : Fin p,
          (realWishartGram R)⁻¹ u r *
            ((∑ row : Fin k, E row r * R row s) +
              ∑ row : Fin k, R row r * E row s)) *
          (realWishartGram R)⁻¹ s v) =
        ∑ s : Fin p, ∑ r : Fin p, ∑ row : Fin k, F s r row := by
    apply Finset.sum_congr rfl
    intro s _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r _
    exact hrow s r
  have hTsum :
      (∑ t : Fin p,
        (∑ q : Fin p, R a q * (realWishartGram R)⁻¹ q t) * D t i) =
        ∑ t : Fin p, ∑ q : Fin p, T t q := by
    apply Finset.sum_congr rfl
    intro t _
    rw [Finset.sum_mul]
  rw [hrowsum]
  rw [hTsum]
  change
    -(1 / 2 : ℝ) *
        (∑ t : Fin p, ∑ q : Fin p, ∑ s : Fin p, ∑ r : Fin p,
          ∑ row : Fin k, F s r row * (realWishartGram R)⁻¹ x y * T t q) =
      (-(∑ s : Fin p, ∑ r : Fin p, ∑ row : Fin k, F s r row)) *
        (realWishartGram R)⁻¹ x y *
          ((1 / 2 : ℝ) * ∑ t : Fin p, ∑ q : Fin p, T t q)
  exact neg_half_sum_four_product_factor F T
    ((realWishartGram R)⁻¹ x y)

/-- A double inverse-entry test times the explicit linearization of the
Stein field is integrable at the order-four threshold. -/
theorem integrable_inverseWishartDoubleEntryTest_mul_steinVectorFieldLinearization_apply
    {k p : ℕ} (hgap : p + 8 ≤ k)
    (u v x y : Fin p) (D : Matrix (Fin p) (Fin p) ℝ)
    (E : Matrix (Fin k) (Fin p) ℝ)
    (a : Fin k) (i : Fin p) :
    Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        inverseWishartDoubleEntryTest u v x y R *
          steinVectorFieldLinearization R D E a i)
      (halfGaussianMatrix k p) := by
  have hfirstTerm (r s : Fin p) : Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        inverseWishartDoubleEntryTest u v x y R *
          (E a r * ((realWishartGram R)⁻¹ r s * D s i)))
      (halfGaussianMatrix k p) := by
    let indices : Fin 3 → Fin p × Fin p :=
      ![(u, v), (x, y), (r, s)]
    have hbase := integrable_inverseWishartEntryProduct_halfGaussianMatrix
      (k := k) (p := p) (q := 3) (by omega) indices
    have hscaled := (hbase.mul_const (E a r)).mul_const (D s i)
    simpa [indices, inverseWishartDoubleEntryTest,
      inverseWishartEntryProduct, Fin.prod_univ_three,
      mul_assoc, mul_comm, mul_left_comm] using hscaled
  have hfirstSum := integrable_finsetSum (Finset.univ : Finset (Fin p))
    (fun r _ ↦ integrable_finsetSum (Finset.univ : Finset (Fin p))
      (fun s _ ↦ hfirstTerm r s))
  have hfirst : Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        inverseWishartDoubleEntryTest u v x y R *
          (E * ((realWishartGram R)⁻¹ * D)) a i)
      (halfGaussianMatrix k p) := by
    apply hfirstSum.congr
    filter_upwards [] with R
    simp only [inverseWishartDoubleEntryTest, Matrix.mul_apply]
    simp only [Finset.mul_sum, Finset.sum_mul]

  have hsecondTerm (b : Fin k) (r q s t : Fin p) : Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        inverseWishartDoubleEntryTest u v x y R *
          ((R a q * (realWishartGram R)⁻¹ q r * E b r) *
            (R b s * (realWishartGram R)⁻¹ s t * D t i)))
      (halfGaussianMatrix k p) := by
    let indices : Fin 4 → Fin p × Fin p :=
      ![(u, v), (x, y), (q, r), (s, t)]
    have hbase :=
      integrable_two_matrixCoordinates_mul_inverseWishartEntryProduct_halfGaussianMatrix
        (q := 4) (by norm_num) (by omega) a b q s indices
    have hscaled := (hbase.mul_const (E b r)).mul_const (D t i)
    simpa [indices, inverseWishartDoubleEntryTest,
      inverseWishartEntryProduct, Fin.prod_univ_four,
      mul_assoc, mul_comm, mul_left_comm] using hscaled
  have hsecondSum := integrable_finsetSum (Finset.univ : Finset (Fin k))
    (fun b _ ↦ integrable_finsetSum (Finset.univ : Finset (Fin p))
      (fun t _ ↦ integrable_finsetSum (Finset.univ : Finset (Fin p))
        (fun s _ ↦ integrable_finsetSum (Finset.univ : Finset (Fin p))
          (fun r _ ↦ integrable_finsetSum (Finset.univ : Finset (Fin p))
            (fun q _ ↦ hsecondTerm b r q s t)))))
  have hsecond : Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        inverseWishartDoubleEntryTest u v x y R *
          (((R * (realWishartGram R)⁻¹) * E.transpose) *
            (R * (realWishartGram R)⁻¹ * D)) a i)
      (halfGaussianMatrix k p) := by
    apply hsecondSum.congr
    filter_upwards [] with R
    simp only [inverseWishartDoubleEntryTest, Matrix.mul_apply,
      Matrix.transpose_apply]
    simp only [Finset.mul_sum, Finset.sum_mul]

  have hthirdTerm (t : Fin p) (b : Fin k) (r q s : Fin p) : Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        inverseWishartDoubleEntryTest u v x y R *
          ((R a q * (realWishartGram R)⁻¹ q r * R b r * E b t) *
            ((realWishartGram R)⁻¹ t s * D s i)))
      (halfGaussianMatrix k p) := by
    let indices : Fin 4 → Fin p × Fin p :=
      ![(u, v), (x, y), (q, r), (t, s)]
    have hbase :=
      integrable_two_matrixCoordinates_mul_inverseWishartEntryProduct_halfGaussianMatrix
        (q := 4) (by norm_num) (by omega) a b q r indices
    have hscaled := (hbase.mul_const (E b t)).mul_const (D s i)
    simpa [indices, inverseWishartDoubleEntryTest,
      inverseWishartEntryProduct, Fin.prod_univ_four,
      mul_assoc, mul_comm, mul_left_comm] using hscaled
  have hthirdSum := integrable_finsetSum (Finset.univ : Finset (Fin p))
    (fun t _ ↦ integrable_finsetSum (Finset.univ : Finset (Fin p))
      (fun s _ ↦ integrable_finsetSum (Finset.univ : Finset (Fin k))
        (fun b _ ↦ integrable_finsetSum (Finset.univ : Finset (Fin p))
          (fun r _ ↦ integrable_finsetSum (Finset.univ : Finset (Fin p))
            (fun q _ ↦ hthirdTerm t b r q s)))))
  have hthird : Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        inverseWishartDoubleEntryTest u v x y R *
          ((((R * (realWishartGram R)⁻¹) * R.transpose) * E) *
            ((realWishartGram R)⁻¹ * D)) a i)
      (halfGaussianMatrix k p) := by
    apply hthirdSum.congr
    filter_upwards [] with R
    simp only [inverseWishartDoubleEntryTest, Matrix.mul_apply,
      Matrix.transpose_apply]
    simp only [Finset.mul_sum, Finset.sum_mul]

  have hcombined := ((hfirst.sub hsecond).sub hthird).const_mul (1 / 2 : ℝ)
  apply hcombined.congr
  filter_upwards [] with R
  simp only [steinVectorFieldLinearization,
    Matrix.smul_apply, smul_eq_mul, Pi.sub_apply, Matrix.sub_apply]
  ring

/-- The derivative-defined double-entry test times a Stein coordinate is
integrable. -/
theorem integrable_inverseWishartDoubleEntryTestDerivative_mul_steinVectorFieldValue_apply
    {k p : ℕ} (hgap : p + 8 ≤ k)
    (u v x y : Fin p) (E : Matrix (Fin k) (Fin p) ℝ)
    (D : Matrix (Fin p) (Fin p) ℝ)
    (a : Fin k) (i : Fin p) :
    Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        inverseWishartDoubleEntryTestDerivative u v x y R E *
          steinVectorFieldValue R D a i)
      (halfGaussianMatrix k p) := by
  have h1 :=
    integrable_inverseWishartEntryExplicitDerivative_mul_oneEntry_mul_steinValue
      hgap u v x y E D a i
  have h2 :=
    integrable_inverseWishartEntryExplicitDerivative_mul_oneEntry_mul_steinValue
      hgap x y u v E D a i
  have hexplicit := h1.add h2
  apply hexplicit.congr
  filter_upwards [
    ae_isUnit_det_realWishartGram_halfGaussianMatrix k p (by omega)]
      with R hR
  simp only [Pi.add_apply]
  rw [inverseWishartDoubleEntryTestDerivative_apply u v x y R E hR]
  ring

/-- Matrix-law integrability of the complete product-rule derivative of a
double-entry weighted Stein coordinate. -/
theorem integrable_inverseWishartDoubleEntryWeightedSteinComponentDerivative_halfGaussianMatrix
    {k p : ℕ} (hgap : p + 8 ≤ k)
    (u v x y : Fin p) (D : Matrix (Fin p) (Fin p) ℝ)
    (E : Matrix (Fin k) (Fin p) ℝ)
    (a : Fin k) (i : Fin p) :
    Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        inverseWishartDoubleEntryTestDerivative u v x y R E *
            steinVectorFieldValue R D a i +
          inverseWishartDoubleEntryTest u v x y R *
            steinVectorFieldLinearization R D E a i)
      (halfGaussianMatrix k p) :=
  (integrable_inverseWishartDoubleEntryTestDerivative_mul_steinVectorFieldValue_apply
      hgap u v x y E D a i).add
    (integrable_inverseWishartDoubleEntryTest_mul_steinVectorFieldLinearization_apply
      hgap u v x y D E a i)

/-- Exact flattened coordinate families for the double-entry test. -/
structure HalfGaussianInverseWishartDoubleEntrySteinFamilies
    {k p n : ℕ} (hdim : n + 1 = k * p)
    (u v x y : Fin p) (D : Matrix (Fin p) (Fin p) ℝ) : Prop where
  value : ∀ i, Integrable
    (flattenedWeightedSteinComponent hdim
      (inverseWishartDoubleEntryTest u v x y) D i)
    (halfGaussianPi (n + 1))
  derivative : ∀ i, Integrable
    (flattenedWeightedSteinComponentDerivative hdim
      (inverseWishartDoubleEntryTest u v x y)
      (inverseWishartDoubleEntryTestDerivative u v x y) D i)
    (halfGaussianPi (n + 1))
  radial : ∀ i, Integrable
    (fun q ↦ 2 * q i * flattenedWeightedSteinComponent hdim
      (inverseWishartDoubleEntryTest u v x y) D i q)
    (halfGaussianPi (n + 1))

/-- The exact matrix-law estimates discharge every flattened family. -/
theorem halfGaussianInverseWishartDoubleEntrySteinFamilies
    {k p n : ℕ} (hdim : n + 1 = k * p) (hgap : p + 8 ≤ k)
    (u v x y : Fin p) (D : Matrix (Fin p) (Fin p) ℝ) :
    HalfGaussianInverseWishartDoubleEntrySteinFamilies
      hdim u v x y D := by
  let e := flatSuccMatrixMeasurableEquiv hdim
  have hmp : MeasurePreserving e (halfGaussianPi (n + 1))
      (halfGaussianMatrix k p) :=
    measurePreserving_flatSuccMatrixMeasurableEquiv hdim
  refine ⟨?_, ?_, ?_⟩
  · intro q
    let a := flatCoordinateRow hdim q
    let i := flatCoordinateColumn hdim q
    have hm :=
      integrable_inverseWishartDoubleEntryTest_mul_steinVectorFieldValue_apply
        (by omega) u v x y D a i
    have hf := hmp.integrable_comp_of_integrable hm
    exact hf.congr (Filter.Eventually.of_forall fun q ↦ by rfl)
  · intro q
    let E := flatCoordinateMatrixUnit hdim q
    let a := flatCoordinateRow hdim q
    let i := flatCoordinateColumn hdim q
    have hm :=
      integrable_inverseWishartDoubleEntryWeightedSteinComponentDerivative_halfGaussianMatrix
        hgap u v x y D E a i
    have hf := hmp.integrable_comp_of_integrable hm
    exact hf.congr (Filter.Eventually.of_forall fun q ↦ by rfl)
  · intro q
    let a := flatCoordinateRow hdim q
    let i := flatCoordinateColumn hdim q
    have hm :=
      integrable_inverseWishartDoubleEntryTest_mul_steinVectorFieldValue_radial
        (by omega) u v x y D a i
    have hf := hmp.integrable_comp_of_integrable hm
    exact hf.congr (Filter.Eventually.of_forall fun qv ↦ by
      change 2 * (flatSuccMatrixMeasurableEquiv hdim qv) a i *
          (inverseWishartDoubleEntryTest u v x y
              (flatSuccMatrixMeasurableEquiv hdim qv) *
            steinVectorFieldValue
              (flatSuccMatrixMeasurableEquiv hdim qv) D a i) =
        2 * qv q *
          (inverseWishartDoubleEntryTest u v x y
              (flatSuccMatrixMeasurableEquiv hdim qv) *
            steinVectorFieldValue
              (flatSuccMatrixMeasurableEquiv hdim qv) D a i)
      rw [show (flatSuccMatrixMeasurableEquiv hdim qv) a i = qv q by
        simpa [a, i] using
          flatSuccMatrix_apply_flatCoordinatePair hdim qv q])

/-- Stein--Haff for a double-entry test, reduced only to its literal
coordinate-family package. -/
theorem halfGaussian_inverseWishart_doubleEntry_steinHaff_of_families
    {k p n : ℕ} (hdim : n + 1 = k * p) (hp : p < k)
    (hgap : p + 6 ≤ k) (u v x y : Fin p)
    (D : Matrix (Fin p) (Fin p) ℝ) (hD : D.IsSymm)
    (H : HalfGaussianInverseWishartDoubleEntrySteinFamilies
      hdim u v x y D) :
    Integrable
        (fun R : Matrix (Fin k) (Fin p) ℝ ↦
          inverseWishartDoubleEntryTest u v x y R *
            (inverseGramScoreCoefficient (Fin k) (Fin p) *
              Matrix.trace ((realWishartGram R)⁻¹ * D)))
        (halfGaussianMatrix k p) ∧
      Integrable
        (fun R : Matrix (Fin k) (Fin p) ℝ ↦
          inverseWishartDoubleEntryTest u v x y R * Matrix.trace D -
            (-(((realWishartGram R)⁻¹ * D *
                (realWishartGram R)⁻¹) u v) *
                (realWishartGram R)⁻¹ x y -
              (realWishartGram R)⁻¹ u v *
                (((realWishartGram R)⁻¹ * D *
                  (realWishartGram R)⁻¹) x y)))
        (halfGaussianMatrix k p) ∧
      ((∫ R, inverseWishartDoubleEntryTest u v x y R *
            (inverseGramScoreCoefficient (Fin k) (Fin p) *
              Matrix.trace ((realWishartGram R)⁻¹ * D))
          ∂halfGaussianMatrix k p) =
        ∫ R, inverseWishartDoubleEntryTest u v x y R * Matrix.trace D -
            (-(((realWishartGram R)⁻¹ * D *
                (realWishartGram R)⁻¹) u v) *
                (realWishartGram R)⁻¹ x y -
              (realWishartGram R)⁻¹ u v *
                (((realWishartGram R)⁻¹ * D *
                  (realWishartGram R)⁻¹) x y))
          ∂halfGaussianMatrix k p) := by
  have h :=
    steinHaff_halfGaussianMatrix_of_nonsingular_fderiv_and_flattenedSteinFamilies
      hdim hp
      (inverseWishartDoubleEntryTest u v x y)
      (inverseWishartDoubleEntryTestDerivative u v x y) D
      (fun R ↦
        -(((realWishartGram R)⁻¹ * D * (realWishartGram R)⁻¹) u v) *
            (realWishartGram R)⁻¹ x y -
          (realWishartGram R)⁻¹ u v *
            (((realWishartGram R)⁻¹ * D *
              (realWishartGram R)⁻¹) x y))
      (fun R hR ↦
        hasFDerivAt_inverseWishartDoubleEntryTest u v x y R hR)
      (fun R hR ↦
        inverseWishartDoubleEntryTestDerivative_steinVectorFieldValue
          u v x y R D hD hR)
      (integrable_inverseWishartDoubleEntrySteinDerivativeValue
        hgap u v x y D)
      H.value H.derivative H.radial
  simpa only using h

/-- Unconditional double-entry Stein--Haff identity at the exact order-four
coordinate-family threshold. -/
theorem halfGaussian_inverseWishart_doubleEntry_steinHaff
    {k p n : ℕ} (hdim : n + 1 = k * p) (hgap : p + 8 ≤ k)
    (u v x y : Fin p) (D : Matrix (Fin p) (Fin p) ℝ)
    (hD : D.IsSymm) :
    Integrable
        (fun R : Matrix (Fin k) (Fin p) ℝ ↦
          inverseWishartDoubleEntryTest u v x y R *
            (inverseGramScoreCoefficient (Fin k) (Fin p) *
              Matrix.trace ((realWishartGram R)⁻¹ * D)))
        (halfGaussianMatrix k p) ∧
      Integrable
        (fun R : Matrix (Fin k) (Fin p) ℝ ↦
          inverseWishartDoubleEntryTest u v x y R * Matrix.trace D -
            (-(((realWishartGram R)⁻¹ * D *
                (realWishartGram R)⁻¹) u v) *
                (realWishartGram R)⁻¹ x y -
              (realWishartGram R)⁻¹ u v *
                (((realWishartGram R)⁻¹ * D *
                  (realWishartGram R)⁻¹) x y)))
        (halfGaussianMatrix k p) ∧
      ((∫ R, inverseWishartDoubleEntryTest u v x y R *
            (inverseGramScoreCoefficient (Fin k) (Fin p) *
              Matrix.trace ((realWishartGram R)⁻¹ * D))
          ∂halfGaussianMatrix k p) =
        ∫ R, inverseWishartDoubleEntryTest u v x y R * Matrix.trace D -
            (-(((realWishartGram R)⁻¹ * D *
                (realWishartGram R)⁻¹) u v) *
                (realWishartGram R)⁻¹ x y -
              (realWishartGram R)⁻¹ u v *
                (((realWishartGram R)⁻¹ * D *
                  (realWishartGram R)⁻¹) x y))
          ∂halfGaussianMatrix k p) :=
  halfGaussian_inverseWishart_doubleEntry_steinHaff_of_families
    hdim (by omega) (by omega) u v x y D hD
      (halfGaussianInverseWishartDoubleEntrySteinFamilies
        hdim hgap u v x y D)

/-! ## Exact third-entry inverse-Wishart recursion -/

/-- The integral of two prescribed inverse-Gram entries. -/
def halfGaussianInverseWishartDoubleEntryIntegral
    (k p : ℕ) (u v x y : Fin p) : ℝ :=
  ∫ R : Matrix (Fin k) (Fin p) ℝ,
    (realWishartGram R)⁻¹ u v * (realWishartGram R)⁻¹ x y
    ∂halfGaussianMatrix k p

/-- The integral of three prescribed inverse-Gram entries. -/
def halfGaussianInverseWishartThirdEntryIntegral
    (k p : ℕ) (u v x y i j : Fin p) : ℝ :=
  ∫ R : Matrix (Fin k) (Fin p) ℝ,
    (realWishartGram R)⁻¹ u v * (realWishartGram R)⁻¹ x y *
      (realWishartGram R)⁻¹ i j
    ∂halfGaussianMatrix k p

/-- Raw exact order-three entry recursion from the double-entry Stein test. -/
theorem halfGaussian_inverseWishart_thirdEntry_steinRecursion_raw
    {k p : ℕ} (hgap : p + 8 ≤ k)
    (i j u v x y : Fin p) :
    inverseWishartEntryGap k p *
        halfGaussianInverseWishartThirdEntryIntegral k p u v x y i j =
      ∫ R : Matrix (Fin k) (Fin p) ℝ,
        (realWishartGram R)⁻¹ u v * (realWishartGram R)⁻¹ x y *
            (2 * realKroneckerDelta i j) +
          ((realWishartGram R)⁻¹ u j * (realWishartGram R)⁻¹ i v +
              (realWishartGram R)⁻¹ u i * (realWishartGram R)⁻¹ j v) *
            (realWishartGram R)⁻¹ x y +
          (realWishartGram R)⁻¹ u v *
            ((realWishartGram R)⁻¹ x j * (realWishartGram R)⁻¹ i y +
              (realWishartGram R)⁻¹ x i * (realWishartGram R)⁻¹ j y)
        ∂halfGaussianMatrix k p := by
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
  have hHaff := halfGaussian_inverseWishart_doubleEntry_steinHaff
    hdim hgap u v x y D hD
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
  have hsandwich (a b : Fin p) :
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        ((realWishartGram R)⁻¹ * D * (realWishartGram R)⁻¹) a b) =
      (fun R ↦
        (realWishartGram R)⁻¹ a j * (realWishartGram R)⁻¹ i b +
          (realWishartGram R)⁻¹ a i * (realWishartGram R)⁻¹ j b) := by
    funext R
    simpa only [D] using
      matrix_mul_symmetricSingle_mul_entry (realWishartGram R)⁻¹ i j a b
  rw [hcoeff] at heq
  calc
    inverseWishartEntryGap k p *
        halfGaussianInverseWishartThirdEntryIntegral k p u v x y i j =
      ∫ R : Matrix (Fin k) (Fin p) ℝ,
        inverseWishartDoubleEntryTest u v x y R *
          (c / 2 * (2 * (realWishartGram R)⁻¹ i j))
        ∂halfGaussianMatrix k p := by
      unfold halfGaussianInverseWishartThirdEntryIntegral
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with R
      dsimp only [c, inverseWishartDoubleEntryTest]
      ring
    _ = ∫ R : Matrix (Fin k) (Fin p) ℝ,
        inverseWishartDoubleEntryTest u v x y R *
          (c / 2 * Matrix.trace ((realWishartGram R)⁻¹ * D))
        ∂halfGaussianMatrix k p := by
      apply integral_congr_ae
      filter_upwards [] with R
      rw [congrFun htraceInv R]
    _ = ∫ R : Matrix (Fin k) (Fin p) ℝ,
        inverseWishartDoubleEntryTest u v x y R * Matrix.trace D -
          (-(((realWishartGram R)⁻¹ * D *
              (realWishartGram R)⁻¹) u v) *
              (realWishartGram R)⁻¹ x y -
            (realWishartGram R)⁻¹ u v *
              (((realWishartGram R)⁻¹ * D *
                (realWishartGram R)⁻¹) x y))
        ∂halfGaussianMatrix k p := heq
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with R
      rw [htraceD, congrFun (hsandwich u v) R,
        congrFun (hsandwich x y) R]
      simp only [inverseWishartDoubleEntryTest]
      ring

/-- Explicit five-term third-entry recursion, with integral linearity
justified from the inverse-entry moment engine. -/
theorem halfGaussian_inverseWishart_thirdEntry_steinRecursion
    {k p : ℕ} (hgap : p + 8 ≤ k)
    (i j u v x y : Fin p) :
    inverseWishartEntryGap k p *
        halfGaussianInverseWishartThirdEntryIntegral k p u v x y i j =
      2 * realKroneckerDelta i j *
          halfGaussianInverseWishartDoubleEntryIntegral k p u v x y +
        halfGaussianInverseWishartThirdEntryIntegral k p u j i v x y +
        halfGaussianInverseWishartThirdEntryIntegral k p u i j v x y +
        halfGaussianInverseWishartThirdEntryIntegral k p u v x j i y +
        halfGaussianInverseWishartThirdEntryIntegral k p u v x i j y := by
  have hdouble (a b c d : Fin p) : Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        (realWishartGram R)⁻¹ a b * (realWishartGram R)⁻¹ c d)
      (halfGaussianMatrix k p) := by
    let indices : Fin 2 → Fin p × Fin p := ![(a, b), (c, d)]
    have hbase := integrable_inverseWishartEntryProduct_halfGaussianMatrix
      (k := k) (p := p) (q := 2) (by omega) indices
    apply hbase.congr
    filter_upwards [] with R
    simp [indices, inverseWishartEntryProduct, Fin.prod_univ_two]
  have htriple (a b c d e f : Fin p) : Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        (realWishartGram R)⁻¹ a b * (realWishartGram R)⁻¹ c d *
          (realWishartGram R)⁻¹ e f)
      (halfGaussianMatrix k p) := by
    let indices : Fin 3 → Fin p × Fin p := ![(a, b), (c, d), (e, f)]
    have hbase := integrable_inverseWishartEntryProduct_halfGaussianMatrix
      (k := k) (p := p) (q := 3) (by omega) indices
    apply hbase.congr
    filter_upwards [] with R
    simp [indices, inverseWishartEntryProduct, Fin.prod_univ_three]
  have h0 : Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        (realWishartGram R)⁻¹ u v * (realWishartGram R)⁻¹ x y *
          (2 * realKroneckerDelta i j))
      (halfGaussianMatrix k p) :=
    (hdouble u v x y).mul_const (2 * realKroneckerDelta i j)
  have h1 := htriple u j i v x y
  have h2 := htriple u i j v x y
  have h3 := htriple u v x j i y
  have h4 := htriple u v x i j y
  let f0 : Matrix (Fin k) (Fin p) ℝ → ℝ := fun R ↦
    (realWishartGram R)⁻¹ u v * (realWishartGram R)⁻¹ x y *
      (2 * realKroneckerDelta i j)
  let f1 : Matrix (Fin k) (Fin p) ℝ → ℝ := fun R ↦
    (realWishartGram R)⁻¹ u j * (realWishartGram R)⁻¹ i v *
      (realWishartGram R)⁻¹ x y
  let f2 : Matrix (Fin k) (Fin p) ℝ → ℝ := fun R ↦
    (realWishartGram R)⁻¹ u i * (realWishartGram R)⁻¹ j v *
      (realWishartGram R)⁻¹ x y
  let f3 : Matrix (Fin k) (Fin p) ℝ → ℝ := fun R ↦
    (realWishartGram R)⁻¹ u v *
      ((realWishartGram R)⁻¹ x j * (realWishartGram R)⁻¹ i y)
  let f4 : Matrix (Fin k) (Fin p) ℝ → ℝ := fun R ↦
    (realWishartGram R)⁻¹ u v *
      ((realWishartGram R)⁻¹ x i * (realWishartGram R)⁻¹ j y)
  have hi0 : Integrable f0 (halfGaussianMatrix k p) := by
    simpa only [f0] using h0
  have hi1 : Integrable f1 (halfGaussianMatrix k p) := by
    simpa only [f1] using h1
  have hi2 : Integrable f2 (halfGaussianMatrix k p) := by
    simpa only [f2] using h2
  have hi3 : Integrable f3 (halfGaussianMatrix k p) := by
    apply h3.congr
    filter_upwards [] with R
    simp only [f3]
    ring
  have hi4 : Integrable f4 (halfGaussianMatrix k p) := by
    apply h4.congr
    filter_upwards [] with R
    simp only [f4]
    ring
  rw [halfGaussian_inverseWishart_thirdEntry_steinRecursion_raw
    hgap i j u v x y]
  have hsum : Integrable (fun R ↦ f0 R + f1 R + f2 R + f3 R + f4 R)
      (halfGaussianMatrix k p) :=
    (((hi0.add hi1).add hi2).add hi3).add hi4
  calc
    (∫ R : Matrix (Fin k) (Fin p) ℝ,
        (realWishartGram R)⁻¹ u v * (realWishartGram R)⁻¹ x y *
            (2 * realKroneckerDelta i j) +
          ((realWishartGram R)⁻¹ u j * (realWishartGram R)⁻¹ i v +
              (realWishartGram R)⁻¹ u i * (realWishartGram R)⁻¹ j v) *
            (realWishartGram R)⁻¹ x y +
          (realWishartGram R)⁻¹ u v *
            ((realWishartGram R)⁻¹ x j * (realWishartGram R)⁻¹ i y +
              (realWishartGram R)⁻¹ x i * (realWishartGram R)⁻¹ j y)
        ∂halfGaussianMatrix k p) =
      ∫ R : Matrix (Fin k) (Fin p) ℝ,
        f0 R + f1 R + f2 R + f3 R + f4 R
        ∂halfGaussianMatrix k p := by
      apply integral_congr_ae
      filter_upwards [] with R
      dsimp only [f0, f1, f2, f3, f4]
      ring
    _ = (∫ R, f0 R ∂halfGaussianMatrix k p) +
          (∫ R, f1 R ∂halfGaussianMatrix k p) +
          (∫ R, f2 R ∂halfGaussianMatrix k p) +
          (∫ R, f3 R ∂halfGaussianMatrix k p) +
          (∫ R, f4 R ∂halfGaussianMatrix k p) := by
      have h01 := integral_add hi0 hi1
      have h012 := integral_add (hi0.add hi1) hi2
      have h0123 := integral_add ((hi0.add hi1).add hi2) hi3
      have h01234 := integral_add (((hi0.add hi1).add hi2).add hi3) hi4
      simp only [Pi.add_apply] at h012 h0123 h01234
      calc
        (∫ R, f0 R + f1 R + f2 R + f3 R + f4 R
            ∂halfGaussianMatrix k p) =
            (∫ R, f0 R + f1 R + f2 R + f3 R
              ∂halfGaussianMatrix k p) +
            ∫ R, f4 R ∂halfGaussianMatrix k p := by
              simpa only [Pi.add_apply] using h01234
        _ = ((∫ R, f0 R + f1 R + f2 R ∂halfGaussianMatrix k p) +
              ∫ R, f3 R ∂halfGaussianMatrix k p) +
            ∫ R, f4 R ∂halfGaussianMatrix k p := by rw [h0123]
        _ = (((∫ R, f0 R + f1 R ∂halfGaussianMatrix k p) +
              ∫ R, f2 R ∂halfGaussianMatrix k p) +
              ∫ R, f3 R ∂halfGaussianMatrix k p) +
            ∫ R, f4 R ∂halfGaussianMatrix k p := by rw [h012]
        _ = _ := by rw [h01]
    _ = _ := by
      unfold halfGaussianInverseWishartDoubleEntryIntegral
      unfold halfGaussianInverseWishartThirdEntryIntegral
      dsimp only [f0, f1, f2, f3, f4]
      rw [integral_mul_const]
      ring

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08
