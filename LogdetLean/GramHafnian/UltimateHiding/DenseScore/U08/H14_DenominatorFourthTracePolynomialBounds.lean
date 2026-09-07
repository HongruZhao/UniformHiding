import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.InverseWishartSecondEntryStein
import Mathlib.Tactic

/-!
# Denominator-only fourth trace-polynomial bounds for H14

This module works only with the real Gaussian denominator matrix.  It does
not use the finite numerator Wick producer, H6, or any H3--H18 endpoint.

The analytic engine below applies the already checked nonsingular
Stein--Haff closure to a product of three inverse-Gram entries.  Its fourth
entry recursion is the reusable order-four producer.  The final section
contracts that recursion into the five trace partitions and proves the two
dense polynomial bounds requested by
`H14DenominatorFourthTracePolynomialBounds`.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.Elementwise

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08

noncomputable section

open LogdetLean.GramHafnian
open LogdetLean.GramHafnian.Wishart
open LogdetLean.GramHafnian.UltimateHiding.DenseScore

set_option maxHeartbeats 3600000

/-! ## Triple-entry differential calculus -/

/-- Product of three prescribed inverse-Gram entries. -/
def inverseWishartTripleEntryTest {k p : ℕ}
    (a b c d e f : Fin p)
    (R : Matrix (Fin k) (Fin p) ℝ) : ℝ :=
  (realWishartGram R)⁻¹ a b *
    (realWishartGram R)⁻¹ c d *
      (realWishartGram R)⁻¹ e f

/-- Its canonical Frechet derivative. -/
def inverseWishartTripleEntryTestDerivative {k p : ℕ}
    (a b c d e f : Fin p)
    (R : Matrix (Fin k) (Fin p) ℝ) :
    Matrix (Fin k) (Fin p) ℝ →L[ℝ] ℝ :=
  fderiv ℝ (inverseWishartTripleEntryTest a b c d e f) R

/-- The triple product is Frechet differentiable on the full-rank locus. -/
theorem hasFDerivAt_inverseWishartTripleEntryTest
    {k p : ℕ} (a b c d e f : Fin p)
    (R : Matrix (Fin k) (Fin p) ℝ)
    (hfull : IsUnit (realWishartGram R).det) :
    HasFDerivAt (inverseWishartTripleEntryTest a b c d e f)
      (inverseWishartTripleEntryTestDerivative a b c d e f R) R := by
  have h1 := hasFDerivAt_inverseWishartEntryTest a b R hfull
  have h2 := hasFDerivAt_inverseWishartEntryTest c d R hfull
  have h3 := hasFDerivAt_inverseWishartEntryTest e f R hfull
  exact ((h1.mul h2).mul h3).differentiableAt.hasFDerivAt

/-- Explicit product-rule derivative in a lifted symmetric Gram direction. -/
theorem inverseWishartTripleEntryTestDerivative_steinVectorFieldValue
    {k p : ℕ} (a b c d e f : Fin p)
    (R : Matrix (Fin k) (Fin p) ℝ)
    (D : Matrix (Fin p) (Fin p) ℝ) (hD : D.IsSymm)
    (hfull : IsUnit (realWishartGram R).det) :
    inverseWishartTripleEntryTestDerivative a b c d e f R
        (steinVectorFieldValue R D) =
      -(((realWishartGram R)⁻¹ * D * (realWishartGram R)⁻¹) a b) *
          (realWishartGram R)⁻¹ c d * (realWishartGram R)⁻¹ e f -
        (realWishartGram R)⁻¹ a b *
          (((realWishartGram R)⁻¹ * D * (realWishartGram R)⁻¹) c d) *
          (realWishartGram R)⁻¹ e f -
        (realWishartGram R)⁻¹ a b * (realWishartGram R)⁻¹ c d *
          (((realWishartGram R)⁻¹ * D * (realWishartGram R)⁻¹) e f) := by
  let V := steinVectorFieldValue R D
  have hlocal :=
    (hasFDerivAt_inverseWishartTripleEntryTest a b c d e f R hfull).hasLineDerivAt V
  have h1 :=
    (hasFDerivAt_inverseWishartEntryTest a b R hfull).hasLineDerivAt V
  have h2 :=
    (hasFDerivAt_inverseWishartEntryTest c d R hfull).hasLineDerivAt V
  have h3 :=
    (hasFDerivAt_inverseWishartEntryTest e f R hfull).hasLineDerivAt V
  have hprod := (h1.mul h2).mul h3
  have heq := hlocal.unique hprod
  dsimp only [V] at heq
  simp only [zero_smul, add_zero, Pi.mul_apply] at heq
  have hv1 := inverseWishartEntryTestDerivative_steinVectorFieldValue
    a b R D hD hfull
  have hv2 := inverseWishartEntryTestDerivative_steinVectorFieldValue
    c d R D hD hfull
  have hv3 := inverseWishartEntryTestDerivative_steinVectorFieldValue
    e f R D hD hfull
  have halg {x y z : ℝ}
      (hx : x = -(((realWishartGram R)⁻¹ * D *
        (realWishartGram R)⁻¹) a b))
      (hy : y = -(((realWishartGram R)⁻¹ * D *
        (realWishartGram R)⁻¹) c d))
      (hz : z = -(((realWishartGram R)⁻¹ * D *
        (realWishartGram R)⁻¹) e f)) :
      ((x * inverseWishartEntryTest c d R +
            inverseWishartEntryTest a b R * y) *
          inverseWishartEntryTest e f R +
        inverseWishartEntryTest a b R * inverseWishartEntryTest c d R * z) =
        -(((realWishartGram R)⁻¹ * D * (realWishartGram R)⁻¹) a b) *
            (realWishartGram R)⁻¹ c d * (realWishartGram R)⁻¹ e f -
          (realWishartGram R)⁻¹ a b *
            (((realWishartGram R)⁻¹ * D * (realWishartGram R)⁻¹) c d) *
            (realWishartGram R)⁻¹ e f -
          (realWishartGram R)⁻¹ a b * (realWishartGram R)⁻¹ c d *
            (((realWishartGram R)⁻¹ * D * (realWishartGram R)⁻¹) e f) := by
    rw [hx, hy, hz]
    simp only [inverseWishartEntryTest]
    ring
  exact heq.trans (halg hv1 hv2 hv3)

/-- Full product-rule formula in an arbitrary rectangular direction. -/
theorem inverseWishartTripleEntryTestDerivative_apply
    {k p : ℕ} (a b c d e f : Fin p)
    (R E : Matrix (Fin k) (Fin p) ℝ)
    (hfull : IsUnit (realWishartGram R).det) :
    inverseWishartTripleEntryTestDerivative a b c d e f R E =
      (-((realWishartGram R)⁻¹ *
          (E.transpose * R + R.transpose * E) *
          (realWishartGram R)⁻¹)) a b *
          (realWishartGram R)⁻¹ c d * (realWishartGram R)⁻¹ e f +
        (realWishartGram R)⁻¹ a b *
          (-((realWishartGram R)⁻¹ *
            (E.transpose * R + R.transpose * E) *
            (realWishartGram R)⁻¹)) c d *
          (realWishartGram R)⁻¹ e f +
        (realWishartGram R)⁻¹ a b * (realWishartGram R)⁻¹ c d *
          (-((realWishartGram R)⁻¹ *
            (E.transpose * R + R.transpose * E) *
            (realWishartGram R)⁻¹)) e f := by
  have hlocal :=
    (hasFDerivAt_inverseWishartTripleEntryTest a b c d e f R hfull).hasLineDerivAt E
  have h1 :=
    (hasFDerivAt_inverseWishartEntryTest a b R hfull).hasLineDerivAt E
  have h2 :=
    (hasFDerivAt_inverseWishartEntryTest c d R hfull).hasLineDerivAt E
  have h3 :=
    (hasFDerivAt_inverseWishartEntryTest e f R hfull).hasLineDerivAt E
  have hprod := (h1.mul h2).mul h3
  have heq := hlocal.unique hprod
  simp only [zero_smul, add_zero, Pi.mul_apply] at heq
  have hv1 := h1.unique
    (hasDerivAt_inverse_realWishartGram_entry_matrixLine R E hfull a b)
  have hv2 := h2.unique
    (hasDerivAt_inverse_realWishartGram_entry_matrixLine R E hfull c d)
  have hv3 := h3.unique
    (hasDerivAt_inverse_realWishartGram_entry_matrixLine R E hfull e f)
  have halg {r s t : ℝ}
      (hr : r = (-((realWishartGram R)⁻¹ *
        (E.transpose * R + R.transpose * E) *
        (realWishartGram R)⁻¹)) a b)
      (hs : s = (-((realWishartGram R)⁻¹ *
        (E.transpose * R + R.transpose * E) *
        (realWishartGram R)⁻¹)) c d)
      (ht : t = (-((realWishartGram R)⁻¹ *
        (E.transpose * R + R.transpose * E) *
        (realWishartGram R)⁻¹)) e f) :
      ((r * inverseWishartEntryTest c d R +
            inverseWishartEntryTest a b R * s) *
          inverseWishartEntryTest e f R +
        inverseWishartEntryTest a b R * inverseWishartEntryTest c d R * t) =
        (-((realWishartGram R)⁻¹ *
            (E.transpose * R + R.transpose * E) *
            (realWishartGram R)⁻¹)) a b *
            (realWishartGram R)⁻¹ c d * (realWishartGram R)⁻¹ e f +
          (realWishartGram R)⁻¹ a b *
            (-((realWishartGram R)⁻¹ *
              (E.transpose * R + R.transpose * E) *
              (realWishartGram R)⁻¹)) c d *
            (realWishartGram R)⁻¹ e f +
          (realWishartGram R)⁻¹ a b * (realWishartGram R)⁻¹ c d *
            (-((realWishartGram R)⁻¹ *
              (E.transpose * R + R.transpose * E) *
              (realWishartGram R)⁻¹)) e f := by
    rw [hr, hs, ht]
    simp only [inverseWishartEntryTest]
    ring
  exact heq.trans (halg hv1 hv2 hv3)

/-! ## Matrix-law integrability for the triple-entry Stein test -/

/-- The explicit Stein-direction derivative of a triple entry product is
integrable once fourth inverse-entry products exist. -/
theorem integrable_inverseWishartTripleEntrySteinDerivativeValue
    {k p : ℕ} (hgap : p + 8 ≤ k)
    (a b c d e f : Fin p) (D : Matrix (Fin p) (Fin p) ℝ) :
    Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        -(((realWishartGram R)⁻¹ * D * (realWishartGram R)⁻¹) a b) *
            (realWishartGram R)⁻¹ c d * (realWishartGram R)⁻¹ e f -
          (realWishartGram R)⁻¹ a b *
            (((realWishartGram R)⁻¹ * D * (realWishartGram R)⁻¹) c d) *
            (realWishartGram R)⁻¹ e f -
          (realWishartGram R)⁻¹ a b * (realWishartGram R)⁻¹ c d *
            (((realWishartGram R)⁻¹ * D * (realWishartGram R)⁻¹) e f))
      (halfGaussianMatrix k p) := by
  have hterm (u v x y z w : Fin p) : Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        (((realWishartGram R)⁻¹ * D * (realWishartGram R)⁻¹) u v) *
          (realWishartGram R)⁻¹ x y * (realWishartGram R)⁻¹ z w)
      (halfGaussianMatrix k p) := by
    have hmonomial (i j : Fin p) : Integrable
        (fun R : Matrix (Fin k) (Fin p) ℝ ↦
          (realWishartGram R)⁻¹ u i * D i j *
            (realWishartGram R)⁻¹ j v *
              (realWishartGram R)⁻¹ x y *
                (realWishartGram R)⁻¹ z w)
        (halfGaussianMatrix k p) := by
      let indices : Fin 4 → Fin p × Fin p :=
        ![(u, i), (j, v), (x, y), (z, w)]
      have hbase := integrable_inverseWishartEntryProduct_halfGaussianMatrix
        (k := k) (p := p) (q := 4) (by omega) indices
      have hscaled := hbase.mul_const (D i j)
      simpa [indices, inverseWishartEntryProduct, Fin.prod_univ_four,
        mul_assoc, mul_comm, mul_left_comm] using hscaled
    have hsum := integrable_finsetSum (Finset.univ : Finset (Fin p))
      (fun i _ ↦ integrable_finsetSum (Finset.univ : Finset (Fin p))
        (fun j _ ↦ hmonomial i j))
    apply hsum.congr
    filter_upwards [] with R
    simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
  have h := (((hterm a b c d e f).neg.sub (hterm c d a b e f)).sub
    (hterm e f a b c d))
  apply h.congr
  filter_upwards [] with R
  simp only [Pi.sub_apply, Pi.neg_apply]
  ring

/-- Value component of the triple-entry weighted Stein field. -/
theorem integrable_inverseWishartTripleEntryTest_mul_steinVectorFieldValue_apply
    {k p : ℕ} (hgap : p + 8 ≤ k)
    (u v x y z w : Fin p) (D : Matrix (Fin p) (Fin p) ℝ)
    (a : Fin k) (i : Fin p) :
    Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        inverseWishartTripleEntryTest u v x y z w R *
          steinVectorFieldValue R D a i)
      (halfGaussianMatrix k p) := by
  have hterm (s t : Fin p) : Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        (1 / 2 : ℝ) *
          (R a s *
            ((realWishartGram R)⁻¹ u v *
              (realWishartGram R)⁻¹ x y *
              (realWishartGram R)⁻¹ z w *
              (realWishartGram R)⁻¹ s t)) * D t i)
      (halfGaussianMatrix k p) := by
    let indices : Fin 4 → Fin p × Fin p :=
      ![(u, v), (x, y), (z, w), (s, t)]
    have hbase :=
      integrable_matrixCoordinate_mul_inverseWishartEntryProduct_halfGaussianMatrix
        (q := 4) (by norm_num) (by omega) a s indices
    have hscaled := (hbase.mul_const (D t i)).const_mul (1 / 2 : ℝ)
    simpa [indices, inverseWishartEntryProduct, Fin.prod_univ_four,
      mul_assoc, mul_comm, mul_left_comm] using hscaled
  have hsum := integrable_finsetSum (Finset.univ : Finset (Fin p))
    (fun s _ ↦ integrable_finsetSum (Finset.univ : Finset (Fin p))
      (fun t _ ↦ hterm s t))
  apply hsum.congr
  filter_upwards [] with R
  simp only [inverseWishartTripleEntryTest, steinVectorFieldValue,
    Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  ring

/-- Radial value component; only two Gaussian coordinates and four inverse
entries occur. -/
theorem integrable_inverseWishartTripleEntryTest_mul_steinVectorFieldValue_radial
    {k p : ℕ} (hgap : p + 8 ≤ k)
    (u v x y z w : Fin p) (D : Matrix (Fin p) (Fin p) ℝ)
    (a : Fin k) (i : Fin p) :
    Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        2 * R a i *
          (inverseWishartTripleEntryTest u v x y z w R *
            steinVectorFieldValue R D a i))
      (halfGaussianMatrix k p) := by
  have hterm (s t : Fin p) : Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        R a i * R a s *
          ((realWishartGram R)⁻¹ u v *
            (realWishartGram R)⁻¹ x y *
            (realWishartGram R)⁻¹ z w *
            (realWishartGram R)⁻¹ s t) * D t i)
      (halfGaussianMatrix k p) := by
    let indices : Fin 4 → Fin p × Fin p :=
      ![(u, v), (x, y), (z, w), (s, t)]
    have hbase :=
      integrable_two_matrixCoordinates_mul_inverseWishartEntryProduct_halfGaussianMatrix
        (q := 4) (by norm_num) (by omega) a a i s indices
    have hscaled := hbase.mul_const (D t i)
    simpa [indices, inverseWishartEntryProduct, Fin.prod_univ_four,
      mul_assoc, mul_comm, mul_left_comm] using hscaled
  have hsum := integrable_finsetSum (Finset.univ : Finset (Fin p))
    (fun s _ ↦ integrable_finsetSum (Finset.univ : Finset (Fin p))
      (fun t _ ↦ hterm s t))
  apply hsum.congr
  filter_upwards [] with R
  simp only [inverseWishartTripleEntryTest, steinVectorFieldValue,
    Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  ring

private theorem neg_half_sum_five_product_factor
    {I J S R W : Type*}
    [Fintype I] [Fintype J] [Fintype S] [Fintype R] [Fintype W]
    (F : S → R → W → ℝ) (T : I → J → ℝ) (x z : ℝ) :
    -(1 / 2 : ℝ) *
        (∑ i : I, ∑ j : J, ∑ s : S, ∑ r : R, ∑ w : W,
          F s r w * x * z * T i j) =
      (-(∑ s : S, ∑ r : R, ∑ w : W, F s r w)) *
        x * z * ((1 / 2 : ℝ) * ∑ i : I, ∑ j : J, T i j) := by
  classical
  let C : ℝ := (∑ s : S, ∑ r : R, ∑ w : W, F s r w) * x * z
  have hfactor (i : I) (j : J) :
      (∑ s : S, ∑ r : R, ∑ w : W, F s r w * x * z * T i j) =
        T i j * C := by
    calc
      (∑ s : S, ∑ r : R, ∑ w : W, F s r w * x * z * T i j) =
          ∑ s : S, ∑ r : R, ∑ w : W, F s r w * (x * z * T i j) := by
            apply Finset.sum_congr rfl
            intro s _
            apply Finset.sum_congr rfl
            intro r _
            apply Finset.sum_congr rfl
            intro w _
            ring
      _ = ∑ s : S, ∑ r : R, (∑ w : W, F s r w) * (x * z * T i j) := by
        apply Finset.sum_congr rfl
        intro s _
        apply Finset.sum_congr rfl
        intro r _
        exact (Finset.sum_mul Finset.univ (fun w : W ↦ F s r w)
          (x * z * T i j)).symm
      _ = ∑ s : S, (∑ r : R, ∑ w : W, F s r w) * (x * z * T i j) := by
        apply Finset.sum_congr rfl
        intro s _
        exact (Finset.sum_mul Finset.univ
          (fun r : R ↦ ∑ w : W, F s r w) (x * z * T i j)).symm
      _ = (∑ s : S, ∑ r : R, ∑ w : W, F s r w) * (x * z * T i j) :=
        (Finset.sum_mul Finset.univ
          (fun s : S ↦ ∑ r : R, ∑ w : W, F s r w) (x * z * T i j)).symm
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

/-- One explicit inverse-entry derivative, two additional inverse entries,
and a Stein-field coordinate are integrable in the dense order-five range. -/
theorem integrable_inverseWishartEntryExplicitDerivative_mul_twoEntries_mul_steinValue
    {k p : ℕ} (hgap : p + 10 ≤ k)
    (u v x y z w : Fin p) (E : Matrix (Fin k) (Fin p) ℝ)
    (D : Matrix (Fin p) (Fin p) ℝ)
    (a : Fin k) (i : Fin p) :
    Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        (-((realWishartGram R)⁻¹ *
            (E.transpose * R + R.transpose * E) *
            (realWishartGram R)⁻¹)) u v *
          (realWishartGram R)⁻¹ x y * (realWishartGram R)⁻¹ z w *
          steinVectorFieldValue R D a i)
      (halfGaussianMatrix k p) := by
  have hmonomial (r s : Fin p) (row : Fin k) (t q : Fin p) :
      Integrable
        (fun R : Matrix (Fin k) (Fin p) ℝ ↦
          (((realWishartGram R)⁻¹ u r *
              (E row r * R row s + R row r * E row s) *
              (realWishartGram R)⁻¹ s v) *
            (realWishartGram R)⁻¹ x y * (realWishartGram R)⁻¹ z w) *
            (R a q * (realWishartGram R)⁻¹ q t * D t i))
        (halfGaussianMatrix k p) := by
    let indices : Fin 5 → Fin p × Fin p :=
      ![(u, r), (s, v), (x, y), (z, w), (q, t)]
    have hfirst :=
      integrable_two_matrixCoordinates_mul_inverseWishartEntryProduct_halfGaussianMatrix
        (q := 5) (by norm_num) (by omega) row a s q indices
    have hsecond :=
      integrable_two_matrixCoordinates_mul_inverseWishartEntryProduct_halfGaussianMatrix
        (q := 5) (by norm_num) (by omega) row a r q indices
    have hfirstScaled := (hfirst.mul_const (E row r)).mul_const (D t i)
    have hsecondScaled := (hsecond.mul_const (E row s)).mul_const (D t i)
    apply (hfirstScaled.add hsecondScaled).congr
    filter_upwards [] with R
    simp [indices, inverseWishartEntryProduct, Fin.prod_univ_five]
    ring
  have hsum : Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        -(1 / 2 : ℝ) *
          (∑ t : Fin p, ∑ q : Fin p, ∑ s : Fin p,
            ∑ r : Fin p, ∑ row : Fin k,
              (((realWishartGram R)⁻¹ u r *
                  (E row r * R row s + R row r * E row s) *
                  (realWishartGram R)⁻¹ s v) *
                (realWishartGram R)⁻¹ x y *
                (realWishartGram R)⁻¹ z w) *
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
          ∑ row : Fin k, F s r row * (realWishartGram R)⁻¹ x y *
            (realWishartGram R)⁻¹ z w * T t q) =
      (-(∑ s : Fin p, ∑ r : Fin p, ∑ row : Fin k, F s r row)) *
        (realWishartGram R)⁻¹ x y * (realWishartGram R)⁻¹ z w *
          ((1 / 2 : ℝ) * ∑ t : Fin p, ∑ q : Fin p, T t q)
  exact neg_half_sum_five_product_factor F T
    ((realWishartGram R)⁻¹ x y) ((realWishartGram R)⁻¹ z w)

/-- A triple inverse-entry test times the explicit linearization of the
Stein field is integrable at the order-five threshold. -/
theorem integrable_inverseWishartTripleEntryTest_mul_steinVectorFieldLinearization_apply
    {k p : ℕ} (hgap : p + 10 ≤ k)
    (u v x y z w : Fin p) (D : Matrix (Fin p) (Fin p) ℝ)
    (E : Matrix (Fin k) (Fin p) ℝ)
    (a : Fin k) (i : Fin p) :
    Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        inverseWishartTripleEntryTest u v x y z w R *
          steinVectorFieldLinearization R D E a i)
      (halfGaussianMatrix k p) := by
  have hfirstTerm (r s : Fin p) : Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        inverseWishartTripleEntryTest u v x y z w R *
          (E a r * ((realWishartGram R)⁻¹ r s * D s i)))
      (halfGaussianMatrix k p) := by
    let indices : Fin 4 → Fin p × Fin p :=
      ![(u, v), (x, y), (z, w), (r, s)]
    have hbase := integrable_inverseWishartEntryProduct_halfGaussianMatrix
      (k := k) (p := p) (q := 4) (by omega) indices
    have hscaled := (hbase.mul_const (E a r)).mul_const (D s i)
    simpa [indices, inverseWishartTripleEntryTest,
      inverseWishartEntryProduct, Fin.prod_univ_four,
      mul_assoc, mul_comm, mul_left_comm] using hscaled
  have hfirstSum := integrable_finsetSum (Finset.univ : Finset (Fin p))
    (fun r _ ↦ integrable_finsetSum (Finset.univ : Finset (Fin p))
      (fun s _ ↦ hfirstTerm r s))
  have hfirst : Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        inverseWishartTripleEntryTest u v x y z w R *
          (E * ((realWishartGram R)⁻¹ * D)) a i)
      (halfGaussianMatrix k p) := by
    apply hfirstSum.congr
    filter_upwards [] with R
    simp only [inverseWishartTripleEntryTest, Matrix.mul_apply]
    simp only [Finset.mul_sum, Finset.sum_mul]

  have hsecondTerm (b : Fin k) (r q s t : Fin p) : Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        inverseWishartTripleEntryTest u v x y z w R *
          ((R a q * (realWishartGram R)⁻¹ q r * E b r) *
            (R b s * (realWishartGram R)⁻¹ s t * D t i)))
      (halfGaussianMatrix k p) := by
    let indices : Fin 5 → Fin p × Fin p :=
      ![(u, v), (x, y), (z, w), (q, r), (s, t)]
    have hbase :=
      integrable_two_matrixCoordinates_mul_inverseWishartEntryProduct_halfGaussianMatrix
        (q := 5) (by norm_num) (by omega) a b q s indices
    have hscaled := (hbase.mul_const (E b r)).mul_const (D t i)
    simpa [indices, inverseWishartTripleEntryTest,
      inverseWishartEntryProduct, Fin.prod_univ_five,
      mul_assoc, mul_comm, mul_left_comm] using hscaled
  have hsecondSum := integrable_finsetSum (Finset.univ : Finset (Fin k))
    (fun b _ ↦ integrable_finsetSum (Finset.univ : Finset (Fin p))
      (fun t _ ↦ integrable_finsetSum (Finset.univ : Finset (Fin p))
        (fun s _ ↦ integrable_finsetSum (Finset.univ : Finset (Fin p))
          (fun r _ ↦ integrable_finsetSum (Finset.univ : Finset (Fin p))
            (fun q _ ↦ hsecondTerm b r q s t)))))
  have hsecond : Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        inverseWishartTripleEntryTest u v x y z w R *
          (((R * (realWishartGram R)⁻¹) * E.transpose) *
            (R * (realWishartGram R)⁻¹ * D)) a i)
      (halfGaussianMatrix k p) := by
    apply hsecondSum.congr
    filter_upwards [] with R
    simp only [inverseWishartTripleEntryTest, Matrix.mul_apply,
      Matrix.transpose_apply]
    simp only [Finset.mul_sum, Finset.sum_mul]

  have hthirdTerm (t : Fin p) (b : Fin k) (r q s : Fin p) : Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        inverseWishartTripleEntryTest u v x y z w R *
          ((R a q * (realWishartGram R)⁻¹ q r * R b r * E b t) *
            ((realWishartGram R)⁻¹ t s * D s i)))
      (halfGaussianMatrix k p) := by
    let indices : Fin 5 → Fin p × Fin p :=
      ![(u, v), (x, y), (z, w), (q, r), (t, s)]
    have hbase :=
      integrable_two_matrixCoordinates_mul_inverseWishartEntryProduct_halfGaussianMatrix
        (q := 5) (by norm_num) (by omega) a b q r indices
    have hscaled := (hbase.mul_const (E b t)).mul_const (D s i)
    simpa [indices, inverseWishartTripleEntryTest,
      inverseWishartEntryProduct, Fin.prod_univ_five,
      mul_assoc, mul_comm, mul_left_comm] using hscaled
  have hthirdSum := integrable_finsetSum (Finset.univ : Finset (Fin p))
    (fun t _ ↦ integrable_finsetSum (Finset.univ : Finset (Fin p))
      (fun s _ ↦ integrable_finsetSum (Finset.univ : Finset (Fin k))
        (fun b _ ↦ integrable_finsetSum (Finset.univ : Finset (Fin p))
          (fun r _ ↦ integrable_finsetSum (Finset.univ : Finset (Fin p))
            (fun q _ ↦ hthirdTerm t b r q s)))))
  have hthird : Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        inverseWishartTripleEntryTest u v x y z w R *
          ((((R * (realWishartGram R)⁻¹) * R.transpose) * E) *
            ((realWishartGram R)⁻¹ * D)) a i)
      (halfGaussianMatrix k p) := by
    apply hthirdSum.congr
    filter_upwards [] with R
    simp only [inverseWishartTripleEntryTest, Matrix.mul_apply,
      Matrix.transpose_apply]
    simp only [Finset.mul_sum, Finset.sum_mul]

  have hcombined := ((hfirst.sub hsecond).sub hthird).const_mul (1 / 2 : ℝ)
  apply hcombined.congr
  filter_upwards [] with R
  simp only [steinVectorFieldLinearization,
    Matrix.smul_apply, smul_eq_mul, Pi.sub_apply, Matrix.sub_apply]
  ring

/-- The derivative-defined triple-entry test times a Stein coordinate is
integrable. -/
theorem integrable_inverseWishartTripleEntryTestDerivative_mul_steinVectorFieldValue_apply
    {k p : ℕ} (hgap : p + 10 ≤ k)
    (u v x y z w : Fin p) (E : Matrix (Fin k) (Fin p) ℝ)
    (D : Matrix (Fin p) (Fin p) ℝ)
    (a : Fin k) (i : Fin p) :
    Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        inverseWishartTripleEntryTestDerivative u v x y z w R E *
          steinVectorFieldValue R D a i)
      (halfGaussianMatrix k p) := by
  have h1 :=
    integrable_inverseWishartEntryExplicitDerivative_mul_twoEntries_mul_steinValue
      hgap u v x y z w E D a i
  have h2 :=
    integrable_inverseWishartEntryExplicitDerivative_mul_twoEntries_mul_steinValue
      hgap x y u v z w E D a i
  have h3 :=
    integrable_inverseWishartEntryExplicitDerivative_mul_twoEntries_mul_steinValue
      hgap z w u v x y E D a i
  have hexplicit := (h1.add h2).add h3
  apply hexplicit.congr
  filter_upwards [
    ae_isUnit_det_realWishartGram_halfGaussianMatrix k p (by omega)]
      with R hR
  simp only [Pi.add_apply]
  rw [inverseWishartTripleEntryTestDerivative_apply u v x y z w R E hR]
  ring

/-- Matrix-law integrability of the complete product-rule derivative of a
triple-entry weighted Stein coordinate. -/
theorem integrable_inverseWishartTripleEntryWeightedSteinComponentDerivative_halfGaussianMatrix
    {k p : ℕ} (hgap : p + 10 ≤ k)
    (u v x y z w : Fin p) (D : Matrix (Fin p) (Fin p) ℝ)
    (E : Matrix (Fin k) (Fin p) ℝ)
    (a : Fin k) (i : Fin p) :
    Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        inverseWishartTripleEntryTestDerivative u v x y z w R E *
            steinVectorFieldValue R D a i +
          inverseWishartTripleEntryTest u v x y z w R *
            steinVectorFieldLinearization R D E a i)
      (halfGaussianMatrix k p) :=
  (integrable_inverseWishartTripleEntryTestDerivative_mul_steinVectorFieldValue_apply
      hgap u v x y z w E D a i).add
    (integrable_inverseWishartTripleEntryTest_mul_steinVectorFieldLinearization_apply
      hgap u v x y z w D E a i)

/-- Exact flattened coordinate families for the triple-entry test. -/
structure HalfGaussianInverseWishartTripleEntrySteinFamilies
    {k p n : ℕ} (hdim : n + 1 = k * p)
    (u v x y z w : Fin p) (D : Matrix (Fin p) (Fin p) ℝ) : Prop where
  value : ∀ i, Integrable
    (flattenedWeightedSteinComponent hdim
      (inverseWishartTripleEntryTest u v x y z w) D i)
    (halfGaussianPi (n + 1))
  derivative : ∀ i, Integrable
    (flattenedWeightedSteinComponentDerivative hdim
      (inverseWishartTripleEntryTest u v x y z w)
      (inverseWishartTripleEntryTestDerivative u v x y z w) D i)
    (halfGaussianPi (n + 1))
  radial : ∀ i, Integrable
    (fun q ↦ 2 * q i * flattenedWeightedSteinComponent hdim
      (inverseWishartTripleEntryTest u v x y z w) D i q)
    (halfGaussianPi (n + 1))

/-- The exact matrix-law estimates discharge every flattened family. -/
theorem halfGaussianInverseWishartTripleEntrySteinFamilies
    {k p n : ℕ} (hdim : n + 1 = k * p) (hgap : p + 10 ≤ k)
    (u v x y z w : Fin p) (D : Matrix (Fin p) (Fin p) ℝ) :
    HalfGaussianInverseWishartTripleEntrySteinFamilies
      hdim u v x y z w D := by
  let e := flatSuccMatrixMeasurableEquiv hdim
  have hmp : MeasurePreserving e (halfGaussianPi (n + 1))
      (halfGaussianMatrix k p) :=
    measurePreserving_flatSuccMatrixMeasurableEquiv hdim
  refine ⟨?_, ?_, ?_⟩
  · intro q
    let a := flatCoordinateRow hdim q
    let i := flatCoordinateColumn hdim q
    have hm :=
      integrable_inverseWishartTripleEntryTest_mul_steinVectorFieldValue_apply
        (by omega) u v x y z w D a i
    have hf := hmp.integrable_comp_of_integrable hm
    exact hf.congr (Filter.Eventually.of_forall fun q ↦ by rfl)
  · intro q
    let E := flatCoordinateMatrixUnit hdim q
    let a := flatCoordinateRow hdim q
    let i := flatCoordinateColumn hdim q
    have hm :=
      integrable_inverseWishartTripleEntryWeightedSteinComponentDerivative_halfGaussianMatrix
        hgap u v x y z w D E a i
    have hf := hmp.integrable_comp_of_integrable hm
    exact hf.congr (Filter.Eventually.of_forall fun q ↦ by rfl)
  · intro q
    let a := flatCoordinateRow hdim q
    let i := flatCoordinateColumn hdim q
    have hm :=
      integrable_inverseWishartTripleEntryTest_mul_steinVectorFieldValue_radial
        (by omega) u v x y z w D a i
    have hf := hmp.integrable_comp_of_integrable hm
    exact hf.congr (Filter.Eventually.of_forall fun qv ↦ by
      change 2 * (flatSuccMatrixMeasurableEquiv hdim qv) a i *
          (inverseWishartTripleEntryTest u v x y z w
              (flatSuccMatrixMeasurableEquiv hdim qv) *
            steinVectorFieldValue
              (flatSuccMatrixMeasurableEquiv hdim qv) D a i) =
        2 * qv q *
          (inverseWishartTripleEntryTest u v x y z w
              (flatSuccMatrixMeasurableEquiv hdim qv) *
            steinVectorFieldValue
              (flatSuccMatrixMeasurableEquiv hdim qv) D a i)
      rw [show (flatSuccMatrixMeasurableEquiv hdim qv) a i = qv q by
        simpa [a, i] using
          flatSuccMatrix_apply_flatCoordinatePair hdim qv q])

/-- Stein--Haff for a triple-entry test, reduced only to its literal
coordinate-family package. -/
theorem halfGaussian_inverseWishart_tripleEntry_steinHaff_of_families
    {k p n : ℕ} (hdim : n + 1 = k * p) (hp : p < k)
    (hgap : p + 8 ≤ k) (u v x y z w : Fin p)
    (D : Matrix (Fin p) (Fin p) ℝ) (hD : D.IsSymm)
    (H : HalfGaussianInverseWishartTripleEntrySteinFamilies
      hdim u v x y z w D) :
    Integrable
        (fun R : Matrix (Fin k) (Fin p) ℝ ↦
          inverseWishartTripleEntryTest u v x y z w R *
            (inverseGramScoreCoefficient (Fin k) (Fin p) *
              Matrix.trace ((realWishartGram R)⁻¹ * D)))
        (halfGaussianMatrix k p) ∧
      Integrable
        (fun R : Matrix (Fin k) (Fin p) ℝ ↦
          inverseWishartTripleEntryTest u v x y z w R * Matrix.trace D -
            (-(((realWishartGram R)⁻¹ * D *
                (realWishartGram R)⁻¹) u v) *
                (realWishartGram R)⁻¹ x y * (realWishartGram R)⁻¹ z w -
              (realWishartGram R)⁻¹ u v *
                (((realWishartGram R)⁻¹ * D *
                  (realWishartGram R)⁻¹) x y) *
                (realWishartGram R)⁻¹ z w -
              (realWishartGram R)⁻¹ u v * (realWishartGram R)⁻¹ x y *
                (((realWishartGram R)⁻¹ * D *
                  (realWishartGram R)⁻¹) z w)))
        (halfGaussianMatrix k p) ∧
      ((∫ R, inverseWishartTripleEntryTest u v x y z w R *
            (inverseGramScoreCoefficient (Fin k) (Fin p) *
              Matrix.trace ((realWishartGram R)⁻¹ * D))
          ∂halfGaussianMatrix k p) =
        ∫ R, inverseWishartTripleEntryTest u v x y z w R * Matrix.trace D -
            (-(((realWishartGram R)⁻¹ * D *
                (realWishartGram R)⁻¹) u v) *
                (realWishartGram R)⁻¹ x y * (realWishartGram R)⁻¹ z w -
              (realWishartGram R)⁻¹ u v *
                (((realWishartGram R)⁻¹ * D *
                  (realWishartGram R)⁻¹) x y) *
                (realWishartGram R)⁻¹ z w -
              (realWishartGram R)⁻¹ u v * (realWishartGram R)⁻¹ x y *
                (((realWishartGram R)⁻¹ * D *
                  (realWishartGram R)⁻¹) z w))
          ∂halfGaussianMatrix k p) := by
  have h :=
    steinHaff_halfGaussianMatrix_of_nonsingular_fderiv_and_flattenedSteinFamilies
      hdim hp
      (inverseWishartTripleEntryTest u v x y z w)
      (inverseWishartTripleEntryTestDerivative u v x y z w) D
      (fun R ↦
        -(((realWishartGram R)⁻¹ * D * (realWishartGram R)⁻¹) u v) *
            (realWishartGram R)⁻¹ x y * (realWishartGram R)⁻¹ z w -
          (realWishartGram R)⁻¹ u v *
            (((realWishartGram R)⁻¹ * D * (realWishartGram R)⁻¹) x y) *
            (realWishartGram R)⁻¹ z w -
          (realWishartGram R)⁻¹ u v * (realWishartGram R)⁻¹ x y *
            (((realWishartGram R)⁻¹ * D * (realWishartGram R)⁻¹) z w))
      (fun R hR ↦
        hasFDerivAt_inverseWishartTripleEntryTest u v x y z w R hR)
      (fun R hR ↦
        inverseWishartTripleEntryTestDerivative_steinVectorFieldValue
          u v x y z w R D hD hR)
      (integrable_inverseWishartTripleEntrySteinDerivativeValue
        hgap u v x y z w D)
      H.value H.derivative H.radial
  simpa only using h

/-- Unconditional triple-entry Stein--Haff identity at the exact order-five
coordinate-family threshold. -/
theorem halfGaussian_inverseWishart_tripleEntry_steinHaff
    {k p n : ℕ} (hdim : n + 1 = k * p) (hgap : p + 10 ≤ k)
    (u v x y z w : Fin p) (D : Matrix (Fin p) (Fin p) ℝ)
    (hD : D.IsSymm) :
    Integrable
        (fun R : Matrix (Fin k) (Fin p) ℝ ↦
          inverseWishartTripleEntryTest u v x y z w R *
            (inverseGramScoreCoefficient (Fin k) (Fin p) *
              Matrix.trace ((realWishartGram R)⁻¹ * D)))
        (halfGaussianMatrix k p) ∧
      Integrable
        (fun R : Matrix (Fin k) (Fin p) ℝ ↦
          inverseWishartTripleEntryTest u v x y z w R * Matrix.trace D -
            (-(((realWishartGram R)⁻¹ * D *
                (realWishartGram R)⁻¹) u v) *
                (realWishartGram R)⁻¹ x y * (realWishartGram R)⁻¹ z w -
              (realWishartGram R)⁻¹ u v *
                (((realWishartGram R)⁻¹ * D *
                  (realWishartGram R)⁻¹) x y) *
                (realWishartGram R)⁻¹ z w -
              (realWishartGram R)⁻¹ u v * (realWishartGram R)⁻¹ x y *
                (((realWishartGram R)⁻¹ * D *
                  (realWishartGram R)⁻¹) z w)))
        (halfGaussianMatrix k p) ∧
      ((∫ R, inverseWishartTripleEntryTest u v x y z w R *
            (inverseGramScoreCoefficient (Fin k) (Fin p) *
              Matrix.trace ((realWishartGram R)⁻¹ * D))
          ∂halfGaussianMatrix k p) =
        ∫ R, inverseWishartTripleEntryTest u v x y z w R * Matrix.trace D -
            (-(((realWishartGram R)⁻¹ * D *
                (realWishartGram R)⁻¹) u v) *
                (realWishartGram R)⁻¹ x y * (realWishartGram R)⁻¹ z w -
              (realWishartGram R)⁻¹ u v *
                (((realWishartGram R)⁻¹ * D *
                  (realWishartGram R)⁻¹) x y) *
                (realWishartGram R)⁻¹ z w -
              (realWishartGram R)⁻¹ u v * (realWishartGram R)⁻¹ x y *
                (((realWishartGram R)⁻¹ * D *
                  (realWishartGram R)⁻¹) z w))
          ∂halfGaussianMatrix k p) :=
  halfGaussian_inverseWishart_tripleEntry_steinHaff_of_families
    hdim (by omega) (by omega) u v x y z w D hD
      (halfGaussianInverseWishartTripleEntrySteinFamilies
        hdim hgap u v x y z w D)

/-! ## Exact fourth-entry inverse-Wishart recursion -/

/-- The integral of three prescribed inverse-Gram entries. -/
def halfGaussianInverseWishartTripleEntryIntegral
    (k p : ℕ) (u v x y z w : Fin p) : ℝ :=
  ∫ R : Matrix (Fin k) (Fin p) ℝ,
    (realWishartGram R)⁻¹ u v * (realWishartGram R)⁻¹ x y *
      (realWishartGram R)⁻¹ z w
    ∂halfGaussianMatrix k p

/-- The integral of four prescribed inverse-Gram entries. -/
def halfGaussianInverseWishartFourthEntryIntegral
    (k p : ℕ) (u v x y z w i j : Fin p) : ℝ :=
  ∫ R : Matrix (Fin k) (Fin p) ℝ,
    (realWishartGram R)⁻¹ u v * (realWishartGram R)⁻¹ x y *
      (realWishartGram R)⁻¹ z w * (realWishartGram R)⁻¹ i j
    ∂halfGaussianMatrix k p

/-- Exact order-four entry recursion.  This is the maximal shared
inverse-Wishart producer before any trace contraction or dense estimate. -/
theorem halfGaussian_inverseWishart_fourthEntry_steinRecursion_raw
    {k p : ℕ} (hgap : p + 10 ≤ k)
    (i j u v x y z w : Fin p) :
    inverseWishartEntryGap k p *
        halfGaussianInverseWishartFourthEntryIntegral
          k p u v x y z w i j =
      ∫ R : Matrix (Fin k) (Fin p) ℝ,
        (realWishartGram R)⁻¹ u v * (realWishartGram R)⁻¹ x y *
            (realWishartGram R)⁻¹ z w *
            (2 * realKroneckerDelta i j) +
          ((realWishartGram R)⁻¹ u j * (realWishartGram R)⁻¹ i v +
              (realWishartGram R)⁻¹ u i * (realWishartGram R)⁻¹ j v) *
            (realWishartGram R)⁻¹ x y * (realWishartGram R)⁻¹ z w +
          (realWishartGram R)⁻¹ u v *
            ((realWishartGram R)⁻¹ x j * (realWishartGram R)⁻¹ i y +
              (realWishartGram R)⁻¹ x i * (realWishartGram R)⁻¹ j y) *
            (realWishartGram R)⁻¹ z w +
          (realWishartGram R)⁻¹ u v * (realWishartGram R)⁻¹ x y *
            ((realWishartGram R)⁻¹ z j * (realWishartGram R)⁻¹ i w +
              (realWishartGram R)⁻¹ z i * (realWishartGram R)⁻¹ j w)
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
  have hHaff := halfGaussian_inverseWishart_tripleEntry_steinHaff
    hdim hgap u v x y z w D hD
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
        halfGaussianInverseWishartFourthEntryIntegral
          k p u v x y z w i j =
      ∫ R : Matrix (Fin k) (Fin p) ℝ,
        inverseWishartTripleEntryTest u v x y z w R *
          (c / 2 * (2 * (realWishartGram R)⁻¹ i j))
        ∂halfGaussianMatrix k p := by
      unfold halfGaussianInverseWishartFourthEntryIntegral
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with R
      dsimp only [c, inverseWishartTripleEntryTest]
      ring
    _ = ∫ R : Matrix (Fin k) (Fin p) ℝ,
        inverseWishartTripleEntryTest u v x y z w R *
          (c / 2 * Matrix.trace ((realWishartGram R)⁻¹ * D))
        ∂halfGaussianMatrix k p := by
      apply integral_congr_ae
      filter_upwards [] with R
      rw [congrFun htraceInv R]
    _ = ∫ R : Matrix (Fin k) (Fin p) ℝ,
        inverseWishartTripleEntryTest u v x y z w R * Matrix.trace D -
          (-(((realWishartGram R)⁻¹ * D * (realWishartGram R)⁻¹) u v) *
              (realWishartGram R)⁻¹ x y * (realWishartGram R)⁻¹ z w -
            (realWishartGram R)⁻¹ u v *
              (((realWishartGram R)⁻¹ * D * (realWishartGram R)⁻¹) x y) *
              (realWishartGram R)⁻¹ z w -
            (realWishartGram R)⁻¹ u v * (realWishartGram R)⁻¹ x y *
              (((realWishartGram R)⁻¹ * D * (realWishartGram R)⁻¹) z w))
        ∂halfGaussianMatrix k p := heq
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with R
      rw [htraceD, congrFun (hsandwich u v) R,
        congrFun (hsandwich x y) R, congrFun (hsandwich z w) R]
      simp only [inverseWishartTripleEntryTest]
      ring

/-- Explicit seven-term fourth-entry recursion, obtained from the raw
Stein identity by justified integral linearity. -/
theorem halfGaussian_inverseWishart_fourthEntry_steinRecursion
    {k p : ℕ} (hgap : p + 10 ≤ k)
    (i j u v x y z w : Fin p) :
    inverseWishartEntryGap k p *
        halfGaussianInverseWishartFourthEntryIntegral
          k p u v x y z w i j =
      2 * realKroneckerDelta i j *
          halfGaussianInverseWishartTripleEntryIntegral k p u v x y z w +
        halfGaussianInverseWishartFourthEntryIntegral k p u j i v x y z w +
        halfGaussianInverseWishartFourthEntryIntegral k p u i j v x y z w +
        halfGaussianInverseWishartFourthEntryIntegral k p u v x j i y z w +
        halfGaussianInverseWishartFourthEntryIntegral k p u v x i j y z w +
        halfGaussianInverseWishartFourthEntryIntegral k p u v x y z j i w +
        halfGaussianInverseWishartFourthEntryIntegral k p u v x y z i j w := by
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
  have hfour (a b c d e f g h : Fin p) : Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        (realWishartGram R)⁻¹ a b * (realWishartGram R)⁻¹ c d *
          (realWishartGram R)⁻¹ e f * (realWishartGram R)⁻¹ g h)
      (halfGaussianMatrix k p) := by
    let indices : Fin 4 → Fin p × Fin p :=
      ![(a, b), (c, d), (e, f), (g, h)]
    have hbase := integrable_inverseWishartEntryProduct_halfGaussianMatrix
      (k := k) (p := p) (q := 4) (by omega) indices
    apply hbase.congr
    filter_upwards [] with R
    simp [indices, inverseWishartEntryProduct, Fin.prod_univ_four]
  have h0 : Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        (realWishartGram R)⁻¹ u v * (realWishartGram R)⁻¹ x y *
          (realWishartGram R)⁻¹ z w * (2 * realKroneckerDelta i j))
      (halfGaussianMatrix k p) :=
    (htriple u v x y z w).mul_const (2 * realKroneckerDelta i j)
  have h1 := hfour u j i v x y z w
  have h2 := hfour u i j v x y z w
  have h3 := hfour u v x j i y z w
  have h4 := hfour u v x i j y z w
  have h5 := hfour u v x y z j i w
  have h6 := hfour u v x y z i j w
  let f0 : Matrix (Fin k) (Fin p) ℝ → ℝ := fun R ↦
    (realWishartGram R)⁻¹ u v * (realWishartGram R)⁻¹ x y *
      (realWishartGram R)⁻¹ z w * (2 * realKroneckerDelta i j)
  let f1 : Matrix (Fin k) (Fin p) ℝ → ℝ := fun R ↦
    (realWishartGram R)⁻¹ u j * (realWishartGram R)⁻¹ i v *
      (realWishartGram R)⁻¹ x y * (realWishartGram R)⁻¹ z w
  let f2 : Matrix (Fin k) (Fin p) ℝ → ℝ := fun R ↦
    (realWishartGram R)⁻¹ u i * (realWishartGram R)⁻¹ j v *
      (realWishartGram R)⁻¹ x y * (realWishartGram R)⁻¹ z w
  let f3 : Matrix (Fin k) (Fin p) ℝ → ℝ := fun R ↦
    (realWishartGram R)⁻¹ u v * (realWishartGram R)⁻¹ x j *
      (realWishartGram R)⁻¹ i y * (realWishartGram R)⁻¹ z w
  let f4 : Matrix (Fin k) (Fin p) ℝ → ℝ := fun R ↦
    (realWishartGram R)⁻¹ u v * (realWishartGram R)⁻¹ x i *
      (realWishartGram R)⁻¹ j y * (realWishartGram R)⁻¹ z w
  let f5 : Matrix (Fin k) (Fin p) ℝ → ℝ := fun R ↦
    (realWishartGram R)⁻¹ u v * (realWishartGram R)⁻¹ x y *
      (realWishartGram R)⁻¹ z j * (realWishartGram R)⁻¹ i w
  let f6 : Matrix (Fin k) (Fin p) ℝ → ℝ := fun R ↦
    (realWishartGram R)⁻¹ u v * (realWishartGram R)⁻¹ x y *
      (realWishartGram R)⁻¹ z i * (realWishartGram R)⁻¹ j w
  have hf0 : Integrable f0 (halfGaussianMatrix k p) := by
    simpa only [f0] using h0
  have hf1 : Integrable f1 (halfGaussianMatrix k p) := by
    simpa only [f1] using h1
  have hf2 : Integrable f2 (halfGaussianMatrix k p) := by
    simpa only [f2] using h2
  have hf3 : Integrable f3 (halfGaussianMatrix k p) := by
    simpa only [f3] using h3
  have hf4 : Integrable f4 (halfGaussianMatrix k p) := by
    simpa only [f4] using h4
  have hf5 : Integrable f5 (halfGaussianMatrix k p) := by
    simpa only [f5] using h5
  have hf6 : Integrable f6 (halfGaussianMatrix k p) := by
    simpa only [f6] using h6
  rw [halfGaussian_inverseWishart_fourthEntry_steinRecursion_raw
    hgap i j u v x y z w]
  calc
    (∫ R : Matrix (Fin k) (Fin p) ℝ,
        (realWishartGram R)⁻¹ u v * (realWishartGram R)⁻¹ x y *
            (realWishartGram R)⁻¹ z w *
            (2 * realKroneckerDelta i j) +
          ((realWishartGram R)⁻¹ u j * (realWishartGram R)⁻¹ i v +
              (realWishartGram R)⁻¹ u i * (realWishartGram R)⁻¹ j v) *
            (realWishartGram R)⁻¹ x y * (realWishartGram R)⁻¹ z w +
          (realWishartGram R)⁻¹ u v *
            ((realWishartGram R)⁻¹ x j * (realWishartGram R)⁻¹ i y +
              (realWishartGram R)⁻¹ x i * (realWishartGram R)⁻¹ j y) *
            (realWishartGram R)⁻¹ z w +
          (realWishartGram R)⁻¹ u v * (realWishartGram R)⁻¹ x y *
            ((realWishartGram R)⁻¹ z j * (realWishartGram R)⁻¹ i w +
              (realWishartGram R)⁻¹ z i * (realWishartGram R)⁻¹ j w)
        ∂halfGaussianMatrix k p) =
      ∫ R : Matrix (Fin k) (Fin p) ℝ,
        ((((((f0 R + f1 R) + f2 R) + f3 R) + f4 R) + f5 R) + f6 R)
        ∂halfGaussianMatrix k p := by
      apply integral_congr_ae
      filter_upwards [] with R
      simp only [f0, f1, f2, f3, f4, f5, f6]
      ring
    _ =
      (∫ R, f0 R ∂halfGaussianMatrix k p) +
      (∫ R, f1 R ∂halfGaussianMatrix k p) +
      (∫ R, f2 R ∂halfGaussianMatrix k p) +
      (∫ R, f3 R ∂halfGaussianMatrix k p) +
      (∫ R, f4 R ∂halfGaussianMatrix k p) +
      (∫ R, f5 R ∂halfGaussianMatrix k p) +
      (∫ R, f6 R ∂halfGaussianMatrix k p) := by
      have hs1 :
          (∫ R, f0 R + f1 R ∂halfGaussianMatrix k p) =
            (∫ R, f0 R ∂halfGaussianMatrix k p) +
              ∫ R, f1 R ∂halfGaussianMatrix k p := by
        simpa only [Pi.add_apply] using integral_add hf0 hf1
      have hs2 :
          (∫ R, (f0 R + f1 R) + f2 R ∂halfGaussianMatrix k p) =
            (∫ R, f0 R + f1 R ∂halfGaussianMatrix k p) +
              ∫ R, f2 R ∂halfGaussianMatrix k p := by
        simpa only [Pi.add_apply] using integral_add (hf0.add hf1) hf2
      have hs3 :
          (∫ R, ((f0 R + f1 R) + f2 R) + f3 R
            ∂halfGaussianMatrix k p) =
            (∫ R, (f0 R + f1 R) + f2 R ∂halfGaussianMatrix k p) +
              ∫ R, f3 R ∂halfGaussianMatrix k p := by
        simpa only [Pi.add_apply] using integral_add ((hf0.add hf1).add hf2) hf3
      have hs4 :
          (∫ R, (((f0 R + f1 R) + f2 R) + f3 R) + f4 R
            ∂halfGaussianMatrix k p) =
            (∫ R, ((f0 R + f1 R) + f2 R) + f3 R
              ∂halfGaussianMatrix k p) +
              ∫ R, f4 R ∂halfGaussianMatrix k p := by
        simpa only [Pi.add_apply] using
          integral_add (((hf0.add hf1).add hf2).add hf3) hf4
      have hs5 :
          (∫ R, ((((f0 R + f1 R) + f2 R) + f3 R) + f4 R) + f5 R
            ∂halfGaussianMatrix k p) =
            (∫ R, (((f0 R + f1 R) + f2 R) + f3 R) + f4 R
              ∂halfGaussianMatrix k p) +
              ∫ R, f5 R ∂halfGaussianMatrix k p := by
        simpa only [Pi.add_apply] using
          integral_add ((((hf0.add hf1).add hf2).add hf3).add hf4) hf5
      have hs6 :
          (∫ R, (((((f0 R + f1 R) + f2 R) + f3 R) + f4 R) + f5 R) + f6 R
            ∂halfGaussianMatrix k p) =
            (∫ R, ((((f0 R + f1 R) + f2 R) + f3 R) + f4 R) + f5 R
              ∂halfGaussianMatrix k p) +
              ∫ R, f6 R ∂halfGaussianMatrix k p := by
        simpa only [Pi.add_apply] using
          integral_add (((((hf0.add hf1).add hf2).add hf3).add hf4).add hf5) hf6
      rw [hs6, hs5, hs4, hs3, hs2, hs1]
    _ = _ := by
      simp only [f0, f1, f2, f3, f4, f5, f6]
      unfold halfGaussianInverseWishartTripleEntryIntegral
        halfGaussianInverseWishartFourthEntryIntegral
      rw [show (∫ R : Matrix (Fin k) (Fin p) ℝ,
          (realWishartGram R)⁻¹ u v * (realWishartGram R)⁻¹ x y *
            (realWishartGram R)⁻¹ z w * (2 * realKroneckerDelta i j)
          ∂halfGaussianMatrix k p) =
        2 * realKroneckerDelta i j *
          (∫ R : Matrix (Fin k) (Fin p) ℝ,
            (realWishartGram R)⁻¹ u v * (realWishartGram R)⁻¹ x y *
              (realWishartGram R)⁻¹ z w
            ∂halfGaussianMatrix k p) by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with R
        ring]

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08
