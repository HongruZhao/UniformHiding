import A3.GSVSpectralSupport
import A3.Shared.PolynomialNullity
import Mathlib.Probability.ProductMeasure

open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open Matrix MeasureTheory ProbabilityTheory

noncomputable section
namespace A3Research

variable {K : Type*} [NormedField K] [MeasurableSpace K] [BorelSpace K]
  [SecondCountableTopology K]

local instance genericMatrixMeasurable (i j : Type*) : MeasurableSpace (Matrix i j K) := by
  unfold Matrix
  infer_instance

local instance genericMatrixBorel (i j : Type*) [Finite i] [Finite j] :
    BorelSpace (Matrix i j K) :=
  inferInstanceAs (BorelSpace (i → j → K))

/-- Regrouping a finite iid scalar law into rows preserves its entire law. -/
theorem measurePreserving_iid_curry (rows n : ℕ) (mu : Measure K)
    [IsProbabilityMeasure mu] :
    MeasurePreserving (MeasurableEquiv.curry (Fin rows) (Fin n) K)
      (Measure.pi fun _ : Fin rows × Fin n ↦ mu)
      (Measure.pi fun _ : Fin rows ↦ Measure.pi fun _ : Fin n ↦ mu) := by
  refine ⟨(MeasurableEquiv.curry (Fin rows) (Fin n) K).measurable, ?_⟩
  rw [← Measure.infinitePi_eq_pi, ← Measure.infinitePi_eq_pi]
  simp_rw [← Measure.infinitePi_eq_pi]
  exact Measure.infinitePi_map_curry (fun _ : Fin rows ↦ fun _ : Fin n ↦ mu)

def leadingMinorPolynomial (rows n : ℕ) (h : n ≤ rows) :
    MvPolynomial (Fin rows × Fin n) K :=
  Matrix.det (Matrix.of fun i j : Fin n ↦ MvPolynomial.X (Fin.castLE h i, j))

theorem eval_leadingMinorPolynomial (rows n : ℕ) (h : n ≤ rows)
    (z : Fin rows × Fin n → K) :
    MvPolynomial.eval z (leadingMinorPolynomial (K := K) rows n h) =
      Matrix.det (Matrix.of fun i j : Fin n ↦ z (Fin.castLE h i, j)) := by
  have hmap : (Matrix.of fun i j : Fin n ↦ MvPolynomial.X (Fin.castLE h i, j)).map
      (MvPolynomial.eval z) = Matrix.of (fun i j : Fin n ↦ z (Fin.castLE h i, j)) := by
    ext i j
    simp
  exact ((MvPolynomial.eval z).map_det
    (Matrix.of fun i j : Fin n ↦ MvPolynomial.X (Fin.castLE h i, j))).trans
      (congrArg Matrix.det hmap)

theorem leadingMinorPolynomial_ne_zero (rows n : ℕ) (h : n ≤ rows) :
    leadingMinorPolynomial (K := K) rows n h ≠ 0 := by
  let z : Fin rows × Fin n → K := fun p ↦ if p.1.val = p.2.val then 1 else 0
  have hz : (Matrix.of fun i j : Fin n ↦ z (Fin.castLE h i, j)) =
      (1 : Matrix (Fin n) (Fin n) K) := by
    ext i j
    simp only [z, Matrix.of_apply, Fin.castLE, Matrix.one_apply]
    simp only [Fin.ext_iff]
  intro hp
  have he := congrArg (MvPolynomial.eval z) hp
  rw [eval_leadingMinorPolynomial, hz, Matrix.det_one, map_zero] at he
  exact one_ne_zero he

/-- A square leading minor of a rectangular iid atomless matrix is nonzero almost surely. -/
theorem ae_det_leadingMinor_ne_zero (rows n : ℕ) (h : n ≤ rows)
    (mu : Measure K) [IsProbabilityMeasure mu] [NullSingletonClass mu] :
    ∀ᵐ X ∂(Measure.pi fun _ : Fin rows ↦ Measure.pi fun _ : Fin n ↦ mu),
      Matrix.det (Matrix.of fun i j : Fin n ↦ X (Fin.castLE h i) j) ≠ 0 := by
  have ha := ae_mvPolynomial_eval_ne_zero mu
    (leadingMinorPolynomial (K := K) rows n h) (leadingMinorPolynomial_ne_zero rows n h)
  have hs : MeasurableSet {X : Fin rows → Fin n → K |
      Matrix.det (Matrix.of fun i j : Fin n ↦ X (Fin.castLE h i) j) ≠ 0} := by
    have hc : Continuous (fun X : Fin rows → Fin n → K ↦
        Matrix.of fun i j : Fin n ↦ X (Fin.castLE h i) j) := by fun_prop
    have hm := hc.matrix_det.measurable
    exact (hm.eq_const 0).setOf.compl
  rw [← (measurePreserving_iid_curry rows n mu).map_eq]
  apply (ae_map_iff (MeasurableEquiv.curry (Fin rows) (Fin n) K).measurable.aemeasurable hs).mpr
  simpa only [eval_leadingMinorPolynomial, MeasurableEquiv.curry_apply] using ha

theorem injective_mulVec_of_det_leadingMinor_ne_zero {rows n : ℕ} (h : n ≤ rows)
    (X : Matrix (Fin rows) (Fin n) K)
    (hdet : Matrix.det (Matrix.of fun i j : Fin n ↦ X (Fin.castLE h i) j) ≠ 0) :
    Function.Injective X.mulVec := by
  have hminor : IsUnit (Matrix.of fun i j : Fin n ↦ X (Fin.castLE h i) j) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hinj := Matrix.mulVec_injective_iff_isUnit.mpr hminor
  intro v w hvw
  apply hinj
  funext i
  exact congrFun hvw (Fin.castLE h i)

end A3Research

namespace LogdetLean.GramHafnian

theorem injective_circularGaussianCoordinate : Function.Injective circularGaussianCoordinate := by
  have hs : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2)
  intro q p h
  have hn : (q.1 : ℂ) + (q.2 : ℂ) * Complex.I =
      (p.1 : ℂ) + (p.2 : ℂ) * Complex.I := by
    have hh := congrArg (fun z : ℂ ↦ z * (Real.sqrt 2 : ℂ)) h
    simpa [circularGaussianCoordinate, hs] using hh
  apply Prod.ext
  · simpa using congrArg Complex.re hn
  · simpa using congrArg Complex.im hn

instance circularGaussian_isProbabilityMeasure : IsProbabilityMeasure circularGaussian :=
  Measure.isProbabilityMeasure_map measurable_circularGaussianCoordinate.aemeasurable

instance circularGaussian_nullSingletonClass : NullSingletonClass circularGaussian where
  measure_singleton z := by
    letI : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
    rw [circularGaussian, Measure.map_apply measurable_circularGaussianCoordinate
      (measurableSet_singleton z)]
    exact ((Set.finite_singleton z).preimage
      injective_circularGaussianCoordinate.injOn).measure_zero _

end LogdetLean.GramHafnian
