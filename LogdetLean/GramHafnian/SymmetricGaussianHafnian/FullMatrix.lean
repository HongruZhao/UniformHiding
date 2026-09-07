import LogdetLean.GramHafnian.SymmetricGaussianHafnian.GaussianPerturbationScaled

/-!
# Full complex symmetric Gaussian matrix adapters

The direct small ball theorems use one coordinate for each unordered off
diagonal edge.  This file supplies the exact full matrix law used in the
Article, proves that its off diagonal pushforward is the edge Gaussian law,
and proves that arbitrary diagonal coordinates do not change the ordinary
hafnian.  No scientific axiom is introduced.
-/

open MeasureTheory ProbabilityTheory

namespace LogdetLean.GramHafnian.SymmetricGaussianHafnian

noncomputable section

/-- Full symmetric matrix coordinates, with off diagonal data first and
diagonal data second. -/
abbrev ComplexFullSymmetricCoordinates (n : ℕ) :=
  (Edge (Fin (2 * n)) → ℂ) × (Fin (2 * n) → ℂ)

/-- The full symmetric matrix assembled from its edge and diagonal data. -/
def matrixOfFullSymmetricCoordinates {n : ℕ}
    (p : ComplexFullSymmetricCoordinates n) :
    Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ :=
  fun i j ↦ if h : i = j then p.2 i else p.1 (edgeOfNe i j h)

@[simp] theorem matrixOfFullSymmetricCoordinates_diag {n : ℕ}
    (p : ComplexFullSymmetricCoordinates n) (i : Fin (2 * n)) :
    matrixOfFullSymmetricCoordinates p i i = p.2 i := by
  simp [matrixOfFullSymmetricCoordinates]

@[simp] theorem matrixOfFullSymmetricCoordinates_apply_ne {n : ℕ}
    (p : ComplexFullSymmetricCoordinates n) (i j : Fin (2 * n))
    (h : i ≠ j) :
    matrixOfFullSymmetricCoordinates p i j = p.1 (edgeOfNe i j h) := by
  simp [matrixOfFullSymmetricCoordinates, h]

theorem matrixOfFullSymmetricCoordinates_symmetric {n : ℕ}
    (p : ComplexFullSymmetricCoordinates n) (i j : Fin (2 * n)) :
    matrixOfFullSymmetricCoordinates p i j =
      matrixOfFullSymmetricCoordinates p j i := by
  by_cases h : i = j
  · subst j
    rfl
  · have h' : j ≠ i := Ne.symm h
    simp only [matrixOfFullSymmetricCoordinates_apply_ne p i j h,
      matrixOfFullSymmetricCoordinates_apply_ne p j i h']
    rw [edgeOfNe_swap i j h]

/-- Ordinary hafnian of the assembled full matrix. -/
def fullSymmetricHafnian {n : ℕ}
    (p : ComplexFullSymmetricCoordinates n) : ℂ :=
  hafnian (matrixOfFullSymmetricCoordinates p)

/-- Exact diagonal invariance adapter: ordinary hafnian of the full matrix is
the edge hafnian of its off diagonal coordinates. -/
theorem fullSymmetricHafnian_eq_edgeHafnian {n : ℕ}
    (p : ComplexFullSymmetricCoordinates n) :
    fullSymmetricHafnian p = edgeHafnian p.1 := by
  classical
  unfold fullSymmetricHafnian edgeHafnian
  rw [← typeHafnian_fin_eq_hafnian]
  unfold typeHafnian typeMatchingMonomial
  apply Finset.sum_congr rfl
  intro M hM
  apply Finset.prod_congr rfl
  intro i hi
  have hne : i ≠ M i := (M.mate_ne i).symm
  simp [matrixOfFullSymmetricCoordinates, matrixOfEdges, hne]

@[fun_prop] theorem measurable_fullSymmetricHafnian {n : ℕ} :
    Measurable (fullSymmetricHafnian : ComplexFullSymmetricCoordinates n → ℂ) := by
  have hfun :
      (fullSymmetricHafnian : ComplexFullSymmetricCoordinates n → ℂ) =
        fun p ↦ edgeHafnian p.1 := by
    funext p
    exact fullSymmetricHafnian_eq_edgeHafnian p
  rw [hfun]
  fun_prop

/-- Literal complex variance two diagonal law. -/
def complexVarianceTwoDiagonalLaw (n : ℕ) : Measure (Fin (2 * n) → ℂ) :=
  (standardGaussianProduct (Fin (2 * n))).map
    (fun z i ↦ (Real.sqrt 2 : ℂ) * z i)

instance complexVarianceTwoDiagonalLaw_probability (n : ℕ) :
    IsProbabilityMeasure (complexVarianceTwoDiagonalLaw n) := by
  unfold complexVarianceTwoDiagonalLaw
  have hmeas : Measurable
      (fun z : Fin (2 * n) → ℂ ↦ fun i ↦ (Real.sqrt 2 : ℂ) * z i) := by
    fun_prop
  exact Measure.isProbabilityMeasure_map hmeas.aemeasurable

/-- Full complex symmetric Gaussian law: independent standard circular
Gaussian off diagonal entries and independent variance two diagonal entries. -/
def complexSymmetricGaussianFullMatrixLaw (n : ℕ) :
    Measure (ComplexFullSymmetricCoordinates n) :=
  (edgeGaussian (Fin (2 * n))).prod (complexVarianceTwoDiagonalLaw n)

instance complexSymmetricGaussianFullMatrixLaw_probability (n : ℕ) :
    IsProbabilityMeasure (complexSymmetricGaussianFullMatrixLaw n) := by
  unfold complexSymmetricGaussianFullMatrixLaw
  infer_instance

/-- Exact off diagonal pushforward of the full symmetric Gaussian law. -/
theorem complexSymmetricGaussianFullMatrixLaw_map_offDiagonal (n : ℕ) :
    (complexSymmetricGaussianFullMatrixLaw n).map Prod.fst =
      edgeGaussian (Fin (2 * n)) := by
  simp [complexSymmetricGaussianFullMatrixLaw]

/-- Componentwise addition of full symmetric coordinates. -/
def addFullSymmetricCoordinates {n : ℕ}
    (p q : ComplexFullSymmetricCoordinates n) :
    ComplexFullSymmetricCoordinates n :=
  (p.1 + q.1, p.2 + q.2)

/-- Adding arbitrary diagonal perturbations still does not affect the
hafnian. -/
theorem fullSymmetricHafnian_add_eq_edgeHafnian {n : ℕ}
    (p q : ComplexFullSymmetricCoordinates n) :
    fullSymmetricHafnian (addFullSymmetricCoordinates p q) =
      edgeHafnian (p.1 + q.1) := by
  simpa [addFullSymmetricCoordinates] using
    fullSymmetricHafnian_eq_edgeHafnian
      (addFullSymmetricCoordinates p q)

end

end LogdetLean.GramHafnian.SymmetricGaussianHafnian
