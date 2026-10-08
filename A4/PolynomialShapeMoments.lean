import A4.DirectMomentsEntryPolynomial
import A4.PolynomialIntegrability
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

open MeasureTheory Matrix
open scoped BigOperators ENNReal NNReal

noncomputable section

namespace MatsumotoPaper

/-- A polynomial observable in the literal real matrix entries. -/
abbrev MatrixEntryPolynomial (d : ℕ) := MvPolynomial (Fin d × Fin d) ℝ

def evaluateMatrixEntryPolynomial {d : ℕ} (P : MatrixEntryPolynomial d)
    (x : RealMatrix d) : ℝ :=
  MvPolynomial.eval (fun a ↦ x a.1 a.2) P

/-- Repeated entry slots of one multivariate monomial. -/
abbrev MatrixMonomialSlots {d : ℕ} (e : (Fin d × Fin d) →₀ ℕ) :=
  Σ a : Fin d × Fin d, Fin (e a)

def matrixMonomialEntryShapePolynomial {d : ℕ}
    (e : (Fin d × Fin d) →₀ ℕ) (sigma : RealMatrix d) : Polynomial ℝ :=
  entryProductShapePolynomial
    (fun i ↦ ((Fintype.equivFin (MatrixMonomialSlots e)).symm i).1.1)
    (fun i ↦ ((Fintype.equivFin (MatrixMonomialSlots e)).symm i).1.2) sigma

theorem prod_entries_eq_matrixMonomial {d : ℕ}
    (e : (Fin d × Fin d) →₀ ℕ) (x : RealMatrix d) :
    (∏ t : MatrixMonomialSlots e, x t.1.1 t.1.2) =
      ∏ a : Fin d × Fin d, (x a.1 a.2) ^ e a := by
  rw [Fintype.prod_sigma]
  simp

theorem W_d.integral_matrixMonomial_eq_eval_shapePolynomial
    {d : ℕ} {beta : ℝ} {sigma : SymPosDef d} (W : W_d d beta sigma)
    (e : (Fin d × Fin d) →₀ ℕ) :
    (∫ w, ∏ a : Fin d × Fin d, (w.1 a.1 a.2) ^ e a ∂W.toMeasure) =
      (matrixMonomialEntryShapePolynomial e sigma.1).eval beta := by
  let E := (Fintype.equivFin (MatrixMonomialSlots e)).symm
  have hfun : (fun w : SymPosDef d ↦
      ∏ a : Fin d × Fin d, (w.1 a.1 a.2) ^ e a) =
      fun w ↦ ∏ i : Fin (Fintype.card (MatrixMonomialSlots e)),
        w.1 (E i).1.1 (E i).1.2 := by
    funext w
    rw [← prod_entries_eq_matrixMonomial]
    exact (E.prod_comp (fun t : MatrixMonomialSlots e ↦ w.1 t.1.1 t.1.2)).symm
  rw [hfun]
  exact W.integral_prod_entries_eq_eval_entryProductShapePolynomial _ _

theorem W_d.integrable_matrixMonomial {d : ℕ} {beta : ℝ} {sigma : SymPosDef d}
    (W : W_d d beta sigma) (e : (Fin d × Fin d) →₀ ℕ) :
    Integrable (fun w ↦ ∏ a : Fin d × Fin d, (w.1 a.1 a.2) ^ e a) W.toMeasure := by
  have h := W.memLp_prod_entries
    (fun t : MatrixMonomialSlots e ↦ t.1.1)
    (fun t : MatrixMonomialSlots e ↦ t.1.2) (1 : ℝ≥0)
  simpa only [ENNReal.coe_one, memLp_one_iff_integrable,
    prod_entries_eq_matrixMonomial] using h

/-- The full expectation of any polynomial entry observable is a genuine
univariate polynomial in the Wishart shape. -/
def polynomialObservableShapePolynomial {d : ℕ} (P : MatrixEntryPolynomial d)
    (sigma : RealMatrix d) : Polynomial ℝ :=
  ∑ e ∈ P.support, Polynomial.C (P.coeff e) *
    matrixMonomialEntryShapePolynomial e sigma

theorem W_d.integrable_polynomialObservable {d : ℕ} {beta : ℝ} {sigma : SymPosDef d}
    (W : W_d d beta sigma) (P : MatrixEntryPolynomial d) :
    Integrable (fun w ↦ evaluateMatrixEntryPolynomial P w.1) W.toMeasure := by
  classical
  simp only [evaluateMatrixEntryPolynomial, MvPolynomial.eval_eq']
  apply integrable_finsetSum
  intro e _
  exact (W.integrable_matrixMonomial e).const_mul _

theorem W_d.integral_polynomialObservable_eq_eval_shapePolynomial
    {d : ℕ} {beta : ℝ} {sigma : SymPosDef d} (W : W_d d beta sigma)
    (P : MatrixEntryPolynomial d) :
    (∫ w, evaluateMatrixEntryPolynomial P w.1 ∂W.toMeasure) =
      (polynomialObservableShapePolynomial P sigma.1).eval beta := by
  classical
  simp only [evaluateMatrixEntryPolynomial, MvPolynomial.eval_eq',
    polynomialObservableShapePolynomial, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro e _
    rw [integral_const_mul, W.integral_matrixMonomial_eq_eval_shapePolynomial]
  · intro e _
    exact (W.integrable_matrixMonomial e).const_mul _

/-- The generic variable matrix makes every adjugate entry a literal
multivariate entry polynomial, including dimension zero. -/
def variableEntryMatrix (d : ℕ) : Matrix (Fin d) (Fin d) (MatrixEntryPolynomial d) :=
  fun i j ↦ MvPolynomial.X (i, j)

def adjugateEntryProductPolynomial {d n : ℕ} (i j : Fin n → Fin d) :
    MatrixEntryPolynomial d :=
  ∏ k : Fin n, (variableEntryMatrix d).adjugate (i k) (j k)

theorem evaluate_variableEntryMatrix {d : ℕ} (x : RealMatrix d) :
    (MvPolynomial.eval (fun a : Fin d × Fin d ↦ x a.1 a.2)).mapMatrix
      (variableEntryMatrix d) = x := by
  ext i j
  simp [variableEntryMatrix, RingHom.mapMatrix_apply]

theorem evaluate_adjugateEntryProductPolynomial {d n : ℕ}
    (i j : Fin n → Fin d) (x : RealMatrix d) :
    evaluateMatrixEntryPolynomial (adjugateEntryProductPolynomial i j) x =
      ∏ k : Fin n, x.adjugate (i k) (j k) := by
  classical
  unfold evaluateMatrixEntryPolynomial adjugateEntryProductPolynomial
  rw [map_prod]
  have hmap := (MvPolynomial.eval (fun a : Fin d × Fin d ↦ x a.1 a.2)).map_adjugate
    (variableEntryMatrix d)
  rw [evaluate_variableEntryMatrix] at hmap
  apply Finset.prod_congr rfl
  intro k _
  exact congrArg (fun A ↦ A (i k) (j k)) hmap

def adjugateEntryProductShapePolynomial {d n : ℕ} (i j : Fin n → Fin d)
    (sigma : RealMatrix d) : Polynomial ℝ :=
  polynomialObservableShapePolynomial (adjugateEntryProductPolynomial i j) sigma

theorem W_d.integral_prod_adjugate_entries_eq_eval_shapePolynomial
    {d n : ℕ} {beta : ℝ} {sigma : SymPosDef d} (W : W_d d beta sigma)
    (i j : Fin n → Fin d) :
    (∫ w, ∏ k : Fin n, w.1.adjugate (i k) (j k) ∂W.toMeasure) =
      (adjugateEntryProductShapePolynomial i j sigma.1).eval beta := by
  simpa only [evaluate_adjugateEntryProductPolynomial,
    adjugateEntryProductShapePolynomial] using
    W.integral_polynomialObservable_eq_eval_shapePolynomial (adjugateEntryProductPolynomial i j)

end MatsumotoPaper
