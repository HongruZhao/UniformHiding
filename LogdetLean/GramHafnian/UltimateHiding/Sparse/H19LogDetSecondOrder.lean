import LogdetLean.GramHafnian.UltimateHiding.Sparse.H19ScalarLimits
import LogdetLean.ElementaryNormalizationCLT
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic

/-!
# A second-order log-determinant inequality

This file contains the deterministic matrix inequality used by the direct
quantitative Jiang-density route.  It has no probabilistic or scientific
input.
-/

open scoped BigOperators ComplexOrder MatrixOrder

namespace LogdetLean.GramHafnian.UltimateHiding.Sparse

noncomputable section

/-- The elementary scalar second-order upper bound for `log (1-x)`. -/
theorem log_one_sub_le_neg_sub_half_sq_h19
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Real.log (1 - x) ≤ -x - x ^ 2 / 2 := by
  have h := LogdetLean.sq_le_neg_two_mul_add_log_one_sub hx0 hx1
  linarith

/-- A positive-semidefinite contraction has eigenvalues at most one. -/
theorem eigenvalues_le_one_of_one_sub_posSemidef_h19
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.PosSemidef)
    (hcomp : (1 - A).PosSemidef) (i : n) :
    hA.isHermitian.eigenvalues i ≤ 1 := by
  have hAle : A ≤ (1 : Matrix n n ℂ) := by
    simpa only [Matrix.le_iff] using hcomp
  have hspectral : ∀ x ∈ spectrum ℝ A, x ≤ (1 : ℝ) :=
    (le_algebraMap_iff_spectrum_le (R := ℝ) (A := Matrix n n ℂ)
      (a := A) hA.isHermitian).mp hAle
  exact hspectral _ (by
    rw [hA.isHermitian.spectrum_real_eq_range_eigenvalues]
    exact ⟨i, rfl⟩)

/-- The real trace of the square of a Hermitian complex matrix is the sum of
the squares of its real eigenvalues. -/
theorem trace_mul_self_re_eq_sum_eigenvalues_sq_h19
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    (Matrix.trace (A * A)).re =
      ∑ i : n, (hA.eigenvalues i) ^ 2 := by
  have hpow :
      Matrix.trace (A ^ 2) =
        ∑ i : n, (((hA.eigenvalues i : ℝ) : ℂ) ^ 2) := by
    conv_lhs => rw [hA.spectral_theorem]
    rw [← map_pow]
    rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
      Unitary.coe_star_mul_self, one_mul]
    rw [Matrix.diagonal_pow, Matrix.trace_diagonal]
    rfl
  have hAA : A * A = A ^ 2 := by noncomm_ring
  rw [hAA, hpow, Complex.re_sum]
  norm_cast

/-- Second-order log-determinant bound for a complex positive-semidefinite
contraction.  Strict positivity of the real determinant excludes the boundary
eigenvalue `1`, so the scalar logarithmic bound can be summed spectrally. -/
theorem log_det_one_sub_le_neg_trace_sub_half_trace_sq_h19
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.PosSemidef)
    (hcomp : (1 - A).PosSemidef)
    (hdet : 0 < (Matrix.det (1 - A)).re) :
    Real.log ((Matrix.det (1 - A)).re) ≤
      -(Matrix.trace A).re - (Matrix.trace (A * A)).re / 2 := by
  let hH : A.IsHermitian := hA.isHermitian
  have hdetComplex :
      Matrix.det ((1 : Matrix n n ℂ) - A) =
        (((∏ i : n, (1 - hH.eigenvalues i)) : ℝ) : ℂ) := by
    simpa [hH] using
      det_one_sub_smul_hermitian_eq_prod_eigenvalues A hH (1 : ℂ)
  have hdetReal :
      (Matrix.det (1 - A)).re = ∏ i : n, (1 - hH.eigenvalues i) := by
    simpa only [Complex.ofReal_re] using congrArg Complex.re hdetComplex
  have hfactorNonneg (i : n) : 0 ≤ 1 - hH.eigenvalues i := by
    exact sub_nonneg.mpr
      (eigenvalues_le_one_of_one_sub_posSemidef_h19 A hA hcomp i)
  have hprodPos : 0 < ∏ i : n, (1 - hH.eigenvalues i) := by
    rw [← hdetReal]
    exact hdet
  have hfactorNe (i : n) : 1 - hH.eigenvalues i ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mp hprodPos.ne' i (Finset.mem_univ i)
  have hfactorPos (i : n) : 0 < 1 - hH.eigenvalues i := by
    exact lt_of_le_of_ne (hfactorNonneg i) (Ne.symm (hfactorNe i))
  have heigenNonneg (i : n) : 0 ≤ hH.eigenvalues i :=
    hA.eigenvalues_nonneg i
  have heigenLt (i : n) : hH.eigenvalues i < 1 := by
    linarith [hfactorPos i]
  have htrace : (Matrix.trace A).re = ∑ i : n, hH.eigenvalues i := by
    rw [hH.trace_eq_sum_eigenvalues, Complex.re_sum]
    simp
  have htraceSq :
      (Matrix.trace (A * A)).re = ∑ i : n, (hH.eigenvalues i) ^ 2 :=
    trace_mul_self_re_eq_sum_eigenvalues_sq_h19 A hH
  rw [hdetReal, Real.log_prod (fun i _hi ↦ hfactorNe i), htrace, htraceSq]
  calc
    ∑ i : n, Real.log (1 - hH.eigenvalues i) ≤
        ∑ i : n, (-hH.eigenvalues i - (hH.eigenvalues i) ^ 2 / 2) := by
      exact Finset.sum_le_sum fun i _hi ↦
        log_one_sub_le_neg_sub_half_sq_h19
          (heigenNonneg i) (heigenLt i)
    _ = -(∑ i : n, hH.eigenvalues i) -
          (∑ i : n, (hH.eigenvalues i) ^ 2) / 2 := by
      rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
      simp only [Finset.sum_div]

end

end LogdetLean.GramHafnian.UltimateHiding.Sparse
