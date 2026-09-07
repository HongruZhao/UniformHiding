import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16DirectGaussGreenReduction
import Mathlib.Tactic

/-!
# Compact containment of the COE coordinate support

Positive definiteness of `I - Cᴴ C` forces every independent symmetric
coordinate to have norm strictly below one.  This supplies the fixed compact
ambient box needed for lower-jet envelopes and boundary-layer cutoffs.
-/

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open scoped ComplexOrder BigOperators

theorem h16COECoordinate_norm_lt_one_of_support
    {N : ℕ} {x : ComplexSymmetricCoordinates N}
    (hx : coeCornerSupport (complexSymmetricMatrixOfCoordinates x)) :
    ‖x‖ < 1 := by
  rw [pi_norm_lt_iff (by norm_num : (0 : ℝ) < 1)]
  intro ij
  let C := complexSymmetricMatrixOfCoordinates x
  have hdiag := hx.diag_pos (i := ij.1.2)
  have hdiagReal := (RCLike.lt_iff_re_im.mp hdiag).1
  have hsum :
      (∑ k : Fin N, Complex.normSq (C k ij.1.2)) < 1 := by
    simpa [Matrix.sub_apply, Matrix.one_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Complex.star_def,
      ← Complex.normSq_eq_conj_mul_self] using hdiagReal
  have hterm : Complex.normSq (C ij.1.1 ij.1.2) ≤
      ∑ k : Fin N, Complex.normSq (C k ij.1.2) := by
    exact Finset.single_le_sum
      (fun k _ ↦ Complex.normSq_nonneg (C k ij.1.2))
      (Finset.mem_univ ij.1.1)
  have hsq : Complex.normSq (x ij) < 1 := by
    have hentry : C ij.1.1 ij.1.2 = x ij := by
      simp [C, complexSymmetricMatrixOfCoordinates, ij.2]
    rw [← hentry]
    exact hterm.trans_lt hsum
  rw [Complex.normSq_eq_norm_sq] at hsq
  nlinarith [norm_nonneg (x ij)]

theorem h16COECoordinateSupport_subset_closedBall :
    {x : ComplexSymmetricCoordinates N |
      coeCornerSupport (complexSymmetricMatrixOfCoordinates x)} ⊆
      Metric.closedBall 0 1 := by
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (h16COECoordinate_norm_lt_one_of_support hx).le

theorem isCompact_h16COECoordinateSupport_closedBall (N : ℕ) :
    IsCompact (Metric.closedBall
      (0 : ComplexSymmetricCoordinates N) 1) :=
  isCompact_closedBall _ _

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
