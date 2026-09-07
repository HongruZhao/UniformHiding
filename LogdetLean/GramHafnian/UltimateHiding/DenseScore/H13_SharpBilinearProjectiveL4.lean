import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H13_BilinearProjectiveL4
import Mathlib.Tactic

/-!
# Sharper linearization of the H13 bilinear projective L4 bound

The exact fourth-power estimate already gives the constant `sqrt 2` after
taking a square root.  This file retains that information with the rational
majorant `3/2`, improving the earlier convenient constant `2`.
-/

open MeasureTheory
open scoped ComplexOrder MatrixOrder

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- Rationally sharpened squared `L4` bound for the conjugate-bilinear
projective factor. -/
theorem lpNorm_conjugateBilinearPair_four_sq_le_three_halves_h13
    {N : ℕ} (hN : 1 ≤ N) (R : ConcreteMatrixState N)
    (hR : R.IsSymm) :
    lpNorm (fun v : ComplexUnitSphere N =>
      complexProjectiveConjugateBilinearPair v R) 4
        (complexUnitSphereProbabilityMeasure N) ^ 2 ≤
      (3 / 2 : ℝ) *
        (Matrix.trace (R * R.conjTranspose)).re / (N : ℝ) := by
  let x := lpNorm (fun v : ComplexUnitSphere N =>
    complexProjectiveConjugateBilinearPair v R) 4
      (complexUnitSphereProbabilityMeasure N)
  let t := (Matrix.trace (R * R.conjTranspose)).re
  let n : ℝ := N
  have hfour := lpNorm_conjugateBilinearPair_four_pow_four_le_h13
    hN R hR
  have hGram : (R * R.conjTranspose).PosSemidef :=
    Matrix.posSemidef_self_mul_conjTranspose R
  have ht : 0 ≤ t := by
    exact (Complex.nonneg_iff.mp hGram.trace_nonneg).1
  have hn : 0 < n := by
    dsimp only [n]
    exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hx : 0 ≤ x := lpNorm_nonneg
  change x ^ 2 ≤ (3 / 2 : ℝ) * t / n
  change x ^ 4 ≤ 2 * t ^ 2 / n ^ 2 at hfour
  have hrelax : 2 * t ^ 2 / n ^ 2 ≤
      ((3 / 2 : ℝ) * t / n) ^ 2 := by
    rw [div_pow]
    have hn2 : 0 < n ^ 2 := pow_pos hn 2
    apply (div_le_div_iff_of_pos_right hn2).2
    nlinarith [sq_nonneg t]
  have hsquare : (x ^ 2) ^ 2 ≤ ((3 / 2 : ℝ) * t / n) ^ 2 := by
    calc
      (x ^ 2) ^ 2 = x ^ 4 := by ring
      _ ≤ 2 * t ^ 2 / n ^ 2 := hfour
      _ ≤ ((3 / 2 : ℝ) * t / n) ^ 2 := hrelax
  have hrhs : 0 ≤ (3 / 2 : ℝ) * t / n := by positivity
  exact (sq_le_sq₀ (sq_nonneg x) hrhs).mp hsquare

/-- The conjugate-transpose bilinear factor has the same sharpened bound. -/
theorem lpNorm_transposeBilinearPair_conjTranspose_four_sq_le_three_halves_h13
    {N : ℕ} (hN : 1 ≤ N) (R : ConcreteMatrixState N)
    (hR : R.IsSymm) :
    lpNorm (fun v : ComplexUnitSphere N =>
      complexProjectiveTransposeBilinearPair v R.conjTranspose) 4
        (complexUnitSphereProbabilityMeasure N) ^ 2 ≤
      (3 / 2 : ℝ) *
        (Matrix.trace (R * R.conjTranspose)).re / (N : ℝ) := by
  have h := lpNorm_conjugateBilinearPair_four_sq_le_three_halves_h13
    hN R hR
  let f : ComplexUnitSphere N → ℂ := fun v =>
    complexProjectiveConjugateBilinearPair v R
  have heq : (fun v : ComplexUnitSphere N =>
      complexProjectiveTransposeBilinearPair v R.conjTranspose) = star f := by
    funext v
    exact complexProjectiveTransposeBilinearPair_conjTranspose_eq_star_h13 v R
  rw [heq]
  change lpNorm (star f) 4 (complexUnitSphereProbabilityMeasure N) ^ 2 ≤ _
  have hstar : lpNorm (star f) 4 (complexUnitSphereProbabilityMeasure N) =
      lpNorm f 4 (complexUnitSphereProbabilityMeasure N) := by
    have hfMeas : AEStronglyMeasurable f
        (complexUnitSphereProbabilityMeasure N) := by
      dsimp only [f]
      exact (measurable_complexProjectiveConjugateBilinearPair_h13 R).aestronglyMeasurable
    have hstarMeas : AEStronglyMeasurable (star f)
        (complexUnitSphereProbabilityMeasure N) := hfMeas.star
    calc
      lpNorm (star f) 4 (complexUnitSphereProbabilityMeasure N) =
          lpNorm (fun v => ‖(star f) v‖) 4
            (complexUnitSphereProbabilityMeasure N) :=
        (lpNorm_norm hstarMeas 4).symm
      _ = lpNorm (fun v => ‖f v‖) 4
          (complexUnitSphereProbabilityMeasure N) := by
        congr 1
        funext v
        simp
      _ = lpNorm f 4 (complexUnitSphereProbabilityMeasure N) :=
        lpNorm_norm hfMeas 4
  rw [hstar]
  simpa only [f] using h

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
