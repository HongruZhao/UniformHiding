import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H7LineIdentifications
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H7RankOneScalar

/-!
# CONDITIONAL rank-one line closure for H7

This module isolates the sole remaining matrix-algebra input on a rank-one
line: the local determinant-ratio identity.  From that explicit parameter it
derives the literal likelihood identity and the exact cubic score.  It is
CONDITIONAL and is not an H7 proof.
-/

open Function
open scoped Matrix Topology

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- **CONDITIONAL.** The Jacobian and `rpow` algebra turn the local
rank-one determinant lemma into the literal rank-one likelihood core. -/
theorem h16CoordinateLikelihoodCore_rankOne_eventuallyEq_CONDITIONAL
    {N K : ℕ} (v : ComplexUnitSphere N) (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A))
    (hdet :
      (fun t : ℝ =>
        h16GeneralCOEInverseDeterminant K
            (t • complexRankOneProjection v) A /
          concreteCOEBaseDeterminant K A) =ᶠ[nhds 0]
      (fun t : ℝ =>
        Real.exp (-4 * t) * concreteRankOneLikelihoodBracket K v t A)) :
    (fun t : ℝ => h16CoordinateLikelihoodCore K A
      (t • concreteMatrixRealCoordinates (complexRankOneProjection v))) =ᶠ[nhds 0]
    (fun t : ℝ => concreteRankOneLikelihoodCore K v t A) := by
  have hbase : concreteCOEBaseDeterminant K A ≠ 0 :=
    ((RCLike.lt_iff_re_im.mp hsupport.det_pos).1).ne'
  have hbracketPos : ∀ᶠ t in nhds 0,
      0 < concreteRankOneLikelihoodBracket K v t A := by
    have hcont : ContinuousAt
        (fun t : ℝ => concreteRankOneLikelihoodBracket K v t A) 0 := by
      unfold concreteRankOneLikelihoodBracket
      fun_prop
    exact continuousAt_const.eventually_lt hcont (by simp)
  filter_upwards [hdet, hbracketPos] with t hdet_t hB
  rw [h16CoordinateLikelihoodCore_matrix_line]
  unfold h16GeneralCOELikelihoodCore
  rw [if_neg hbase, hdet_t]
  have htrace :
      (Matrix.trace (t • complexRankOneProjection v)).re = t := by
    change (Matrix.trace (((t : ℝ) : ℂ) • complexRankOneProjection v)).re = t
    rw [Matrix.trace_smul, trace_complexRankOneProjection]
    simp
  rw [htrace]
  unfold concreteRankOneLikelihoodCore
  let p : ℝ := coeCornerDensityExponent N K
  let d : ℝ := (K : ℝ) - (N : ℝ)
  change Real.exp (-2 * ((N : ℝ) + 1) * t) *
      (Real.exp (-4 * t) * concreteRankOneLikelihoodBracket K v t A) ^ p =
    Real.exp (2 * t) ^ (-d) *
      concreteRankOneLikelihoodBracket K v t A ^ p
  rw [Real.rpow_def_of_pos
      (mul_pos (Real.exp_pos _) hB),
    Real.rpow_def_of_pos (Real.exp_pos _),
    Real.rpow_def_of_pos hB,
    Real.log_mul (Real.exp_ne_zero _) hB.ne',
    Real.log_exp, Real.log_exp,
    ← Real.exp_add, ← Real.exp_add]
  congr 1
  unfold p d coeCornerDensityExponent
  ring

/-- **CONDITIONAL.** Once the local determinant-ratio lemma is supplied, the
rank-one diagonal field of H7 is kernel-derived from the literal likelihood. -/
theorem h16CoordinateLikelihoodCore_rankOne_iteratedDeriv_three_CONDITIONAL
    {N K : ℕ} (v : ComplexUnitSphere N) (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A))
    (hdet :
      (fun t : ℝ =>
        h16GeneralCOEInverseDeterminant K
            (t • complexRankOneProjection v) A /
          concreteCOEBaseDeterminant K A) =ᶠ[nhds 0]
      (fun t : ℝ =>
        Real.exp (-4 * t) * concreteRankOneLikelihoodBracket K v t A)) :
    iteratedDeriv 3
        (fun t : ℝ => h16CoordinateLikelihoodCore K A
          (t • concreteMatrixRealCoordinates (complexRankOneProjection v))) 0 =
      concreteRankOneDensityScoreThree N K v A := by
  rw [(h16CoordinateLikelihoodCore_rankOne_eventuallyEq_CONDITIONAL
    v A hsupport hdet).iteratedDeriv_eq 3]
  exact concreteRankOneLikelihoodCore_iteratedDeriv_three_eq_score v A

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
