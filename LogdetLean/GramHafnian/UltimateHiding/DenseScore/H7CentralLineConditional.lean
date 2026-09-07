import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H7CentralScalar
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ConcreteCentralCubicDefinitions

/-!
# CONDITIONAL central-line closure for H7

This module isolates the three remaining trace-kernel jets of the literal
central log determinant.  From those explicit parameters it derives all
three logarithmic scores, the third density score, and the coordinate-line
identity.  It is CONDITIONAL and is not an H7 proof.
-/

open Function
open scoped Matrix Topology

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

private theorem h7Central_linear_jet_one (c : ℝ) :
    iteratedDeriv 1 (fun t : ℝ => c * t) 0 = c := by
  simpa [iteratedDeriv_id] using
    (iteratedDeriv_const_mul_field (x := (0 : ℝ)) (n := 1)
      c (id : ℝ → ℝ))

private theorem h7Central_linear_jet_two (c : ℝ) :
    iteratedDeriv 2 (fun t : ℝ => c * t) 0 = 0 := by
  simpa [iteratedDeriv_id] using
    (iteratedDeriv_const_mul_field (x := (0 : ℝ)) (n := 2)
      c (id : ℝ → ℝ))

private theorem h7Central_linear_jet_three (c : ℝ) :
    iteratedDeriv 3 (fun t : ℝ => c * t) 0 = 0 := by
  simpa [iteratedDeriv_id] using
    (iteratedDeriv_const_mul_field (x := (0 : ℝ)) (n := 3)
      c (id : ℝ → ℝ))

private theorem concreteCOEExponent_ne_zero_of_boundary
    {N K : ℕ} (hboundary : 2 * N + 8 ≤ K) :
    concreteCOEExponent N K ≠ 0 := by
  have hcast : (2 : ℝ) * (N : ℝ) + 1 < (K : ℝ) := by
    exact_mod_cast (show 2 * N + 1 < K by omega)
  unfold concreteCOEExponent
  linarith

/-- **CONDITIONAL.** The first central log-determinant trace jet gives the
literal first logarithmic score. -/
theorem h7CentralLogModel_jet_one_CONDITIONAL
    {N K : ℕ} (hboundary : 2 * N + 8 ≤ K)
    (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A))
    (hlogdetOne :
      iteratedDeriv 1 (h7CentralLogDeterminantRatio K A) 0 =
        4 * concreteCOETraceOne N K A / concreteCOEExponent N K) :
    iteratedDeriv 1 (h7CentralLogModel K A) 0 =
      concreteCentralLogScoreOne N K A := by
  have hc : concreteCOEExponent N K ≠ 0 :=
    concreteCOEExponent_ne_zero_of_boundary hboundary
  have hlog1 : ContDiffAt ℝ 1 (h7CentralLogDeterminantRatio K A) 0 :=
    (h7CentralLogDeterminantRatio_contDiffAt_three A hsupport).of_le
      (by norm_num)
  have hscaled1 : ContDiffAt ℝ 1
      (fun t => coeCornerDensityExponent N K *
        h7CentralLogDeterminantRatio K A t) 0 := by
    simpa only [smul_eq_mul] using
      hlog1.const_smul (coeCornerDensityExponent N K)
  rw [show h7CentralLogModel K A =
      (fun t : ℝ => (-2 * (N : ℝ) * ((N : ℝ) + 1)) * t) +
        (fun t => coeCornerDensityExponent N K *
          h7CentralLogDeterminantRatio K A t) by rfl]
  rw [iteratedDeriv_add (by fun_prop) hscaled1]
  rw [h7Central_linear_jet_one, iteratedDeriv_const_mul_field, hlogdetOne]
  unfold concreteCentralLogScoreOne coeCornerDensityExponent
  field_simp [hc]
  unfold concreteCOEExponent
  ring

/-- **CONDITIONAL.** The second central log-determinant trace jet gives the
literal second logarithmic score. -/
theorem h7CentralLogModel_jet_two_CONDITIONAL
    {N K : ℕ} (hboundary : 2 * N + 8 ≤ K)
    (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A))
    (hlogdetTwo :
      iteratedDeriv 2 (h7CentralLogDeterminantRatio K A) 0 =
        -16 * (concreteCOETraceOne N K A / concreteCOEExponent N K +
          concreteCOETraceTwo N K A / concreteCOEExponent N K ^ 2)) :
    iteratedDeriv 2 (h7CentralLogModel K A) 0 =
      concreteCentralLogScoreTwo N K A := by
  have hc : concreteCOEExponent N K ≠ 0 :=
    concreteCOEExponent_ne_zero_of_boundary hboundary
  have hlog2 : ContDiffAt ℝ 2 (h7CentralLogDeterminantRatio K A) 0 :=
    (h7CentralLogDeterminantRatio_contDiffAt_three A hsupport).of_le
      (by norm_num)
  have hscaled2 : ContDiffAt ℝ 2
      (fun t => coeCornerDensityExponent N K *
        h7CentralLogDeterminantRatio K A t) 0 := by
    simpa only [smul_eq_mul] using
      hlog2.const_smul (coeCornerDensityExponent N K)
  rw [show h7CentralLogModel K A =
      (fun t : ℝ => (-2 * (N : ℝ) * ((N : ℝ) + 1)) * t) +
        (fun t => coeCornerDensityExponent N K *
          h7CentralLogDeterminantRatio K A t) by rfl]
  rw [iteratedDeriv_add (by fun_prop) hscaled2]
  rw [h7Central_linear_jet_two, iteratedDeriv_const_mul_field, hlogdetTwo]
  unfold concreteCentralLogScoreTwo coeCornerDensityExponent
  field_simp [hc]
  unfold concreteCOEExponent
  ring

/-- **CONDITIONAL.** The third central log-determinant trace jet gives the
literal third logarithmic score. -/
theorem h7CentralLogModel_jet_three_CONDITIONAL
    {N K : ℕ} (hboundary : 2 * N + 8 ≤ K)
    (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A))
    (hlogdetThree :
      iteratedDeriv 3 (h7CentralLogDeterminantRatio K A) 0 =
        64 * (concreteCOETraceOne N K A / concreteCOEExponent N K +
          3 * concreteCOETraceTwo N K A / concreteCOEExponent N K ^ 2 +
          2 * concreteCOETraceThree N K A / concreteCOEExponent N K ^ 3)) :
    iteratedDeriv 3 (h7CentralLogModel K A) 0 =
      concreteCentralLogScoreThree N K A := by
  have hc : concreteCOEExponent N K ≠ 0 :=
    concreteCOEExponent_ne_zero_of_boundary hboundary
  have hscaled3 : ContDiffAt ℝ 3
      (fun t => coeCornerDensityExponent N K *
        h7CentralLogDeterminantRatio K A t) 0 := by
    simpa only [smul_eq_mul] using
      (h7CentralLogDeterminantRatio_contDiffAt_three A hsupport).const_smul
        (coeCornerDensityExponent N K)
  rw [show h7CentralLogModel K A =
      (fun t : ℝ => (-2 * (N : ℝ) * ((N : ℝ) + 1)) * t) +
        (fun t => coeCornerDensityExponent N K *
          h7CentralLogDeterminantRatio K A t) by rfl]
  rw [iteratedDeriv_add (by fun_prop) hscaled3]
  rw [h7Central_linear_jet_three, iteratedDeriv_const_mul_field, hlogdetThree]
  unfold concreteCentralLogScoreThree coeCornerDensityExponent
  field_simp [hc]
  unfold concreteCOEExponent
  ring

/-- **CONDITIONAL.** The three explicit trace-kernel jets determine the third
derivative of the literal central likelihood. -/
theorem h7CentralLikelihoodCore_iteratedDeriv_three_CONDITIONAL
    {N K : ℕ} (hboundary : 2 * N + 8 ≤ K)
    (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A))
    (hlogdetOne :
      iteratedDeriv 1 (h7CentralLogDeterminantRatio K A) 0 =
        4 * concreteCOETraceOne N K A / concreteCOEExponent N K)
    (hlogdetTwo :
      iteratedDeriv 2 (h7CentralLogDeterminantRatio K A) 0 =
        -16 * (concreteCOETraceOne N K A / concreteCOEExponent N K +
          concreteCOETraceTwo N K A / concreteCOEExponent N K ^ 2))
    (hlogdetThree :
      iteratedDeriv 3 (h7CentralLogDeterminantRatio K A) 0 =
        64 * (concreteCOETraceOne N K A / concreteCOEExponent N K +
          3 * concreteCOETraceTwo N K A / concreteCOEExponent N K ^ 2 +
          2 * concreteCOETraceThree N K A / concreteCOEExponent N K ^ 3)) :
    iteratedDeriv 3 (h7CentralLikelihoodCore K A) 0 =
      concreteCentralDensityScoreThree N K A := by
  rw [iteratedDeriv_three_eq_densityBell_log_of_contDiffAt_one
    (h7CentralLikelihoodCore K A)
    (h7CentralLikelihoodCore_contDiffAt_three A hsupport)
    (h7CentralLikelihoodCore_zero_on_support A hsupport)]
  rw [(h7CentralLikelihoodCore_log_eventuallyEq_model A hsupport).iteratedDeriv_eq 1,
    (h7CentralLikelihoodCore_log_eventuallyEq_model A hsupport).iteratedDeriv_eq 2,
    (h7CentralLikelihoodCore_log_eventuallyEq_model A hsupport).iteratedDeriv_eq 3]
  rw [h7CentralLogModel_jet_one_CONDITIONAL hboundary A hsupport hlogdetOne,
    h7CentralLogModel_jet_two_CONDITIONAL hboundary A hsupport hlogdetTwo,
    h7CentralLogModel_jet_three_CONDITIONAL hboundary A hsupport hlogdetThree]
  rfl

/-- **CONDITIONAL.** The explicit central trace-kernel jets identify the H7
coordinate likelihood on the identity line with its central cubic score. -/
theorem h16CoordinateLikelihoodCore_central_iteratedDeriv_three_CONDITIONAL
    {N K : ℕ} (hboundary : 2 * N + 8 ≤ K)
    (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A))
    (hlogdetOne :
      iteratedDeriv 1 (h7CentralLogDeterminantRatio K A) 0 =
        4 * concreteCOETraceOne N K A / concreteCOEExponent N K)
    (hlogdetTwo :
      iteratedDeriv 2 (h7CentralLogDeterminantRatio K A) 0 =
        -16 * (concreteCOETraceOne N K A / concreteCOEExponent N K +
          concreteCOETraceTwo N K A / concreteCOEExponent N K ^ 2))
    (hlogdetThree :
      iteratedDeriv 3 (h7CentralLogDeterminantRatio K A) 0 =
        64 * (concreteCOETraceOne N K A / concreteCOEExponent N K +
          3 * concreteCOETraceTwo N K A / concreteCOEExponent N K ^ 2 +
          2 * concreteCOETraceThree N K A / concreteCOEExponent N K ^ 3)) :
    iteratedDeriv 3
        (fun t : ℝ => h16CoordinateLikelihoodCore K A
          (t • concreteMatrixRealCoordinates (1 : ConcreteMatrixState N))) 0 =
      concreteCentralDensityScoreThree N K A := by
  rw [h16CoordinateLikelihoodCore_central_line]
  exact h7CentralLikelihoodCore_iteratedDeriv_three_CONDITIONAL
    hboundary A hsupport hlogdetOne hlogdetTwo hlogdetThree

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
