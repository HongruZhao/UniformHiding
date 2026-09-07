import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H7CentralLineGeometry
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H7ScalarBell

/-!
# Scalar Bell reduction on the H7 central line

This module rewrites the logarithm of the literal central likelihood as its
linear Jacobian term plus the normalized log determinant.  The remaining
trace-kernel jets are intentionally not assumed here.
-/

open Function
open scoped Matrix Topology

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- Explicit logarithmic model for the central likelihood. -/
def h7CentralLogModel {N : ℕ} (K : ℕ)
    (A : ConcreteMatrixState N) (t : ℝ) : ℝ :=
  (-2 * (N : ℝ) * ((N : ℝ) + 1)) * t +
    coeCornerDensityExponent N K * h7CentralLogDeterminantRatio K A t

/-- The normalized central determinant ratio is positive near the supported
base point. -/
theorem h7CentralDeterminantRatio_eventually_pos
    {N K : ℕ} (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    ∀ᶠ t in nhds 0,
      0 < h7CentralInverseDeterminant K A t /
        concreteCOEBaseDeterminant K A := by
  have hbase : concreteCOEBaseDeterminant K A ≠ 0 :=
    ((RCLike.lt_iff_re_im.mp hsupport.det_pos).1).ne'
  have hdet3 : ContDiffAt ℝ 3
      (h7CentralInverseDeterminant K A) 0 :=
    (h7CentralInverseDeterminant_contDiffAt_top A).of_le (by norm_num)
  have hcont : ContinuousAt
      (fun t : ℝ => h7CentralInverseDeterminant K A t /
        concreteCOEBaseDeterminant K A) 0 :=
    hdet3.continuousAt.div_const _
  apply continuousAt_const.eventually_lt hcont
  rw [h7CentralInverseDeterminant_zero, div_self hbase]
  norm_num

/-- Locally, the logarithm of the literal central likelihood is the explicit
Jacobian-plus-logdet model. -/
theorem h7CentralLikelihoodCore_log_eventuallyEq_model
    {N K : ℕ} (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    (fun t : ℝ => Real.log (h7CentralLikelihoodCore K A t)) =ᶠ[nhds 0]
      h7CentralLogModel K A := by
  have hbase : concreteCOEBaseDeterminant K A ≠ 0 :=
    ((RCLike.lt_iff_re_im.mp hsupport.det_pos).1).ne'
  filter_upwards [h7CentralDeterminantRatio_eventually_pos A hsupport]
    with t hratio
  unfold h7CentralLikelihoodCore
  rw [if_neg hbase]
  change Real.log
      (Real.exp (-2 * (N : ℝ) * ((N : ℝ) + 1) * t) *
        (h7CentralInverseDeterminant K A t /
          concreteCOEBaseDeterminant K A) ^
            (coeCornerDensityExponent N K)) =
    h7CentralLogModel K A t
  rw [Real.log_mul (Real.exp_ne_zero _)
      (ne_of_gt (Real.rpow_pos_of_pos hratio _)),
    Real.log_exp, Real.log_rpow hratio]
  unfold h7CentralLogModel h7CentralLogDeterminantRatio
  rfl

/-- The central logarithmic model is locally `C³`. -/
theorem h7CentralLogModel_contDiffAt_three
    {N K : ℕ} (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    ContDiffAt ℝ 3 (h7CentralLogModel K A) 0 := by
  unfold h7CentralLogModel
  exact (by fun_prop : ContDiffAt ℝ 3
      (fun t : ℝ => (-2 * (N : ℝ) * ((N : ℝ) + 1)) * t) 0).add
    ((h7CentralLogDeterminantRatio_contDiffAt_three A hsupport).const_smul
      (coeCornerDensityExponent N K))

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
