import A2.TakagiChartDifferential
import A2.TakagiRadialSqrtDerivative

open A2Research
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

theorem contDiffAt_takagiCayleyOrbitChart {N : ℕ} {k : ℕ∞ω}
    (U : Matrix.unitaryGroup (Fin N) ℂ) (x : TakagiRealCoordinates N)
    (hpos : ∀ i, 0 < (takagiAngularRadialCoordinatesEquiv N x).2 i) :
    ContDiffAt ℝ k (takagiCayleyOrbitChart U) x := by
  let e := takagiAngularRadialLinearEquiv N
  let a : TakagiRealCoordinates N → TakagiAngularCoordinates N := fun y => (e y).1
  let r : TakagiRealCoordinates N → (Fin N → ℝ) := fun y => (e y).2
  have ha : ContDiff ℝ k a := contDiff_fst.comp e.toContinuousLinearEquiv.contDiff
  have hr : ContDiff ℝ k r := contDiff_snd.comp e.toContinuousLinearEquiv.contDiff
  let H : TakagiRealCoordinates N → Matrix (Fin N) (Fin N) ℂ :=
    fun y => takagiAngularSkewCLM N (a y)
  have hh : ContDiff ℝ k H := (takagiAngularSkewCLM N).contDiff.comp ha
  have hsk : (H x).conjTranspose = -H x :=
    (takagiAngularSkewEquiv N (a x)).property
  have hdet : (1 - H x).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (isUnit_one_sub_skewHermitian (H x) hsk)).ne_zero
  have hi : ContDiffAt ℝ k (fun y => (1 - H y)⁻¹) x :=
    contDiffAt_matrix_nonsing_inv (contDiffAt_const.sub hh.contDiffAt) hdet
  let V : TakagiRealCoordinates N → Matrix (Fin N) (Fin N) ℂ :=
    fun y => (U : Matrix (Fin N) (Fin N) ℂ) * takagiCayley (H y)
  have hv : ContDiffAt ℝ k V x :=
    contDiffAt_matrix_mul contDiffAt_const
      (contDiffAt_matrix_mul (contDiffAt_const.add hh.contDiffAt) hi)
  have hrt : ContDiffAt ℝ k (fun y => takagiRadialSqrtMatrix (r y)) x :=
    (contDiffAt_takagiRadialSqrtMatrix (r x) hpos).comp x hr.contDiffAt
  have hvt : ContDiffAt ℝ k (fun y => (V y).transpose) x := by
    refine contDiffAt_pi' fun i => contDiffAt_pi' fun j => ?_
    exact contDiffAt_pi.mp (contDiffAt_pi.mp hv j) i
  let M : TakagiRealCoordinates N → Matrix (Fin N) (Fin N) ℂ :=
    fun y => V y * takagiRadialSqrtMatrix (r y) * (V y).transpose
  have hm : ContDiffAt ℝ k M x := contDiffAt_matrix_mul (contDiffAt_matrix_mul hv hrt) hvt
  let Q : Matrix (Fin N) (Fin N) ℂ →L[ℝ] TakagiRealCoordinates N :=
    (takagiRealComplexCoordinatesEquiv N).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((symmetricCoordinateProjection N).restrictScalars ℝ).toContinuousLinearMap
  have hout := Q.contDiff.contDiffAt.comp x hm
  convert! hout using 1

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
