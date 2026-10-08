import A2.WeylIntegrationLiteralBridge
import A2.TakagiCayleyChart

open MeasureTheory Set Function

noncomputable section

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

theorem continuous_takagiAngularRadialCoordinatesEquiv (N : ℕ) :
    Continuous (takagiAngularRadialCoordinatesEquiv N) := by
  have hf : Continuous (fun x : TakagiRealCoordinates N ↦
      (takagiAngularRadialCoordinatesEquiv N x).1) := by
    apply continuous_pi
    intro p
    change Continuous (fun x : TakagiRealCoordinates N ↦ x p.val)
    exact continuous_apply p.val
  have hs : Continuous (fun x : TakagiRealCoordinates N ↦
      (takagiAngularRadialCoordinatesEquiv N x).2) := by
    apply continuous_pi
    intro i
    change Continuous (fun x : TakagiRealCoordinates N ↦ x (takagiRadialKey i))
    exact continuous_apply (takagiRadialKey i)
  exact hf.prodMk hs

theorem continuous_takagiOrbit (N : ℕ) :
    Continuous (fun z : Matrix.unitaryGroup (Fin N) ℂ × (Fin N → ℝ) ↦
      takagiOrbit z.1 z.2) := by
  let u : Matrix.unitaryGroup (Fin N) ℂ × (Fin N → ℝ) →
      Matrix (Fin N) (Fin N) ℂ := fun z ↦ z.1
  have hu : Continuous u := continuous_subtype_val.comp continuous_fst
  have hr : Continuous (fun z : Matrix.unitaryGroup (Fin N) ℂ × (Fin N → ℝ) ↦
      fun i ↦ (Real.sqrt (z.2 i) : ℂ)) := by
    apply continuous_pi
    intro i
    fun_prop
  exact (hu.matrix_mul hr.matrix_diagonal).matrix_mul hu.matrix_transpose

theorem continuous_takagiRealOrbitCoordinates (N : ℕ) :
    Continuous (fun z : Matrix.unitaryGroup (Fin N) ℂ × (Fin N → ℝ) ↦
      takagiRealOrbitCoordinates z.1 z.2) := by
  apply (takagiRealComplexCoordinatesEquiv N).symm.toContinuousLinearEquiv.continuous.comp
  apply continuous_pi
  intro ij
  exact (continuous_takagiOrbit N).matrix_elem ij.val.1 ij.val.2

/-- The actual bounded-atlas orbit map is globally measurable, including
nonpositive radii where smoothness is not asserted. -/
theorem continuous_takagiCayleyOrbitChart {N : ℕ}
    (U : Matrix.unitaryGroup (Fin N) ℂ) : Continuous (takagiCayleyOrbitChart U) := by
  let e := takagiAngularRadialCoordinatesEquiv N
  have he : Continuous e := continuous_takagiAngularRadialCoordinatesEquiv N
  have hang : Continuous (fun x : TakagiRealCoordinates N ↦ U * takagiAngularCayley (e x).1) :=
    continuous_const.mul ((continuous_takagiAngularCayley N).comp (continuous_fst.comp he))
  change Continuous (fun x : TakagiRealCoordinates N ↦
    takagiRealOrbitCoordinates (U * takagiAngularCayley (e x).1) (e x).2)
  have hpair : Continuous (fun x : TakagiRealCoordinates N ↦
      (U * takagiAngularCayley (e x).1, (e x).2)) :=
    hang.prodMk (continuous_snd.comp he)
  have hc := (continuous_takagiRealOrbitCoordinates N).comp
    (f := fun x : TakagiRealCoordinates N ↦ (U * takagiAngularCayley (e x).1, (e x).2)) hpair
  exact hc

theorem measurable_takagiCayleyOrbitChart {N : ℕ}
    (U : Matrix.unitaryGroup (Fin N) ℂ) : Measurable (takagiCayleyOrbitChart U) :=
  (continuous_takagiCayleyOrbitChart U).measurable

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
