import A2.TakagiAngularCoordinates
import A2.TakagiOrbit

open scoped Matrix

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

abbrev TakagiCayleyOpenUnitary (N : ℕ) :=
  {U : Matrix.unitaryGroup (Fin N) ℂ // IsUnit ((U : Matrix (Fin N) (Fin N) ℂ) + 1)}

def takagiAngularCayley {N : ℕ} (a : TakagiAngularCoordinates N) :
    Matrix.unitaryGroup (Fin N) ℂ :=
  takagiCayleyUnitary (takagiAngularSkewEquiv N a)
    (show ((takagiAngularSkewEquiv N a) : Matrix (Fin N) (Fin N) ℂ).conjTranspose =
      -(takagiAngularSkewEquiv N a) from (takagiAngularSkewEquiv N a).property)

def takagiAngularCayleyEquiv (N : ℕ) :
    TakagiAngularCoordinates N ≃ TakagiCayleyOpenUnitary N where
  toFun a := by
    let H : Matrix (Fin N) (Fin N) ℂ := takagiAngularSkewEquiv N a
    have hH : H.conjTranspose = -H := (takagiAngularSkewEquiv N a).property
    refine ⟨takagiAngularCayley a, ?_⟩
    change IsUnit (takagiCayley H + 1)
    exact isUnit_takagiCayley_add_one H hH
  invFun U := takagiSkewAngularCoordinates (takagiCayleyInverse
    (U.val : Matrix (Fin N) (Fin N) ℂ))
  left_inv a := by
    change takagiSkewAngularCoordinates (takagiCayleyInverse
      (takagiCayley (takagiSkewMatrix (takagiAngularEmbed a)))) = a
    rw [takagiCayleyInverse_takagiCayley _ (takagiSkewMatrix_skewHermitian _)]
    exact takagiSkewAngularCoordinates_skewMatrix a
  right_inv U := by
    apply Subtype.ext
    apply Subtype.ext
    change takagiCayley (takagiSkewMatrix (takagiAngularEmbed
      (takagiSkewAngularCoordinates (takagiCayleyInverse
        (U.val : Matrix (Fin N) (Fin N) ℂ))))) = (U.val : Matrix (Fin N) (Fin N) ℂ)
    rw [takagiSkewMatrix_angularCoordinates _
      (takagiCayleyInverse_skewHermitian U.val U.property)]
    exact takagiCayley_takagiCayleyInverse U.val U.property

theorem continuous_takagiSkewAngularCoordinates (N : ℕ) :
    Continuous (@takagiSkewAngularCoordinates N) := by
  apply continuous_pi
  intro p
  by_cases hb : p.val.2 = 0
  · simp only [takagiSkewAngularCoordinates, hb, if_true]
    exact Complex.continuous_re.comp
      (show Continuous (fun H : Matrix (Fin N) (Fin N) ℂ => H p.val.1.val.1 p.val.1.val.2) from by fun_prop)
  · simp only [takagiSkewAngularCoordinates, hb, if_false]
    exact Complex.continuous_im.comp
      (show Continuous (fun H : Matrix (Fin N) (Fin N) ℂ => H p.val.1.val.1 p.val.1.val.2) from by fun_prop)

theorem continuousAt_matrix_inverse_complex {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ)
    (hA : IsUnit A) : ContinuousAt (fun B : Matrix (Fin N) (Fin N) ℂ => B⁻¹) A := by
  have hd : A.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp hA).ne_zero
  exact continuousAt_matrix_inv A (by
    simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ hd)

theorem continuous_takagiAngularCayley (N : ℕ) :
    Continuous (@takagiAngularCayley N) := by
  apply Continuous.subtype_mk
  let h : TakagiAngularCoordinates N → Matrix (Fin N) (Fin N) ℂ := fun a =>
    takagiAngularSkewEquiv N a
  have hh : Continuous h :=
    continuous_subtype_val.comp (takagiAngularSkewEquiv N).toContinuousLinearEquiv.continuous
  have hi : Continuous (fun a => (1 - h a)⁻¹) := by
    apply continuous_iff_continuousAt.mpr
    intro a
    exact (continuousAt_matrix_inverse_complex _
      (isUnit_one_sub_skewHermitian (h a)
        (show (h a).conjTranspose = -h a from (takagiAngularSkewEquiv N a).property))).comp
          (f := fun b : TakagiAngularCoordinates N => 1 - h b)
          (continuous_const.sub hh).continuousAt
  exact (continuous_const.add hh).matrix_mul hi

theorem continuous_takagiAngularCayleyEquiv_symm (N : ℕ) :
    Continuous (takagiAngularCayleyEquiv N).symm := by
  apply (continuous_takagiSkewAngularCoordinates N).comp
  have hu : Continuous (fun U : TakagiCayleyOpenUnitary N =>
      (U.val : Matrix (Fin N) (Fin N) ℂ)) :=
    continuous_subtype_val.comp continuous_subtype_val
  have hi : Continuous (fun U : TakagiCayleyOpenUnitary N =>
      ((U.val : Matrix (Fin N) (Fin N) ℂ) + 1)⁻¹) := by
    apply continuous_iff_continuousAt.mpr
    intro U
    exact (continuousAt_matrix_inverse_complex _ U.property).comp
      (f := fun V : TakagiCayleyOpenUnitary N => (V.val : Matrix (Fin N) (Fin N) ℂ) + 1)
      (hu.add continuous_const).continuousAt
  exact (hu.sub continuous_const).matrix_mul hi

def takagiAngularCayleyHomeomorph (N : ℕ) :
    TakagiAngularCoordinates N ≃ₜ TakagiCayleyOpenUnitary N where
  toEquiv := takagiAngularCayleyEquiv N
  continuous_toFun := by
    exact (continuous_takagiAngularCayley N).subtype_mk _
  continuous_invFun := continuous_takagiAngularCayleyEquiv_symm N

def takagiCayleyOrbitChart {N : ℕ} (U : Matrix.unitaryGroup (Fin N) ℂ)
    (x : TakagiRealCoordinates N) : TakagiRealCoordinates N :=
  let p := takagiAngularRadialCoordinatesEquiv N x
  takagiRealOrbitCoordinates (U * takagiAngularCayley p.1) p.2

theorem takagiAngularCayley_injective (N : ℕ) :
    Function.Injective (@takagiAngularCayley N) := by
  intro a b hab
  apply (takagiAngularCayleyEquiv N).injective
  exact Subtype.ext hab

theorem takagiCayleyOpenUnitary_isOpen (N : ℕ) :
    IsOpen {U : Matrix.unitaryGroup (Fin N) ℂ |
      IsUnit ((U : Matrix (Fin N) (Fin N) ℂ) + 1)} := by
  have hc : Continuous (fun U : Matrix.unitaryGroup (Fin N) ℂ =>
      ((U : Matrix (Fin N) (Fin N) ℂ) + 1).det) :=
    (continuous_subtype_val.add continuous_const).matrix_det
  convert ((isClosed_singleton : IsClosed ({0} : Set ℂ)).preimage hc).isOpen_compl using 1
  ext U
  simp [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]

theorem takagiAngularCayley_isOpenMap (N : ℕ) : IsOpenMap (@takagiAngularCayley N) := by
  have h := (takagiCayleyOpenUnitary_isOpen N).isOpenMap_subtype_val.comp
    (takagiAngularCayleyHomeomorph N).isOpenMap
  exact h

theorem takagiAngularCayley_zero (N : ℕ) :
    takagiAngularCayley (0 : TakagiAngularCoordinates N) = 1 := by
  apply Subtype.ext
  change takagiCayley (((takagiAngularSkewEquiv N) 0) : Matrix (Fin N) (Fin N) ℂ) = 1
  rw [map_zero]
  simp [takagiCayley]

theorem takagiAngularCayley_ball_isOpen (N : ℕ) (r : ℝ) :
    IsOpen ((@takagiAngularCayley N) '' Metric.ball 0 r) :=
  takagiAngularCayley_isOpenMap N _ Metric.isOpen_ball

theorem one_mem_takagiAngularCayley_ball (N : ℕ) (r : ℝ) (hr : 0 < r) :
    (1 : Matrix.unitaryGroup (Fin N) ℂ) ∈ (@takagiAngularCayley N) '' Metric.ball 0 r := by
  refine ⟨0, ?_, takagiAngularCayley_zero N⟩
  simpa using hr

def takagiCayleyAngularDensity {N : ℕ} (a : TakagiAngularCoordinates N) : ℝ :=
  |LinearMap.det (takagiCayleyAngularCoordinateEquiv a).toLinearMap|

theorem takagiCayleyAngularDensity_pos {N : ℕ} (a : TakagiAngularCoordinates N) :
    0 < takagiCayleyAngularDensity a :=
  abs_pos.mpr (takagiCayleyAngularCoordinateEquiv_det_ne_zero a)

theorem continuous_takagiCayleyAngularDensity (N : ℕ) :
    Continuous (@takagiCayleyAngularDensity N) := by
  let H : TakagiAngularCoordinates N → Matrix (Fin N) (Fin N) ℂ := fun a =>
    takagiAngularSkewEquiv N a
  have hH : Continuous H :=
    continuous_subtype_val.comp (takagiAngularSkewEquiv N).toContinuousLinearEquiv.continuous
  have hp : Continuous (fun a => (1 + H a)⁻¹) := by
    apply continuous_iff_continuousAt.mpr
    intro a
    exact (continuousAt_matrix_inverse_complex _ (isUnit_one_add_skewHermitian (H a)
      (show (H a).conjTranspose = -H a from (takagiAngularSkewEquiv N a).property))).comp
      (f := fun a : TakagiAngularCoordinates N => 1 + H a)
      (continuous_const.add hH).continuousAt
  have hm : Continuous (fun a => (1 - H a)⁻¹) := by
    apply continuous_iff_continuousAt.mpr
    intro a
    exact (continuousAt_matrix_inverse_complex _ (isUnit_one_sub_skewHermitian (H a)
      (show (H a).conjTranspose = -H a from (takagiAngularSkewEquiv N a).property))).comp
      (f := fun a : TakagiAngularCoordinates N => 1 - H a)
      (continuous_const.sub hH).continuousAt
  have hmat : Continuous (fun a : TakagiAngularCoordinates N => LinearMap.toMatrix'
      (takagiCayleyAngularCoordinateEquiv a).toLinearMap) := by
    apply continuous_pi
    intro p
    apply continuous_pi
    intro q
    change Continuous (fun a =>
      takagiSkewAngularCoordinates (takagiCayleyAngularTangent (H a)
        (takagiAngularSkewEquiv N (Pi.single q 1))) p)
    have hc : Continuous (fun a => takagiCayleyAngularTangent (H a)
        (takagiAngularSkewEquiv N (Pi.single q 1))) := by
      exact ((show Continuous (fun _ : TakagiAngularCoordinates N => (2 : ℝ)) from
        continuous_const).smul ((hp.matrix_mul continuous_const).matrix_mul hm))
    exact (continuous_apply p).comp ((continuous_takagiSkewAngularCoordinates N).comp hc)
  change Continuous (fun a => |LinearMap.det (takagiCayleyAngularCoordinateEquiv a).toLinearMap|)
  simp_rw [← LinearMap.det_toMatrix']
  exact hmat.matrix_det.abs

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
