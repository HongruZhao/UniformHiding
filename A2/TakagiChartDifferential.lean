import A2.TakagiCayleyDerivative
import A2.UnitaryCongruenceVolume

open scoped Matrix Matrix.Norms.Elementwise

noncomputable section

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

def takagiAngularRadialLinearEquiv (N : ℕ) :
    TakagiRealCoordinates N ≃ₗ[ℝ] TakagiAngularCoordinates N × (Fin N → ℝ) where
  toFun x := takagiAngularRadialCoordinatesEquiv N x
  invFun p := (takagiAngularRadialCoordinatesEquiv N).symm p
  left_inv := (takagiAngularRadialCoordinatesEquiv N).left_inv
  right_inv := (takagiAngularRadialCoordinatesEquiv N).right_inv
  map_add' x y := by
    apply Prod.ext <;> funext p <;> rfl
  map_smul' r x := by
    apply Prod.ext <;> funext p <;> rfl

def takagiCayleySourceDifferential {N : ℕ} (a : TakagiAngularCoordinates N) :
    TakagiRealCoordinates N →ₗ[ℝ] TakagiRealCoordinates N :=
  (takagiAngularRadialLinearEquiv N).symm.toLinearMap.comp
    (((takagiCayleyAngularCoordinateEquiv a).toLinearMap.prodMap (LinearMap.id :
      (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ))).comp (takagiAngularRadialLinearEquiv N).toLinearMap)

theorem takagiCayleySourceDifferential_det {N : ℕ} (a : TakagiAngularCoordinates N) :
    LinearMap.det (takagiCayleySourceDifferential a) =
      LinearMap.det (takagiCayleyAngularCoordinateEquiv a).toLinearMap := by
  have heq := LinearMap.det_conj
    ((takagiCayleyAngularCoordinateEquiv a).toLinearMap.prodMap
      (LinearMap.id : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ)))
    (takagiAngularRadialLinearEquiv N).symm
  simp only [LinearEquiv.symm_symm] at heq
  rw [takagiCayleySourceDifferential, heq]
  rw [LinearMap.det_prodMap, LinearMap.det_id, mul_one]

theorem takagiCayleySourceDifferential_split {N : ℕ} (a : TakagiAngularCoordinates N)
    (x : TakagiRealCoordinates N) :
    takagiAngularRadialLinearEquiv N (takagiCayleySourceDifferential a x) =
      (takagiCayleyAngularCoordinateEquiv a (takagiAngularRadialLinearEquiv N x).1,
        (takagiAngularRadialLinearEquiv N x).2) := by
  simp [takagiCayleySourceDifferential, LinearMap.prodMap_apply]

def takagiCayleyOrbitChartDerivative {N : ℕ} (U : Matrix.unitaryGroup (Fin N) ℂ)
    (x : TakagiRealCoordinates N) : TakagiRealCoordinates N →L[ℝ] TakagiRealCoordinates N :=
  let p := takagiAngularRadialLinearEquiv N x
  (A2Research.realCoordinateCongruenceLinearMap N (U * takagiAngularCayley p.1)).toContinuousLinearMap.comp
    ((takagiDiagonalDifferential p.2).toContinuousLinearMap.comp
      (takagiCayleySourceDifferential p.1).toContinuousLinearMap)

theorem abs_det_takagiCayleyOrbitChartDerivative {N : ℕ}
    (U : Matrix.unitaryGroup (Fin N) ℂ) (x : TakagiRealCoordinates N)
    (hpos : ∀ i, 0 < (takagiAngularRadialLinearEquiv N x).2 i) :
    |LinearMap.det (takagiCayleyOrbitChartDerivative U x).toLinearMap| =
      takagiCayleyAngularDensity (takagiAngularRadialLinearEquiv N x).1 *
        H6DensityTransform.vandermondeAbs N (takagiAngularRadialLinearEquiv N x).2 := by
  let p := takagiAngularRadialLinearEquiv N x
  change |LinearMap.det ((A2Research.realCoordinateCongruenceLinearMap N
      (U * takagiAngularCayley p.1)).comp
        ((takagiDiagonalDifferential p.2).comp (takagiCayleySourceDifferential p.1)))| = _
  rw [LinearMap.det_comp, LinearMap.det_comp, abs_mul, abs_mul,
    A2Research.abs_det_realCoordinateCongruenceLinearMap, one_mul,
    takagiCayleySourceDifferential_det]
  have hd : |LinearMap.det (takagiDiagonalDifferential p.2)| = H6DensityTransform.vandermondeAbs N p.2 := by
    rw [takagiDiagonalDifferential_det p.2 hpos]
    simp only [H6DensityTransform.vandermondeAbs, Finset.abs_prod, abs_sub_comm]
  rw [hd]
  exact mul_comm _ _

theorem det_takagiCayleyOrbitChartDerivative_ne_zero {N : ℕ}
    (U : Matrix.unitaryGroup (Fin N) ℂ) (x : TakagiRealCoordinates N)
    (hreg : IsRegularTakagiSpectrum (takagiAngularRadialLinearEquiv N x).2) :
    LinearMap.det (takagiCayleyOrbitChartDerivative U x).toLinearMap ≠ 0 := by
  rw [← abs_pos, abs_det_takagiCayleyOrbitChartDerivative U x hreg.1]
  apply mul_pos (takagiCayleyAngularDensity_pos _)
  unfold H6DensityTransform.vandermondeAbs
  apply Finset.prod_pos
  intro p hp
  have hp' : p.1 < p.2 := by simpa [H6DensityTransform.strictPairs] using hp
  apply abs_pos.mpr
  apply sub_ne_zero.mpr
  exact fun h => (ne_of_lt hp') (hreg.2 h)

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
