import A3.WishartBlockDeterminant

open scoped BigOperators

noncomputable section

namespace A3Research

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable {Z Y : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [FiniteDimensional ℝ Z] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [FiniteDimensional ℝ Y]

def wishartColumnMap (F : Y → Y) (R : Z → Y) (v : ℝ × (Z × Y)) : ℝ × (Z × Y) :=
  (v.1, ((Real.sqrt v.1) • v.2.1, F v.2.2 + R v.2.1))

def wishartColumnDerivative (p : ℝ) (z : Z)
    (F' : Y →L[ℝ] Y) (R' : Z →L[ℝ] Y) : ℝ × (Z × Y) →L[ℝ] ℝ × (Z × Y) :=
  let P : ℝ × (Z × Y) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ (Z × Y)
  let Zp : ℝ × (Z × Y) →L[ℝ] Z :=
    (ContinuousLinearMap.fst ℝ Z Y).comp (ContinuousLinearMap.snd ℝ ℝ (Z × Y))
  let Yp : ℝ × (Z × Y) →L[ℝ] Y :=
    (ContinuousLinearMap.snd ℝ Z Y).comp (ContinuousLinearMap.snd ℝ ℝ (Z × Y))
  P.prod (((Real.sqrt p) • Zp + ((1 / (2 * Real.sqrt p)) • P).smulRight z).prod
    (F'.comp Yp + R'.comp Zp))

/-- The actual differential of a squared-pivot Cholesky column. -/
theorem hasFDerivAt_wishartColumnMap {F : Y → Y} {R : Z → Y}
    (p : ℝ) (z : Z) (y : Y) (hp : 0 < p)
    (F' : Y →L[ℝ] Y) (R' : Z →L[ℝ] Y)
    (hF : HasFDerivAt F F' y) (hR : HasFDerivAt R R' z) :
    HasFDerivAt (wishartColumnMap F R) (wishartColumnDerivative p z F' R') (p, (z, y)) := by
  let P : ℝ × (Z × Y) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ (Z × Y)
  let Zp : ℝ × (Z × Y) →L[ℝ] Z :=
    (ContinuousLinearMap.fst ℝ Z Y).comp (ContinuousLinearMap.snd ℝ ℝ (Z × Y))
  let Yp : ℝ × (Z × Y) →L[ℝ] Y :=
    (ContinuousLinearMap.snd ℝ Z Y).comp (ContinuousLinearMap.snd ℝ ℝ (Z × Y))
  have hP := P.hasFDerivAt (x := (p, (z, y)))
  have hZ := Zp.hasFDerivAt (x := (p, (z, y)))
  have hY := Yp.hasFDerivAt (x := (p, (z, y)))
  have h := hP.prodMk (((hP.sqrt hp.ne').smul hZ).prodMk
    ((hF.comp (p, (z, y)) hY).add (hR.comp (p, (z, y)) hZ)))
  convert h using 1 <;> try rfl

/-- The strict-lower derivative blocks disappear from the Jacobian. -/
theorem det_wishartColumnDerivative (p : ℝ) (z : Z)
    (F' : Y →L[ℝ] Y) (R' : Z →L[ℝ] Y) :
    (wishartColumnDerivative p z F' R').toLinearMap.det =
      (Real.sqrt p) ^ Module.finrank ℝ Z * F'.toLinearMap.det := by
  have heq : (wishartColumnDerivative p z F' R').toLinearMap =
      wishartLowerBlockMap (LinearMap.id : ℝ →ₗ[ℝ] ℝ)
        ((LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight ((1 / (2 * Real.sqrt p)) • z, (0 : Y)))
        (wishartLowerBlockMap ((Real.sqrt p) • (LinearMap.id : Z →ₗ[ℝ] Z))
          R'.toLinearMap F'.toLinearMap) := by
    apply LinearMap.ext
    intro v
    simp [wishartColumnDerivative, wishartLowerBlockMap, smul_smul, mul_comm, add_comm]
  rw [heq]
  rw [det_wishartLowerBlockMap, det_wishartLowerBlockMap, LinearMap.det_smul]
  simp

end A3Research
