import A2.TakagiChartTangent

open scoped Matrix Matrix.Norms.Elementwise

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

def takagiChartAngularProjection (N : ℕ) :
    TakagiRealCoordinates N →L[ℝ] TakagiAngularCoordinates N :=
  ((LinearMap.fst ℝ (TakagiAngularCoordinates N) (Fin N → ℝ)).comp
    (takagiAngularRadialLinearEquiv N).toLinearMap).toContinuousLinearMap

def takagiChartRadialProjection (N : ℕ) :
    TakagiRealCoordinates N →L[ℝ] (Fin N → ℝ) :=
  ((LinearMap.snd ℝ (TakagiAngularCoordinates N) (Fin N → ℝ)).comp
    (takagiAngularRadialLinearEquiv N).toLinearMap).toContinuousLinearMap

def takagiMatrixTransposeCLM (N : ℕ) :
    Matrix (Fin N) (Fin N) ℂ →L[ℝ] Matrix (Fin N) (Fin N) ℂ :=
  ({ toFun := Matrix.transpose
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } :
    Matrix (Fin N) (Fin N) ℂ →ₗ[ℝ] Matrix (Fin N) (Fin N) ℂ).toContinuousLinearMap

def takagiMatrixRealCoordinatesCLM (N : ℕ) :
    Matrix (Fin N) (Fin N) ℂ →L[ℝ] TakagiRealCoordinates N :=
  (takagiRealComplexCoordinatesEquiv N).symm.toLinearMap.toContinuousLinearMap.comp
    ((A2Research.symmetricCoordinateProjection N).restrictScalars ℝ).toContinuousLinearMap

def takagiChartUnitaryMatrix {N : ℕ} (U : Matrix.unitaryGroup (Fin N) ℂ)
    (x : TakagiRealCoordinates N) : Matrix (Fin N) (Fin N) ℂ :=
  (U * takagiAngularCayley (takagiChartAngularProjection N x)).val

def takagiChartUnitaryMatrixDerivative {N : ℕ} (U : Matrix.unitaryGroup (Fin N) ℂ)
    (x : TakagiRealCoordinates N) :
    TakagiRealCoordinates N →L[ℝ] Matrix (Fin N) (Fin N) ℂ :=
  (mulLeftLinearMap (Fin N) ℝ U.val).toContinuousLinearMap.comp
    ((takagiAngularCayleyMatrixDerivative (takagiChartAngularProjection N x)).comp
      (takagiChartAngularProjection N))

theorem hasFDerivAt_takagiChartUnitaryMatrix {N : ℕ} (U : Matrix.unitaryGroup (Fin N) ℂ)
    (x : TakagiRealCoordinates N) :
    HasFDerivAt (takagiChartUnitaryMatrix U) (takagiChartUnitaryMatrixDerivative U x) x := by
  have ha := (hasFDerivAt_takagiAngularCayley (takagiChartAngularProjection N x)).comp x
    (takagiChartAngularProjection N).hasFDerivAt
  exact (mulLeftLinearMap (Fin N) ℝ U.val).toContinuousLinearMap.hasFDerivAt.comp x ha

def takagiCayleyOrbitMatrixDerivative {N : ℕ} (U : Matrix.unitaryGroup (Fin N) ℂ)
    (x : TakagiRealCoordinates N) :
    TakagiRealCoordinates N →L[ℝ] Matrix (Fin N) (Fin N) ℂ :=
  let V := takagiChartUnitaryMatrix U x
  let D := takagiRadialSqrtMatrix (takagiChartRadialProjection N x)
  let V' := takagiChartUnitaryMatrixDerivative U x
  let D' := (takagiRadialSqrtDerivative (takagiChartRadialProjection N x)).comp
    (takagiChartRadialProjection N)
  A2Research.matrixMulDerivative (V * D) V.transpose
    (A2Research.matrixMulDerivative V D V' D') ((takagiMatrixTransposeCLM N).comp V')

theorem hasFDerivAt_takagiCayleyOrbitMatrix {N : ℕ}
    (U : Matrix.unitaryGroup (Fin N) ℂ) (x : TakagiRealCoordinates N)
    (hpos : ∀ i, 0 < (takagiAngularRadialLinearEquiv N x).2 i) :
    HasFDerivAt (fun y => takagiOrbit (U * takagiAngularCayley (takagiChartAngularProjection N y))
      (takagiChartRadialProjection N y)) (takagiCayleyOrbitMatrixDerivative U x) x := by
  have hv := hasFDerivAt_takagiChartUnitaryMatrix U x
  have hd := (hasFDerivAt_takagiRadialSqrtMatrix (takagiChartRadialProjection N x) hpos).comp x
    (takagiChartRadialProjection N).hasFDerivAt
  have ht := (takagiMatrixTransposeCLM N).hasFDerivAt.comp x hv
  exact A2Research.hasFDerivAt_matrix_mul (A2Research.hasFDerivAt_matrix_mul hv hd) ht

theorem takagiChartUnitaryMatrixDerivative_source {N : ℕ}
    (U : Matrix.unitaryGroup (Fin N) ℂ) (x v : TakagiRealCoordinates N) :
    takagiChartUnitaryMatrixDerivative U x v = takagiChartUnitaryMatrix U x *
      takagiSkewMatrix (takagiCayleySourceDifferential (takagiChartAngularProjection N x) v) := by
  change U.val * takagiAngularCayleyMatrixDerivative (takagiChartAngularProjection N x)
    (takagiAngularRadialLinearEquiv N v).1 = _
  rw [takagiAngularCayleyMatrixDerivative_source]
  exact (Matrix.mul_assoc _ _ _).symm

theorem takagiCayleyOrbitMatrixDerivative_source {N : ℕ}
    (U : Matrix.unitaryGroup (Fin N) ℂ) (x v : TakagiRealCoordinates N) :
    takagiCayleyOrbitMatrixDerivative U x v =
      takagiChartUnitaryMatrix U x *
        takagiDiagonalOrbitTangent (takagiChartRadialProjection N x)
          (takagiCayleySourceDifferential (takagiChartAngularProjection N x) v) *
            (takagiChartUnitaryMatrix U x).transpose := by
  unfold takagiCayleyOrbitMatrixDerivative
  simp only [A2Research.matrixMulDerivative_apply, ContinuousLinearMap.comp_apply]
  rw [takagiChartUnitaryMatrixDerivative_source]
  have hrad : takagiRadialSqrtDerivative (takagiChartRadialProjection N x)
      (takagiChartRadialProjection N v) =
        takagiRadialMatrix (takagiChartRadialProjection N x)
          (takagiCayleySourceDifferential (takagiChartAngularProjection N x) v) :=
    takagiRadialSqrtDerivative_source (takagiChartRadialProjection N x)
      (takagiChartAngularProjection N x) v
  rw [hrad]
  change (takagiChartUnitaryMatrix U x *
      takagiSkewMatrix (takagiCayleySourceDifferential (takagiChartAngularProjection N x) v) *
        takagiRadialSqrtMatrix (takagiChartRadialProjection N x) +
      takagiChartUnitaryMatrix U x *
        takagiRadialMatrix (takagiChartRadialProjection N x)
          (takagiCayleySourceDifferential (takagiChartAngularProjection N x) v)) *
            (takagiChartUnitaryMatrix U x).transpose +
      (takagiChartUnitaryMatrix U x * takagiRadialSqrtMatrix (takagiChartRadialProjection N x)) *
        (takagiChartUnitaryMatrix U x *
          takagiSkewMatrix (takagiCayleySourceDifferential (takagiChartAngularProjection N x) v)).transpose = _
  rw [Matrix.transpose_mul]
  unfold takagiDiagonalOrbitTangent takagiRadialSqrtMatrix
  noncomm_ring

theorem takagiCayleyOrbitChartDerivative_eq_actual {N : ℕ}
    (U : Matrix.unitaryGroup (Fin N) ℂ) (x : TakagiRealCoordinates N) :
    (takagiMatrixRealCoordinatesCLM N).comp (takagiCayleyOrbitMatrixDerivative U x) =
      takagiCayleyOrbitChartDerivative U x := by
  apply ContinuousLinearMap.ext
  intro v
  rw [ContinuousLinearMap.comp_apply, takagiCayleyOrbitMatrixDerivative_source]
  let W := U * takagiAngularCayley (takagiChartAngularProjection N x)
  let lambda := takagiChartRadialProjection N x
  let z := takagiCayleySourceDifferential (takagiChartAngularProjection N x) v
  change (takagiRealComplexCoordinatesEquiv N).symm
      (A2Research.symmetricCoordinateProjection N
        (W.val * takagiDiagonalOrbitTangent lambda z * W.val.transpose)) =
    (takagiRealComplexCoordinatesEquiv N).symm
      (A2Research.unitaryCongruenceRepresentation N W
        (takagiRealComplexCoordinatesEquiv N (takagiDiagonalDifferential lambda z)))
  congr 1
  funext ij
  have hrec : complexSymmetricMatrixOfCoordinates
      (takagiRealComplexCoordinatesEquiv N (takagiDiagonalDifferential lambda z)) =
        takagiDiagonalOrbitTangent lambda z := takagiDiagonalOrbitTangent_reconstruct lambda z
  rw [A2Research.unitaryCongruenceRepresentation_apply, hrec]
  rfl

/-- The literal orbit chart has the factored derivative whose determinant was
computed in squared singular values. -/
theorem hasFDerivAt_takagiCayleyOrbitChart {N : ℕ}
    (U : Matrix.unitaryGroup (Fin N) ℂ) (x : TakagiRealCoordinates N)
    (hpos : ∀ i, 0 < (takagiAngularRadialLinearEquiv N x).2 i) :
    HasFDerivAt (takagiCayleyOrbitChart U) (takagiCayleyOrbitChartDerivative U x) x := by
  have h := (takagiMatrixRealCoordinatesCLM N).hasFDerivAt.comp x
    (hasFDerivAt_takagiCayleyOrbitMatrix U x hpos)
  rw [takagiCayleyOrbitChartDerivative_eq_actual] at h
  exact h

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
