import A3.HermitianOrbitChartAlgebra

open scoped Matrix Matrix.Norms.Elementwise ContDiff

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

namespace A3Research

variable {n : ℕ} {K : Type*} [RCLike K]

def hermitianChartRadialProjection (n : ℕ) (K : Type*) [RCLike K] :
    HermitianCoordinates n K →L[ℝ] (Fin n → ℝ) :=
  (LinearMap.fst ℝ (Fin n → ℝ) (HermitianCoordinateIndex n → K)).toContinuousLinearMap

def hermitianChartAngularProjection (n : ℕ) (K : Type*) [RCLike K] :
    HermitianCoordinates n K →L[ℝ] (HermitianCoordinateIndex n → K) :=
  (LinearMap.snd ℝ (Fin n → ℝ) (HermitianCoordinateIndex n → K)).toContinuousLinearMap

def hermitianRealDiagonalLinearMap (n : ℕ) (K : Type*) [RCLike K] :
    (Fin n → ℝ) →ₗ[ℝ] Matrix (Fin n) (Fin n) K where
  toFun := fun r ↦ Matrix.diagonal (fun i ↦ (r i : K))
  map_add' := fun _ _ ↦ by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.diagonal_apply, hij]
  map_smul' := fun _ _ ↦ by
    ext i j
    simp [Matrix.diagonal_apply, RCLike.real_smul_eq_coe_mul]

def hermitianMatrixConjTransposeCLM (n : ℕ) (K : Type*) [RCLike K] :
    Matrix (Fin n) (Fin n) K →L[ℝ] Matrix (Fin n) (Fin n) K :=
  ({ toFun := Matrix.conjTranspose
     map_add' := fun _ _ ↦ Matrix.conjTranspose_add _ _
     map_smul' := fun _ _ ↦ by simp [Matrix.conjTranspose_smul] } :
      Matrix (Fin n) (Fin n) K →ₗ[ℝ] Matrix (Fin n) (Fin n) K).toContinuousLinearMap

def hermitianChartUnitaryMatrix (U : Matrix.unitaryGroup (Fin n) K)
    (x : HermitianCoordinates n K) : Matrix (Fin n) (Fin n) K :=
  (U * hermitianAngularCayley x.2).val

def hermitianChartUnitaryMatrixDerivative (U : Matrix.unitaryGroup (Fin n) K)
    (x : HermitianCoordinates n K) :
    HermitianCoordinates n K →L[ℝ] Matrix (Fin n) (Fin n) K :=
  (mulLeftLinearMap (Fin n) ℝ U.val).toContinuousLinearMap.comp
    ((hermitianAngularCayleyMatrixDerivative x.2).comp (hermitianChartAngularProjection n K))

theorem hasFDerivAt_hermitianChartUnitaryMatrix (U : Matrix.unitaryGroup (Fin n) K)
    (x : HermitianCoordinates n K) :
    HasFDerivAt (hermitianChartUnitaryMatrix U) (hermitianChartUnitaryMatrixDerivative U x) x := by
  have ha := (hasFDerivAt_hermitianAngularCayleyMatrix x.2).comp x
    (hermitianChartAngularProjection n K).hasFDerivAt
  exact (mulLeftLinearMap (Fin n) ℝ U.val).toContinuousLinearMap.hasFDerivAt.comp x ha

def hermitianCayleyOrbitMatrixDerivative (U : Matrix.unitaryGroup (Fin n) K)
    (x : HermitianCoordinates n K) :
    HermitianCoordinates n K →L[ℝ] Matrix (Fin n) (Fin n) K :=
  let V := hermitianChartUnitaryMatrix U x
  let D := (hermitianRealDiagonalLinearMap n K) x.1
  let V' := hermitianChartUnitaryMatrixDerivative U x
  let D' := (hermitianRealDiagonalLinearMap n K).toContinuousLinearMap.comp
    (hermitianChartRadialProjection n K)
  matrixMulDerivativeRCLike (V * D) V.conjTranspose
    (matrixMulDerivativeRCLike V D V' D') ((hermitianMatrixConjTransposeCLM n K).comp V')

theorem hasFDerivAt_hermitianCayleyOrbitMatrix (U : Matrix.unitaryGroup (Fin n) K)
    (x : HermitianCoordinates n K) :
    HasFDerivAt (fun y : HermitianCoordinates n K ↦
      hermitianOrbitMatrix (U * hermitianAngularCayley y.2) y.1)
      (hermitianCayleyOrbitMatrixDerivative U x) x := by
  have hv := hasFDerivAt_hermitianChartUnitaryMatrix U x
  have hd := (hermitianRealDiagonalLinearMap n K).toContinuousLinearMap.hasFDerivAt.comp x
    (hermitianChartRadialProjection n K).hasFDerivAt
  have ht := (hermitianMatrixConjTransposeCLM n K).hasFDerivAt.comp x hv
  exact hasFDerivAt_matrix_mul_rclike (hasFDerivAt_matrix_mul_rclike hv hd) ht

theorem hermitianAngularCayleyMatrixDerivative_source
    (a b : HermitianCoordinateIndex n → K) :
    hermitianAngularCayleyMatrixDerivative a b = (hermitianAngularCayley a).val *
      hermitianCayleyLeftTangent (hermitianAngularSkewMatrix a) (hermitianAngularSkewMatrix b) := by
  have h := hermitianCayleyMatrixDerivative_leftTrivialized
    (hermitianAngularSkewMatrix a) (hermitianAngularSkewMatrix b)
      (hermitianAngularSkewMatrix_skewHermitian a)
  have hm := congrArg (fun D : Matrix (Fin n) (Fin n) K ↦ (hermitianAngularCayley a).val * D) h
  have hU : hermitianCayleyMatrix (hermitianAngularSkewMatrix a) *
      (hermitianCayleyMatrix (hermitianAngularSkewMatrix a)).conjTranspose = 1 :=
    (hermitianAngularCayley a).property.2
  dsimp only [hermitianAngularCayley] at hm
  rw [← Matrix.mul_assoc, hU, one_mul] at hm
  exact hm

theorem hermitianChartUnitaryMatrixDerivative_source (U : Matrix.unitaryGroup (Fin n) K)
    (x v : HermitianCoordinates n K) :
    hermitianChartUnitaryMatrixDerivative U x v = hermitianChartUnitaryMatrix U x *
      hermitianCayleyLeftTangent (hermitianAngularSkewMatrix x.2) (hermitianAngularSkewMatrix v.2) := by
  change U.val * hermitianAngularCayleyMatrixDerivative x.2 v.2 = _
  rw [hermitianAngularCayleyMatrixDerivative_source]
  exact (Matrix.mul_assoc _ _ _).symm

theorem hermitianCayleyOrbitMatrixDerivative_source (U : Matrix.unitaryGroup (Fin n) K)
    (x v : HermitianCoordinates n K) :
    hermitianCayleyOrbitMatrixDerivative U x v =
      hermitianChartUnitaryMatrix U x *
        hermitianMatrixOfCoordinates (hermitianDiagonalDifferential x.1
          (hermitianOrbitSourceDifferential x.2 v)) *
            (hermitianChartUnitaryMatrix U x).conjTranspose := by
  let A := hermitianCayleyLeftTangent (hermitianAngularSkewMatrix x.2)
    (hermitianAngularSkewMatrix v.2)
  have hA : A.conjTranspose = -A := hermitianCayleyLeftTangent_skewHermitian _ _
    (hermitianAngularSkewMatrix_skewHermitian x.2)
    (hermitianAngularSkewMatrix_skewHermitian v.2)
  have hrec : hermitianMatrixOfCoordinates (hermitianDiagonalDifferential x.1
      (hermitianOrbitSourceDifferential x.2 v)) =
      A * Matrix.diagonal (fun i ↦ (x.1 i : K)) -
        Matrix.diagonal (fun i ↦ (x.1 i : K)) * A +
          Matrix.diagonal (fun i ↦ (v.1 i : K)) := by
    have hupp : hermitianAngularTangentOperator x.2 v.2 =
        fun ij ↦ A ij.1.1 ij.1.2 := by
      funext ij
      exact hermitianAngularTangentOperator_apply x.2 v.2 ij
    rw [hermitianOrbitSourceDifferential_apply, hupp]
    exact hermitianSkewCommutator_reconstruct A hA x.1 v.1
  rw [hrec]
  unfold hermitianCayleyOrbitMatrixDerivative
  simp only [matrixMulDerivativeRCLike_apply, ContinuousLinearMap.comp_apply]
  rw [hermitianChartUnitaryMatrixDerivative_source]
  change (hermitianChartUnitaryMatrix U x * A * Matrix.diagonal (fun i ↦ (x.1 i : K)) +
      hermitianChartUnitaryMatrix U x * Matrix.diagonal (fun i ↦ (v.1 i : K))) *
        (hermitianChartUnitaryMatrix U x).conjTranspose +
      (hermitianChartUnitaryMatrix U x * Matrix.diagonal (fun i ↦ (x.1 i : K))) *
        (hermitianChartUnitaryMatrix U x * A).conjTranspose = _
  rw [Matrix.conjTranspose_mul, hA]
  noncomm_ring

theorem hermitianCayleyOrbitChartDerivative_eq_actual (U : Matrix.unitaryGroup (Fin n) K)
    (x : HermitianCoordinates n K) :
    (hermitianCoordinateProjectionLinearMap n K).toContinuousLinearMap.comp
      (hermitianCayleyOrbitMatrixDerivative U x) = hermitianCayleyOrbitChartDerivative U x := by
  apply ContinuousLinearMap.ext
  intro v
  rw [ContinuousLinearMap.comp_apply, hermitianCayleyOrbitMatrixDerivative_source]
  rfl

/-- The derivative whose determinant was computed is the literal orbit-chart derivative. -/
theorem hasFDerivAt_hermitianCayleyOrbitChart (U : Matrix.unitaryGroup (Fin n) K)
    (x : HermitianCoordinates n K) :
    HasFDerivAt (hermitianCayleyOrbitChart U) (hermitianCayleyOrbitChartDerivative U x) x := by
  have h := (hermitianCoordinateProjectionLinearMap n K).toContinuousLinearMap.hasFDerivAt.comp x
    (hasFDerivAt_hermitianCayleyOrbitMatrix U x)
  rw [hermitianCayleyOrbitChartDerivative_eq_actual] at h
  exact h

theorem contDiff_hermitianCayleyOrbitChart (U : Matrix.unitaryGroup (Fin n) K) (k : ℕ∞ω) :
    ContDiff ℝ k (hermitianCayleyOrbitChart U) := by
  have hv : ContDiff ℝ k (hermitianChartUnitaryMatrix U) :=
    (mulLeftLinearMap (Fin n) ℝ U.val).toContinuousLinearMap.contDiff.comp
      ((contDiff_hermitianAngularCayleyMatrix k).comp (hermitianChartAngularProjection n K).contDiff)
  have hd : ContDiff ℝ k (fun x : HermitianCoordinates n K ↦
      (hermitianRealDiagonalLinearMap n K) x.1) :=
    (hermitianRealDiagonalLinearMap n K).toContinuousLinearMap.contDiff.comp
      (hermitianChartRadialProjection n K).contDiff
  have ht := (hermitianMatrixConjTransposeCLM n K).contDiff.comp hv
  exact (hermitianCoordinateProjectionLinearMap n K).toContinuousLinearMap.contDiff.comp
    (contDiff_matrix_mul (contDiff_matrix_mul hv hd) ht)

end A3Research
