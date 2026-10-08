import A2.TakagiChartDifferential
import A2.TakagiRadialSqrtDerivative

open scoped Matrix Matrix.Norms.Elementwise

noncomputable section

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

theorem takagiSkewMatrix_ignores_radial {N : ℕ} (x : TakagiRealCoordinates N) :
    takagiSkewMatrix x =
      (takagiAngularSkewEquiv N (takagiAngularRadialLinearEquiv N x).1 :
        Matrix (Fin N) (Fin N) ℂ) := by
  ext i j
  by_cases he : i = j
  · subst j
    simp [takagiAngularSkewEquiv, takagiSkewMatrix, takagiAngularEmbed,
      IsTakagiRadialKey, takagiAngularRadialLinearEquiv]
  · by_cases hij : i ≤ j <;>
      simp [takagiAngularSkewEquiv, takagiSkewMatrix, takagiAngularEmbed,
        IsTakagiRadialKey, takagiAngularRadialLinearEquiv,
        takagiAngularRadialCoordinatesEquiv_fst_apply, he, Ne.symm he, hij]

theorem takagiCayleySourceDifferential_skew {N : ℕ}
    (a : TakagiAngularCoordinates N) (x : TakagiRealCoordinates N) :
    takagiSkewMatrix (takagiCayleySourceDifferential a x) =
      takagiCayleyAngularTangent (takagiAngularSkewEquiv N a) (takagiSkewMatrix x) := by
  rw [takagiSkewMatrix_ignores_radial]
  rw [takagiCayleySourceDifferential_split]
  rw [takagiSkewMatrix_ignores_radial x]
  change ((takagiAngularSkewEquiv N)
    ((takagiAngularSkewEquiv N).symm
      ((takagiCayleyAngularEquiv (takagiAngularSkewEquiv N a)
        (show ((takagiAngularSkewEquiv N a) : Matrix (Fin N) (Fin N) ℂ).conjTranspose =
          -(takagiAngularSkewEquiv N a) from (takagiAngularSkewEquiv N a).property))
            ((takagiAngularSkewEquiv N) (takagiAngularRadialLinearEquiv N x).1))) :
      Matrix (Fin N) (Fin N) ℂ) = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem takagiCayleySourceDifferential_radial {N : ℕ}
    (a : TakagiAngularCoordinates N) (x : TakagiRealCoordinates N) (i : Fin N) :
    takagiCayleySourceDifferential a x (takagiRadialKey i) = x (takagiRadialKey i) := by
  exact congrArg (fun p : TakagiAngularCoordinates N × (Fin N → ℝ) => p.2 i)
    (takagiCayleySourceDifferential_split a x)

theorem takagiRadialSqrtDerivative_source {N : ℕ}
    (lambda : Fin N → ℝ) (a : TakagiAngularCoordinates N) (x : TakagiRealCoordinates N) :
    takagiRadialSqrtDerivative lambda (takagiAngularRadialLinearEquiv N x).2 =
      takagiRadialMatrix lambda (takagiCayleySourceDifferential a x) := by
  rw [takagiRadialSqrtDerivative_apply]
  unfold takagiRadialMatrix
  congr 1
  funext i
  rw [show (⟨(i, i), le_refl i⟩, (0 : Fin 2)) = takagiRadialKey i from rfl,
    takagiCayleySourceDifferential_radial]
  simp [div_eq_mul_inv, mul_comm, takagiAngularRadialLinearEquiv,
    takagiAngularRadialCoordinatesEquiv_snd_apply]

theorem takagiAngularCayleyMatrixDerivative_source {N : ℕ}
    (a : TakagiAngularCoordinates N) (x : TakagiRealCoordinates N) :
    takagiAngularCayleyMatrixDerivative a (takagiAngularRadialLinearEquiv N x).1 =
      (takagiAngularCayley a : Matrix (Fin N) (Fin N) ℂ) *
        takagiSkewMatrix (takagiCayleySourceDifferential a x) := by
  rw [takagiCayleySourceDifferential_skew, takagiSkewMatrix_ignores_radial x]
  let H : Matrix (Fin N) (Fin N) ℂ := takagiAngularSkewEquiv N a
  let D : Matrix (Fin N) (Fin N) ℂ := takagiAngularSkewEquiv N (takagiAngularRadialLinearEquiv N x).1
  have hH : H.conjTranspose = -H := (takagiAngularSkewEquiv N a).property
  change takagiCayleyMatrixDerivative H D = takagiCayley H * takagiCayleyAngularTangent H D
  rw [← takagiCayleyMatrixDerivative_leftTrivialized H D hH, ← Matrix.mul_assoc]
  have hu : takagiCayley H * (takagiCayley H).conjTranspose = 1 :=
    (takagiCayley_mem_unitaryGroup H hH).2
  rw [hu, one_mul]

theorem takagiDiagonalOrbitTangent_symmetric {N : ℕ}
    (lambda : Fin N → ℝ) (x : TakagiRealCoordinates N) :
    (takagiDiagonalOrbitTangent lambda x).transpose = takagiDiagonalOrbitTangent lambda x := by
  unfold takagiDiagonalOrbitTangent
  simp only [Matrix.transpose_add, Matrix.transpose_mul, Matrix.diagonal_transpose,
    Matrix.transpose_transpose, takagiRadialMatrix]
  abel

theorem takagiDiagonalOrbitTangent_reconstruct {N : ℕ}
    (lambda : Fin N → ℝ) (x : TakagiRealCoordinates N) :
    A2Research.symmetricCoordinateEmbedding N
      (takagiRealComplexCoordinatesEquiv N (takagiDiagonalDifferential lambda x)) =
        takagiDiagonalOrbitTangent lambda x := by
  have he : takagiRealComplexCoordinatesEquiv N (takagiDiagonalDifferential lambda x) =
      A2Research.symmetricCoordinateProjection N (takagiDiagonalOrbitTangent lambda x) := by
    funext ij
    exact (takagiDiagonalOrbitTangent_upper_coordinates lambda x ij).symm
  rw [he]
  exact A2Research.symmetricCoordinateEmbedding_projection _
    (takagiDiagonalOrbitTangent_symmetric lambda x)

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
