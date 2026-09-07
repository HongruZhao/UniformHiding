import LogdetLean.GramHafnian.UltimateHiding.Sparse.H19HaarCornerSupportBalance

/-!
# Measure-level equality of the two successor-column densities

The explicit top-coordinate Haar-column density uses the open unit ball,
while the literal Jiang successor fiber uses the closed unit ball.  When the
successor exponent is zero these functions differ on the unit sphere, but the
sphere has zero complex Lebesgue measure.  This file transports the existing
Euclidean sphere-nullness result to raw complex-column coordinates and proves
the exact equality of the two `withDensity` measures without a strict ambient
size assumption.
-/

open Matrix MeasureTheory
open scoped ComplexOrder MatrixOrder BigOperators ENNReal

namespace LogdetLean.GramHafnian.UltimateHiding.Sparse

noncomputable section

/-- Pointwise, the closed-ball spelling of the Haar-column density is the
literal Jiang successor-fiber density. -/
theorem h19BaseColumnRawClosedPDF_eq_jiangHaarCornerSuccFiberPDF
    {M K N : ℕ} (hsize : K + (N + 1) ≤ M) (u : Fin K → ℂ) :
    h19BaseColumnRawClosedPDF K (M - K - N) u =
      jiangHaarCornerSuccFiberPDF M K N u := by
  have hexp : M - K - N - 1 = M - K - (N + 1) := by omega
  have hnormsq :=
    h19BaseColumn_euclideanNormSq_eq_complexColumnNormSq K u
  have hnorm_nonneg :
      0 ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℂ (Fin K))‖ :=
    norm_nonneg _
  have hnorm_iff :
      ‖(WithLp.toLp 2 u : EuclideanSpace ℂ (Fin K))‖ ≤ 1 ↔
        complexColumnNormSq u ≤ 1 := by
    rw [← hnormsq]
    constructor <;> intro h <;> nlinarith
  unfold h19BaseColumnRawClosedPDF h19BaseColumnVectorClosedPDF
  unfold jiangHaarCornerSuccFiberPDF
  rw [h19BaseColumnNormalizer_eq_jiangHaarCornerSuccFiberNormalizer hsize,
    hexp]
  by_cases hu : complexColumnNormSq u ≤ 1
  · rw [if_pos (hnorm_iff.mpr hu), if_pos hu]
    rw [hnormsq]
  · rw [if_neg (not_congr hnorm_iff |>.mpr hu), if_neg hu]

/-- The open-ball Haar-column density and the closed-ball Jiang successor
fiber define the same complex-column Lebesgue-density measure.  This includes
the boundary exponent-zero case: `withDensity_h19BaseColumnVectorClosedPDF_eq`
uses `Measure.addHaar_sphere` to discard the Euclidean unit sphere, and the
measure-preserving `WithLp.ofLp` identification transports that result to the
raw column type. -/
theorem withDensity_h19BaseColumnRawPDF_eq_jiangSuccFiber
    {M K N : ℕ} (hK : 0 < K) (hsize : K + (N + 1) ≤ M) :
    (complexColumnLebesgueVolume K).withDensity
        (h19BaseColumnRawPDF K (M - K - N)) =
      (complexColumnLebesgueVolume K).withDensity
        (jiangHaarCornerSuccFiberPDF M K N) := by
  have hopenRaw := LogdetLean.measurePreserving_map_withDensity_comp
    (measurePreserving_h19BaseColumnOfLp K)
    (h19BaseColumnRawPDF K (M - K - N))
    (measurable_h19BaseColumnRawPDF K (M - K - N))
  have hclosedRaw := LogdetLean.measurePreserving_map_withDensity_comp
    (measurePreserving_h19BaseColumnOfLp K)
    (h19BaseColumnRawClosedPDF K (M - K - N))
    (measurable_h19BaseColumnRawClosedPDF K (M - K - N))
  have hopenComp :
      h19BaseColumnRawPDF K (M - K - N) ∘
          (WithLp.ofLp : EuclideanSpace ℂ (Fin K) → (Fin K → ℂ)) =
        h19BaseColumnVectorPDF K (M - K - N) := by
    funext x
    rfl
  have hclosedComp :
      h19BaseColumnRawClosedPDF K (M - K - N) ∘
          (WithLp.ofLp : EuclideanSpace ℂ (Fin K) → (Fin K → ℂ)) =
        h19BaseColumnVectorClosedPDF K (M - K - N) := by
    funext x
    rfl
  rw [hopenComp] at hopenRaw
  rw [hclosedComp] at hclosedRaw
  have hraw :
      (volume : Measure (Fin K → ℂ)).withDensity
          (h19BaseColumnRawPDF K (M - K - N)) =
        (volume : Measure (Fin K → ℂ)).withDensity
          (h19BaseColumnRawClosedPDF K (M - K - N)) := by
    calc
      (volume : Measure (Fin K → ℂ)).withDensity
          (h19BaseColumnRawPDF K (M - K - N)) =
        Measure.map WithLp.ofLp
          ((volume : Measure (EuclideanSpace ℂ (Fin K))).withDensity
            (h19BaseColumnVectorPDF K (M - K - N))) := hopenRaw.symm
      _ = Measure.map WithLp.ofLp
          ((volume : Measure (EuclideanSpace ℂ (Fin K))).withDensity
            (h19BaseColumnVectorClosedPDF K (M - K - N))) := by
        rw [withDensity_h19BaseColumnVectorClosedPDF_eq
          (by omega : 1 ≤ K)]
      _ = (volume : Measure (Fin K → ℂ)).withDensity
          (h19BaseColumnRawClosedPDF K (M - K - N)) := hclosedRaw
  rw [complexColumnLebesgueVolume_eq_volume]
  calc
    (volume : Measure (Fin K → ℂ)).withDensity
        (h19BaseColumnRawPDF K (M - K - N)) =
      (volume : Measure (Fin K → ℂ)).withDensity
        (h19BaseColumnRawClosedPDF K (M - K - N)) := hraw
    _ = (volume : Measure (Fin K → ℂ)).withDensity
        (jiangHaarCornerSuccFiberPDF M K N) := by
      congr 1
      funext u
      exact
        h19BaseColumnRawClosedPDF_eq_jiangHaarCornerSuccFiberPDF hsize u

end

end LogdetLean.GramHafnian.UltimateHiding.Sparse
