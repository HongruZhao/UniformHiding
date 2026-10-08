import A3.BetaMatrixAlgebra

open scoped BigOperators Matrix.Norms.Elementwise ComplexOrder MatrixOrder ENNReal
open Matrix MeasureTheory Set

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

namespace A3Research

variable {n : ℕ} {K : Type*} [RCLike K]
  [MeasureSpace K] [BorelSpace K] [PolishSpace K]
  [(hermitianCoordinateVolume n K).IsAddHaarMeasure]

theorem map_hermitianCongruence_volume
    {C : Matrix (Fin n) (Fin n) K} (hC : C.PosDef) :
    Measure.map (hermitianCoordinateConjugationLinearMap C) (hermitianCoordinateVolume n K) =
      ENNReal.ofReal ((RCLike.re C.det) ^ (2 + Module.finrank ℝ K * (n - 1)))⁻¹ •
        hermitianCoordinateVolume n K := by
  have hd : LinearMap.det (hermitianCoordinateConjugationLinearMap C) ≠ 0 := by
    apply abs_pos.mp
    rw [abs_det_hermitianCoordinateConjugation_posDef hC]
    exact pow_pos (re_det_pos_of_posDef hC) _
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar (hermitianCoordinateVolume n K) hd,
    abs_inv, abs_det_hermitianCoordinateConjugation_posDef hC]

theorem measurableEmbedding_hermitianCongruence
    {C : Matrix (Fin n) (Fin n) K} (hC : IsUnit C) :
    MeasurableEmbedding (hermitianCoordinateConjugationLinearMap C) :=
  (hermitianCoordinateConjugationLinearEquiv C hC).toContinuousLinearEquiv.toHomeomorph.isClosedEmbedding.measurableEmbedding

theorem map_hermitianCongruence_betaDomain
    {C : Matrix (Fin n) (Fin n) K} (hC : C.PosDef) :
    Measure.map (hermitianCoordinateConjugationLinearMap C)
        ((hermitianCoordinateVolume n K).restrict (hermitianBetaDomain n K)) =
      ENNReal.ofReal ((RCLike.re C.det) ^ (2 + Module.finrank ℝ K * (n - 1)))⁻¹ •
        (hermitianCoordinateVolume n K).restrict (hermitianSumSlice (C * C)) := by
  have hp : (hermitianCoordinateConjugationLinearMap C) ⁻¹' hermitianSumSlice (C * C) =
      hermitianBetaDomain n K := by
    ext x
    exact hermitianConjugation_mem_sumSlice_iff hC x
  rw [← hp, ← (measurableEmbedding_hermitianCongruence hC.isUnit).restrict_map,
    map_hermitianCongruence_volume hC, Measure.restrict_smul]

end A3Research
