import A2.UnitaryCongruenceVolume

open MeasureTheory Matrix
open LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

namespace A2Research

theorem map_unitaryCongruence_complexSymmetricMatrixVolume (N : ℕ)
    (U : Matrix.unitaryGroup (Fin N) ℂ) :
    Measure.map (fun C : Matrix (Fin N) (Fin N) ℂ ↦
      (U : Matrix (Fin N) (Fin N) ℂ) * C * (U : Matrix (Fin N) (Fin N) ℂ).transpose)
      (complexSymmetricMatrixVolume N) = complexSymmetricMatrixVolume N := by
  have hc : Measurable (fun C : Matrix (Fin N) (Fin N) ℂ ↦
      (U : Matrix (Fin N) (Fin N) ℂ) * C * (U : Matrix (Fin N) (Fin N) ℂ).transpose) := by
    fun_prop
  have hembed := measurable_complexSymmetricMatrixOfCoordinates N
  have hρ := measurePreserving_unitaryCongruenceRepresentation N U
  have hfun : (fun x : ComplexSymmetricCoordinates N ↦
      (U : Matrix (Fin N) (Fin N) ℂ) * complexSymmetricMatrixOfCoordinates x *
        (U : Matrix (Fin N) (Fin N) ℂ).transpose) =
      complexSymmetricMatrixOfCoordinates ∘ unitaryCongruenceRepresentation N U := by
    funext x
    exact (symmetricCoordinateEmbedding_congruence
      (U : Matrix (Fin N) (Fin N) ℂ) x).symm
  rw [complexSymmetricMatrixVolume, Measure.map_map hc hembed]
  change Measure.map (fun x : ComplexSymmetricCoordinates N ↦
    (U : Matrix (Fin N) (Fin N) ℂ) * complexSymmetricMatrixOfCoordinates x *
      (U : Matrix (Fin N) (Fin N) ℂ).transpose) (complexSymmetricCoordinateVolume N) = _
  rw [hfun, ← Measure.map_map hembed hρ.measurable, hρ.map_eq]

end A2Research
