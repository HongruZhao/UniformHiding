import A2.UnitaryCongruenceVolume
import A2.SpectrumTakagiStabilizer

open A2Research

noncomputable section

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

theorem takagiOrbitCoordinates_mul {N : ℕ}
    (U V : Matrix.unitaryGroup (Fin N) ℂ) (lambda : Fin N → ℝ) :
    takagiOrbitCoordinates (U * V) lambda =
      unitaryCongruenceRepresentation N U (takagiOrbitCoordinates V lambda) := by
  funext ij
  rw [unitaryCongruenceRepresentation_apply,
    complexSymmetricMatrixOfCoordinates_takagiOrbit]
  exact congrArg (fun C : Matrix (Fin N) (Fin N) ℂ => C ij.val.1 ij.val.2)
    (takagiOrbit_mul U V lambda)

theorem takagiRealOrbitCoordinates_mul {N : ℕ}
    (U V : Matrix.unitaryGroup (Fin N) ℂ) (lambda : Fin N → ℝ) :
    takagiRealOrbitCoordinates (U * V) lambda =
      realCoordinateCongruenceLinearMap N U (takagiRealOrbitCoordinates V lambda) := by
  change (takagiRealComplexCoordinatesEquiv N).symm
      (takagiOrbitCoordinates (U * V) lambda) =
    (takagiRealComplexCoordinatesEquiv N).symm
      (unitaryCongruenceRepresentation N U ((takagiRealComplexCoordinatesEquiv N)
        ((takagiRealComplexCoordinatesEquiv N).symm (takagiOrbitCoordinates V lambda))))
  rw [LinearEquiv.apply_symm_apply, takagiOrbitCoordinates_mul U V lambda]

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
