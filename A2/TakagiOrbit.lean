import A2.OrbitJacobianTangent

open scoped Matrix

noncomputable section

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

def IsRegularTakagiSpectrum {N : ℕ} (lambda : Fin N → ℝ) : Prop :=
  (∀ i, 0 < lambda i) ∧ Function.Injective lambda

def takagiOrbit {N : ℕ} (U : Matrix.unitaryGroup (Fin N) ℂ) (lambda : Fin N → ℝ) :
    Matrix (Fin N) (Fin N) ℂ :=
  (U : Matrix (Fin N) (Fin N) ℂ) *
    Matrix.diagonal (fun i => (Real.sqrt (lambda i) : ℂ)) *
      (U : Matrix (Fin N) (Fin N) ℂ).transpose

theorem takagiOrbit_symmetric {N : ℕ}
    (U : Matrix.unitaryGroup (Fin N) ℂ) (lambda : Fin N → ℝ) :
    (takagiOrbit U lambda).transpose = takagiOrbit U lambda := by
  simp [takagiOrbit, Matrix.transpose_mul, Matrix.mul_assoc]

def takagiOrbitCoordinates {N : ℕ}
    (U : Matrix.unitaryGroup (Fin N) ℂ) (lambda : Fin N → ℝ) :
    ComplexSymmetricCoordinates N := fun ij => takagiOrbit U lambda ij.val.1 ij.val.2

def takagiRealOrbitCoordinates {N : ℕ}
    (U : Matrix.unitaryGroup (Fin N) ℂ) (lambda : Fin N → ℝ) : TakagiRealCoordinates N :=
  (takagiRealComplexCoordinatesEquiv N).symm (takagiOrbitCoordinates U lambda)

theorem complexSymmetricMatrixOfCoordinates_takagiOrbit {N : ℕ}
    (U : Matrix.unitaryGroup (Fin N) ℂ) (lambda : Fin N → ℝ) :
    complexSymmetricMatrixOfCoordinates (takagiOrbitCoordinates U lambda) =
      takagiOrbit U lambda := by
  ext i j
  by_cases hij : i ≤ j
  · simp [complexSymmetricMatrixOfCoordinates, hij, takagiOrbitCoordinates]
  · simp only [complexSymmetricMatrixOfCoordinates, hij, dite_false, takagiOrbitCoordinates]
    exact congrArg (fun M : Matrix (Fin N) (Fin N) ℂ => M i j)
      (takagiOrbit_symmetric U lambda)

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
