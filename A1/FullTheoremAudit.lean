import A1

open MeasureTheory
open LogdetLean.GramHafnian.LocalAnticoncentration
noncomputable section

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore.FriedmanMelloA1

theorem A1_exact_original_target_verified : Target := A1_friedmanMello_matrixLaw

example : ∀ {n m : ℕ}, 1 ≤ m → (h2mn : 2 * m ≤ n) →
    Measure.map (fun U : Matrix.unitaryGroup (Fin n) ℂ ↦
      let S := FriedmanMelloA1.S U
      let s := FriedmanMelloA1.s (dimensionLe h2mn) S
      s) (unitaryHaarProbabilityMeasure n) = determinantDensityProbabilityMeasure n m :=
  A1_friedmanMello_matrixLaw

#check A1_friedmanMello_matrixLaw
#print axioms A1_friedmanMello_matrixLaw
#print axioms A1_exact_original_target_verified

end LogdetLean.GramHafnian.UltimateHiding.DenseScore.FriedmanMelloA1

run_cmd Lean.logInfo "A1_FULL_TARGET_EXACT_KERNEL_CHECKED"
