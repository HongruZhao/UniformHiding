import LogdetLean.GramHafnian.UltimateHiding.Dense.HaarAmbientCongruenceInvariance
import LogdetLean.GramHafnian.UltimateHiding.Dense.GLUnitaryConjugationAdapter

/-!
# Haar ambient law as an invariant input for the `GL/U` adapter

This short module translates the block-Haar congruence theorem into the
pointwise and averaged predicates used by the generic H2 measure-action
adapter.  It contains no axioms.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.Dense

noncomputable section

open LocalAnticoncentration

theorem concreteHaarAmbientLaw_isProbability_internal
    (H : UnitaryHaarProbabilityFamily) {N K m : ℕ}
    (hNK : N ≤ K) (hKm : K ≤ m) :
    IsProbabilityMeasure (concreteHaarAmbientLaw H N K m) := by
  let _ : IsProbabilityMeasure (scaledHaarTransposeGramLaw H m N K) :=
    scaledHaarTransposeGramLaw_isProbability H (hNK.trans hKm) hKm
  unfold concreteHaarAmbientLaw normalizedHaarTransposeGramLaw
  exact Measure.isProbabilityMeasure_map
    (measurable_normalizeTransposeGram N K).aemeasurable

theorem concreteHaarAmbientLaw_isPointwiseUnitaryCongruenceInvariant
    (H : UnitaryHaarProbabilityFamily) {N K m : ℕ}
    (hNK : N ≤ K) (hKm : K ≤ m) :
    IsPointwiseUnitaryCongruenceInvariant N
      (concreteHaarAmbientLaw H N K m) := by
  intro U
  change Measure.map
      (fun A : ConcreteMatrixState N ↦
        complexMatrixGLVal N (unitaryToComplexMatrixGL N U) * A *
          (complexMatrixGLVal N
            (unitaryToComplexMatrixGL N U)).transpose)
      (concreteHaarAmbientLaw H N K m) =
    concreteHaarAmbientLaw H N K m
  have hval : complexMatrixGLVal N (unitaryToComplexMatrixGL N U) =
      (U : Matrix (Fin N) (Fin N) ℂ) := rfl
  rw [hval]
  exact concreteHaarAmbientLaw_map_unitaryCongruence H
    (hNK.trans hKm) hKm U

theorem concreteHaarAmbientLaw_isUnitaryCongruenceInvariant
    (H : UnitaryHaarProbabilityFamily) {N K m : ℕ}
    (hNK : N ≤ K) (hKm : K ≤ m) :
    IsUnitaryCongruenceInvariant N
      (concreteHaarAmbientLaw H N K m) := by
  letI : IsProbabilityMeasure (concreteHaarAmbientLaw H N K m) :=
    concreteHaarAmbientLaw_isProbability_internal H hNK hKm
  exact (concreteHaarAmbientLaw_isPointwiseUnitaryCongruenceInvariant
    H hNK hKm).toAveraged

end


end LogdetLean.GramHafnian.UltimateHiding.Dense
