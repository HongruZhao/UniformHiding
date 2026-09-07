import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H7TrilinearBundle
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Fixed-state projective integrability for H7

The H7 witness integrates only over the compact complex unit sphere with the
matrix state fixed.  Consequently every continuous trilinear expression in
the centered rank-one coordinates is integrable; no COE resolvent moment is
needed for these two structure fields.
-/

open MeasureTheory
open scoped Matrix

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- The real coordinate vector of the centered rank-one direction varies
continuously on the complex unit sphere. -/
theorem continuous_concreteCenteredOrbitalCoordinates (N : ℕ) :
    Continuous (fun v : ComplexUnitSphere N ↦
      concreteMatrixRealCoordinates (concreteCenteredOrbitalDirection N v)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  apply continuous_pi
  intro b
  fin_cases b <;>
    simp [concreteMatrixRealCoordinates,
      concreteCenteredOrbitalDirection, Matrix.sub_apply,
      complexRankOneProjection, Matrix.smul_apply, Matrix.one_apply] <;>
    fun_prop

/-- A continuous scalar function on the compact unit sphere is integrable
for its probability measure. -/
theorem continuous_integrable_complexUnitSphere
    {N : ℕ} (hN : 1 ≤ N) {f : ComplexUnitSphere N → ℝ}
    (hf : Continuous f) :
    Integrable f (complexUnitSphereProbabilityMeasure N) := by
  letI : IsProbabilityMeasure (complexUnitSphereProbabilityMeasure N) :=
    complexUnitSphereProbabilityMeasure_isProbability hN
  simpa only [integrableOn_univ] using
    hf.continuousOn.integrableOn_compact
      (μ := complexUnitSphereProbabilityMeasure N) isCompact_univ

/-- The cubic centered diagonal of any continuous trilinear form is
integrable on the fixed-state projective parameter. -/
theorem integrable_symmetricTrilinear_centeredDiagonal
    {N : ℕ} (hN : 1 ≤ N)
    (T : SymmetricRealTrilinearForm (ConcreteMatrixRealCoordinates N)) :
    Integrable (fun v : ComplexUnitSphere N ↦
      let q := concreteMatrixRealCoordinates
        (concreteCenteredOrbitalDirection N v)
      T.form q q q)
      (complexUnitSphereProbabilityMeasure N) := by
  let q : ComplexUnitSphere N → ConcreteMatrixRealCoordinates N := fun v ↦
    concreteMatrixRealCoordinates (concreteCenteredOrbitalDirection N v)
  have hq : Continuous q := by
    simpa only [q] using continuous_concreteCenteredOrbitalCoordinates N
  have hfirst : Continuous (fun v ↦ T.form (q v)) :=
    T.form.continuous.comp hq
  have hsecond : Continuous (fun v ↦ T.form (q v) (q v)) :=
    hfirst.clm_apply hq
  have hthird : Continuous (fun v ↦ T.form (q v) (q v) (q v)) :=
    hsecond.clm_apply hq
  apply continuous_integrable_complexUnitSphere hN
  simpa only [q] using hthird

/-- The scalar-centered-centered partial of any continuous trilinear form is
integrable on the fixed-state projective parameter. -/
theorem integrable_symmetricTrilinear_mixed
    {N : ℕ} (hN : 1 ≤ N)
    (T : SymmetricRealTrilinearForm (ConcreteMatrixRealCoordinates N)) :
    Integrable (fun v : ComplexUnitSphere N ↦
      T.form
        (concreteMatrixRealCoordinates (1 : ConcreteMatrixState N))
        (concreteMatrixRealCoordinates (concreteCenteredOrbitalDirection N v))
        (concreteMatrixRealCoordinates (concreteCenteredOrbitalDirection N v)))
      (complexUnitSphereProbabilityMeasure N) := by
  let q : ComplexUnitSphere N → ConcreteMatrixRealCoordinates N := fun v ↦
    concreteMatrixRealCoordinates (concreteCenteredOrbitalDirection N v)
  let i := concreteMatrixRealCoordinates (1 : ConcreteMatrixState N)
  have hq : Continuous q := by
    simpa only [q] using continuous_concreteCenteredOrbitalCoordinates N
  have hsecond : Continuous (fun v ↦ T.form i (q v)) :=
    (T.form i).continuous.comp hq
  have hthird : Continuous (fun v ↦ T.form i (q v) (q v)) :=
    hsecond.clm_apply hq
  apply continuous_integrable_complexUnitSphere hN
  simpa only [q, i] using hthird

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
