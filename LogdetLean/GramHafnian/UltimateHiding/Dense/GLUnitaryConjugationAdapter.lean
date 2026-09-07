import LogdetLean.GramHafnian.UltimateHiding.Dense.GLUnitaryCongruenceAdapter

/-!
# Conjugation-invariant factor laws preserve invariant state laws

This module supplies the elementary group-action bridge needed by H2.  A
factor law on `GL_N(C)` which is invariant under conjugation by `U(N)`
commutes with each unitary Dirac mass.  Consequently its transpose-congruence
action sends unitary-invariant matrix laws to unitary-invariant matrix laws.

There are no axioms in this file.
-/

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.Dense

noncomputable section

/-- Conjugation of an invertible matrix by the canonical copy of `U(N)`. -/
def unitaryGLConjugation (N : ℕ)
    (U : Matrix.unitaryGroup (Fin N) ℂ)
    (g : ComplexMatrixGL N) : ComplexMatrixGL N :=
  unitaryToComplexMatrixGL N U * g *
    (unitaryToComplexMatrixGL N U)⁻¹

theorem measurable_unitaryGLConjugation (N : ℕ)
    (U : Matrix.unitaryGroup (Fin N) ℂ) :
    Measurable (unitaryGLConjugation N U) := by
  unfold unitaryGLConjugation
  exact (measurable_mul_const
      (unitaryToComplexMatrixGL N U)⁻¹).comp
    (measurable_const_mul (unitaryToComplexMatrixGL N U))

/-- A factor law is central under conjugation by the unitary subgroup. -/
def IsUnitaryConjugationInvariant (N : ℕ)
    (xi : Measure (ComplexMatrixGL N)) : Prop :=
  ∀ U : Matrix.unitaryGroup (Fin N) ℂ,
    Measure.map (unitaryGLConjugation N U) xi = xi

/-- A unitary Dirac mass commutes in convolution with every law invariant
under conjugation by that unitary. -/
theorem dirac_unitary_mconv_eq_mconv_dirac_of_conjugationInvariant
    {N : ℕ} {xi : Measure (ComplexMatrixGL N)}
    [IsProbabilityMeasure xi]
    (hxi : IsUnitaryConjugationInvariant N xi)
    (U : Matrix.unitaryGroup (Fin N) ℂ) :
    Measure.dirac (unitaryToComplexMatrixGL N U) ∗ₘ xi =
      xi ∗ₘ Measure.dirac (unitaryToComplexMatrixGL N U) := by
  let u := unitaryToComplexMatrixGL N U
  have hconj : Measurable (unitaryGLConjugation N U) :=
    measurable_unitaryGLConjugation N U
  have hright : Measurable (fun g : ComplexMatrixGL N ↦ g * u) :=
    measurable_mul_const u
  rw [Measure.dirac_mconv, Measure.mconv_dirac]
  calc
    Measure.map (fun g : ComplexMatrixGL N ↦ u * g) xi =
        Measure.map
          ((fun g : ComplexMatrixGL N ↦ g * u) ∘
            unitaryGLConjugation N U) xi := by
      apply Measure.map_congr
      filter_upwards [] with g
      simp [unitaryGLConjugation, u, Function.comp_def, mul_assoc]
    _ = Measure.map (fun g : ComplexMatrixGL N ↦ g * u)
          (Measure.map (unitaryGLConjugation N U) xi) :=
      (Measure.map_map hright hconj).symm
    _ = Measure.map (fun g : ComplexMatrixGL N ↦ g * u) xi := by
      rw [hxi U]

/-- Acting by a Dirac factor is the ordinary pointwise transpose-congruence
pushforward. -/
theorem congruenceMeasureAction_dirac
    (N : ℕ) (g : ComplexMatrixGL N)
    (mu : Measure (ConcreteMatrixState N)) [IsProbabilityMeasure mu] :
    congruenceMeasureAction N (Measure.dirac g) mu =
      Measure.map (fun A : ConcreteMatrixState N ↦
        complexGLTransposeCongruence N g A) mu := by
  unfold congruenceMeasureAction
  rw [Measure.prod_dirac]
  rw [Measure.map_map (measurable_complexGLTransposeCongruence N)
    measurable_prodMk_right]
  apply Measure.map_congr
  filter_upwards [] with A
  rfl

/-- Haar-averaged invariance implies invariance under every individual
unitary. -/
theorem IsUnitaryCongruenceInvariant.toPointwise
    {N : ℕ} {mu : Measure (ConcreteMatrixState N)}
    [IsProbabilityMeasure mu]
    (hmu : IsUnitaryCongruenceInvariant N mu) :
    IsPointwiseUnitaryCongruenceInvariant N mu := by
  change congruenceMeasureAction N (unitaryHaarGLMeasure N) mu = mu at hmu
  intro U
  have hleft := dirac_unitary_mconv_unitaryHaarGLMeasure N U
  calc
    Measure.map
        (fun A : ConcreteMatrixState N ↦
          complexGLTransposeCongruence N
            (unitaryToComplexMatrixGL N U) A) mu =
        congruenceMeasureAction N
          (Measure.dirac (unitaryToComplexMatrixGL N U)) mu :=
      (congruenceMeasureAction_dirac N
        (unitaryToComplexMatrixGL N U) mu).symm
    _ = congruenceMeasureAction N
          (Measure.dirac (unitaryToComplexMatrixGL N U))
          (congruenceMeasureAction N (unitaryHaarGLMeasure N) mu) := by
      rw [hmu]
    _ = congruenceMeasureAction N
          (Measure.dirac (unitaryToComplexMatrixGL N U) ∗ₘ
            unitaryHaarGLMeasure N) mu :=
      (congruenceMeasureAction_mconv
        (Measure.dirac (unitaryToComplexMatrixGL N U))
        (unitaryHaarGLMeasure N) mu).symm
    _ = congruenceMeasureAction N (unitaryHaarGLMeasure N) mu := by
      rw [hleft]
    _ = mu := hmu

/-- The group-theoretic preservation lemma used by the concrete H2 factors. -/
theorem IsUnitaryConjugationInvariant.preservesUnitaryCongruenceInvariant
    {N : ℕ} {xi : Measure (ComplexMatrixGL N)}
    [IsProbabilityMeasure xi]
    (hxi : IsUnitaryConjugationInvariant N xi) :
    PreservesUnitaryCongruenceInvariant N xi := by
  intro mu hmuProbability hmu
  letI : IsProbabilityMeasure mu := hmuProbability
  have hmuPointwise : IsPointwiseUnitaryCongruenceInvariant N mu :=
    hmu.toPointwise
  have houtPointwise : IsPointwiseUnitaryCongruenceInvariant N
      (congruenceMeasureAction N xi mu) := by
    intro U
    have hdirac : congruenceMeasureAction N
        (Measure.dirac (unitaryToComplexMatrixGL N U)) mu = mu := by
      rw [congruenceMeasureAction_dirac]
      exact hmuPointwise U
    calc
      Measure.map
          (fun A : ConcreteMatrixState N ↦
            complexGLTransposeCongruence N
              (unitaryToComplexMatrixGL N U) A)
          (congruenceMeasureAction N xi mu) =
          congruenceMeasureAction N
            (Measure.dirac (unitaryToComplexMatrixGL N U))
            (congruenceMeasureAction N xi mu) :=
        (congruenceMeasureAction_dirac N
          (unitaryToComplexMatrixGL N U)
          (congruenceMeasureAction N xi mu)).symm
      _ = congruenceMeasureAction N
            (Measure.dirac (unitaryToComplexMatrixGL N U) ∗ₘ xi) mu :=
        (congruenceMeasureAction_mconv
          (Measure.dirac (unitaryToComplexMatrixGL N U)) xi mu).symm
      _ = congruenceMeasureAction N
            (xi ∗ₘ Measure.dirac (unitaryToComplexMatrixGL N U)) mu := by
        rw [dirac_unitary_mconv_eq_mconv_dirac_of_conjugationInvariant
          hxi U]
      _ = congruenceMeasureAction N xi
            (congruenceMeasureAction N
              (Measure.dirac (unitaryToComplexMatrixGL N U)) mu) :=
        congruenceMeasureAction_mconv xi
          (Measure.dirac (unitaryToComplexMatrixGL N U)) mu
      _ = congruenceMeasureAction N xi mu := by rw [hdirac]
  exact houtPointwise.toAveraged

end

end LogdetLean.GramHafnian.UltimateHiding.Dense
