import LogdetLean.GramHafnian.UltimateHiding.Dense.ConcreteFactorUnitaryInvariance
import LogdetLean.GramHafnian.UltimateHiding.Dense.GLConcreteFactorLifts
import LogdetLean.GramHafnian.UltimateHiding.Dense.GLUnitaryConjugationAdapter
import LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep.ConcreteCorrelatedPath

/-!
# The concrete H2 factors as conjugation-invariant `GL_N(C)` actions

This module connects the reusable group-theoretic sandwich adapter to the two
concrete positive factor laws.  It proves conjugation invariance and identifies
the resulting transpose-congruence actions with the pre-existing orbital and
one-column kernels.  No new axiom is introduced here.
-/

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.Dense

noncomputable section

/-! ## A generic mapped-factor action identity -/

theorem congruenceMeasureAction_map_factor
    {N : ℕ} {Param : Type*} [MeasurableSpace Param]
    (param : Measure Param) [IsProbabilityMeasure param]
    (factor : Param → ComplexMatrixGL N) (hfactor : Measurable factor)
    (mu : Measure (ConcreteMatrixState N)) [IsProbabilityMeasure mu] :
    congruenceMeasureAction N (Measure.map factor param) mu =
      Measure.map
        (fun p : ConcreteMatrixState N × Param ↦
          complexGLTransposeCongruence N (factor p.2) p.1)
        (mu.prod param) := by
  unfold congruenceMeasureAction
  let act : ConcreteMatrixState N × ComplexMatrixGL N →
      ConcreteMatrixState N :=
    fun p ↦ complexGLTransposeCongruence N p.2 p.1
  have hact : Measurable act := measurable_complexGLTransposeCongruence N
  have hprod :
      mu.prod (Measure.map factor param) =
        Measure.map (Prod.map id factor) (mu.prod param) := by
    calc
      mu.prod (Measure.map factor param) =
          (Measure.map id mu).prod (Measure.map factor param) := by
        rw [Measure.map_id]
      _ = Measure.map (Prod.map id factor) (mu.prod param) :=
        Measure.map_prod_map mu param measurable_id hfactor
  rw [hprod, Measure.map_map hact (measurable_id.prodMap hfactor)]
  rfl

/-! ## Pointwise covariance of the `GL` lifts -/

theorem concreteOrbitalFactorGLLift_unitarySphereAction
    {N : ℕ} (hN : 1 ≤ N)
    (U : Matrix.unitaryGroup (Fin N) ℂ)
    (s : ℝ) (v : ComplexUnitSphere N) :
    unitaryGLConjugation N U (concreteOrbitalFactorGLLift hN s v) =
      concreteOrbitalFactorGLLift hN s (unitarySphereAction U v) := by
  apply Units.ext
  change unitaryMatrixConjugation U (concreteOrbitalFactor N s v) =
    concreteOrbitalFactor N s (unitarySphereAction U v)
  exact (concreteOrbitalFactor_unitarySphereAction U s v).symm

theorem concreteOrbitalFactorGL_unitarySphereAction
    {N : ℕ} (U : Matrix.unitaryGroup (Fin N) ℂ)
    (s : ℝ) (v : ComplexUnitSphere N) :
    unitaryGLConjugation N U (concreteOrbitalFactorGL N s v) =
      concreteOrbitalFactorGL N s (unitarySphereAction U v) := by
  apply Units.ext
  change unitaryMatrixConjugation U (concreteOrbitalFactor N s v) =
    concreteOrbitalFactor N s (unitarySphereAction U v)
  exact (concreteOrbitalFactor_unitarySphereAction U s v).symm

theorem concreteOneColumnFactorGLLift_unitarySphereAction
    {m N : ℕ} (hm : 1 ≤ m)
    (U : Matrix.unitaryGroup (Fin N) ℂ)
    (q : ℝ) (v : ComplexUnitSphere N) :
    unitaryGLConjugation N U (concreteOneColumnFactorGLLift hm q v) =
      concreteOneColumnFactorGLLift hm q (unitarySphereAction U v) := by
  by_cases hq : 0 < q
  · apply Units.ext
    simp only [concreteOneColumnFactorGLLift, hq, dite_true]
    change unitaryMatrixConjugation U (concreteOneColumnFactor m N q v) =
      concreteOneColumnFactor m N q (unitarySphereAction U v)
    exact (concreteOneColumnFactor_unitarySphereAction m U q v).symm
  · simp [concreteOneColumnFactorGLLift, hq, unitaryGLConjugation]

theorem concreteOneColumnFactorGL_unitarySphereAction
    {m N : ℕ} (U : Matrix.unitaryGroup (Fin N) ℂ)
    (q : ℝ) (v : ComplexUnitSphere N) :
    unitaryGLConjugation N U (concreteOneColumnFactorGL m N q v) =
      concreteOneColumnFactorGL m N q (unitarySphereAction U v) := by
  by_cases hm : 1 ≤ m
  · simpa only [concreteOneColumnFactorGL, hm, dite_true] using
      concreteOneColumnFactorGLLift_unitarySphereAction hm U q v
  · simp [concreteOneColumnFactorGL, hm, unitaryGLConjugation]

/-! ## Conjugation invariance and preservation -/

theorem concreteOrbitalGLFactorLaw_conjugationInvariant
    {N : ℕ} (hN : 1 ≤ N) (s : ℝ) :
    IsUnitaryConjugationInvariant N (concreteOrbitalGLFactorLaw N s) := by
  intro U
  unfold concreteOrbitalGLFactorLaw
  rw [Measure.map_map (measurable_unitaryGLConjugation N U)
    (measurable_concreteOrbitalFactorGL N s)]
  calc
    Measure.map
        (unitaryGLConjugation N U ∘ concreteOrbitalFactorGL N s)
        (complexUnitSphereProbabilityMeasure N) =
      Measure.map
        (concreteOrbitalFactorGL N s ∘ unitarySphereAction U)
        (complexUnitSphereProbabilityMeasure N) := by
          apply Measure.map_congr
          filter_upwards [] with v
          exact concreteOrbitalFactorGL_unitarySphereAction U s v
    _ = Measure.map (concreteOrbitalFactorGL N s)
          (Measure.map (unitarySphereAction U)
            (complexUnitSphereProbabilityMeasure N)) := by
      rw [Measure.map_map (measurable_concreteOrbitalFactorGL N s)
        (measurable_unitarySphereAction U)]
    _ = Measure.map (concreteOrbitalFactorGL N s)
          (complexUnitSphereProbabilityMeasure N) := by
      rw [map_complexUnitSphereProbabilityMeasure_unitarySphereAction hN U]

theorem concreteOneColumnGLFactorLaw_conjugationInvariant
    {m N : ℕ} (hN : 1 ≤ N) (hNm : N ≤ m) :
    IsUnitaryConjugationInvariant N
      (concreteOneColumnGLFactorLaw m N) := by
  intro U
  unfold concreteOneColumnGLFactorLaw
  let rotate : ℝ × ComplexUnitSphere N →
      ℝ × ComplexUnitSphere N :=
    Prod.map id (unitarySphereAction U)
  have hrotate : Measurable rotate :=
    measurable_id.prodMap (measurable_unitarySphereAction U)
  have hlift := measurable_concreteOneColumnFactorGL m N
  rw [Measure.map_map (measurable_unitaryGLConjugation N U) hlift]
  calc
    Measure.map
        (unitaryGLConjugation N U ∘
          fun p : ℝ × ComplexUnitSphere N ↦
            concreteOneColumnFactorGL m N p.1 p.2)
        (concreteOneColumnParameterLaw m N) =
      Measure.map
        ((fun p : ℝ × ComplexUnitSphere N ↦
            concreteOneColumnFactorGL m N p.1 p.2) ∘ rotate)
        (concreteOneColumnParameterLaw m N) := by
          apply Measure.map_congr
          filter_upwards [] with p
          exact concreteOneColumnFactorGL_unitarySphereAction
            U p.1 p.2
    _ = Measure.map
          (fun p : ℝ × ComplexUnitSphere N ↦
            concreteOneColumnFactorGL m N p.1 p.2)
          (Measure.map rotate (concreteOneColumnParameterLaw m N)) := by
      rw [Measure.map_map hlift hrotate]
    _ = Measure.map
          (fun p : ℝ × ComplexUnitSphere N ↦
            concreteOneColumnFactorGL m N p.1 p.2)
          (concreteOneColumnParameterLaw m N) := by
      rw [map_concreteOneColumnParameterLaw_unitarySphereAction hN hNm U]

theorem concreteOrbitalGLFactorLaw_preservesUnitaryCongruenceInvariant
    {N : ℕ} (hN : 1 ≤ N) (s : ℝ) :
    PreservesUnitaryCongruenceInvariant N
      (concreteOrbitalGLFactorLaw N s) := by
  let _ : IsProbabilityMeasure (concreteOrbitalGLFactorLaw N s) :=
    concreteOrbitalGLFactorLaw_isProbability hN s
  exact IsUnitaryConjugationInvariant.preservesUnitaryCongruenceInvariant
    (concreteOrbitalGLFactorLaw_conjugationInvariant hN s)

theorem concreteOneColumnGLFactorLaw_preservesUnitaryCongruenceInvariant
    {m N : ℕ} (hN : 1 ≤ N) (hNm : N ≤ m) :
    PreservesUnitaryCongruenceInvariant N
      (concreteOneColumnGLFactorLaw m N) := by
  let _ : IsProbabilityMeasure (concreteOneColumnGLFactorLaw m N) :=
    concreteOneColumnGLFactorLaw_isProbability hN hNm
  exact IsUnitaryConjugationInvariant.preservesUnitaryCongruenceInvariant
    (concreteOneColumnGLFactorLaw_conjugationInvariant hN hNm)

/-! ## Identification with the concrete kernels -/

theorem congruenceMeasureAction_concreteOrbitalGLFactorLaw
    {N : ℕ} (hN : 1 ≤ N) (s : ℝ)
    (mu : Measure (ConcreteMatrixState N)) [IsProbabilityMeasure mu] :
    congruenceMeasureAction N (concreteOrbitalGLFactorLaw N s) mu =
      concreteOrbitalMatrixKernel N s ∘ₘ mu := by
  let sphere := complexUnitSphereProbabilityMeasure N
  let _ : IsProbabilityMeasure sphere :=
    complexUnitSphereProbabilityMeasure_isProbability hN
  unfold concreteOrbitalGLFactorLaw
  rw [congruenceMeasureAction_map_factor sphere
    (concreteOrbitalFactorGL N s)
    (measurable_concreteOrbitalFactorGL N s) mu]
  have hprod :=
    LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep.independentUpdateKernel_comp_eq_map_prod
      mu sphere
        (fun p : ConcreteMatrixState N × ComplexUnitSphere N ↦
          concreteOrbitalMatrixUpdate N s p.2 p.1)
        (measurable_concreteOrbitalMatrixUpdate N s)
  unfold concreteOrbitalMatrixKernel
  unfold independentUpdateKernel
  rw [hprod]
  apply Measure.map_congr
  filter_upwards [] with p
  unfold complexGLTransposeCongruence concreteOrbitalMatrixUpdate
  rw [complexMatrixGLVal_concreteOrbitalFactorGL]

theorem congruenceMeasureAction_concreteOneColumnGLFactorLaw
    {m N : ℕ} (hN : 1 ≤ N) (hNm : N ≤ m)
    (mu : Measure (ConcreteMatrixState N)) [IsProbabilityMeasure mu] :
    congruenceMeasureAction N (concreteOneColumnGLFactorLaw m N) mu =
      concreteOneColumnMatrixKernel m N ∘ₘ mu := by
  let param := concreteOneColumnParameterLaw m N
  let _ : IsProbabilityMeasure param :=
    concreteOneColumnParameterLaw_isProbability hN hNm
  unfold concreteOneColumnGLFactorLaw
  rw [congruenceMeasureAction_map_factor param
    (fun p : ℝ × ComplexUnitSphere N ↦
      concreteOneColumnFactorGL m N p.1 p.2)
    (measurable_concreteOneColumnFactorGL m N) mu]
  unfold concreteOneColumnMatrixKernel concreteAmbientOneColumnKernel
  unfold ambientOneColumnKernel
  have hprod :=
    LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep.independentUpdateKernel_comp_eq_map_prod
      mu param
        (fun p : ConcreteMatrixState N × (ℝ × ComplexUnitSphere N) ↦
          concreteOneColumnMatrixUpdate m N p.2.1 p.2.2 p.1)
        (measurable_concreteOneColumnMatrixUpdate m N)
  unfold independentUpdateKernel
  dsimp only [param, concreteOneColumnParameterLaw] at hprod
  rw [hprod]
  apply Measure.map_congr
  have hlift := complexMatrixGLVal_concreteOneColumnFactorGL_ae hN hNm
  have hliftProd := (Measure.quasiMeasurePreserving_snd
    (μ := mu) (ν := param)).ae hlift
  filter_upwards [hliftProd] with p hp
  unfold complexGLTransposeCongruence concreteOneColumnMatrixUpdate
  rw [hp]

end

end LogdetLean.GramHafnian.UltimateHiding.Dense
