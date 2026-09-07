import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ConcreteCubicWIdentification
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ConcreteAveragedRankOneCubicDefinitions
import Mathlib.Tactic

/-!
# Exact projective average of the literal rank-one cubic score

This module combines the internally proved non-bilinear contraction with the
exact `w_v` and `x_v w_v` projective contractions.  The result identifies the
literal projective integral before any norm is taken.  Its low-order
projective moment inputs are proved internally in the imported modules.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

theorem integrable_concreteRankOneCubicNonW
    {N K : ℕ} (hN : 1 ≤ N) (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    Integrable (fun v : ComplexUnitSphere N ↦
      concreteRankOneCubicNonW N K v A)
      (complexUnitSphereProbabilityMeasure N) := by
  let sphere := complexUnitSphereProbabilityMeasure N
  letI : IsProbabilityMeasure sphere :=
    complexUnitSphereProbabilityMeasure_isProbability hN
  let s : ComplexUnitSphere N → ℝ :=
    fun v ↦ concreteCenteredProjectiveTrace N K v A
  let a := 8 * cubicTraceCoefficientThree (concreteCOEExponent N K)
  let b := 8 * cubicTraceCoefficientTwo (concreteCOEExponent N K)
    ((N : ℝ) + 1)
  let d := 8 * cubicTraceCoefficientOne (concreteCOEExponent N K)
    ((N : ℝ) + 1)
  let e := 8 * cubicTraceCoefficientZero (concreteCOEExponent N K)
    ((N : ℝ) + 1)
  have hs1 : Integrable s sphere := by
    simpa only [s, sphere] using integrable_concreteCenteredProjectiveTrace hN A
  have hs2 : Integrable (fun v ↦ s v ^ 2) sphere := by
    simpa only [s, sphere] using
      integrable_concreteCenteredProjectiveTrace_sq hN A hsupport
  have hs3 : Integrable (fun v ↦ s v ^ 3) sphere := by
    simpa only [s, sphere] using
      integrable_concreteCenteredProjectiveTrace_cube hN A hsupport
  rw [show (fun v ↦ concreteRankOneCubicNonW N K v A) =
      (fun v ↦ a * s v ^ 3 + b * s v ^ 2 + d * s v + e) by
    funext v
    simp only [concreteRankOneCubicNonW, averagedCubicNonWExpression,
      a, b, d, e, s]
    ring]
  exact (((hs3.const_mul a).add (hs2.const_mul b)).add
    (hs1.const_mul d)).add (integrable_const e)

theorem integrable_concreteRankOneCubicW
    {N K : ℕ} (hN : 1 ≤ N) (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    Integrable (fun v : ComplexUnitSphere N ↦ concreteRankOneCubicW N K v A)
      (complexUnitSphereProbabilityMeasure N) := by
  let w : ComplexUnitSphere N → ℝ := fun v ↦ concreteCOEW v K A
  let xw : ComplexUnitSphere N → ℝ := fun v ↦
    concreteCOEX v K A * concreteCOEW v K A
  let a : ℝ := 24 * concreteCOEExponent N K * ((N : ℝ) + 2)
  let b : ℝ := -(24 * concreteCOEExponent N K *
    (concreteCOEExponent N K - 2))
  have hw : Integrable w (complexUnitSphereProbabilityMeasure N) := by
    simpa only [w] using integrable_concreteCOEW hN A
  have hxw : Integrable xw (complexUnitSphereProbabilityMeasure N) := by
    simpa only [xw] using integrable_concreteCOEX_mul_W hN A hsupport
  rw [show (fun v ↦ concreteRankOneCubicW N K v A) =
      fun v ↦ a * w v + b * xw v by
    funext v
    simp only [concreteRankOneCubicW, a, b, w, xw]
    ring]
  exact (hw.const_mul a).add (hxw.const_mul b)

/-- Exact projective contraction of the literal rank-one third density
score to the closed trace expression. -/
theorem integral_concreteRankOneDensityScoreThree
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K)
    (A : ConcreteMatrixState N)
    (hsymm : (unscaleCOECorner K A).IsSymm)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    (∫ v : ComplexUnitSphere N,
      concreteRankOneDensityScoreThree N K v A
        ∂(complexUnitSphereProbabilityMeasure N)) =
      concreteAveragedRankOneCubicDensity N K A := by
  have hc : concreteCOEExponent N K ≠ 0 := by
    unfold concreteCOEExponent
    have hdenseR : (16 : ℝ) * (N : ℝ) ≤ (K : ℝ) := by
      exact_mod_cast hdense
    have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    nlinarith
  have hnonW := integrable_concreteRankOneCubicNonW hN A hsupport
  have hwithW := integrable_concreteRankOneCubicW
    (K := K) hN A hsupport
  rw [show (fun v ↦ concreteRankOneDensityScoreThree N K v A) =
      fun v ↦ concreteRankOneCubicNonW N K v A +
        concreteRankOneCubicW N K v A by
    funext v
    exact concreteRankOneDensityScoreThree_eq_nonW_add_W hN hdense v A]
  rw [integral_add hnonW hwithW,
    integral_concreteRankOneCubicNonW hN A hsupport]
  have hw := integral_concreteRankOneCubicW_expression
    hN A hc hsymm hsupport
  change _ + (∫ v : ComplexUnitSphere N,
      concreteRankOneCubicW N K v A
        ∂(complexUnitSphereProbabilityMeasure N)) = _
  rw [show (∫ v : ComplexUnitSphere N,
      concreteRankOneCubicW N K v A
        ∂(complexUnitSphereProbabilityMeasure N)) =
      averagedCubicWTraceExpression (N : ℝ) (concreteCOEExponent N K)
        (concreteCOETraceZW N K A)
        (concreteCOETraceZTraceZW N K A)
        (concreteCOETraceZTwoW N K A) by
    simpa only [concreteRankOneCubicW] using hw]
  rfl

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
