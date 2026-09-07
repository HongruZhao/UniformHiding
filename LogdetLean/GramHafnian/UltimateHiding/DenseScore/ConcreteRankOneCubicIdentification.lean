import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ConcreteProjectiveCubicIdentification
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CenteredCubicTraceClosure
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CenteredFlowGeometry
import Mathlib.Tactic

/-!
# Exact identification of the averaged rank-one cubic score

The cubic density score is split pointwise, before absolute values, into its
non-bilinear polynomial in `s_v = Tr(P_v (Y-(N+1)I))` and the terms containing
`w_v`.  This module proves the non-bilinear projective contraction exactly.
The separate `w_v` contraction is supplied by the projective bilinear-moment
module.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- Pointwise non-`w` summand after the centered-coordinate substitution. -/
def concreteRankOneCubicNonW (N K : ℕ)
    (v : ComplexUnitSphere N) (A : ConcreteMatrixState N) : ℝ :=
  averagedCubicNonWExpression (N : ℝ) (concreteCOEExponent N K)
    (concreteCenteredProjectiveTrace N K v A)
    (concreteCenteredProjectiveTrace N K v A ^ 2)
    (concreteCenteredProjectiveTrace N K v A ^ 3)

/-- Pointwise part containing the bilinear statistic `w_v`. -/
def concreteRankOneCubicW (N K : ℕ)
    (v : ComplexUnitSphere N) (A : ConcreteMatrixState N) : ℝ :=
  24 * concreteCOEExponent N K *
    (((N : ℝ) + 2) * concreteCOEW v K A -
      (concreteCOEExponent N K - 2) *
        concreteCOEX v K A * concreteCOEW v K A)

/-- The centered projective coordinate is exactly
`s_v = c x_v-(N+1)`. -/
theorem concreteCenteredProjectiveTrace_eq_exponent_mul_X_sub
    {N K : ℕ} (v : ComplexUnitSphere N)
    (A : ConcreteMatrixState N) :
    concreteCenteredProjectiveTrace N K v A =
      concreteCOEExponent N K * concreteCOEX v K A - ((N : ℝ) + 1) := by
  rw [concreteCenteredProjectiveTrace, complexProjectiveTracePair_eq_trace]
  simp only [concreteCOECenteredMatrix, concreteCOEY, Matrix.mul_sub,
    Matrix.mul_smul, Matrix.mul_one, Matrix.trace_sub, Matrix.trace_smul,
    trace_complexRankOneProjection, concreteCOEX, concreteRealTrace,
    Complex.sub_re]
  simp only [smul_eq_mul]
  rw [Complex.mul_re]
  norm_num

/-- Exact pointwise split of the rank-one cubic density score. -/
theorem concreteRankOneDensityScoreThree_eq_nonW_add_W
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K)
    (v : ComplexUnitSphere N) (A : ConcreteMatrixState N) :
    concreteRankOneDensityScoreThree N K v A =
      concreteRankOneCubicNonW N K v A +
        concreteRankOneCubicW N K v A := by
  let c := concreteCOEExponent N K
  let n : ℝ := N
  let x := concreteCOEX v K A
  let w := concreteCOEW v K A
  let s := concreteCenteredProjectiveTrace N K v A
  have hc : c ≠ 0 := by
    dsimp only [c, concreteCOEExponent]
    have hdenseR : (16 : ℝ) * (N : ℝ) ≤ (K : ℝ) := by
      exact_mod_cast hdense
    have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    nlinarith
  have hs : s = c * x - (n + 1) := by
    simpa only [s, c, x, n] using
      concreteCenteredProjectiveTrace_eq_exponent_mul_X_sub v A
  have hx : x = (s + (n + 1)) / c := by
    rw [hs]
    field_simp [hc]
    ring
  have hnonW := coeRankOneDensityScoreThree_nonW_centered_expansion
    (c := c) (p := n + 1) (s := s) (x := x) hc hx
  have hw := coeRankOneDensityScoreThree_w_cancellation c n x w
  change coeRankOneDensityScoreThree c n x w = _
  rw [show coeRankOneDensityScoreThree c n x w =
      coeRankOneDensityScoreThree c n x 0 +
        24 * c * ((n + 2) * w - (c - 2) * x * w) by linarith [hw]]
  change coeRankOneDensityScoreThree c n x 0 + _ =
    averagedCubicNonWExpression n c s (s ^ 2) (s ^ 3) + _
  congr 1
  · unfold coeRankOneDensityScoreThree densityBellThree
      coeRankOneLogScoreOne coeRankOneLogScoreTwo coeRankOneLogScoreThree
      averagedCubicNonWExpression
    have hscore :
        (2 * (c * x - (n + 1))) ^ 3 +
            3 * (2 * (c * x - (n + 1))) *
              (-4 * c * (x + x ^ 2 + 0)) +
            8 * c * (x + 3 * x ^ 2 + 2 * x ^ 3 + 3 * 0 + 6 * x * 0) =
          8 * s ^ 3 - 24 * c * s * (x + x ^ 2) +
            8 * c * (x + 3 * x ^ 2 + 2 * x ^ 3) := by
      rw [hs]
      ring
    rw [hscore, hnonW]

/-- Exact projective integral of the non-`w` summand. -/
theorem integral_concreteRankOneCubicNonW
    {N K : ℕ} (hN : 1 ≤ N) (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    (∫ v : ComplexUnitSphere N, concreteRankOneCubicNonW N K v A
      ∂(complexUnitSphereProbabilityMeasure N)) =
      averagedCubicNonWExpression (N : ℝ) (concreteCOEExponent N K)
        (concreteProjectiveMeanS N K A)
        (concreteProjectiveMeanSSquare N K A)
        (concreteProjectiveMeanSCube N K A) := by
  let sphere := complexUnitSphereProbabilityMeasure N
  letI : IsProbabilityMeasure sphere :=
    complexUnitSphereProbabilityMeasure_isProbability hN
  let s : ComplexUnitSphere N → ℝ :=
    fun v ↦ concreteCenteredProjectiveTrace N K v A
  let a := 8 * cubicTraceCoefficientThree (concreteCOEExponent N K)
  let b := 8 * cubicTraceCoefficientTwo (concreteCOEExponent N K) ((N : ℝ) + 1)
  let d := 8 * cubicTraceCoefficientOne (concreteCOEExponent N K) ((N : ℝ) + 1)
  let e := 8 * cubicTraceCoefficientZero (concreteCOEExponent N K) ((N : ℝ) + 1)
  have hs1 : Integrable s sphere := by
    simpa only [s, sphere] using integrable_concreteCenteredProjectiveTrace hN A
  have hs2 : Integrable (fun v ↦ s v ^ 2) sphere := by
    simpa only [s, sphere] using
      integrable_concreteCenteredProjectiveTrace_sq hN A hsupport
  have hs3 : Integrable (fun v ↦ s v ^ 3) sphere := by
    simpa only [s, sphere] using
      integrable_concreteCenteredProjectiveTrace_cube hN A hsupport
  have hpoint : (fun v ↦ concreteRankOneCubicNonW N K v A) =
      a • (fun v ↦ s v ^ 3) + b • (fun v ↦ s v ^ 2) +
        d • s + fun _ ↦ e := by
    funext v
    simp only [concreteRankOneCubicNonW, averagedCubicNonWExpression,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, a, b, d, e, s]
    ring
  rw [hpoint]
  change (∫ v, (((a • (fun v ↦ s v ^ 3) +
      b • (fun v ↦ s v ^ 2)) + d • s) +
      (fun _ : ComplexUnitSphere N ↦ e)) v ∂sphere) = _
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have h3 : Integrable (fun v ↦ a * s v ^ 3) sphere := hs3.const_mul a
  have h2 : Integrable (fun v ↦ b * s v ^ 2) sphere := hs2.const_mul b
  have h1 : Integrable (fun v ↦ d * s v) sphere := hs1.const_mul d
  calc
    (∫ v, a * s v ^ 3 + b * s v ^ 2 + d * s v + e ∂sphere) =
        (∫ v, a * s v ^ 3 + b * s v ^ 2 + d * s v ∂sphere) +
          ∫ _ : ComplexUnitSphere N, e ∂sphere :=
      integral_add ((h3.add h2).add h1) (integrable_const e)
    _ = ((∫ v, a * s v ^ 3 + b * s v ^ 2 ∂sphere) +
          ∫ v, d * s v ∂sphere) +
          ∫ _ : ComplexUnitSphere N, e ∂sphere := by
      congr 1
      exact integral_add (h3.add h2) h1
    _ = (((∫ v, a * s v ^ 3 ∂sphere) +
          ∫ v, b * s v ^ 2 ∂sphere) +
          ∫ v, d * s v ∂sphere) +
          ∫ _ : ComplexUnitSphere N, e ∂sphere := by
      congr 2
      exact integral_add h3 h2
    _ = a * concreteProjectiveMeanSCube N K A +
          b * concreteProjectiveMeanSSquare N K A +
          d * concreteProjectiveMeanS N K A + e := by
      rw [integral_const_mul, integral_const_mul, integral_const_mul,
        integral_const,
        integral_concreteCenteredProjectiveTrace hN A,
        integral_concreteCenteredProjectiveTrace_sq hN A hsupport,
        integral_concreteCenteredProjectiveTrace_cube hN A hsupport]
      simp only [measureReal_def, IsProbabilityMeasure.measure_univ,
        ENNReal.toReal_one, one_smul]
    _ = averagedCubicNonWExpression (N : ℝ) (concreteCOEExponent N K)
          (concreteProjectiveMeanS N K A)
          (concreteProjectiveMeanSSquare N K A)
          (concreteProjectiveMeanSCube N K A) := by
      simp only [a, b, d, e, averagedCubicNonWExpression]
      ring

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
