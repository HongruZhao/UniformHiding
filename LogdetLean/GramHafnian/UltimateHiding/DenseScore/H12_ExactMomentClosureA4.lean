import LogdetLean.GramHafnian.UltimateHiding.DenseScore.MatsumotoA4InternalClosure
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H12_ProjectiveFourthLow
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.H14_FiniteGaussianFourthWickFormulaClosure
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.H14_MatsumotoTraceFourReductionConditional
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.H14_DenominatorFourthTraceContraction
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H6_A2Prime_A1TraceTransport
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.FriedmanMelloSupportFromDensity
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ConcreteScaledCOECornerProbability
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# Exact H12 fourth-moment closure from approved A1--A4

This module supplies the missing literal H12 adapter.  Approved Matsumoto A4
provides the identity-scale inverse-Wishart fourth trace, the checked finite
Gaussian Wick contraction supplies the numerator moment, exact H6 (A2--A3)
transports the radial law, and approved A1 supplies the almost-everywhere COE
support.  The original external H12 declaration is not invoked.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.LocalAnticoncentration
open U08
open Matrix Unitary

set_option maxHeartbeats 3600000

/-! ## A4 to the existing denominator bound contract -/

/-- The source-faithful A4 integrability output and the checked scalar
contraction together discharge the denominator trace-four contract used by
the finite Wick producer. -/
theorem h12MatsumotoIdentityTraceFourBoundContract_of_A4_internal
    (N K : ℕ) : H14MatsumotoIdentityTraceFourBoundContract N K := by
  refine ⟨?_, ?_⟩
  · intro hgap
    by_cases hN0 : N = 0
    · exact (h14MatsumotoIdentityTraceFourBoundContract_internal N K).1 hgap
    · have hN : 1 ≤ N := by omega
      have hA4 := h12h14_matsumotoIdentityTraceFourMoment_of_A4_internal
        (d := N) (k := K - N) (by omega) (by omega)
      have hfun :
          h12h14MatsumotoIdentityScaledInverseTraceFour N (K - N)
              (halfGaussianMatsumotoGamma N (K - N)) =
            matsumotoIdentityScaledInverseTraceFour N K := by
        funext R
        rfl
      rw [← hfun]
      exact hA4.integrable
  · intro hN hdense
    exact (h14MatsumotoIdentityTraceFourBoundContract_internal N K).2 hN hdense

/-- Denominator-only Wick-polynomial bounds with A4 supplying the literal
identity-scale integrability branch. -/
theorem h12DenominatorFourthTracePolynomialBounds_of_A4_internal
    (N K : ℕ) : H14DenominatorFourthTracePolynomialBounds N K :=
  h14DenominatorFourthTracePolynomialBounds_of_matsumotoTraceFour_conditional
    (h12MatsumotoIdentityTraceFourBoundContract_of_A4_internal N K)

/-! ## Deterministic first-score projective contraction -/

/-- The radial trace bracket produced by removing the scalar matrix mode. -/
def h12ConcreteTracelessBracket (N K : ℕ)
    (A : ConcreteMatrixState N) : ℝ :=
  concreteCOETraceTwo N K A -
    (N : ℝ)⁻¹ * concreteCOETraceOne N K A ^ 2

/-- A deliberately slack power-of-two envelope for the fixed-matrix fourth
projective contraction. -/
def h12ProjectiveFourthEnvelope (N K : ℕ)
    (A : ConcreteMatrixState N) : ℝ :=
  1024 * h12ConcreteTracelessBracket N K A ^ 2 / (N : ℝ) ^ 4

theorem h12ProjectiveFourthEnvelope_nonneg
    (N K : ℕ) (A : ConcreteMatrixState N) :
    0 ≤ h12ProjectiveFourthEnvelope N K A := by
  unfold h12ProjectiveFourthEnvelope
  positivity

/-- The literal first centered log score is twice the real centered
projective trace on the COE support. -/
theorem concreteCenteredEll_one_eq_centeredTracePair_re_h12_internal
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (A : ConcreteMatrixState N) (v : ComplexUnitSphere N)
    (hsymm : (unscaleCOECorner K A).IsSymm)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    concreteCenteredEll 1 N K (A, v) =
      2 * (complexCenteredProjectiveTracePair v
        (concreteCOEY N K A)).re := by
  unfold concreteCenteredEll
  rw [← coeCorner_centeredDensityScore_one_eq_logScore hN v A hsupport]
  rw [coeCorner_centeredDensityScore_one_eq_explicit_external_derived
    hN hgap v A hsymm hsupport]
  unfold concreteCenteredRankOneFirstDensityScore
    concreteCenteredRankOneFirstDensityScoreComplex
  simp [Complex.mul_re]

theorem h12_traceZeroPart_isHermitian_of_support
    {N K : ℕ} (hN : 1 ≤ N) (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    (h14ProjectiveTraceZeroPart (concreteCOEY N K A)).IsHermitian := by
  let Y := concreteCOEY N K A
  have hY : Y.IsHermitian := concreteCOEY_isHermitian_of_support A hsupport
  have htim : (Matrix.trace Y).im = 0 := by
    simpa only [Y] using concreteCOEY_trace_im_eq_zero_of_support A hsupport
  have hc : IsSelfAdjoint
      (((((N : ℝ)⁻¹ : ℝ) : ℂ) * Matrix.trace Y)) := by
    rw [isSelfAdjoint_iff]
    apply Complex.ext
    · simp [htim]
    · simp [htim]
  unfold h14ProjectiveTraceZeroPart
  exact hY.sub (Matrix.isHermitian_one.smul hc)

/-- The squared trace of the scalar-free part is the concrete traceless
quadratic bracket. -/
theorem trace_traceZeroPart_sq_re_eq_h12ConcreteTracelessBracket
    {N K : ℕ} (hN : 1 ≤ N) (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    (Matrix.trace
      (h14ProjectiveTraceZeroPart (concreteCOEY N K A) *
        h14ProjectiveTraceZeroPart (concreteCOEY N K A))).re =
      h12ConcreteTracelessBracket N K A := by
  let Y := concreteCOEY N K A
  let a : ℂ := (((N : ℝ)⁻¹ : ℝ) : ℂ)
  have hn : (N : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hN)
  have htim : (Matrix.trace Y).im = 0 := by
    simpa only [Y] using concreteCOEY_trace_im_eq_zero_of_support A hsupport
  have haN : a * (N : ℂ) = 1 := by
    dsimp only [a]
    exact_mod_cast inv_mul_cancel₀ hn
  unfold h14ProjectiveTraceZeroPart
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, Matrix.trace_sub,
    Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
  change
    (Matrix.trace (Y * Y) -
      a * Matrix.trace Y * Matrix.trace Y -
      a * Matrix.trace Y *
        (Matrix.trace Y - a * Matrix.trace Y * (N : ℂ))).re = _
  have htrace0 :
      Matrix.trace Y - a * Matrix.trace Y * (N : ℂ) = 0 := by
    calc
      Matrix.trace Y - a * Matrix.trace Y * (N : ℂ) =
          Matrix.trace Y - Matrix.trace Y * (a * (N : ℂ)) := by ring
      _ = 0 := by rw [haN]; ring
  rw [htrace0, mul_zero, sub_zero]
  change
    (Matrix.trace (Y * Y) - a * Matrix.trace Y * Matrix.trace Y).re =
      (Matrix.trace (Y * Y)).re -
        (N : ℝ)⁻¹ * (Matrix.trace Y).re ^ 2
  dsimp only [a]
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, htim, zero_mul, mul_zero, sub_zero, add_zero]
  ring

private theorem isHermitian_trace_pow_eq_sum_eigenvalues_pow_h12
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.IsHermitian) (r : ℕ) :
    Matrix.trace (A ^ r) =
      ∑ i, ((hA.eigenvalues i : ℝ) : ℂ) ^ r := by
  conv_lhs => rw [hA.spectral_theorem]
  rw [← map_pow]
  rw [conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul]
  rw [Matrix.diagonal_pow, Matrix.trace_diagonal]
  rfl

private theorem isHermitian_trace_four_re_le_trace_two_re_sq_h12
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    (Matrix.trace (A * A * A * A)).re ≤
      (Matrix.trace (A * A)).re ^ 2 := by
  have h2 := isHermitian_trace_pow_eq_sum_eigenvalues_pow_h12 A hA 2
  have h4 := isHermitian_trace_pow_eq_sum_eigenvalues_pow_h12 A hA 4
  have hsum := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := Finset.univ)
    (f := fun i ↦ hA.eigenvalues i ^ 2)
    (fun i _ ↦ sq_nonneg (hA.eigenvalues i))
  have hAA : A * A = A ^ 2 := by noncomm_ring
  have hAAAA : A * A * A * A = A ^ 4 := by noncomm_ring
  rw [hAAAA, hAA, h2, h4, Complex.re_sum, Complex.re_sum]
  norm_cast at hsum ⊢
  calc
    ∑ i, hA.eigenvalues i ^ 4 =
        ∑ i, (hA.eigenvalues i ^ 2) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ (∑ i, hA.eigenvalues i ^ 2) ^ 2 := hsum

theorem trace_traceZeroPart_four_re_le_sq_h12
    {N K : ℕ} (hN : 1 ≤ N) (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    (Matrix.trace
      (h14ProjectiveTraceZeroPart (concreteCOEY N K A) *
        h14ProjectiveTraceZeroPart (concreteCOEY N K A) *
        h14ProjectiveTraceZeroPart (concreteCOEY N K A) *
        h14ProjectiveTraceZeroPart (concreteCOEY N K A))).re ≤
      h12ConcreteTracelessBracket N K A ^ 2 := by
  let A0 := h14ProjectiveTraceZeroPart (concreteCOEY N K A)
  have hA0 := h12_traceZeroPart_isHermitian_of_support hN A hsupport
  have hraw := isHermitian_trace_four_re_le_trace_two_re_sq_h12 A0 hA0
  have ht2 := trace_traceZeroPart_sq_re_eq_h12ConcreteTracelessBracket
    hN A hsupport
  simpa only [A0, pow_two, Matrix.mul_assoc, ht2] using hraw

/-- Fixed-matrix H12 fibre package.  The scalar part is removed before the
exact fourth projective moment is bounded. -/
theorem h12_fixedMatrix_projectiveFourth_package_internal
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (A : ConcreteMatrixState N)
    (hsymm : (unscaleCOECorner K A).IsSymm)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    Integrable (fun v : ComplexUnitSphere N ↦
        concreteCenteredEll 1 N K (A, v) ^ 4)
        (complexUnitSphereProbabilityMeasure N) ∧
      (∫ v : ComplexUnitSphere N,
        ‖concreteCenteredEll 1 N K (A, v) ^ 4‖
          ∂(complexUnitSphereProbabilityMeasure N)) ≤
        h12ProjectiveFourthEnvelope N K A := by
  let Y := concreteCOEY N K A
  let A0 := h14ProjectiveTraceZeroPart Y
  let sphere := complexUnitSphereProbabilityMeasure N
  have hA0 : A0.IsHermitian := by
    simpa only [A0, Y] using
      h12_traceZeroPart_isHermitian_of_support hN A hsupport
  have htr0 : Matrix.trace A0 = 0 := by
    simpa only [A0, Y] using trace_h14ProjectiveTraceZeroPart hN Y
  have hpair (v : ComplexUnitSphere N) :
      concreteCenteredEll 1 N K (A, v) =
        2 * (complexProjectiveTracePair v A0).re := by
    rw [concreteCenteredEll_one_eq_centeredTracePair_re_h12_internal
      hN hgap A v hsymm hsupport]
    rw [show A0 = h14ProjectiveTraceZeroPart Y by rfl,
      complexProjectiveTracePair_h14ProjectiveTraceZeroPart hN v Y]
  have hbase := integrable_complexProjectiveTracePair_fourth hN A0
  have hreal : Integrable (fun v : ComplexUnitSphere N ↦
      (complexProjectiveTracePair v A0).re ^ 4) sphere := by
    apply hbase.re.congr
    filter_upwards [] with v
    have him :=
      complexProjectiveTracePair_im_eq_zero_of_isHermitian_h12_low v A0 hA0
    simp [pow_succ, Complex.mul_re, him]
  have hscore : Integrable (fun v : ComplexUnitSphere N ↦
      concreteCenteredEll 1 N K (A, v) ^ 4) sphere := by
    apply (hreal.const_mul 16).congr
    filter_upwards [] with v
    rw [hpair v]
    ring
  refine ⟨hscore, ?_⟩
  have hexact := integral_complexProjectiveTracePair_re_fourth_eq_h12_low
    hN A0 hA0
  rw [htr0] at hexact
  simp only [Complex.zero_re, zero_pow (by norm_num : 4 ≠ 0),
    zero_pow (by norm_num : 2 ≠ 0), zero_mul, mul_zero, zero_add] at hexact
  let n : ℝ := N
  let t2 : ℝ := h12ConcreteTracelessBracket N K A
  let t4 : ℝ := (Matrix.trace (A0 * A0 * A0 * A0)).re
  have hn : 0 < n := by
    dsimp only [n]
    exact_mod_cast (show 0 < N by omega)
  have ht2eq : (Matrix.trace (A0 * A0)).re = t2 := by
    simpa only [A0, Y, t2] using
      trace_traceZeroPart_sq_re_eq_h12ConcreteTracelessBracket hN A hsupport
  have ht4le : t4 ≤ t2 ^ 2 := by
    simpa only [A0, Y, t4, t2] using
      trace_traceZeroPart_four_re_le_sq_h12 hN A hsupport
  have hD : n ^ 4 ≤ n * (n + 1) * (n + 2) * (n + 3) := by
    have hn0 : 0 ≤ n := hn.le
    calc
      n ^ 4 = n * n * n * n := by ring
      _ ≤ n * (n + 1) * (n + 2) * (n + 3) := by
        gcongr <;> linarith
  have hDpos : 0 < n * (n + 1) * (n + 2) * (n + 3) := by positivity
  have hinv :
      (n * (n + 1) * (n + 2) * (n + 3))⁻¹ ≤ (n ^ 4)⁻¹ :=
    (inv_le_inv₀ hDpos (by positivity)).2 hD
  calc
    (∫ v : ComplexUnitSphere N,
        ‖concreteCenteredEll 1 N K (A, v) ^ 4‖ ∂sphere) =
        ∫ v : ComplexUnitSphere N,
          concreteCenteredEll 1 N K (A, v) ^ 4 ∂sphere := by
      apply integral_congr_ae
      filter_upwards [] with v
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    _ = 16 * ∫ v : ComplexUnitSphere N,
          (complexProjectiveTracePair v A0).re ^ 4 ∂sphere := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with v
      rw [hpair v]
      ring
    _ = 16 * ((n * (n + 1) * (n + 2) * (n + 3))⁻¹ *
          (3 * t2 ^ 2 + 6 * t4)) := by
      rw [hexact]
      rw [ht2eq]
      dsimp only [n, t4]
      ring
    _ ≤ 16 * ((n * (n + 1) * (n + 2) * (n + 3))⁻¹ *
          (9 * t2 ^ 2)) := by
      gcongr
      nlinarith
    _ ≤ 16 * ((n ^ 4)⁻¹ * (9 * t2 ^ 2)) := by
      gcongr
    _ ≤ 1024 * t2 ^ 2 / n ^ 4 := by
      rw [inv_eq_one_div]
      field_simp [ne_of_gt hn]
      nlinarith [sq_nonneg t2]
    _ = h12ProjectiveFourthEnvelope N K A := by
      rfl

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
