import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H11H13_ExactIndependentReduction
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CenteredDensityScoreTwoScratch
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CenteredLogScoreOneSquareTwoDerived
import Mathlib.Tactic

/-!
# H13 deterministic reduction to one explicit trace-kernel derivative

The literal first centered logarithmic score is already explicit.  This file
proves its operator-radius bound and removes it completely from the remaining
H13 deterministic calculation.  The only deterministic estimate left is a bound
for the derivative of `centeredThirdLogTraceKernel`, the concrete rational
matrix expression whose derivative is the third log score.

There is no probability or scientific axiom in this file.
-/

open MeasureTheory
open scoped Matrix.Norms.L2Operator

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- The literal first log score agrees with the explicit centered projective
trace formula on the open COE support. -/
theorem concreteCenteredEll_one_eq_firstDensityScore_h13_internal
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (A : ConcreteMatrixState N) (v : ComplexUnitSphere N)
    (hsymm : (unscaleCOECorner K A).IsSymm)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    concreteCenteredEll 1 N K (A, v) =
      concreteCenteredRankOneFirstDensityScore N K v A := by
  unfold concreteCenteredEll
  calc
    concreteCenteredLogScore 1 N K v A =
        concreteCenteredDensityScore 1 N K v A :=
      (coeCorner_centeredDensityScore_one_eq_logScore
        hN v A hsupport).symm
    _ = concreteCenteredRankOneFirstDensityScore N K v A :=
      coeCorner_centeredDensityScore_one_eq_explicit_external_derived
        hN hgap v A hsymm hsupport

/-- Exact operator-radius bound for the first log score.  Thus the first
factor in H13 is not an independent deterministic blocker. -/
theorem concreteCenteredEll_one_abs_le_four_opRadius_h13_internal
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (A : ConcreteMatrixState N) (v : ComplexUnitSphere N)
    (hsymm : (unscaleCOECorner K A).IsSymm)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    |concreteCenteredEll 1 N K (A, v)| ≤
      4 * concreteHigherScoreOpRadius N K A := by
  rw [concreteCenteredEll_one_eq_firstDensityScore_h13_internal
    hN hgap A v hsymm hsupport]
  have hpair :=
    abs_re_trace_centeredDirection_mul_le_two_h14 hN v
      (concreteCOEY N K A)
  rw [trace_concreteCenteredOrbitalDirection_mul] at hpair
  unfold concreteCenteredRankOneFirstDensityScore
    concreteCenteredRankOneFirstDensityScoreComplex
    concreteHigherScoreOpRadius
  norm_num [Complex.mul_re]
  calc
    2 * |(complexCenteredProjectiveTracePair v
        (concreteCOEY N K A)).re| ≤
        2 * (2 * ‖concreteCOEY N K A‖) :=
      mul_le_mul_of_nonneg_left hpair (by norm_num)
    _ = 4 * ‖concreteCOEY N K A‖ := by ring

/-- The genuinely remaining deterministic H13 input.  It mentions no log
score: it is only the derivative of the explicit finite trace-resolvent
kernel.  Global measurability of the third totalized derivative is proved
internally in `CenteredLogScoreOneSquareTwoDerived`. -/
structure H13ThirdTraceKernelDerivativePackage (N K : ℕ) : Prop where
  derivative_abs_le_on_support :
    ∀ (A : ConcreteMatrixState N) (v : ComplexUnitSphere N),
      (unscaleCOECorner K A).IsSymm →
      coeCornerSupport (unscaleCOECorner K A) →
      |deriv (fun t : ℝ ↦ -8 *
          (centeredThirdLogTraceKernel
            (concreteCenteredOrbitalDirection N v)
            (unscaleCOECorner K A) t).re) 0| ≤
        512 *
          (concreteHigherScoreOpRadius N K A /
            concreteCOEExponent N K) *
          (1 + concreteHigherScoreOpRadius N K A /
            concreteCOEExponent N K) ^ 2

/-- The trace-kernel derivative estimate gives the exact third-score radial
bound needed after multiplying by the internally bounded first score. -/
theorem concreteCenteredEll_three_abs_le_of_traceKernelDerivative_h13
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K)
    (A : ConcreteMatrixState N) (v : ComplexUnitSphere N)
    (hsymm : (unscaleCOECorner K A).IsSymm)
    (hsupport : coeCornerSupport (unscaleCOECorner K A))
    (hderiv :
      |deriv (fun t : ℝ ↦ -8 *
          (centeredThirdLogTraceKernel
            (concreteCenteredOrbitalDirection N v)
            (unscaleCOECorner K A) t).re) 0| ≤
        512 *
          (concreteHigherScoreOpRadius N K A /
            concreteCOEExponent N K) *
          (1 + concreteHigherScoreOpRadius N K A /
            concreteCOEExponent N K) ^ 2) :
    |concreteCenteredEll 3 N K (A, v)| ≤
      256 * concreteHigherScoreOpRadius N K A *
        (1 + concreteHigherScoreOpRadius N K A /
          concreteCOEExponent N K) ^ 2 := by
  let c : ℝ := concreteCOEExponent N K
  let r : ℝ := concreteHigherScoreOpRadius N K A
  let b : ℝ := 1 + r / c
  have hc : 0 < c := by
    simpa only [c] using concreteCOEExponent_pos_of_higherScoreGap hgap
  have hp_eq : coeCornerDensityExponent N K = c / 2 := by
    rfl
  have hp : 0 ≤ coeCornerDensityExponent N K := by
    rw [hp_eq]
    positivity
  have hscore := concreteCenteredLogScore_three_eq_traceKernel_deriv
    v A hsymm hsupport
  change |concreteCenteredLogScore 3 N K v A| ≤ _
  rw [hscore, abs_mul, abs_of_nonneg hp]
  change coeCornerDensityExponent N K *
      |deriv (fun t : ℝ ↦ -8 *
        (centeredThirdLogTraceKernel
          (concreteCenteredOrbitalDirection N v)
          (unscaleCOECorner K A) t).re) 0| ≤ _
  calc
    coeCornerDensityExponent N K *
        |deriv (fun t : ℝ ↦ -8 *
          (centeredThirdLogTraceKernel
            (concreteCenteredOrbitalDirection N v)
            (unscaleCOECorner K A) t).re) 0| ≤
        coeCornerDensityExponent N K * (512 * (r / c) * b ^ 2) :=
      mul_le_mul_of_nonneg_left (by simpa only [r, c, b] using hderiv) hp
    _ = 256 * r * b ^ 2 := by
      rw [hp_eq]
      field_simp [ne_of_gt hc]
      <;> ring
    _ = 256 * concreteHigherScoreOpRadius N K A *
        (1 + concreteHigherScoreOpRadius N K A /
          concreteCOEExponent N K) ^ 2 := by
      rfl

/-- The new trace-kernel package supplies the old H13 deterministic
interface.  In particular, the first score, its measurability, and its
operator-radius estimate are now all discharged internally. -/
theorem h13HigherScoreDeterministicEnvelope_of_traceKernelPackage
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (H : H13ThirdTraceKernelDerivativePackage N K) :
    H13HigherScoreDeterministicEnvelope N K := by
  constructor
  · exact (measurable_concreteCenteredEll_one hN).mul
      (measurable_concreteCenteredEll_three hN)
  · intro A v hsymm hsupport
    have hOne := concreteCenteredEll_one_abs_le_four_opRadius_h13_internal
      hN hgap A v hsymm hsupport
    have hThree :=
      concreteCenteredEll_three_abs_le_of_traceKernelDerivative_h13
        hgap A v hsymm hsupport
          (H.derivative_abs_le_on_support A v hsymm hsupport)
    have hr : 0 ≤ concreteHigherScoreOpRadius N K A :=
      concreteHigherScoreOpRadius_nonneg N K A
    have hc : 0 < concreteCOEExponent N K :=
      concreteCOEExponent_pos_of_higherScoreGap hgap
    have hb : 0 ≤ 1 + concreteHigherScoreOpRadius N K A /
        concreteCOEExponent N K :=
      add_nonneg zero_le_one (div_nonneg hr hc.le)
    rw [abs_mul]
    calc
      |concreteCenteredEll 1 N K (A, v)| *
          |concreteCenteredEll 3 N K (A, v)| ≤
          (4 * concreteHigherScoreOpRadius N K A) *
            (256 * concreteHigherScoreOpRadius N K A *
              (1 + concreteHigherScoreOpRadius N K A /
                concreteCOEExponent N K) ^ 2) :=
        mul_le_mul hOne hThree (abs_nonneg _)
          (mul_nonneg (by norm_num) hr)
      _ = h13HigherScoreRadialEnvelope N K A := by
        unfold h13HigherScoreRadialEnvelope
        ring

/-- Direct H13 endpoint reducer with the remaining deterministic gap stated
as an explicit trace-kernel derivative package. -/
theorem centeredLogScore_oneThree_momentPackage_of_opRadiusL4_and_traceKernel
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (Hradius : ConcreteHigherScoreOpRadiusL4Package N K)
    (Hkernel : H13ThirdTraceKernelDerivativePackage N K) :
    MemLp (fun p ↦ concreteCenteredEll 1 N K p *
      concreteCenteredEll 3 N K p) 1
        (concreteCenteredScoreProductLaw N K) ∧
      (16 * N ≤ K →
        lpNorm (fun p ↦ concreteCenteredEll 1 N K p *
          concreteCenteredEll 3 N K p) 1
            (concreteCenteredScoreProductLaw N K) ≤
          centeredLogScoreFourthMomentConstant * (N : ℝ) ^ 2) :=
  centeredLogScore_oneThree_momentPackage_of_opRadiusL4_and_deterministic
    hN hgap Hradius
      (h13HigherScoreDeterministicEnvelope_of_traceKernelPackage
        hN hgap Hkernel)

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
