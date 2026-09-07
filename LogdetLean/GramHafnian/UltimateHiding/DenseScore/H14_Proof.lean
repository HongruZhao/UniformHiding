import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ClassicalCenteredLogScoreMomentExternal
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CenteredDensityScoreOneDerived
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CenteredDensityScoreTwoDerived
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H14_XHRBookkeeping
import Mathlib.Tactic

/-!
# H14 symbolic proof: the second centered logarithmic score

This module contains only pointwise score algebra.  On the open COE support,
the second Bell identity says that the second log score is the second density
score minus the square of the first density score.  Substitution of the two
public density-score formulae then cancels the squared projective trace and
leaves the two genuinely quadratic centered sandwiches.

No probability estimate and neither the H12 nor H14 external moment package
is used in these proofs.
-/

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- The exact centered-sandwich expression for the second log score. -/
def h14CenteredSandwichSecondScore (N K : ℕ)
    (A : ConcreteMatrixState N) (v : ComplexUnitSphere N) : ℝ :=
  -4 *
    ((complexCenteredProjectiveSandwich v
        (concreteCOEWMatrix N K A) (concreteCOEY N K A)).re +
      (complexCenteredProjectiveConjugateSandwich v
        (concreteCOERMatrix N K A)).re)

/-- Its pointwise square, before any integration or matrix estimate. -/
def h14CenteredSandwichSecondSquare (N K : ℕ)
    (A : ConcreteMatrixState N) (v : ComplexUnitSphere N) : ℝ :=
  h14CenteredSandwichSecondScore N K A v ^ 2

/-- A candidate `768` traceless-bracket envelope, retained for the explicitly
conditional projective-contraction route.  Unlike H12, H14 has a radial
curvature contribution, so no unconditional domination by this expression
is asserted here. -/
def h14TracelessSquareEnvelope (N K : ℕ)
    (A : ConcreteMatrixState N) : ℝ :=
  768 * (concreteCOETraceTwo N K A -
      (N : ℝ)⁻¹ * concreteCOETraceOne N K A ^ 2) ^ 2 /
    ((N : ℝ) ^ 2 * ((N : ℝ) + 1) ^ 2)

theorem h14TracelessSquareEnvelope_nonneg
    (N K : ℕ) (A : ConcreteMatrixState N) :
    0 ≤ h14TracelessSquareEnvelope N K A := by
  unfold h14TracelessSquareEnvelope
  positivity

/-- Radial trace envelope corresponding to the standard pointwise estimate
`|ell₂| ≤ 16 y (1+y/c)` and the support inequalities
`y² ≤ Tr(Y²)`, `y⁴ ≤ Tr(Y²)²`.  The absolute value makes the
total function nonnegative away from the COE support as well. -/
def h14RadialTraceEnvelope (N K : ℕ)
    (A : ConcreteMatrixState N) : ℝ :=
  512 * (|concreteCOETraceTwo N K A| +
    concreteCOETraceTwo N K A ^ 2 / concreteCOEExponent N K ^ 2)

theorem h14RadialTraceEnvelope_nonneg
    (N K : ℕ) (A : ConcreteMatrixState N) :
    0 ≤ h14RadialTraceEnvelope N K A := by
  unfold h14RadialTraceEnvelope
  positivity

theorem h14CenteredSandwichSecondSquare_nonneg
    (N K : ℕ) (A : ConcreteMatrixState N) (v : ComplexUnitSphere N) :
    0 ≤ h14CenteredSandwichSecondSquare N K A v := by
  unfold h14CenteredSandwichSecondSquare
  positivity

/-- A Hermitian matrix has real centered projective trace in every projective
direction.  This is the elementary reality fact needed for the Bell-square
cancellation. -/
theorem complexCenteredProjectiveTracePair_im_zero_internal
    {N : ℕ} (v : ComplexUnitSphere N) (Y : ConcreteMatrixState N)
    (hY : Y.IsHermitian) :
    (complexCenteredProjectiveTracePair v Y).im = 0 := by
  rw [← trace_concreteCenteredOrbitalDirection_mul]
  have hQ := concreteCenteredOrbitalDirection_isHermitian v
  apply Complex.conj_eq_iff_im.mp
  calc
    star (Matrix.trace (concreteCenteredOrbitalDirection N v * Y)) =
        Matrix.trace
          ((concreteCenteredOrbitalDirection N v * Y).conjTranspose) := by
      rw [Matrix.trace_conjTranspose]
    _ = Matrix.trace (Y * concreteCenteredOrbitalDirection N v) := by
      rw [Matrix.conjTranspose_mul, hY.eq, hQ.eq]
    _ = Matrix.trace (concreteCenteredOrbitalDirection N v * Y) :=
      Matrix.trace_mul_comm _ _

/-- Exact Bell inversion for the literal second centered log score, followed
by substitution of the public first- and second-density-score formulae. -/
theorem centeredLogScore_two_eq_densityScore_sub_firstSquare_internal
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (A : ConcreteMatrixState N) (v : ComplexUnitSphere N)
    (hsymm : (unscaleCOECorner K A).IsSymm)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    concreteCenteredEll 2 N K (A, v) =
      concreteCenteredRankOneSecondDensityScore N K v A -
        concreteCenteredRankOneFirstDensityScore N K v A ^ 2 := by
  have hBell := coeCorner_centeredDensityScore_two_eq_Bell
    hN v A hsupport
  have hOne : concreteCenteredLogScore 1 N K v A =
      concreteCenteredRankOneFirstDensityScore N K v A := by
    calc
      concreteCenteredLogScore 1 N K v A =
          concreteCenteredDensityScore 1 N K v A :=
        (coeCorner_centeredDensityScore_one_eq_logScore
          hN v A hsupport).symm
      _ = concreteCenteredRankOneFirstDensityScore N K v A :=
        coeCorner_centeredDensityScore_one_eq_explicit_external_derived
          hN hgap v A hsymm hsupport
  have hTwo : concreteCenteredDensityScore 2 N K v A =
      concreteCenteredRankOneSecondDensityScore N K v A :=
    coeCorner_centeredDensityScore_two_eq_explicit_external_derived
      hN hgap v A hsymm hsupport
  unfold concreteCenteredEll
  rw [hTwo] at hBell
  rw [hOne] at hBell
  linarith

/-- Fully expanded second log score.  The first-score square cancels the
projective-trace square exactly; only the two centered sandwich contractions
remain. -/
theorem centeredLogScore_two_eq_centeredSandwiches_internal
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (A : ConcreteMatrixState N) (v : ComplexUnitSphere N)
    (hsymm : (unscaleCOECorner K A).IsSymm)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    concreteCenteredEll 2 N K (A, v) =
      -4 *
        ((complexCenteredProjectiveSandwich v
            (concreteCOEWMatrix N K A) (concreteCOEY N K A)).re +
          (complexCenteredProjectiveConjugateSandwich v
            (concreteCOERMatrix N K A)).re) := by
  rw [centeredLogScore_two_eq_densityScore_sub_firstSquare_internal
    hN hgap A v hsymm hsupport]
  have him :
      (complexCenteredProjectiveTracePair v (concreteCOEY N K A)).im = 0 :=
    complexCenteredProjectiveTracePair_im_zero_internal v
      (concreteCOEY N K A)
      (concreteCOEY_isHermitian_of_support A hsupport)
  have hsq :
      (complexCenteredProjectiveTracePair v (concreteCOEY N K A) ^ 2).re =
        (complexCenteredProjectiveTracePair v
          (concreteCOEY N K A)).re ^ 2 := by
    rw [pow_two]
    simp [Complex.mul_re, him]
    ring
  unfold concreteCenteredRankOneFirstDensityScore
    concreteCenteredRankOneFirstDensityScoreComplex
    concreteCenteredRankOneSecondDensityScore
    concreteCenteredRankOneSecondDensityScoreComplex
  simp [Complex.mul_re, Complex.sub_re, him, hsq]
  ring

/-- Definition-packaged form of the exact symbolic expansion. -/
theorem centeredLogScore_two_eq_h14CenteredSandwichSecondScore_internal
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (A : ConcreteMatrixState N) (v : ComplexUnitSphere N)
    (hsymm : (unscaleCOECorner K A).IsSymm)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    concreteCenteredEll 2 N K (A, v) =
      h14CenteredSandwichSecondScore N K A v := by
  simpa only [h14CenteredSandwichSecondScore] using
    centeredLogScore_two_eq_centeredSandwiches_internal
      hN hgap A v hsymm hsupport

/-- Squared form used by the separate conditional probability module. -/
theorem centeredLogScore_two_square_eq_h14CenteredSandwichSecondSquare_internal
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (A : ConcreteMatrixState N) (v : ComplexUnitSphere N)
    (hsymm : (unscaleCOECorner K A).IsSymm)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    concreteCenteredEll 2 N K (A, v) ^ 2 =
      h14CenteredSandwichSecondSquare N K A v := by
  rw [centeredLogScore_two_eq_h14CenteredSandwichSecondScore_internal
    hN hgap A v hsymm hsupport]
  rfl

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
