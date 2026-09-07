import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H13_OneThreeSupportVelocityReduction
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H11_FourProjectiveTraceWord
import Mathlib.Tactic

/-!
# Exact projective expansion of the pure H13 six-word terms

Two of the six support-normal-form H13 words contain three ordinary centered
projectors and no transpose.  This file expands the generic cyclic word

`Tr(Q_v A Q_v B Q_v C)`

into scalar rank-one trace pairings.  Multiplication by the first centered
trace then gives an explicit projective polynomial of degree at most four.

The remaining four H13 words contain `Q_v.transpose`; they require the
bilinear/conjugate projective contraction used in H14 and are intentionally
left separate.  No probability or scientific input occurs here.
-/

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

set_option maxHeartbeats 2400000

/-- Scalar rank-one expansion of `Tr(Q_v A Q_v B Q_v C)`. -/
def h13CenteredTripleTraceProjectiveExpansion
    {N : ℕ} (v : ComplexUnitSphere N)
    (A B C : ConcreteMatrixState N) : ℂ :=
  let a : ℂ := (((N : ℝ)⁻¹ : ℝ) : ℂ)
  let p : ConcreteMatrixState N → ℂ := fun X ↦
    complexProjectiveTracePair v X
  p A * p B * p C -
    a * (p B * p (C * A) + p (A * B) * p C + p A * p (B * C)) +
    a ^ 2 * (p (A * B * C) + p (B * C * A) + p (C * A * B)) -
    a ^ 3 * Matrix.trace (A * B * C)

/-- Exact generic cubic centered-word expansion. -/
theorem trace_centeredDirection_threeWord_expansion_h13
    {N : ℕ} (v : ComplexUnitSphere N)
    (A B C : ConcreteMatrixState N) :
    Matrix.trace
        (concreteCenteredOrbitalDirection N v * A *
          concreteCenteredOrbitalDirection N v * B *
          concreteCenteredOrbitalDirection N v * C) =
      h13CenteredTripleTraceProjectiveExpansion v A B C := by
  let P := complexRankOneProjection v
  let Q := concreteCenteredOrbitalDirection N v
  let a : ℂ := (((N : ℝ)⁻¹ : ℝ) : ℂ)
  have hQ : Q = P - a • (1 : ConcreteMatrixState N) := by rfl
  have hExpand :
      Q * A * Q * B * Q * C =
        P * A * P * B * P * C -
          a • (A * P * B * P * C + P * A * B * P * C +
            P * A * P * B * C) +
          a ^ 2 • (A * B * P * C + A * P * B * C + P * A * B * C) -
          a ^ 3 • (A * B * C) := by
    rw [hQ]
    noncomm_ring
    module
  have hPPP : Matrix.trace (P * A * P * B * P * C) =
      complexProjectiveTracePair v A *
        complexProjectiveTracePair v B *
        complexProjectiveTracePair v C := by
    simpa only [P] using trace_rankOne_mul_threeTracePairs_h11 v A B C
  have hIPP : Matrix.trace (A * P * B * P * C) =
      complexProjectiveTracePair v B *
        complexProjectiveTracePair v (C * A) := by
    calc
      Matrix.trace (A * P * B * P * C) =
          Matrix.trace (A * (P * B * P * C)) := by
        congr 1
        noncomm_ring
      _ = Matrix.trace ((P * B * P * C) * A) :=
        Matrix.trace_mul_comm _ _
      _ = Matrix.trace (P * B * P * (C * A)) := by
        congr 1
        noncomm_ring
      _ = complexProjectiveTracePair v B *
          complexProjectiveTracePair v (C * A) := by
        simpa only [P] using trace_rankOne_mul_mul_mul_h14 v B (C * A)
  have hPIP : Matrix.trace (P * A * B * P * C) =
      complexProjectiveTracePair v (A * B) *
        complexProjectiveTracePair v C := by
    rw [show P * A * B * P * C = P * (A * B) * P * C by
      noncomm_ring]
    simpa only [P] using trace_rankOne_mul_mul_mul_h14 v (A * B) C
  have hPPI : Matrix.trace (P * A * P * B * C) =
      complexProjectiveTracePair v A *
        complexProjectiveTracePair v (B * C) := by
    rw [show P * A * P * B * C = P * A * P * (B * C) by
      noncomm_ring]
    simpa only [P] using trace_rankOne_mul_mul_mul_h14 v A (B * C)
  have hIIP : Matrix.trace (A * B * P * C) =
      complexProjectiveTracePair v (C * A * B) := by
    calc
      Matrix.trace (A * B * P * C) =
          Matrix.trace ((A * B) * (P * C)) := by
        congr 1
        noncomm_ring
      _ = Matrix.trace ((P * C) * (A * B)) :=
        Matrix.trace_mul_comm _ _
      _ = Matrix.trace (P * (C * A * B)) := by
        congr 1
        noncomm_ring
      _ = complexProjectiveTracePair v (C * A * B) := by
        simpa only [P] using
          (complexProjectiveTracePair_eq_trace v (C * A * B)).symm
  have hIPI : Matrix.trace (A * P * B * C) =
      complexProjectiveTracePair v (B * C * A) := by
    calc
      Matrix.trace (A * P * B * C) =
          Matrix.trace (A * (P * B * C)) := by
        congr 1
        noncomm_ring
      _ = Matrix.trace ((P * B * C) * A) :=
        Matrix.trace_mul_comm _ _
      _ = Matrix.trace (P * (B * C * A)) := by
        congr 1
        noncomm_ring
      _ = complexProjectiveTracePair v (B * C * A) := by
        simpa only [P] using
          (complexProjectiveTracePair_eq_trace v (B * C * A)).symm
  have hPII : Matrix.trace (P * A * B * C) =
      complexProjectiveTracePair v (A * B * C) := by
    rw [show P * A * B * C = P * (A * B * C) by noncomm_ring]
    simpa only [P] using
      (complexProjectiveTracePair_eq_trace v (A * B * C)).symm
  change Matrix.trace (Q * A * Q * B * Q * C) = _
  rw [hExpand]
  simp only [Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul,
    smul_eq_mul]
  rw [hPPP, hIPP, hPIP, hPPI, hIIP, hIPI, hPII]
  unfold h13CenteredTripleTraceProjectiveExpansion
  simp only [a]
  ring

/-- The sum of the first and third terms in the H13 six-word kernel, already
expanded into scalar projective trace pairings. -/
def h13PureSixWordProjectiveExpansion
    {N : ℕ} (v : ComplexUnitSphere N)
    (W Z : ConcreteMatrixState N) : ℂ :=
  h13CenteredTripleTraceProjectiveExpansion v W Z Z +
    h13CenteredTripleTraceProjectiveExpansion v W W Z

theorem h13PureSixWord_eq_projectiveExpansion
    {N : ℕ} (v : ComplexUnitSphere N)
    (W Z : ConcreteMatrixState N) :
    Matrix.trace
        (concreteCenteredOrbitalDirection N v * W *
          concreteCenteredOrbitalDirection N v * Z *
          concreteCenteredOrbitalDirection N v * Z) +
      Matrix.trace
        (concreteCenteredOrbitalDirection N v * W *
          concreteCenteredOrbitalDirection N v * W *
          concreteCenteredOrbitalDirection N v * Z) =
      h13PureSixWordProjectiveExpansion v W Z := by
  rw [trace_centeredDirection_threeWord_expansion_h13,
    trace_centeredDirection_threeWord_expansion_h13]
  rfl

/-- Multiplication by the first centered trace exposes the promised total
projective degree at most four for the two pure six-word terms. -/
def h13PureOneThreeProjectivePolynomial
    {N : ℕ} (v : ComplexUnitSphere N)
    (Y W Z : ConcreteMatrixState N) : ℂ :=
  (complexProjectiveTracePair v Y -
      (((N : ℝ)⁻¹ : ℝ) : ℂ) * Matrix.trace Y) *
    h13PureSixWordProjectiveExpansion v W Z

theorem trace_centeredDirection_mul_h13PureSixWord_eq_projectivePolynomial
    {N : ℕ} (v : ComplexUnitSphere N)
    (Y W Z : ConcreteMatrixState N) :
    Matrix.trace (concreteCenteredOrbitalDirection N v * Y) *
      (Matrix.trace
          (concreteCenteredOrbitalDirection N v * W *
            concreteCenteredOrbitalDirection N v * Z *
            concreteCenteredOrbitalDirection N v * Z) +
        Matrix.trace
          (concreteCenteredOrbitalDirection N v * W *
            concreteCenteredOrbitalDirection N v * W *
            concreteCenteredOrbitalDirection N v * Z)) =
      h13PureOneThreeProjectivePolynomial v Y W Z := by
  rw [trace_concreteCenteredOrbitalDirection_mul,
    h13PureSixWord_eq_projectiveExpansion]
  rfl

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
