import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H13_PureSixWordProjectiveExpansion
import Mathlib.Tactic

/-!
# Exact projective expansion of the one-transpose H13 words

Three of the four mixed words in the support-normal-form H13 kernel have the
common shape

`Tr(Q_v A Q_v.transpose B Q_v C)`.

This file expands that shape into scalar projective pairings.  The new mixed
pairing `Tr(P_v A P_v.transpose B)` contains exactly two rank-one projectors;
all other projective terms are linear.  Consequently multiplication by the
first centered trace has total projective degree at most four.  This is pure
finite matrix algebra and uses no probability or scientific input.
-/

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

set_option maxHeartbeats 2400000

/-- The two-projector mixed transpose pairing occurring in the H13 words. -/
def complexProjectiveMixedTransposePair
    {N : ℕ} (v : ComplexUnitSphere N)
    (A B : ConcreteMatrixState N) : ℂ :=
  Matrix.trace
    (complexRankOneProjection v * A *
      (complexRankOneProjection v).transpose * B)

/-- The linear pairing with the transposed rank-one projector. -/
def complexTransposeProjectiveTracePair
    {N : ℕ} (v : ComplexUnitSphere N)
    (A : ConcreteMatrixState N) : ℂ :=
  Matrix.trace ((complexRankOneProjection v).transpose * A)

/-- The maximal three-projector word factors as one ordinary trace pairing
times one mixed transpose pairing. -/
theorem trace_rankOne_mixedTranspose_rankOne_factor_h13
    {N : ℕ} (v : ComplexUnitSphere N)
    (A B C : ConcreteMatrixState N) :
    Matrix.trace
        (complexRankOneProjection v * A *
          (complexRankOneProjection v).transpose * B *
          complexRankOneProjection v * C) =
      complexProjectiveTracePair v C *
        complexProjectiveMixedTransposePair v A B := by
  let P := complexRankOneProjection v
  have hcompress : P * C * P =
      complexProjectiveTracePair v C • P := by
    simpa only [P] using
      complexRankOneProjection_mul_mul_eq_tracePair_smul_h14 v C
  calc
    Matrix.trace (P * A * P.transpose * B * P * C) =
        Matrix.trace ((P * A * P.transpose * B) * (P * C)) := by
      congr 1
      noncomm_ring
    _ = Matrix.trace ((P * C) * (P * A * P.transpose * B)) :=
      Matrix.trace_mul_comm _ _
    _ = Matrix.trace ((P * C * P) * A * P.transpose * B) := by
      congr 1
      noncomm_ring
    _ = Matrix.trace
        ((complexProjectiveTracePair v C • P) * A * P.transpose * B) := by
      rw [hcompress]
    _ = complexProjectiveTracePair v C *
        complexProjectiveMixedTransposePair v A B := by
      simp only [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
      rfl

/-- Moving the ordinary rank-one projector cyclically identifies the other
two-projector word with the same mixed pairing. -/
theorem trace_mul_transposeRankOne_mul_mul_rankOne_eq_mixedPair_h13
    {N : ℕ} (v : ComplexUnitSphere N)
    (A B C : ConcreteMatrixState N) :
    Matrix.trace
        (A * (complexRankOneProjection v).transpose * B *
          complexRankOneProjection v * C) =
      complexProjectiveMixedTransposePair v (C * A) B := by
  let P := complexRankOneProjection v
  calc
    Matrix.trace (A * P.transpose * B * P * C) =
        Matrix.trace ((A * P.transpose * B) * (P * C)) := by
      congr 1
      noncomm_ring
    _ = Matrix.trace ((P * C) * (A * P.transpose * B)) :=
      Matrix.trace_mul_comm _ _
    _ = Matrix.trace (P * (C * A) * P.transpose * B) := by
      congr 1
      noncomm_ring
    _ = complexProjectiveMixedTransposePair v (C * A) B := rfl

/-- The explicit scalar expansion of `Tr(Q A Q.transpose B Q C)`. -/
def h13CenteredTripleMixedTransposeExpansion
    {N : ℕ} (v : ComplexUnitSphere N)
    (A B C : ConcreteMatrixState N) : ℂ :=
  let a : ℂ := (((N : ℝ)⁻¹ : ℝ) : ℂ)
  let p : ConcreteMatrixState N → ℂ := fun X ↦
    complexProjectiveTracePair v X
  let m : ConcreteMatrixState N → ConcreteMatrixState N → ℂ := fun X Y ↦
    complexProjectiveMixedTransposePair v X Y
  p C * m A B -
    a * (m (C * A) B + p (A * B) * p C + m A (B * C)) +
    a ^ 2 *
      (p (C * A * B) + complexTransposeProjectiveTracePair v (B * C * A) +
        p (A * B * C)) -
    a ^ 3 * Matrix.trace (A * B * C)

/-- Exact generic expansion of a centered triple word containing one
transposed centered direction. -/
theorem trace_centeredDirection_mixedTranspose_threeWord_expansion_h13
    {N : ℕ} (v : ComplexUnitSphere N)
    (A B C : ConcreteMatrixState N) :
    Matrix.trace
        (concreteCenteredOrbitalDirection N v * A *
          (concreteCenteredOrbitalDirection N v).transpose * B *
          concreteCenteredOrbitalDirection N v * C) =
      h13CenteredTripleMixedTransposeExpansion v A B C := by
  let P := complexRankOneProjection v
  let Q := concreteCenteredOrbitalDirection N v
  let a : ℂ := (((N : ℝ)⁻¹ : ℝ) : ℂ)
  have hQ : Q = P - a • (1 : ConcreteMatrixState N) := by rfl
  have hQt : Q.transpose = P.transpose - a • (1 : ConcreteMatrixState N) := by
    rw [hQ]
    simp only [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one]
  have hExpand :
      Q * A * Q.transpose * B * Q * C =
        P * A * P.transpose * B * P * C -
          a • (A * P.transpose * B * P * C + P * A * B * P * C +
            P * A * P.transpose * B * C) +
          a ^ 2 • (A * B * P * C + A * P.transpose * B * C +
            P * A * B * C) -
          a ^ 3 • (A * B * C) := by
    rw [hQt, hQ]
    noncomm_ring
    module
  have hPPP : Matrix.trace (P * A * P.transpose * B * P * C) =
      complexProjectiveTracePair v C *
        complexProjectiveMixedTransposePair v A B := by
    simpa only [P] using
      trace_rankOne_mixedTranspose_rankOne_factor_h13 v A B C
  have hIPP : Matrix.trace (A * P.transpose * B * P * C) =
      complexProjectiveMixedTransposePair v (C * A) B := by
    simpa only [P] using
      trace_mul_transposeRankOne_mul_mul_rankOne_eq_mixedPair_h13 v A B C
  have hPIP : Matrix.trace (P * A * B * P * C) =
      complexProjectiveTracePair v (A * B) *
        complexProjectiveTracePair v C := by
    rw [show P * A * B * P * C = P * (A * B) * P * C by
      noncomm_ring]
    simpa only [P] using trace_rankOne_mul_mul_mul_h14 v (A * B) C
  have hPPI : Matrix.trace (P * A * P.transpose * B * C) =
      complexProjectiveMixedTransposePair v A (B * C) := by
    rw [show P * A * P.transpose * B * C =
        P * A * P.transpose * (B * C) by noncomm_ring]
    rfl
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
  have hIPI : Matrix.trace (A * P.transpose * B * C) =
      complexTransposeProjectiveTracePair v (B * C * A) := by
    calc
      Matrix.trace (A * P.transpose * B * C) =
          Matrix.trace (A * (P.transpose * B * C)) := by
        congr 1
        noncomm_ring
      _ = Matrix.trace ((P.transpose * B * C) * A) :=
        Matrix.trace_mul_comm _ _
      _ = Matrix.trace (P.transpose * (B * C * A)) := by
        congr 1
        noncomm_ring
      _ = complexTransposeProjectiveTracePair v (B * C * A) := rfl
  have hPII : Matrix.trace (P * A * B * C) =
      complexProjectiveTracePair v (A * B * C) := by
    rw [show P * A * B * C = P * (A * B * C) by noncomm_ring]
    simpa only [P] using
      (complexProjectiveTracePair_eq_trace v (A * B * C)).symm
  change Matrix.trace (Q * A * Q.transpose * B * Q * C) = _
  rw [hExpand]
  simp only [Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul,
    smul_eq_mul]
  rw [hPPP, hIPP, hPIP, hPPI, hIIP, hIPI, hPII]
  unfold h13CenteredTripleMixedTransposeExpansion
  simp only [a]

/-- The second, fourth and fifth H13 kernel words share the preceding exact
one-transpose expansion. -/
def h13CommonMixedSixWordProjectiveExpansion
    {N : ℕ} (v : ComplexUnitSphere N)
    (W A T Ts Z : ConcreteMatrixState N) : ℂ :=
  h13CenteredTripleMixedTransposeExpansion v T Ts Z +
    h13CenteredTripleMixedTransposeExpansion v T Ts W +
    h13CenteredTripleMixedTransposeExpansion v T Ts A

theorem h13CommonMixedSixWord_eq_projectiveExpansion
    {N : ℕ} (v : ComplexUnitSphere N)
    (W A T Ts Z : ConcreteMatrixState N) :
    Matrix.trace
        (concreteCenteredOrbitalDirection N v * T *
          (concreteCenteredOrbitalDirection N v).transpose * Ts *
          concreteCenteredOrbitalDirection N v * Z) +
      Matrix.trace
        (concreteCenteredOrbitalDirection N v * W *
          concreteCenteredOrbitalDirection N v * T *
          (concreteCenteredOrbitalDirection N v).transpose * Ts) +
      Matrix.trace
        (concreteCenteredOrbitalDirection N v * A *
          concreteCenteredOrbitalDirection N v * T *
          (concreteCenteredOrbitalDirection N v).transpose * Ts) =
      h13CommonMixedSixWordProjectiveExpansion v W A T Ts Z := by
  rw [trace_centeredDirection_mixedTranspose_threeWord_expansion_h13]
  rw [show Matrix.trace
      (concreteCenteredOrbitalDirection N v * W *
        concreteCenteredOrbitalDirection N v * T *
        (concreteCenteredOrbitalDirection N v).transpose * Ts) =
      Matrix.trace
        (concreteCenteredOrbitalDirection N v * T *
          (concreteCenteredOrbitalDirection N v).transpose * Ts *
          concreteCenteredOrbitalDirection N v * W) by
    calc
      _ = Matrix.trace
          ((concreteCenteredOrbitalDirection N v * W) *
            (concreteCenteredOrbitalDirection N v * T *
              (concreteCenteredOrbitalDirection N v).transpose * Ts)) := by
        congr 1
        noncomm_ring
      _ = Matrix.trace
          ((concreteCenteredOrbitalDirection N v * T *
              (concreteCenteredOrbitalDirection N v).transpose * Ts) *
            (concreteCenteredOrbitalDirection N v * W)) :=
        Matrix.trace_mul_comm _ _
      _ = _ := by
        congr 1
        noncomm_ring]
  rw [trace_centeredDirection_mixedTranspose_threeWord_expansion_h13]
  rw [show Matrix.trace
      (concreteCenteredOrbitalDirection N v * A *
        concreteCenteredOrbitalDirection N v * T *
        (concreteCenteredOrbitalDirection N v).transpose * Ts) =
      Matrix.trace
        (concreteCenteredOrbitalDirection N v * T *
          (concreteCenteredOrbitalDirection N v).transpose * Ts *
          concreteCenteredOrbitalDirection N v * A) by
    calc
      _ = Matrix.trace
          ((concreteCenteredOrbitalDirection N v * A) *
            (concreteCenteredOrbitalDirection N v * T *
              (concreteCenteredOrbitalDirection N v).transpose * Ts)) := by
        congr 1
        noncomm_ring
      _ = Matrix.trace
          ((concreteCenteredOrbitalDirection N v * T *
              (concreteCenteredOrbitalDirection N v).transpose * Ts) *
            (concreteCenteredOrbitalDirection N v * A)) :=
        Matrix.trace_mul_comm _ _
      _ = _ := by
        congr 1
        noncomm_ring]
  rw [trace_centeredDirection_mixedTranspose_threeWord_expansion_h13]
  rfl

/-- Multiplying the three common mixed words by the first centered trace
exposes a scalar polynomial of total projective degree at most four. -/
def h13CommonMixedOneThreeProjectivePolynomial
    {N : ℕ} (v : ComplexUnitSphere N)
    (Y W A T Ts Z : ConcreteMatrixState N) : ℂ :=
  (complexProjectiveTracePair v Y -
      (((N : ℝ)⁻¹ : ℝ) : ℂ) * Matrix.trace Y) *
    h13CommonMixedSixWordProjectiveExpansion v W A T Ts Z

theorem trace_centeredDirection_mul_h13CommonMixedSixWord_eq_projectivePolynomial
    {N : ℕ} (v : ComplexUnitSphere N)
    (Y W A T Ts Z : ConcreteMatrixState N) :
    Matrix.trace (concreteCenteredOrbitalDirection N v * Y) *
      (Matrix.trace
          (concreteCenteredOrbitalDirection N v * T *
            (concreteCenteredOrbitalDirection N v).transpose * Ts *
            concreteCenteredOrbitalDirection N v * Z) +
        Matrix.trace
          (concreteCenteredOrbitalDirection N v * W *
            concreteCenteredOrbitalDirection N v * T *
            (concreteCenteredOrbitalDirection N v).transpose * Ts) +
        Matrix.trace
          (concreteCenteredOrbitalDirection N v * A *
            concreteCenteredOrbitalDirection N v * T *
            (concreteCenteredOrbitalDirection N v).transpose * Ts)) =
      h13CommonMixedOneThreeProjectivePolynomial v Y W A T Ts Z := by
  rw [trace_concreteCenteredOrbitalDirection_mul,
    h13CommonMixedSixWord_eq_projectiveExpansion]
  rfl

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
