import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H13_MixedSixWordProjectiveExpansion
import Mathlib.Tactic

/-!
# Exact projective expansion of the final H13 six-word term

The last support-normal-form word is the only one containing two transposed
centered directions.  This module expands the generic shape

`Tr(Q_v A Q_v.transpose B Q_v.transpose C)`.

The top term factors as one transposed linear projective pairing times the
two-projector mixed pairing from `H13_MixedSixWordProjectiveExpansion`.
Thus, after multiplication by the first centered trace, its total projective
degree is again at most four.  No probability or scientific input occurs.
-/

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

set_option maxHeartbeats 2400000

/-- Transposing an ordinary projective trace pairing exchanges the rank-one
projector and the matrix. -/
theorem complexProjectiveTracePair_transpose_eq_transposePair_h13
    {N : ℕ} (v : ComplexUnitSphere N) (A : ConcreteMatrixState N) :
    complexProjectiveTracePair v A.transpose =
      complexTransposeProjectiveTracePair v A := by
  rw [complexProjectiveTracePair_eq_trace]
  unfold complexTransposeProjectiveTracePair
  let P := complexRankOneProjection v
  change Matrix.trace (P * A.transpose) = Matrix.trace (P.transpose * A)
  calc
    Matrix.trace (P * A.transpose) =
        Matrix.trace (P * A.transpose).transpose :=
      (Matrix.trace_transpose _).symm
    _ = Matrix.trace (A * P.transpose) := by
      rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    _ = Matrix.trace (P.transpose * A) := Matrix.trace_mul_comm _ _

/-- Rank-one compression is stable under transpose. -/
theorem transposeRankOneProjection_mul_mul_eq_tracePair_smul_h13
    {N : ℕ} (v : ComplexUnitSphere N) (A : ConcreteMatrixState N) :
    (complexRankOneProjection v).transpose * A *
        (complexRankOneProjection v).transpose =
      complexTransposeProjectiveTracePair v A •
        (complexRankOneProjection v).transpose := by
  have h := congrArg Matrix.transpose
    (complexRankOneProjection_mul_mul_eq_tracePair_smul_h14 v A.transpose)
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.transpose_smul] at h
  rw [complexProjectiveTracePair_transpose_eq_transposePair_h13] at h
  simpa only [Matrix.mul_assoc] using h

/-- Two transposed rank-one projectors in one trace split into two transposed
linear trace pairings. -/
theorem trace_transposeRankOne_mul_twoTracePairs_h13
    {N : ℕ} (v : ComplexUnitSphere N)
    (A B : ConcreteMatrixState N) :
    Matrix.trace
        ((complexRankOneProjection v).transpose * A *
          (complexRankOneProjection v).transpose * B) =
      complexTransposeProjectiveTracePair v A *
        complexTransposeProjectiveTracePair v B := by
  rw [transposeRankOneProjection_mul_mul_eq_tracePair_smul_h13]
  simp only [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  rfl

/-- The maximal word with one ordinary and two transposed rank-one projectors
factors into three scalar projective factors. -/
theorem trace_rankOne_doubleTranspose_factor_h13
    {N : ℕ} (v : ComplexUnitSphere N)
    (A B C : ConcreteMatrixState N) :
    Matrix.trace
        (complexRankOneProjection v * A *
          (complexRankOneProjection v).transpose * B *
          (complexRankOneProjection v).transpose * C) =
      complexTransposeProjectiveTracePair v B *
        complexProjectiveMixedTransposePair v A C := by
  let P := complexRankOneProjection v
  have hcompress : P.transpose * B * P.transpose =
      complexTransposeProjectiveTracePair v B • P.transpose := by
    simpa only [P] using
      transposeRankOneProjection_mul_mul_eq_tracePair_smul_h13 v B
  rw [show P * A * P.transpose * B * P.transpose * C =
      P * A * (P.transpose * B * P.transpose) * C by noncomm_ring]
  rw [hcompress]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul,
    smul_eq_mul]
  unfold complexProjectiveMixedTransposePair
  ring

/-- The explicit scalar expansion of `Tr(Q A Q.transpose B Q.transpose C)`. -/
def h13CenteredTripleDoubleTransposeExpansion
    {N : ℕ} (v : ComplexUnitSphere N)
    (A B C : ConcreteMatrixState N) : ℂ :=
  let a : ℂ := (((N : ℝ)⁻¹ : ℝ) : ℂ)
  let p : ConcreteMatrixState N → ℂ := fun X ↦
    complexProjectiveTracePair v X
  let t : ConcreteMatrixState N → ℂ := fun X ↦
    complexTransposeProjectiveTracePair v X
  let m : ConcreteMatrixState N → ConcreteMatrixState N → ℂ := fun X Y ↦
    complexProjectiveMixedTransposePair v X Y
  t B * m A C -
    a * (t (C * A) * t B + m (A * B) C + m A (B * C)) +
    a ^ 2 * (t (C * A * B) + t (B * C * A) + p (A * B * C)) -
    a ^ 3 * Matrix.trace (A * B * C)

/-- Exact generic expansion of the final double-transpose centered word. -/
theorem trace_centeredDirection_doubleTranspose_threeWord_expansion_h13
    {N : ℕ} (v : ComplexUnitSphere N)
    (A B C : ConcreteMatrixState N) :
    Matrix.trace
        (concreteCenteredOrbitalDirection N v * A *
          (concreteCenteredOrbitalDirection N v).transpose * B *
          (concreteCenteredOrbitalDirection N v).transpose * C) =
      h13CenteredTripleDoubleTransposeExpansion v A B C := by
  let P := complexRankOneProjection v
  let Q := concreteCenteredOrbitalDirection N v
  let a : ℂ := (((N : ℝ)⁻¹ : ℝ) : ℂ)
  have hQ : Q = P - a • (1 : ConcreteMatrixState N) := by rfl
  have hQt : Q.transpose = P.transpose - a • (1 : ConcreteMatrixState N) := by
    rw [hQ]
    simp only [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one]
  have hExpand :
      Q * A * Q.transpose * B * Q.transpose * C =
        P * A * P.transpose * B * P.transpose * C -
          a • (A * P.transpose * B * P.transpose * C +
            P * A * B * P.transpose * C + P * A * P.transpose * B * C) +
          a ^ 2 • (A * B * P.transpose * C + A * P.transpose * B * C +
            P * A * B * C) -
          a ^ 3 • (A * B * C) := by
    rw [hQt, hQ]
    noncomm_ring
    module
  have hPPP : Matrix.trace (P * A * P.transpose * B * P.transpose * C) =
      complexTransposeProjectiveTracePair v B *
        complexProjectiveMixedTransposePair v A C := by
    simpa only [P] using trace_rankOne_doubleTranspose_factor_h13 v A B C
  have hIPP : Matrix.trace (A * P.transpose * B * P.transpose * C) =
      complexTransposeProjectiveTracePair v (C * A) *
        complexTransposeProjectiveTracePair v B := by
    calc
      Matrix.trace (A * P.transpose * B * P.transpose * C) =
          Matrix.trace ((A * P.transpose * B) * (P.transpose * C)) := by
        congr 1
        noncomm_ring
      _ = Matrix.trace ((P.transpose * C) * (A * P.transpose * B)) :=
        Matrix.trace_mul_comm _ _
      _ = Matrix.trace (P.transpose * (C * A) * P.transpose * B) := by
        congr 1
        noncomm_ring
      _ = _ := by
        simpa only [P] using
          trace_transposeRankOne_mul_twoTracePairs_h13 v (C * A) B
  have hPIP : Matrix.trace (P * A * B * P.transpose * C) =
      complexProjectiveMixedTransposePair v (A * B) C := by
    rw [show P * A * B * P.transpose * C =
        P * (A * B) * P.transpose * C by noncomm_ring]
    rfl
  have hPPI : Matrix.trace (P * A * P.transpose * B * C) =
      complexProjectiveMixedTransposePair v A (B * C) := by
    rw [show P * A * P.transpose * B * C =
        P * A * P.transpose * (B * C) by noncomm_ring]
    rfl
  have hIIP : Matrix.trace (A * B * P.transpose * C) =
      complexTransposeProjectiveTracePair v (C * A * B) := by
    calc
      Matrix.trace (A * B * P.transpose * C) =
          Matrix.trace ((A * B) * (P.transpose * C)) := by
        congr 1
        noncomm_ring
      _ = Matrix.trace ((P.transpose * C) * (A * B)) :=
        Matrix.trace_mul_comm _ _
      _ = Matrix.trace (P.transpose * (C * A * B)) := by
        congr 1
        noncomm_ring
      _ = complexTransposeProjectiveTracePair v (C * A * B) := rfl
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
  change Matrix.trace (Q * A * Q.transpose * B * Q.transpose * C) = _
  rw [hExpand]
  simp only [Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul,
    smul_eq_mul]
  rw [hPPP, hIPP, hPIP, hPPI, hIIP, hIPI, hPII]
  unfold h13CenteredTripleDoubleTransposeExpansion
  simp only [a]

/-- Exact expansion of the sixth H13 word itself. -/
theorem h13FinalSixWord_eq_projectiveExpansion
    {N : ℕ} (v : ComplexUnitSphere N)
    (T U Ts : ConcreteMatrixState N) :
    Matrix.trace
        (concreteCenteredOrbitalDirection N v * T *
          (concreteCenteredOrbitalDirection N v).transpose * U *
          (concreteCenteredOrbitalDirection N v).transpose * Ts) =
      h13CenteredTripleDoubleTransposeExpansion v T U Ts :=
  trace_centeredDirection_doubleTranspose_threeWord_expansion_h13 v T U Ts

/-- Multiplication by the first centered trace makes the last word an
explicit scalar projective polynomial of total degree at most four. -/
def h13FinalOneThreeProjectivePolynomial
    {N : ℕ} (v : ComplexUnitSphere N)
    (Y T U Ts : ConcreteMatrixState N) : ℂ :=
  (complexProjectiveTracePair v Y -
      (((N : ℝ)⁻¹ : ℝ) : ℂ) * Matrix.trace Y) *
    h13CenteredTripleDoubleTransposeExpansion v T U Ts

theorem trace_centeredDirection_mul_h13FinalSixWord_eq_projectivePolynomial
    {N : ℕ} (v : ComplexUnitSphere N)
    (Y T U Ts : ConcreteMatrixState N) :
    Matrix.trace (concreteCenteredOrbitalDirection N v * Y) *
      Matrix.trace
        (concreteCenteredOrbitalDirection N v * T *
          (concreteCenteredOrbitalDirection N v).transpose * U *
          (concreteCenteredOrbitalDirection N v).transpose * Ts) =
      h13FinalOneThreeProjectivePolynomial v Y T U Ts := by
  rw [trace_concreteCenteredOrbitalDirection_mul,
    h13FinalSixWord_eq_projectiveExpansion]
  rfl

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
