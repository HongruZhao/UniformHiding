import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H14_CenteredEllTwoProjectiveContraction
import Mathlib.Tactic

/-!
# Exact four-projector trace word for H11

This file isolates the maximal projective word that can occur in the fourth
centered log-determinant jet.  For `Q_v = P_v - I/N`, it expands

`Tr((Q_v Y)^4)`

as a polynomial in the four scalar projective pairings
`Tr(P_v Y^j)`, `1 ≤ j ≤ 4`, and the matrix-only trace `Tr(Y^4)`.
The largest projective degree is exactly four.  The proof is finite
noncommutative algebra plus the rank-one compression already proved for H14;
there is no probability or scientific axiom.
-/

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

set_option maxHeartbeats 1200000

/-- Three rank-one projectors in one cyclic trace split into three scalar
projective trace pairings. -/
theorem trace_rankOne_mul_threeTracePairs_h11
    {N : ℕ} (v : ComplexUnitSphere N)
    (A B C : ConcreteMatrixState N) :
    Matrix.trace
        (complexRankOneProjection v * A * complexRankOneProjection v * B *
          complexRankOneProjection v * C) =
      complexProjectiveTracePair v A *
        complexProjectiveTracePair v B *
        complexProjectiveTracePair v C := by
  rw [show complexRankOneProjection v * A * complexRankOneProjection v * B *
      complexRankOneProjection v * C =
      (complexRankOneProjection v * A * complexRankOneProjection v) * B *
        complexRankOneProjection v * C by noncomm_ring]
  rw [complexRankOneProjection_mul_mul_eq_tracePair_smul_h14]
  simp only [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  rw [trace_rankOne_mul_mul_mul_h14]
  ring

/-- Four rank-one projectors in one cyclic trace split into four scalar
projective trace pairings. -/
theorem trace_rankOne_mul_fourTracePairs_h11
    {N : ℕ} (v : ComplexUnitSphere N)
    (A B C D : ConcreteMatrixState N) :
    Matrix.trace
        (complexRankOneProjection v * A * complexRankOneProjection v * B *
          complexRankOneProjection v * C * complexRankOneProjection v * D) =
      complexProjectiveTracePair v A *
        complexProjectiveTracePair v B *
        complexProjectiveTracePair v C *
        complexProjectiveTracePair v D := by
  rw [show complexRankOneProjection v * A * complexRankOneProjection v * B *
      complexRankOneProjection v * C * complexRankOneProjection v * D =
      (complexRankOneProjection v * A * complexRankOneProjection v) * B *
        complexRankOneProjection v * C * complexRankOneProjection v * D by
      noncomm_ring]
  rw [complexRankOneProjection_mul_mul_eq_tracePair_smul_h14]
  simp only [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  rw [trace_rankOne_mul_threeTracePairs_h11]
  ring

/-- The explicit scalar polynomial obtained by expanding
`Tr(((P_v-I/N)Y)^4)`.  Its five summands have projective degrees
`4, 3, 2, 1, 0`, respectively. -/
def h11FourthCenteredAlternatingTraceExpansion
    {N : ℕ} (v : ComplexUnitSphere N)
    (Y : ConcreteMatrixState N) : ℂ :=
  let a : ℂ := (((N : ℝ)⁻¹ : ℝ) : ℂ)
  let b1 := complexProjectiveTracePair v Y
  let b2 := complexProjectiveTracePair v (Y ^ 2)
  let b3 := complexProjectiveTracePair v (Y ^ 3)
  let b4 := complexProjectiveTracePair v (Y ^ 4)
  b1 ^ 4 - 4 * a * (b1 ^ 2 * b2) +
    a ^ 2 * (4 * b1 * b3 + 2 * b2 ^ 2) -
    4 * a ^ 3 * b4 + a ^ 4 * Matrix.trace (Y ^ 4)

/-- Exact maximal-degree H11 trace-word expansion:

`Tr((Q_vY)^4) = b₁⁴ - 4a b₁²b₂
  + a²(4b₁b₃+2b₂²) - 4a³b₄ + a⁴Tr(Y⁴)`,

where `a=1/N` and `b_j=Tr(P_vY^j)`. -/
theorem trace_centeredDirection_mul_four_expansion_h11
    {N : ℕ} (v : ComplexUnitSphere N)
    (Y : ConcreteMatrixState N) :
    Matrix.trace ((concreteCenteredOrbitalDirection N v * Y) ^ 4) =
      h11FourthCenteredAlternatingTraceExpansion v Y := by
  let P := complexRankOneProjection v
  let Q := concreteCenteredOrbitalDirection N v
  let a : ℂ := (((N : ℝ)⁻¹ : ℝ) : ℂ)
  let X := P * Y
  have hQ : Q = P - a • (1 : ConcreteMatrixState N) := by rfl
  have hQY : Q * Y = X - a • Y := by
    rw [hQ]
    simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, X]
  have hExpand :
      (X - a • Y) ^ 4 =
        X ^ 4 -
          a • (X ^ 3 * Y + X ^ 2 * Y * X + X * Y * X ^ 2 +
            Y * X ^ 3) +
          a ^ 2 • (X ^ 2 * Y ^ 2 + X * Y * X * Y + X * Y ^ 2 * X +
            Y * X ^ 2 * Y + Y * X * Y * X + Y ^ 2 * X ^ 2) -
          a ^ 3 • (X * Y ^ 3 + Y * X * Y ^ 2 + Y ^ 2 * X * Y +
            Y ^ 3 * X) +
          a ^ 4 • Y ^ 4 := by
    noncomm_ring
    module
  change Matrix.trace ((Q * Y) ^ 4) = _
  rw [hQY, hExpand]
  simp only [Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul,
    smul_eq_mul]
  let b1 := complexProjectiveTracePair v Y
  let b2 := complexProjectiveTracePair v (Y ^ 2)
  let b3 := complexProjectiveTracePair v (Y ^ 3)
  let b4 := complexProjectiveTracePair v (Y ^ 4)
  have hX4 : Matrix.trace (X ^ 4) = b1 ^ 4 := by
    rw [show X ^ 4 = P * Y * P * Y * P * Y * P * Y by
      dsimp only [X]
      noncomm_ring]
    rw [trace_rankOne_mul_fourTracePairs_h11]
    simp only [b1]
    ring
  have h31 : Matrix.trace (X ^ 3 * Y) = b1 ^ 2 * b2 := by
    rw [show X ^ 3 * Y = P * Y * P * Y * P * (Y ^ 2) by
      dsimp only [X]
      noncomm_ring]
    rw [trace_rankOne_mul_threeTracePairs_h11]
    simp only [b1, b2]
    ring
  have h32 : Matrix.trace (X ^ 2 * Y * X) = b1 ^ 2 * b2 := by
    rw [show X ^ 2 * Y * X = P * Y * P * (Y ^ 2) * P * Y by
      dsimp only [X]
      noncomm_ring]
    rw [trace_rankOne_mul_threeTracePairs_h11]
    simp only [b1, b2]
    ring
  have h33 : Matrix.trace (X * Y * X ^ 2) = b1 ^ 2 * b2 := by
    rw [show X * Y * X ^ 2 = P * (Y ^ 2) * P * Y * P * Y by
      dsimp only [X]
      noncomm_ring]
    rw [trace_rankOne_mul_threeTracePairs_h11]
    simp only [b1, b2]
    ring
  have h34 : Matrix.trace (Y * X ^ 3) = b1 ^ 2 * b2 := by
    rw [Matrix.trace_mul_comm Y (X ^ 3)]
    exact h31
  have h3 :
      Matrix.trace (X ^ 3 * Y) + Matrix.trace (X ^ 2 * Y * X) +
          Matrix.trace (X * Y * X ^ 2) + Matrix.trace (Y * X ^ 3) =
        4 * (b1 ^ 2 * b2) := by
    rw [h31, h32, h33, h34]
    ring
  have h21 : Matrix.trace (X ^ 2 * Y ^ 2) = b1 * b3 := by
    rw [show X ^ 2 * Y ^ 2 = P * Y * P * (Y ^ 3) by
      dsimp only [X]
      noncomm_ring]
    rw [trace_rankOne_mul_mul_mul_h14]
  have h22 : Matrix.trace (X * Y * X * Y) = b2 ^ 2 := by
    rw [show X * Y * X * Y = P * (Y ^ 2) * P * (Y ^ 2) by
      dsimp only [X]
      noncomm_ring]
    rw [trace_rankOne_mul_mul_mul_h14]
    simp only [b2, pow_two]
  have h23 : Matrix.trace (X * Y ^ 2 * X) = b1 * b3 := by
    rw [show X * Y ^ 2 * X = P * (Y ^ 3) * P * Y by
      dsimp only [X]
      noncomm_ring]
    rw [trace_rankOne_mul_mul_mul_h14]
    simp only [b1, b3]
    ring
  have h24 : Matrix.trace (Y * X ^ 2 * Y) = b1 * b3 := by
    calc
      Matrix.trace (Y * X ^ 2 * Y) =
          Matrix.trace (Y * (X ^ 2 * Y)) := by
        congr 1
        noncomm_ring
      _ = Matrix.trace ((X ^ 2 * Y) * Y) :=
        Matrix.trace_mul_comm _ _
      _ = Matrix.trace (X ^ 2 * Y ^ 2) := by
        congr 1
        noncomm_ring
      _ = b1 * b3 := h21
  have h25 : Matrix.trace (Y * X * Y * X) = b2 ^ 2 := by
    calc
      Matrix.trace (Y * X * Y * X) =
          Matrix.trace (Y * (X * Y * X)) := by
        congr 1
        noncomm_ring
      _ = Matrix.trace ((X * Y * X) * Y) :=
        Matrix.trace_mul_comm _ _
      _ = Matrix.trace (X * Y * X * Y) := rfl
      _ = b2 ^ 2 := h22
  have h26 : Matrix.trace (Y ^ 2 * X ^ 2) = b1 * b3 := by
    rw [Matrix.trace_mul_comm (Y ^ 2) (X ^ 2)]
    exact h21
  have h2 :
      Matrix.trace (X ^ 2 * Y ^ 2) + Matrix.trace (X * Y * X * Y) +
          Matrix.trace (X * Y ^ 2 * X) + Matrix.trace (Y * X ^ 2 * Y) +
          Matrix.trace (Y * X * Y * X) + Matrix.trace (Y ^ 2 * X ^ 2) =
        4 * b1 * b3 + 2 * b2 ^ 2 := by
    rw [h21, h22, h23, h24, h25, h26]
    ring
  have h11 : Matrix.trace (X * Y ^ 3) = b4 := by
    rw [show X * Y ^ 3 = P * (Y ^ 4) by
      dsimp only [X]
      noncomm_ring]
    simpa only [P, b4] using
      (complexProjectiveTracePair_eq_trace v (Y ^ 4)).symm
  have h12 : Matrix.trace (Y * X * Y ^ 2) = b4 := by
    calc
      Matrix.trace (Y * X * Y ^ 2) =
          Matrix.trace (Y * (X * Y ^ 2)) := by
        congr 1
        noncomm_ring
      _ = Matrix.trace ((X * Y ^ 2) * Y) :=
        Matrix.trace_mul_comm _ _
      _ = Matrix.trace (X * Y ^ 3) := by
        congr 1
        noncomm_ring
      _ = b4 := h11
  have h13 : Matrix.trace (Y ^ 2 * X * Y) = b4 := by
    calc
      Matrix.trace (Y ^ 2 * X * Y) =
          Matrix.trace (Y ^ 2 * (X * Y)) := by
        congr 1
        noncomm_ring
      _ = Matrix.trace ((X * Y) * Y ^ 2) :=
        Matrix.trace_mul_comm _ _
      _ = Matrix.trace (X * Y ^ 3) := by
        congr 1
        noncomm_ring
      _ = b4 := h11
  have h14 : Matrix.trace (Y ^ 3 * X) = b4 := by
    rw [Matrix.trace_mul_comm (Y ^ 3) X]
    exact h11
  have h1 :
      Matrix.trace (X * Y ^ 3) + Matrix.trace (Y * X * Y ^ 2) +
          Matrix.trace (Y ^ 2 * X * Y) + Matrix.trace (Y ^ 3 * X) =
        4 * b4 := by
    rw [h11, h12, h13, h14]
    ring
  rw [hX4, h3, h2, h1]
  unfold h11FourthCenteredAlternatingTraceExpansion
  simp only [a, b1, b2, b3, b4]
  ring

/-- Concrete fixed-matrix form of the same H11 word, specialized to the
beta-prime matrix `Y(A)`. -/
theorem concreteH11FourthCenteredTraceWord_expansion_internal
    {N K : ℕ} (A : ConcreteMatrixState N) (v : ComplexUnitSphere N) :
    Matrix.trace
        ((concreteCenteredOrbitalDirection N v * concreteCOEY N K A) ^ 4) =
      h11FourthCenteredAlternatingTraceExpansion v
        (concreteCOEY N K A) :=
  trace_centeredDirection_mul_four_expansion_h11 v (concreteCOEY N K A)

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
