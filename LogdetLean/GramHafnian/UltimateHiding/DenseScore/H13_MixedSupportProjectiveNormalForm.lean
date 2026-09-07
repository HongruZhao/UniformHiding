import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H13_MixedSupportPositiveFactors
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H13_SharpBilinearGramHolder
import Mathlib.Tactic

/-!
# Support normal form and scalar certificate for the H13 mixed expansion

This file rewrites the remaining mixed projective expansion in terms of the
positive support factors `A`, `B`, `P`, and `G` and proves the scalar
coefficient estimate used after Holder.  The analytic sphere integration is
kept in the following module.
-/

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open scoped ComplexOrder MatrixOrder

set_option maxHeartbeats 2400000

/-- The support-normal scalar form of the one-transpose mixed expansion. -/
def h13MixedSupportProjectiveNormalForm
    {N : ℕ} (v : ComplexUnitSphere N) (C : ConcreteMatrixState N) : ℂ :=
  let Z := h13LedgerZ C
  let T := h13LedgerT C
  let A : ConcreteMatrixState N := 1 + 2 • Z
  let B : ConcreteMatrixState N := T * T.conjTranspose
  let R : ConcreteMatrixState N := A * T
  let P : ConcreteMatrixState N := A * B
  let G : ConcreteMatrixState N := T.conjTranspose * A * T
  let a : ℂ := (((N : ℝ)⁻¹ : ℝ) : ℂ)
  complexProjectiveTracePair v A *
      complexProjectiveMixedTransposePair v T T.conjTranspose -
    a *
      (complexProjectiveMixedTransposePair v R T.conjTranspose +
        complexProjectiveTracePair v B * complexProjectiveTracePair v A +
        complexProjectiveMixedTransposePair v T R.conjTranspose) +
    a ^ 2 *
      (complexProjectiveTracePair v P +
        complexProjectiveTracePair v G.transpose +
        complexProjectiveTracePair v P) -
    a ^ 3 * Matrix.trace P

/-- Exact support rewrite of the simplified mixed word. -/
theorem h13CenteredTripleMixedTransposeExpansion_support_normalForm
    {N : ℕ} (v : ComplexUnitSphere N) (C : ConcreteMatrixState N)
    (hsupport : coeCornerSupport C) :
    h13CenteredTripleMixedTransposeExpansion v
        (h13LedgerT C) (h13LedgerT C).conjTranspose
        ((1 : ConcreteMatrixState N) + 2 • h13LedgerZ C) =
      h13MixedSupportProjectiveNormalForm v C := by
  let Z := h13LedgerZ C
  let T := h13LedgerT C
  let A : ConcreteMatrixState N := 1 + 2 • Z
  let B : ConcreteMatrixState N := T * T.conjTranspose
  let R : ConcreteMatrixState N := A * T
  let P : ConcreteMatrixState N := A * B
  let G : ConcreteMatrixState N := T.conjTranspose * A * T
  have hA : A.IsHermitian := by
    simpa only [A, Z] using
      (h13LedgerOneAddTwoZ_posSemidef C hsupport).isHermitian
  have hRstar : R.conjTranspose = T.conjTranspose * A := by
    dsimp only [R]
    rw [Matrix.conjTranspose_mul, hA.eq]
  have hBA : B * A = P := by
    dsimp only [B, A, P, T, Z]
    rw [h13LedgerTGram_mul_oneAddTwoZ_eq C hsupport]
  have hATP : A * T * T.conjTranspose = P := by
    dsimp only [P, B]
    noncomm_ring
  have hG : T.conjTranspose * A * T = G := rfl
  unfold h13CenteredTripleMixedTransposeExpansion
    h13MixedSupportProjectiveNormalForm
  dsimp only [Z, T, A, B, R, P, G]
  rw [hRstar, hBA, hATP, hG]
  rw [← complexProjectiveTracePair_transpose_eq_transposePair_h13]

/-- The rounded mixed-word Holder polynomial is at most one half of the
basic H14 coefficient budget.  The deliberately relaxed constant `128`
also makes this certificate stable under harmless analytic improvements. -/
theorem h13MixedHolderPolynomial_le_halfEnvelope
    (n t u v : ℝ) (hn : 1 ≤ n) (ht : 0 ≤ t) (hu : 0 ≤ u)
    (htlow : t ^ 2 ≤ n * u) (hv : v ≤ t * u) :
    9 * n * t * (n + 2 * t) * (t + u) +
        6 * n * t * (1 + 2 * t) * (t + u) +
        11 * t * (t + u) * (n + 2 * t) +
        17 * t * (t + 3 * u + 2 * v) ≤
      128 * (n ^ 2 * (t ^ 2 + u) + t ^ 4 + n ^ 2 * u ^ 2) := by
  have hn0 : 0 ≤ n := le_trans (by norm_num) hn
  have hn2 : 1 ≤ n ^ 2 := by nlinarith [sq_nonneg n]
  have hn2tu : 2 * (n ^ 2 * t * u) ≤
      n ^ 2 * t ^ 2 + n ^ 2 * u ^ 2 := by
    nlinarith [sq_nonneg (n * t - n * u)]
  have hnt3 : 2 * (n * t ^ 3) ≤ n ^ 2 * t ^ 2 + t ^ 4 := by
    nlinarith [sq_nonneg (n * t - t ^ 2)]
  have hnt2u : 2 * (n * t ^ 2 * u) ≤ t ^ 4 + n ^ 2 * u ^ 2 := by
    nlinarith [sq_nonneg (t ^ 2 - n * u)]
  have hnt2 : n * t ^ 2 ≤ n ^ 2 * u := by
    have := mul_le_mul_of_nonneg_left htlow hn0
    nlinarith
  have hntu : 2 * (n * t * u) ≤ n ^ 2 * t ^ 2 + u ^ 2 := by
    nlinarith [sq_nonneg (n * t - u)]
  have ht3 : 2 * t ^ 3 ≤ t ^ 2 + t ^ 4 := by
    nlinarith [sq_nonneg (t - t ^ 2)]
  have ht2u : 2 * (t ^ 2 * u) ≤ t ^ 4 + u ^ 2 := by
    nlinarith [sq_nonneg (t ^ 2 - u)]
  have htu : 2 * (t * u) ≤ t ^ 2 + u ^ 2 := by
    nlinarith [sq_nonneg (t - u)]
  have htv : t * v ≤ t ^ 2 * u := by
    have h := mul_le_mul_of_nonneg_left hv ht
    nlinarith
  have ht2lift : t ^ 2 ≤ n ^ 2 * t ^ 2 := by
    nlinarith [sq_nonneg t,
      mul_nonneg (sub_nonneg.mpr hn2) (sq_nonneg t)]
  have hu2lift : u ^ 2 ≤ n ^ 2 * u ^ 2 := by
    nlinarith [sq_nonneg u,
      mul_nonneg (sub_nonneg.mpr hn2) (sq_nonneg u)]
  have hexpand :
      9 * n * t * (n + 2 * t) * (t + u) +
          6 * n * t * (1 + 2 * t) * (t + u) +
          11 * t * (t + u) * (n + 2 * t) +
          17 * t * (t + 3 * u + 2 * v) =
        9 * (n ^ 2 * t ^ 2) +
          9 * (n ^ 2 * t * u) +
          30 * (n * t ^ 3) +
          30 * (n * t ^ 2 * u) +
          17 * (n * t ^ 2) + 17 * (n * t * u) +
          22 * t ^ 3 + 22 * (t ^ 2 * u) +
          17 * t ^ 2 + 51 * (t * u) + 34 * (t * v) := by
    ring
  have hcoarse :
      9 * n * t * (n + 2 * t) * (t + u) +
          6 * n * t * (1 + 2 * t) * (t + u) +
          11 * t * (t + u) * (n + 2 * t) +
          17 * t * (t + 3 * u + 2 * v) ≤
        92 * (n ^ 2 * t ^ 2) + 17 * (n ^ 2 * u) +
          87 * t ^ 4 + 100 * (n ^ 2 * u ^ 2) := by
    rw [hexpand]
    nlinarith only [hn2tu, hnt3, hnt2u, hnt2, hntu, ht3,
      ht2u, htu, htv, ht2lift, hu2lift]
  calc
    _ ≤ 92 * (n ^ 2 * t ^ 2) + 17 * (n ^ 2 * u) +
        87 * t ^ 4 + 100 * (n ^ 2 * u ^ 2) := hcoarse
    _ ≤ 128 * (n ^ 2 * (t ^ 2 + u) + t ^ 4 + n ^ 2 * u ^ 2) := by
      nlinarith [mul_nonneg (sq_nonneg n) hu]

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
