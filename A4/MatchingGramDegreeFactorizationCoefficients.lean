import A4.MatchingGramDegreeFactorizationMatrix
import A4.InverseMatchingRecurrenceCoefficient

/-!
# The exact modified Weingarten degree recurrence

The negative Gram determinant conditions and the rectangular degree
factorization are proved in the imported modules.  The resulting recurrence
has only the sharp real parameter inequality as a hypothesis.
-/

open scoped BigOperators Matrix

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace MatsumotoPaper

private abbrev PM (n : ℕ) := A4Standalone.GramHafnian.PerfectMatching n

theorem firstPairSwitchOperator_commutes_orthogonalGram (q : ℕ) (z : ℂ) :
    firstPairSwitchOperator q z * orthogonalGram (q + 1) z =
      orthogonalGram (q + 1) z * firstPairSwitchOperator q z := by
  classical
  simp only [firstPairSwitchOperator, Matrix.add_mul, Matrix.mul_add,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
    Matrix.sum_mul, Matrix.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  exact firstPairRelabelingMatrix_commutes_orthogonalGram q t z

theorem modifiedGramInverse_eq_negative_power (n : ℕ) (gamma : ℝ) :
    modifiedGramInverse n gamma =
      (-2 : ℂ) ^ n • (orthogonalGram n (-2 * (gamma : ℂ)))⁻¹ := by
  unfold modifiedGramInverse
  rw [show (-2 : ℂ) = (-1) * 2 by ring, mul_pow]

theorem modifiedGramInverse_degree_factorization (q : ℕ) (gamma : ℝ)
    (hgamma : (q : ℝ) < gamma) :
    (gamma : ℂ) • (modifiedGramInverse (q + 1) gamma * firstPairEmbeddingMatrix q) -
      (1 / 2 : ℂ) • (∑ t : Fin (2 * q), firstPairRelabelingMatrix q t *
        (modifiedGramInverse (q + 1) gamma * firstPairEmbeddingMatrix q)) =
      firstPairEmbeddingMatrix q * modifiedGramInverse q gamma := by
  classical
  have hbig : ((q + 1 : ℕ) : ℝ) - 1 < gamma := by
    simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using hgamma
  have hsmall : (q : ℝ) - 1 < gamma := by linarith
  simpa only [← modifiedGramInverse_eq_negative_power] using
    A4Research.normalized_inverse_degree_factorization_sum q gamma
      (orthogonalGram (q + 1) (-2 * (gamma : ℂ)))
      (orthogonalGram q (-2 * (gamma : ℂ))) (firstPairEmbeddingMatrix q)
      (firstPairRelabelingMatrix q)
      (orthogonalGram_isUnit_det_negative gamma hbig)
      (orthogonalGram_isUnit_det_negative gamma hsmall)
      (firstPairSwitchOperator_commutes_orthogonalGram q (-2 * (gamma : ℂ)))
      (orthogonalGram_firstPair_degree_factorization q (-2 * (gamma : ℂ)))

theorem mul_firstPairEmbedding_apply {q : ℕ} {J : Type*} [Fintype J]
    (B : Matrix J (PM (q + 1)) ℂ) (j : J) (N : PM q) :
    (B * firstPairEmbeddingMatrix q) j N = B j (firstPairEmbed q N) := by
  classical
  simp [Matrix.mul_apply, firstPairEmbeddingMatrix, mul_ite]

theorem modifiedGramInverse_firstPair_recurrence (q : ℕ) (gamma : ℝ)
    (hgamma : (q : ℝ) < gamma) (M : PM (q + 1)) (N : PM q) :
    (gamma : ℂ) * modifiedGramInverse (q + 1) gamma M (firstPairEmbed q N) -
      (1 / 2 : ℂ) * ∑ t : Fin (2 * q),
        modifiedGramInverse (q + 1) gamma
          (transportPairPartition (firstPairSwitch q t) M) (firstPairEmbed q N) =
      if M (firstVertex q) = secondVertex q then
        modifiedGramInverse q gamma (firstPairDelete M) N else 0 := by
  classical
  have h := congrArg (fun B : Matrix (PM (q + 1)) (PM q) ℂ => B M N)
    (modifiedGramInverse_degree_factorization q gamma hgamma)
  simpa only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply,
    firstPairRelabelingMatrix_mul_apply, mul_firstPairEmbedding_apply,
    firstPairEmbedding_mul_apply] using h

end MatsumotoPaper
