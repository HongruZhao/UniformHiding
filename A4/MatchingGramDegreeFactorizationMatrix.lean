import A4.MatchingGramDegreeFactorizationColoring
import A4.InverseMatchingRecurrenceRelabel

open scoped BigOperators Matrix

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace MatsumotoPaper

private abbrev PM (n : ℕ) := A4Standalone.GramHafnian.PerfectMatching n

theorem firstPair_partner_cases {q : ℕ} (M : PM (q + 1)) :
    M (firstVertex q) = secondVertex q ∨
      ∃ t : Fin (2 * q), M (secondVertex q) = remainingVertex q t := by
  rcases firstPair_vertex_cases (M (secondVertex q)) with h | h | h
  · left
    simpa only [h] using M.apply_apply (secondVertex q)
  · exact False.elim (M.apply_ne (secondVertex q) h)
  · exact Or.inr h

@[simp] theorem firstPairDelete_normalize {q : ℕ} (M : PM (q + 1)) :
    firstPairDelete (firstPairNormalize M) = firstPairDelete M := by
  apply firstPairEmbed_injective q
  rw [firstPairEmbed_delete, firstPairEmbed_delete,
    firstPairNormalize_of_fixed _ (firstPairNormalize_first M)]

theorem firstPairRelabelingMatrix_eq (q : ℕ) (t : Fin (2 * q)) :
    firstPairRelabelingMatrix q t = matchingRelabelMatrix (firstPairSwitch q t) := rfl

theorem firstPairRelabelingMatrix_mul_apply {q : ℕ} (t : Fin (2 * q))
    {J : Type*} (B : Matrix (PM (q + 1)) J ℂ) (M : PM (q + 1)) (j : J) :
    (firstPairRelabelingMatrix q t * B) M j =
      B (transportPairPartition (firstPairSwitch q t) M) j := by
  change (A4Research.relabelingMatrix (matchingRelabelEquiv (firstPairSwitch q t)) * B) M j = _
  rw [A4Research.relabelingMatrix_mul_apply]
  change B (transportPairPartition (firstPairSwitch q t)⁻¹ M) j = _
  simp only [Equiv.Perm.inv_def, firstPairSwitch_symm]

theorem firstPairRelabelingMatrix_commutes_orthogonalGram (q : ℕ)
    (t : Fin (2 * q)) (z : ℂ) :
    firstPairRelabelingMatrix q t * orthogonalGram (q + 1) z =
      orthogonalGram (q + 1) z * firstPairRelabelingMatrix q t :=
  matchingRelabelMatrix_commutes_orthogonalGram _ _

theorem orthogonalGram_mul_firstPairEmbedding_apply {q : ℕ} (z : ℂ)
    (M : PM (q + 1)) (N : PM q) :
    (orthogonalGram (q + 1) z * firstPairEmbeddingMatrix q) M N =
      orthogonalGram (q + 1) z M (firstPairEmbed q N) := by
  classical
  simp [Matrix.mul_apply, firstPairEmbeddingMatrix, mul_ite]

theorem firstPairEmbedding_mul_apply {q : ℕ} {J : Type*}
    (B : Matrix (PM q) J ℂ) (M : PM (q + 1)) (j : J) :
    (firstPairEmbeddingMatrix q * B) M j =
      if M (firstVertex q) = secondVertex q then B (firstPairDelete M) j else 0 := by
  classical
  by_cases hM : M (firstVertex q) = secondVertex q
  · have hE : M = firstPairEmbed q (firstPairDelete M) := by
      rw [firstPairEmbed_delete, firstPairNormalize_of_fixed M hM]
    have heq : ∀ N : PM q, M = firstPairEmbed q N ↔ firstPairDelete M = N := by
      intro N
      constructor
      · intro h
        apply firstPairEmbed_injective q
        exact hE.symm.trans h
      · intro h
        exact hE.trans (congrArg (firstPairEmbed q) h)
    simp only [Matrix.mul_apply, firstPairEmbeddingMatrix, heq, ite_mul, one_mul, zero_mul,
      hM, if_pos]
    simp
  · have heq : ∀ N : PM q, M ≠ firstPairEmbed q N := by
      intro N h
      apply hM
      rw [h, firstPairEmbed_first]
    simp [Matrix.mul_apply, firstPairEmbeddingMatrix, heq, hM]

theorem firstPairSwitchOperator_embedding_apply {q : ℕ} (z : ℂ)
    (B : Matrix (PM q) (PM q) ℂ) (M : PM (q + 1)) (N : PM q) :
    (firstPairSwitchOperator q z * firstPairEmbeddingMatrix q * B) M N =
      z * (firstPairEmbeddingMatrix q * B) M N +
        ∑ t : Fin (2 * q), (firstPairEmbeddingMatrix q * B)
          (transportPairPartition (firstPairSwitch q t) M) N := by
  rw [Matrix.mul_assoc, firstPairSwitchOperator, Matrix.add_mul, Matrix.smul_mul,
    Matrix.one_mul, Matrix.sum_mul]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply,
    firstPairRelabelingMatrix_mul_apply]

theorem orthogonalGram_firstPair_degree_factorization (q : ℕ) (z : ℂ) :
    orthogonalGram (q + 1) z * firstPairEmbeddingMatrix q =
      firstPairSwitchOperator q z * firstPairEmbeddingMatrix q * orthogonalGram q z := by
  classical
  ext M N
  rw [orthogonalGram_mul_firstPairEmbedding_apply,
    firstPairSwitchOperator_embedding_apply, firstPairEmbedding_mul_apply]
  rcases firstPair_partner_cases M with hM | ⟨t, hM⟩
  · have hM' : M (secondVertex q) = firstVertex q := by
      simpa only [hM] using M.apply_apply (firstVertex q)
    have hs : ∀ r : Fin (2 * q),
        ¬ transportPairPartition (firstPairSwitch q r) M (firstVertex q) = secondVertex q := by
      intro r h
      have := (firstPairSwitch_fixed_iff M r).mp h
      rw [hM'] at this
      exact remainingVertex_ne_first q r this.symm
    simp only [hM, if_pos, firstPairEmbedding_mul_apply, hs, if_false, Finset.sum_const_zero,
      add_zero, orthogonalGram]
    rw [matchingKappa_firstPairDelete_of_fixed M N hM, pow_succ]
    ring
  · have hn : ¬ M (firstVertex q) = secondVertex q := by
      intro h
      have h' : M (secondVertex q) = firstVertex q := by
        simpa only [h] using M.apply_apply (firstVertex q)
      exact remainingVertex_ne_first q t (hM.symm.trans h')
    simp only [hn, if_false, mul_zero, zero_add]
    rw [Finset.sum_eq_single t]
    · rw [firstPairEmbedding_mul_apply,
        if_pos ((firstPairSwitch_fixed_iff M t).mpr hM),
        firstPairSwitch_normalizes M t hM, firstPairDelete_normalize]
      exact congrArg (fun k => z ^ k) (matchingKappa_firstPairDelete_of_partner M N t hM)
    · intro r _ hrt
      rw [firstPairEmbedding_mul_apply]
      have hs : ¬ transportPairPartition (firstPairSwitch q r) M (firstVertex q) = secondVertex q := by
        intro h
        have hp := (firstPairSwitch_fixed_iff M r).mp h
        exact hrt (remainingVertex_injective q (hp.symm.trans hM))
      rw [if_neg hs]
    · simp

end MatsumotoPaper
