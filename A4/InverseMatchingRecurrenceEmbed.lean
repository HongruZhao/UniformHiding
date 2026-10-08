import A4.InverseMatchingRecurrenceTensor
import A4.MatchingGramDegreeFactorization

open scoped BigOperators Matrix

noncomputable section
namespace A4Research

open MatsumotoPaper

set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

private abbrev PM (n : ℕ) := A4Standalone.GramHafnian.PerfectMatching n

/-- The exact finite bijection onto matchings containing the first pair. -/
def firstPairFixedEquiv (q : ℕ) :
    PM q ≃ {M : PM (q + 1) // M (firstVertex q) = secondVertex q} where
  toFun N := ⟨firstPairEmbed q N, firstPairEmbed_first q N⟩
  invFun M := firstPairDelete M.1
  left_inv := firstPairDelete_embed q
  right_inv M := by
    apply Subtype.ext
    change firstPairEmbed q (firstPairDelete M.1) = M.1
    rw [firstPairEmbed_delete, firstPairNormalize_of_fixed M.1 M.2]

/-- Restricting a finite sum to the fixed first pair is literally a sum over
the old matching set; no combinatorial multiplicity is introduced. -/
theorem sum_firstPair_fixed {q : ℕ} {R : Type*} [AddCommMonoid R]
    (F : PM (q + 1) → R) :
    (∑ M : PM (q + 1),
      if M (firstVertex q) = secondVertex q then F M else 0) =
      ∑ N : PM q, F (firstPairEmbed q N) := by
  classical
  have hsub : (∑ M : PM (q + 1),
      if M (firstVertex q) = secondVertex q then F M else 0) =
        ∑ M : {M : PM (q + 1) // M (firstVertex q) = secondVertex q}, F M.1 := by
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (fun M ↦ by simp only [Finset.mem_filter,
      Finset.mem_univ, true_and]) _
  rw [hsub, ← (firstPairFixedEquiv q).sum_comp (fun M ↦ F M.1)]
  rfl

theorem firstPairEmbed_pairReps {q : ℕ} (M : PM q) :
    (firstPairEmbed q M).pairReps =
      insert (firstVertex q) (M.pairReps.image (remainingVertex q)) := by
  classical
  ext v
  rcases firstPair_vertex_cases v with rfl | rfl | ⟨i, rfl⟩
  · simp only [A4Standalone.GramHafnian.PerfectMatching.mem_pairReps_iff,
      firstPairEmbed_first, Finset.mem_insert, true_or, iff_true]
    change (0 : ℕ) < 1
    decide
  · have hnot : secondVertex q ∉ (firstPairEmbed q M).pairReps := by
      rw [A4Standalone.GramHafnian.PerfectMatching.mem_pairReps_iff, firstPairEmbed_second]
      change ¬(1 : ℕ) < 0
      omega
    have hnotimage : secondVertex q ∉ M.pairReps.image (remainingVertex q) := by
      intro h
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
      exact remainingVertex_ne_second q i hi
    simp only [hnot, Finset.mem_insert, (firstVertex_ne_second q).symm,
      hnotimage, or_self]
  · have hmem : remainingVertex q i ∈ M.pairReps.image (remainingVertex q) ↔
        i ∈ M.pairReps := by
      constructor
      · intro h
        obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp h
        have : k = i := remainingVertex_injective q heq
        simpa only [this] using hk
      · exact Finset.mem_image_of_mem (remainingVertex q)
    simp only [A4Standalone.GramHafnian.PerfectMatching.mem_pairReps_iff,
      firstPairEmbed_remaining, Finset.mem_insert, remainingVertex_ne_first,
      false_or, hmem]
    change (2 + i.val < 2 + (M i).val) ↔ i.val < (M i).val
    omega

/-- Every embedded matching monomial factors into the distinguished entry
and its old-degree monomial. The vertex array is completely arbitrary. -/
theorem matchingEntryWeight_firstPairEmbed {d q : ℕ}
    (A : Fin d → Fin d → ℂ) (j : Fin (2 * (q + 1)) → Fin d) (M : PM q) :
    matchingEntryWeight A j (firstPairEmbed q M) =
      A (j (firstVertex q)) (j (secondVertex q)) *
        matchingEntryWeight A (fun t ↦ j (remainingVertex q t)) M := by
  classical
  have hnot : firstVertex q ∉ M.pairReps.image (remainingVertex q) := by
    intro h
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
    exact remainingVertex_ne_first q i hi
  unfold matchingEntryWeight
  change (∏ i : (firstPairEmbed q M).pairReps,
      (fun i : Fin (2 * (q + 1)) ↦ A (j i) (j ((firstPairEmbed q M) i))) i.1) = _
  rw [Finset.prod_coe_sort (firstPairEmbed q M).pairReps
      (fun i ↦ A (j i) (j ((firstPairEmbed q M) i))),
    firstPairEmbed_pairReps, Finset.prod_insert hnot,
    firstPairEmbed_first, Finset.prod_image (remainingVertex_injective q).injOn]
  simp_rw [firstPairEmbed_remaining]
  exact congrArg (A (j (firstVertex q)) (j (secondVertex q)) * ·)
    (Finset.prod_coe_sort M.pairReps
      (fun i ↦ A (j (remainingVertex q i)) (j (remainingVertex q (M i))))).symm

/-- The exact weighted first-pair restriction used by the coefficient
recurrence, expressed as its old-degree tensor. -/
theorem sum_firstPair_fixed_matchingWeight {d q : ℕ}
    (f : PM q → ℂ) (A : Fin d → Fin d → ℂ)
    (j : Fin (2 * (q + 1)) → Fin d) :
    (∑ M : PM (q + 1),
      (if M (firstVertex q) = secondVertex q then f (firstPairDelete M) else 0) *
        matchingEntryWeight A j M) =
      A (j (firstVertex q)) (j (secondVertex q)) *
        ∑ N : PM q, f N * matchingEntryWeight A (fun t ↦ j (remainingVertex q t)) N := by
  classical
  simp only [ite_mul, zero_mul]
  rw [sum_firstPair_fixed]
  simp_rw [firstPairDelete_embed, matchingEntryWeight_firstPairEmbed]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro M _
  ring

theorem sum_firstPair_fixed_weingarten {d q : ℕ} (gamma : ℝ)
    (A : Fin d → Fin d → ℂ) (j : Fin (2 * (q + 1)) → Fin d) :
    (∑ M : PM (q + 1),
      (if M (firstVertex q) = secondVertex q then
        modifiedGramInverse q gamma (standardPairPartition q) (firstPairDelete M) else 0) *
        matchingEntryWeight A j M) =
      A (j (firstVertex q)) (j (secondVertex q)) *
        inverseWeingartenVertexTensor q gamma A (fun t ↦ j (remainingVertex q t)) :=
  sum_firstPair_fixed_matchingWeight _ A j

end A4Research
