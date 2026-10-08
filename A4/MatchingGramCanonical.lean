import A4.MatchingGram

/-!
# Canonical ordered pairings and involution matchings

The A4 finite moment sums use canonical permutations.  The Gram operator
uses fixed-point-free involutions.  This file develops the exact bridge;
all degrees are retained, including the empty matching.
-/

open scoped BigOperators Matrix

noncomputable section

namespace MatsumotoPaper

private abbrev PM (n : ℕ) := A4Standalone.GramHafnian.PerfectMatching n

/-- Increasing enumeration of the smaller endpoints of a matching. -/
def matchingPairOrder {n : ℕ} (M : PM n) : Fin n ↪o Fin (2 * n) :=
  M.pairReps.orderEmbOfFin M.card_pairReps

theorem matchingPairOrder_mem {n : ℕ} (M : PM n) (i : Fin n) :
    matchingPairOrder M i ∈ M.pairReps :=
  Finset.orderEmbOfFin_mem M.pairReps M.card_pairReps i

theorem matchingPairOrder_lt_mate {n : ℕ} (M : PM n) (i : Fin n) :
    matchingPairOrder M i < M (matchingPairOrder M i) :=
  (M.mem_pairReps_iff _).mp (matchingPairOrder_mem M i)

theorem matchingPairOrder_surjective {n : ℕ} (M : PM n)
    {j : Fin (2 * n)} (hj : j ∈ M.pairReps) :
    ∃ i : Fin n, matchingPairOrder M i = j := by
  have h := congrArg (fun S => j ∈ S)
    (Finset.range_orderEmbOfFin M.pairReps M.card_pairReps)
  exact h.mpr hj

def matchingSlotEquiv (n : ℕ) : Fin n × Fin 2 ≃ Fin (2 * n) :=
  (finProdFinEquiv : Fin n × Fin 2 ≃ Fin (n * 2)).trans
    (finCongr (Nat.mul_comm n 2))

@[simp] theorem matchingSlotEquiv_zero {n : ℕ} (i : Fin n) :
    matchingSlotEquiv n (i, 0) = leftSlot i := by
  apply Fin.ext
  simp [matchingSlotEquiv, leftSlot, finProdFinEquiv]

@[simp] theorem matchingSlotEquiv_one {n : ℕ} (i : Fin n) :
    matchingSlotEquiv n (i, 1) = rightSlot i := by
  apply Fin.ext
  simp [matchingSlotEquiv, rightSlot, finProdFinEquiv]
  omega

def indexedMatchingVertex {n : ℕ} (M : PM n) (p : Fin n × Fin 2) : Fin (2 * n) :=
  if p.2 = 0 then matchingPairOrder M p.1 else M (matchingPairOrder M p.1)

@[simp] theorem indexedMatchingVertex_zero {n : ℕ} (M : PM n) (i : Fin n) :
    indexedMatchingVertex M (i, 0) = matchingPairOrder M i := by
  simp [indexedMatchingVertex]

@[simp] theorem indexedMatchingVertex_one {n : ℕ} (M : PM n) (i : Fin n) :
    indexedMatchingVertex M (i, 1) = M (matchingPairOrder M i) := by
  simp [indexedMatchingVertex]

theorem indexedMatchingVertex_injective {n : ℕ} (M : PM n) :
    Function.Injective (indexedMatchingVertex M) := by
  rintro ⟨i, b⟩ ⟨j, c⟩ h
  fin_cases b <;> fin_cases c
  · simp [indexedMatchingVertex] at h
    exact Prod.ext h rfl
  · simp [indexedMatchingVertex] at h
    have hi := matchingPairOrder_lt_mate M i
    have hj := matchingPairOrder_lt_mate M j
    rw [h, M.apply_apply] at hi
    exact False.elim (lt_asymm hi hj)
  · simp [indexedMatchingVertex] at h
    have hi := matchingPairOrder_lt_mate M i
    have hj := matchingPairOrder_lt_mate M j
    rw [← h, M.apply_apply] at hj
    exact False.elim (lt_asymm hi hj)
  · simp [indexedMatchingVertex] at h
    exact Prod.ext h rfl

theorem indexedMatchingVertex_surjective {n : ℕ} (M : PM n) :
    Function.Surjective (indexedMatchingVertex M) := by
  intro j
  rcases (M.exactly_one_mem_pairReps j).1 with hj | hj
  · obtain ⟨i, hi⟩ := matchingPairOrder_surjective M hj
    exact ⟨(i, 0), by simpa only [indexedMatchingVertex_zero] using hi⟩
  · obtain ⟨i, hi⟩ := matchingPairOrder_surjective M hj
    refine ⟨(i, 1), ?_⟩
    simp only [indexedMatchingVertex_one, hi, M.apply_apply]

def indexedMatchingEquiv {n : ℕ} (M : PM n) : Fin n × Fin 2 ≃ Fin (2 * n) :=
  Equiv.ofBijective (indexedMatchingVertex M)
    ⟨indexedMatchingVertex_injective M, indexedMatchingVertex_surjective M⟩

def canonicalMatchingPermutation {n : ℕ} (M : PM n) : Equiv.Perm (Fin (2 * n)) :=
  (matchingSlotEquiv n).symm.trans (indexedMatchingEquiv M)

@[simp] theorem canonicalMatchingPermutation_left {n : ℕ} (M : PM n) (i : Fin n) :
    canonicalMatchingPermutation M (leftSlot i) = matchingPairOrder M i := by
  change indexedMatchingVertex M ((matchingSlotEquiv n).symm (leftSlot i)) = _
  rw [← matchingSlotEquiv_zero, Equiv.symm_apply_apply, indexedMatchingVertex_zero]

@[simp] theorem canonicalMatchingPermutation_right {n : ℕ} (M : PM n) (i : Fin n) :
    canonicalMatchingPermutation M (rightSlot i) = M (matchingPairOrder M i) := by
  change indexedMatchingVertex M ((matchingSlotEquiv n).symm (rightSlot i)) = _
  rw [← matchingSlotEquiv_one, Equiv.symm_apply_apply, indexedMatchingVertex_one]

theorem canonicalMatchingPermutation_isCanonical {n : ℕ} (M : PM n) :
    IsCanonicalMatching (canonicalMatchingPermutation M) := by
  constructor
  · intro i
    rw [canonicalMatchingPermutation_left, canonicalMatchingPermutation_right]
    exact matchingPairOrder_lt_mate M i
  · constructor
    · intro hn
      rw [canonicalMatchingPermutation_left]
      have hzero : (⟨0, by omega⟩ : Fin (2 * n)) ∈ M.pairReps := by
        rw [M.mem_pairReps_iff]
        have hne := M.apply_ne (⟨0, by omega⟩ : Fin (2 * n))
        change 0 < (M ⟨0, by omega⟩).val
        have hnval : (M ⟨0, by omega⟩).val ≠ 0 := by
          intro h
          apply hne
          exact Fin.ext h
        omega
      obtain ⟨i, hi⟩ := matchingPairOrder_surjective M hzero
      apply le_antisymm
      · calc matchingPairOrder M ⟨0, hn⟩ ≤ matchingPairOrder M i :=
          (matchingPairOrder M).monotone (by change 0 ≤ i.val; omega)
        _ = ⟨0, by omega⟩ := hi
      · change 0 ≤ (matchingPairOrder M ⟨0, hn⟩).val
        omega
    · intro i j hij
      rw [canonicalMatchingPermutation_left, canonicalMatchingPermutation_left]
      exact (matchingPairOrder M).strictMono hij

def pairPartitionToCanonical {n : ℕ} (M : PM n) : PerfectMatching n :=
  ⟨canonicalMatchingPermutation M, canonicalMatchingPermutation_isCanonical M⟩

@[simp] theorem pairCoordinateEquiv_zero {n : ℕ} (i : Fin n) :
    pairCoordinateEquiv n (i, 0) = leftSlot i := by
  apply Fin.ext
  simp [pairCoordinateEquiv, mulCommFinEquiv, leftSlot, finProdFinEquiv]

@[simp] theorem pairCoordinateEquiv_one {n : ℕ} (i : Fin n) :
    pairCoordinateEquiv n (i, 1) = rightSlot i := by
  apply Fin.ext
  simp [pairCoordinateEquiv, mulCommFinEquiv, rightSlot, finProdFinEquiv]
  omega

@[simp] theorem standardPairPartition_left {n : ℕ} (i : Fin n) :
    standardPairPartition n (leftSlot i) = rightSlot i := by
  change standardMatePerm n (leftSlot i) = rightSlot i
  unfold standardMatePerm
  rw [← pairCoordinateEquiv_zero]
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
  simpa [pairFlip, finTwoSwap] using pairCoordinateEquiv_one i

@[simp] theorem standardPairPartition_right {n : ℕ} (i : Fin n) :
    standardPairPartition n (rightSlot i) = leftSlot i := by
  change standardMatePerm n (rightSlot i) = leftSlot i
  unfold standardMatePerm
  rw [← pairCoordinateEquiv_one]
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
  simpa [pairFlip, finTwoSwap] using pairCoordinateEquiv_zero i

@[simp] theorem transportedPairPartition_left {n : ℕ}
    (g : Equiv.Perm (Fin (2 * n))) (i : Fin n) :
    transportedPairPartition g (g (leftSlot i)) = g (rightSlot i) := by
  simp only [transportedPairPartition, transportPairPartition_apply,
    Equiv.symm_apply_apply, standardPairPartition_left]

@[simp] theorem transportedPairPartition_right {n : ℕ}
    (g : Equiv.Perm (Fin (2 * n))) (i : Fin n) :
    transportedPairPartition g (g (rightSlot i)) = g (leftSlot i) := by
  simp only [transportedPairPartition, transportPairPartition_apply,
    Equiv.symm_apply_apply, standardPairPartition_right]

@[simp] theorem canonicalMatchingPermutation_transport {n : ℕ} (M : PM n) :
    transportedPairPartition (canonicalMatchingPermutation M) = M := by
  apply pairPartition_ext
  intro j
  obtain ⟨s, rfl⟩ := (canonicalMatchingPermutation M).surjective j
  obtain ⟨⟨i, b⟩, rfl⟩ := (matchingSlotEquiv n).surjective s
  fin_cases b
  · change transportedPairPartition (canonicalMatchingPermutation M)
      (canonicalMatchingPermutation M (matchingSlotEquiv n (i, 0))) =
        M (canonicalMatchingPermutation M (matchingSlotEquiv n (i, 0)))
    rw [matchingSlotEquiv_zero, transportedPairPartition_left,
      canonicalMatchingPermutation_left, canonicalMatchingPermutation_right]
  · change transportedPairPartition (canonicalMatchingPermutation M)
      (canonicalMatchingPermutation M (matchingSlotEquiv n (i, 1))) =
        M (canonicalMatchingPermutation M (matchingSlotEquiv n (i, 1)))
    rw [matchingSlotEquiv_one, transportedPairPartition_right,
      canonicalMatchingPermutation_right, canonicalMatchingPermutation_left, M.apply_apply]

def canonicalToPairPartition {n : ℕ} (M : PerfectMatching n) : PM n :=
  transportedPairPartition M.toPerm

@[simp] theorem canonicalToPairPartition_pairPartitionToCanonical {n : ℕ} (M : PM n) :
    canonicalToPairPartition (pairPartitionToCanonical M) = M :=
  canonicalMatchingPermutation_transport M

theorem canonicalMatching_left_eq_order {n : ℕ} (M : PerfectMatching n) :
    (fun i => M.toPerm (leftSlot i)) = matchingPairOrder (canonicalToPairPartition M) := by
  apply Finset.orderEmbOfFin_unique (canonicalToPairPartition M).card_pairReps
  · intro i
    rw [(canonicalToPairPartition M).mem_pairReps_iff]
    change M.toPerm (leftSlot i) <
      transportedPairPartition M.toPerm (M.toPerm (leftSlot i))
    rw [transportedPairPartition_left]
    exact M.property.1 i
  · exact M.property.2.2

@[simp] theorem pairPartitionToCanonical_canonicalToPairPartition {n : ℕ}
    (M : PerfectMatching n) : pairPartitionToCanonical (canonicalToPairPartition M) = M := by
  apply Subtype.ext
  apply Equiv.ext
  intro j
  obtain ⟨⟨i, b⟩, rfl⟩ := (matchingSlotEquiv n).surjective j
  have hleft : matchingPairOrder (canonicalToPairPartition M) i = M.toPerm (leftSlot i) :=
    (congrFun (canonicalMatching_left_eq_order M) i).symm
  fin_cases b
  · change canonicalMatchingPermutation (canonicalToPairPartition M)
      (matchingSlotEquiv n (i, 0)) = M.toPerm (matchingSlotEquiv n (i, 0))
    rw [matchingSlotEquiv_zero, canonicalMatchingPermutation_left, hleft]
  · change canonicalMatchingPermutation (canonicalToPairPartition M)
      (matchingSlotEquiv n (i, 1)) = M.toPerm (matchingSlotEquiv n (i, 1))
    rw [matchingSlotEquiv_one, canonicalMatchingPermutation_right, hleft]
    exact transportedPairPartition_left M.toPerm i

/-- The exact all-degree correspondence between the two matching representations. -/
def canonicalPairPartitionEquiv (n : ℕ) : PerfectMatching n ≃ PM n where
  toFun := canonicalToPairPartition
  invFun := pairPartitionToCanonical
  left_inv := pairPartitionToCanonical_canonicalToPairPartition
  right_inv := canonicalToPairPartition_pairPartitionToCanonical

theorem sum_canonical_eq_sum_pairPartition {n : ℕ} {α : Type*} [AddCommMonoid α]
    (f : PM n → α) : ∑ M : PerfectMatching n, f (canonicalToPairPartition M) =
      ∑ M : PM n, f M :=
  (canonicalPairPartitionEquiv n).sum_comp f

end MatsumotoPaper
