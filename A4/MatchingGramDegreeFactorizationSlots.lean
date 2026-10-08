import A4.MatchingGramDegreeFactorization
import A4.InverseMatchingRecurrenceTensor

open scoped BigOperators Matrix

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace MatsumotoPaper

@[simp] theorem firstVertex_leftSlot (q : ℕ) :
    firstVertex q = leftSlot (0 : Fin (q + 1)) := Fin.ext rfl

@[simp] theorem secondVertex_rightSlot (q : ℕ) :
    secondVertex q = rightSlot (0 : Fin (q + 1)) := Fin.ext rfl

@[simp] theorem remainingVertex_leftSlot {q : ℕ} (i : Fin q) :
    remainingVertex q (leftSlot i) = leftSlot i.succ := by
  apply Fin.ext
  simp only [remainingVertex_val, leftSlot, Fin.val_succ]
  omega

@[simp] theorem remainingVertex_rightSlot {q : ℕ} (i : Fin q) :
    remainingVertex q (rightSlot i) = rightSlot i.succ := by
  apply Fin.ext
  simp only [remainingVertex_val, rightSlot, Fin.val_succ]
  omega

@[simp] theorem firstPairEmbed_standard (q : ℕ) :
    firstPairEmbed q (standardPairPartition q) = standardPairPartition (q + 1) := by
  apply pairPartition_ext
  intro v
  obtain ⟨⟨i, b⟩, rfl⟩ := (matchingSlotEquiv (q + 1)).surjective v
  fin_cases b
  · change firstPairEmbed q (standardPairPartition q) (matchingSlotEquiv (q + 1) (i, 0)) =
      standardPairPartition (q + 1) (matchingSlotEquiv (q + 1) (i, 0))
    rw [matchingSlotEquiv_zero, standardPairPartition_left]
    refine Fin.cases ?_ (fun i => ?_) i
    · rw [← firstVertex_leftSlot, firstPairEmbed_first,
        secondVertex_rightSlot]
    · rw [← remainingVertex_leftSlot, firstPairEmbed_remaining,
        standardPairPartition_left, remainingVertex_rightSlot,
        ]
  · change firstPairEmbed q (standardPairPartition q) (matchingSlotEquiv (q + 1) (i, 1)) =
      standardPairPartition (q + 1) (matchingSlotEquiv (q + 1) (i, 1))
    rw [matchingSlotEquiv_one, standardPairPartition_right]
    refine Fin.cases ?_ (fun i => ?_) i
    · rw [← secondVertex_rightSlot, firstPairEmbed_second,
        firstVertex_leftSlot]
    · rw [← remainingVertex_rightSlot, firstPairEmbed_remaining,
        standardPairPartition_right, remainingVertex_leftSlot,
        ]

end MatsumotoPaper

namespace A4Research

open MatsumotoPaper

@[simp] theorem entryPairListVertices_cons_first {d q : ℕ}
    (p : Fin d × Fin d) (old : EntryPairList d q) :
    entryPairListVertices (Fin.cons p old) (firstVertex q) = p.1 := by
  rw [firstVertex_leftSlot, entryPairListVertices_left]
  rfl

@[simp] theorem entryPairListVertices_cons_second {d q : ℕ}
    (p : Fin d × Fin d) (old : EntryPairList d q) :
    entryPairListVertices (Fin.cons p old) (secondVertex q) = p.2 := by
  rw [secondVertex_rightSlot, entryPairListVertices_right]
  rfl

@[simp] theorem entryPairListVertices_cons_remaining {d q : ℕ}
    (p : Fin d × Fin d) (old : EntryPairList d q) (i : Fin (2 * q)) :
    entryPairListVertices (Fin.cons p old) (remainingVertex q i) =
      entryPairListVertices old i := by
  obtain ⟨⟨i, b⟩, rfl⟩ := (matchingSlotEquiv q).surjective i
  fin_cases b
  · change entryPairListVertices (Fin.cons p old) (remainingVertex q (matchingSlotEquiv q (i, 0))) =
      entryPairListVertices old (matchingSlotEquiv q (i, 0))
    rw [matchingSlotEquiv_zero, remainingVertex_leftSlot,
        entryPairListVertices_left, entryPairListVertices_left]
    rfl
  · change entryPairListVertices (Fin.cons p old) (remainingVertex q (matchingSlotEquiv q (i, 1))) =
      entryPairListVertices old (matchingSlotEquiv q (i, 1))
    rw [matchingSlotEquiv_one, remainingVertex_rightSlot,
        entryPairListVertices_right, entryPairListVertices_right]
    rfl

end A4Research
