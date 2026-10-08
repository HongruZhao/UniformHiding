import A4.MatchingGramColoring
import A4.InverseMomentAlgebraSharp

/-!
# Removing the first pair of a matching

These definitions work on the literal finite involution matching type.  A
first-pair normalization sends the partner of vertex one to vertex zero;
the resulting matching can be restricted to the remaining vertices.
-/

open scoped BigOperators Matrix

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MatsumotoPaper

private abbrev PM (n : ℕ) := A4Standalone.GramHafnian.PerfectMatching n

def firstPairSplitEquiv (q : ℕ) :
    Fin 2 ⊕ Fin (2 * q) ≃ Fin (2 * (q + 1)) :=
  finSumFinEquiv.trans (finCongr (by omega))

def firstVertex (q : ℕ) : Fin (2 * (q + 1)) :=
  firstPairSplitEquiv q (Sum.inl 0)

def secondVertex (q : ℕ) : Fin (2 * (q + 1)) :=
  firstPairSplitEquiv q (Sum.inl 1)

def remainingVertex (q : ℕ) (i : Fin (2 * q)) : Fin (2 * (q + 1)) :=
  firstPairSplitEquiv q (Sum.inr i)

@[simp] theorem firstVertex_val (q : ℕ) : (firstVertex q).val = 0 := rfl
@[simp] theorem secondVertex_val (q : ℕ) : (secondVertex q).val = 1 := rfl
@[simp] theorem remainingVertex_val (q : ℕ) (i : Fin (2 * q)) :
    (remainingVertex q i).val = 2 + i.val := rfl

@[simp] theorem firstVertex_ne_second (q : ℕ) : firstVertex q ≠ secondVertex q := by
  intro h
  have := congrArg Fin.val h
  simp only [firstVertex_val, secondVertex_val] at this
  omega

@[simp] theorem remainingVertex_ne_first (q : ℕ) (i : Fin (2 * q)) :
    remainingVertex q i ≠ firstVertex q := by
  intro h
  have := congrArg Fin.val h
  simp only [remainingVertex_val, firstVertex_val] at this
  omega

@[simp] theorem remainingVertex_ne_second (q : ℕ) (i : Fin (2 * q)) :
    remainingVertex q i ≠ secondVertex q := by
  intro h
  have := congrArg Fin.val h
  simp only [remainingVertex_val, secondVertex_val] at this
  omega

theorem remainingVertex_injective (q : ℕ) : Function.Injective (remainingVertex q) := by
  intro i j h
  apply Sum.inr_injective
  exact (firstPairSplitEquiv q).injective h

theorem firstPair_vertex_cases {q : ℕ} (v : Fin (2 * (q + 1))) :
    v = firstVertex q ∨ v = secondVertex q ∨ ∃ i, v = remainingVertex q i := by
  obtain ⟨v, rfl⟩ := (firstPairSplitEquiv q).surjective v
  rcases v with b | i
  · fin_cases b
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr ⟨i, rfl⟩)

def firstPairEmbed (q : ℕ) (M : PM q) : PM (q + 1) where
  mate := (firstPairSplitEquiv q).permCongr (Equiv.sumCongr finTwoSwap M.mate)
  mate_ne v := by
    obtain ⟨v, rfl⟩ := (firstPairSplitEquiv q).surjective v
    intro h
    have h' := (firstPairSplitEquiv q).injective h
    rcases v with b | i
    · fin_cases b <;> simp [Equiv.permCongr, finTwoSwap] at h'
    · simpa [Equiv.permCongr] using h'
  mate_mate v := by
    obtain ⟨v, rfl⟩ := (firstPairSplitEquiv q).surjective v
    rcases v with b | i
    · fin_cases b <;> simp [Equiv.permCongr, finTwoSwap]
    · simp [Equiv.permCongr, M.apply_apply]

@[simp] theorem firstPairEmbed_first (q : ℕ) (M : PM q) :
    firstPairEmbed q M (firstVertex q) = secondVertex q := by
  simp [firstPairEmbed, firstVertex, secondVertex, Equiv.permCongr, finTwoSwap]

@[simp] theorem firstPairEmbed_second (q : ℕ) (M : PM q) :
    firstPairEmbed q M (secondVertex q) = firstVertex q := by
  simp [firstPairEmbed, firstVertex, secondVertex, Equiv.permCongr, finTwoSwap]

@[simp] theorem firstPairEmbed_remaining (q : ℕ) (M : PM q) (i : Fin (2 * q)) :
    firstPairEmbed q M (remainingVertex q i) = remainingVertex q (M i) := by
  simp [firstPairEmbed, remainingVertex, Equiv.permCongr]

theorem firstPairEmbed_injective (q : ℕ) : Function.Injective (firstPairEmbed q) := by
  intro M N h
  apply pairPartition_ext
  intro i
  apply remainingVertex_injective q
  simpa only [firstPairEmbed_remaining] using congrArg (fun P : PM (q + 1) => P (remainingVertex q i)) h

def FirstPairRemainder (q : ℕ) :=
  {v : Fin (2 * (q + 1)) // v ≠ firstVertex q ∧ v ≠ secondVertex q}

def firstPairRemainderEquiv (q : ℕ) : Fin (2 * q) ≃ FirstPairRemainder q :=
  Equiv.ofBijective (fun i => ⟨remainingVertex q i,
    remainingVertex_ne_first q i, remainingVertex_ne_second q i⟩) (by
      constructor
      · intro i j h
        exact remainingVertex_injective q (congrArg Subtype.val h)
      · intro v
        rcases firstPair_vertex_cases v.val with h | h | ⟨i, hi⟩
        · exact False.elim (v.property.1 h)
        · exact False.elim (v.property.2 h)
        · exact ⟨i, Subtype.ext hi.symm⟩)

@[simp] theorem firstPairRemainderEquiv_val (q : ℕ) (i : Fin (2 * q)) :
    (firstPairRemainderEquiv q i).val = remainingVertex q i := rfl

theorem firstPair_mate_remaining {q : ℕ} (M : PM (q + 1))
    (hM : M (firstVertex q) = secondVertex q) (v : Fin (2 * (q + 1))) :
    (M v ≠ firstVertex q ∧ M v ≠ secondVertex q) ↔
      (v ≠ firstVertex q ∧ v ≠ secondVertex q) := by
  have hM' : M (secondVertex q) = firstVertex q := by
    simpa only [hM] using M.apply_apply (firstVertex q)
  constructor
  · intro hv
    constructor
    · intro h
      exact hv.2 (h ▸ hM)
    · intro h
      exact hv.1 (h ▸ hM')
  · intro hv
    constructor
    · intro h
      have := congrArg M h
      exact hv.2 (by simpa only [M.apply_apply, hM] using this)
    · intro h
      have := congrArg M h
      exact hv.1 (by simpa only [M.apply_apply, hM'] using this)

def firstPairRestrictPerm {q : ℕ} (M : PM (q + 1))
    (hM : M (firstVertex q) = secondVertex q) : Equiv.Perm (Fin (2 * q)) :=
  ((firstPairRemainderEquiv q).trans
    (M.mate.subtypePerm (firstPair_mate_remaining M hM))).trans
      (firstPairRemainderEquiv q).symm

@[simp] theorem firstPairRestrictPerm_remaining {q : ℕ} (M : PM (q + 1))
    (hM : M (firstVertex q) = secondVertex q) (i : Fin (2 * q)) :
    remainingVertex q (firstPairRestrictPerm M hM i) = M (remainingVertex q i) := by
  change (firstPairRemainderEquiv q ((firstPairRemainderEquiv q).symm
    ((M.mate.subtypePerm (firstPair_mate_remaining M hM))
      (firstPairRemainderEquiv q i)))).val = _
  rw [Equiv.apply_symm_apply]
  rfl

def firstPairRestrict {q : ℕ} (M : PM (q + 1))
    (hM : M (firstVertex q) = secondVertex q) : PM q where
  mate := firstPairRestrictPerm M hM
  mate_ne i := by
    intro h
    have h' := congrArg (remainingVertex q) h
    rw [firstPairRestrictPerm_remaining] at h'
    exact M.apply_ne (remainingVertex q i) h'
  mate_mate i := by
    apply remainingVertex_injective q
    rw [firstPairRestrictPerm_remaining, firstPairRestrictPerm_remaining, M.apply_apply]

@[simp] theorem firstPairRestrict_remaining {q : ℕ} (M : PM (q + 1))
    (hM : M (firstVertex q) = secondVertex q) (i : Fin (2 * q)) :
    remainingVertex q (firstPairRestrict M hM i) = M (remainingVertex q i) := by
  exact firstPairRestrictPerm_remaining M hM i

@[simp] theorem firstPairEmbed_restrict {q : ℕ} (M : PM (q + 1))
    (hM : M (firstVertex q) = secondVertex q) :
    firstPairEmbed q (firstPairRestrict M hM) = M := by
  apply pairPartition_ext
  intro v
  rcases firstPair_vertex_cases v with rfl | rfl | ⟨i, rfl⟩
  · exact (firstPairEmbed_first q _).trans hM.symm
  · have hM' : M (secondVertex q) = firstVertex q := by
      simpa only [hM] using M.apply_apply (firstVertex q)
    exact (firstPairEmbed_second q _).trans hM'.symm
  · rw [firstPairEmbed_remaining, firstPairRestrict_remaining]

@[simp] theorem firstPairRestrict_embed (q : ℕ) (M : PM q) :
    firstPairRestrict (firstPairEmbed q M) (firstPairEmbed_first q M) = M := by
  apply firstPairEmbed_injective q
  exact firstPairEmbed_restrict _ _

def firstPairNormalize {q : ℕ} (M : PM (q + 1)) : PM (q + 1) :=
  transportPairPartition (Equiv.swap (firstVertex q) (M (secondVertex q))) M

@[simp] theorem firstPairNormalize_second {q : ℕ} (M : PM (q + 1)) :
    firstPairNormalize M (secondVertex q) = firstVertex q := by
  have hs : Equiv.swap (firstVertex q) (M (secondVertex q)) (secondVertex q) =
      secondVertex q :=
    Equiv.swap_apply_of_ne_of_ne (firstVertex_ne_second q).symm
      (M.apply_ne (secondVertex q)).symm
  simp only [firstPairNormalize, transportPairPartition_apply, Equiv.symm_swap, hs,
    Equiv.swap_apply_right]

@[simp] theorem firstPairNormalize_first {q : ℕ} (M : PM (q + 1)) :
    firstPairNormalize M (firstVertex q) = secondVertex q := by
  simpa only [firstPairNormalize_second] using
    (firstPairNormalize M).apply_apply (secondVertex q)

def firstPairDelete {q : ℕ} (M : PM (q + 1)) : PM q :=
  firstPairRestrict (firstPairNormalize M) (firstPairNormalize_first M)

@[simp] theorem firstPairEmbed_delete {q : ℕ} (M : PM (q + 1)) :
    firstPairEmbed q (firstPairDelete M) = firstPairNormalize M :=
  firstPairEmbed_restrict _ _

theorem firstPairNormalize_of_fixed {q : ℕ} (M : PM (q + 1))
    (hM : M (firstVertex q) = secondVertex q) : firstPairNormalize M = M := by
  have hM' : M (secondVertex q) = firstVertex q := by
    simpa only [hM] using M.apply_apply (firstVertex q)
  simp only [firstPairNormalize, hM', Equiv.swap_self]
  exact transportPairPartition_one M

@[simp] theorem firstPairDelete_embed (q : ℕ) (M : PM q) :
    firstPairDelete (firstPairEmbed q M) = M := by
  apply firstPairEmbed_injective q
  rw [firstPairEmbed_delete, firstPairNormalize_of_fixed _ (firstPairEmbed_first q M)]

def firstPairSwitch (q : ℕ) (t : Fin (2 * q)) :
    Equiv.Perm (Fin (2 * (q + 1))) :=
  Equiv.swap (firstVertex q) (remainingVertex q t)

@[simp] theorem firstPairSwitch_first (q : ℕ) (t : Fin (2 * q)) :
    firstPairSwitch q t (firstVertex q) = remainingVertex q t :=
  Equiv.swap_apply_left _ _

@[simp] theorem firstPairSwitch_remaining_self (q : ℕ) (t : Fin (2 * q)) :
    firstPairSwitch q t (remainingVertex q t) = firstVertex q :=
  Equiv.swap_apply_right _ _

@[simp] theorem firstPairSwitch_second (q : ℕ) (t : Fin (2 * q)) :
    firstPairSwitch q t (secondVertex q) = secondVertex q :=
  Equiv.swap_apply_of_ne_of_ne (firstVertex_ne_second q).symm
    (remainingVertex_ne_second q t).symm

@[simp] theorem firstPairSwitch_symm (q : ℕ) (t : Fin (2 * q)) :
    (firstPairSwitch q t).symm = firstPairSwitch q t := Equiv.symm_swap _ _

theorem firstPairSwitch_fixed_iff {q : ℕ} (M : PM (q + 1)) (t : Fin (2 * q)) :
    transportPairPartition (firstPairSwitch q t) M (firstVertex q) = secondVertex q ↔
      M (secondVertex q) = remainingVertex q t := by
  let N := transportPairPartition (firstPairSwitch q t) M
  have hfixed : N (firstVertex q) = secondVertex q ↔
      N (secondVertex q) = firstVertex q := by
    constructor <;> intro h
    · simpa only [h] using N.apply_apply (firstVertex q)
    · simpa only [h] using N.apply_apply (secondVertex q)
  rw [hfixed]
  change firstPairSwitch q t (M ((firstPairSwitch q t).symm (secondVertex q))) = _ ↔ _
  rw [firstPairSwitch_symm, firstPairSwitch_second]
  constructor
  · intro h
    have := congrArg (firstPairSwitch q t) h
    simpa only [firstPairSwitch, Equiv.swap_apply_self, Equiv.swap_apply_left] using this
  · intro h
    rw [h, firstPairSwitch_remaining_self]

theorem firstPairSwitch_normalizes {q : ℕ} (M : PM (q + 1)) (t : Fin (2 * q))
    (hM : M (secondVertex q) = remainingVertex q t) :
    transportPairPartition (firstPairSwitch q t) M = firstPairNormalize M := by
  simp only [firstPairNormalize, hM]
  rfl

def firstPairEmbeddingMatrix (q : ℕ) : Matrix (PM (q + 1)) (PM q) ℂ :=
  fun P Q => if P = firstPairEmbed q Q then 1 else 0

def firstPairRelabelingMatrix (q : ℕ) (t : Fin (2 * q)) :
    Matrix (PM (q + 1)) (PM (q + 1)) ℂ :=
  fun P R => if P = transportPairPartition (firstPairSwitch q t) R then 1 else 0

def firstPairSwitchOperator (q : ℕ) (z : ℂ) :
    Matrix (PM (q + 1)) (PM (q + 1)) ℂ :=
  z • 1 + ∑ t : Fin (2 * q), firstPairRelabelingMatrix q t

end MatsumotoPaper
