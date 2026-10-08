import A4.MatchingGramDegreeFactorization

/-!
# The exact loop count under first-pair deletion

Colorings give a finite bijective proof of the loop-count identities.  The
coloring counts are already proved for the literal union components.
-/

open scoped BigOperators Matrix

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace MatsumotoPaper

private abbrev PM (n : ℕ) := A4Standalone.GramHafnian.PerfectMatching n

def firstPairColorExtension {q : ℕ} {α : Type*} (a : α)
    (f : Fin (2 * q) → α) : Fin (2 * (q + 1)) → α :=
  Sum.elim (fun _ => a) f ∘ (firstPairSplitEquiv q).symm

@[simp] theorem firstPairColorExtension_first {q : ℕ} {α : Type*}
    (a : α) (f : Fin (2 * q) → α) :
    firstPairColorExtension a f (firstVertex q) = a := by
  simp [firstPairColorExtension, firstVertex]

@[simp] theorem firstPairColorExtension_second {q : ℕ} {α : Type*}
    (a : α) (f : Fin (2 * q) → α) :
    firstPairColorExtension a f (secondVertex q) = a := by
  simp [firstPairColorExtension, secondVertex]

@[simp] theorem firstPairColorExtension_remaining {q : ℕ} {α : Type*}
    (a : α) (f : Fin (2 * q) → α) (i : Fin (2 * q)) :
    firstPairColorExtension a f (remainingVertex q i) = f i := by
  simp [firstPairColorExtension, remainingVertex]

def firstPairEmbeddedColoring {q : ℕ} {α : Type*} (M N : PM q)
    (a : α) (c : CompatibleMatchingColoring M N α) :
    CompatibleMatchingColoring (firstPairEmbed q M) (firstPairEmbed q N) α :=
  ⟨firstPairColorExtension a c.val, by
    constructor
    · intro v
      rcases firstPair_vertex_cases v with rfl | rfl | ⟨i, rfl⟩
      · simp only [firstPairEmbed_first, firstPairColorExtension_second,
          firstPairColorExtension_first]
      · simp only [firstPairEmbed_second, firstPairColorExtension_second,
          firstPairColorExtension_first]
      · simpa only [firstPairEmbed_remaining, firstPairColorExtension_remaining]
          using c.property.1 i
    · intro v
      rcases firstPair_vertex_cases v with rfl | rfl | ⟨i, rfl⟩
      · simp only [firstPairEmbed_first, firstPairColorExtension_second,
          firstPairColorExtension_first]
      · simp only [firstPairEmbed_second, firstPairColorExtension_second,
          firstPairColorExtension_first]
      · simpa only [firstPairEmbed_remaining, firstPairColorExtension_remaining]
          using c.property.2 i⟩

def firstPairRestrictedColoring {q : ℕ} {α : Type*} (M N : PM q)
    (c : CompatibleMatchingColoring (firstPairEmbed q M) (firstPairEmbed q N) α) :
    CompatibleMatchingColoring M N α :=
  ⟨fun i => c.val (remainingVertex q i), by
    constructor
    · intro i
      simpa only [firstPairEmbed_remaining] using c.property.1 (remainingVertex q i)
    · intro i
      simpa only [firstPairEmbed_remaining] using c.property.2 (remainingVertex q i)⟩

def firstPairEmbeddedColoringEquiv {q : ℕ} {α : Type*} (M N : PM q) :
    α × CompatibleMatchingColoring M N α ≃
      CompatibleMatchingColoring (firstPairEmbed q M) (firstPairEmbed q N) α where
  toFun c := firstPairEmbeddedColoring M N c.1 c.2
  invFun c := (c.val (firstVertex q), firstPairRestrictedColoring M N c)
  left_inv c := by
    apply Prod.ext
    · change firstPairColorExtension c.1 c.2.val (firstVertex q) = c.1
      exact firstPairColorExtension_first _ _
    · apply Subtype.ext
      funext i
      exact firstPairColorExtension_remaining _ _ i
  right_inv c := by
    apply Subtype.ext
    funext v
    change firstPairColorExtension (c.val (firstVertex q))
      (fun i => c.val (remainingVertex q i)) v = c.val v
    rcases firstPair_vertex_cases v with rfl | rfl | ⟨i, rfl⟩
    · exact firstPairColorExtension_first _ _
    · have hc : c.val (secondVertex q) = c.val (firstVertex q) := by
        simpa only [firstPairEmbed_first] using c.property.1 (firstVertex q)
      exact (firstPairColorExtension_second _ _).trans hc.symm
    · exact firstPairColorExtension_remaining _ _ i

theorem matchingKappa_firstPairEmbed {q : ℕ} (M N : PM q) :
    matchingKappa (firstPairEmbed q M) (firstPairEmbed q N) = matchingKappa M N + 1 := by
  have hcard := Fintype.card_congr (firstPairEmbeddedColoringEquiv (α := Fin 2) M N)
  rw [Fintype.card_prod, Fintype.card_fin, card_compatibleMatchingColoring,
    card_compatibleMatchingColoring] at hcard
  apply Nat.pow_right_injective (by omega : 2 ≤ 2)
  change (2 : ℕ) ^ matchingKappa (firstPairEmbed q M) (firstPairEmbed q N) =
    2 ^ (matchingKappa M N + 1)
  rw [pow_succ, mul_comm]
  exact hcard.symm

theorem coloring_swap_invariant {ι α : Type*} [DecidableEq ι]
    (f : ι → α) (a b : ι) (hab : f a = f b) (v : ι) :
    f (Equiv.swap a b v) = f v := by
  by_cases ha : v = a
  · subst v
    rw [Equiv.swap_apply_left]
    exact hab.symm
  · by_cases hb : v = b
    · subst v
      rw [Equiv.swap_apply_right]
      exact hab
    · rw [Equiv.swap_apply_of_ne_of_ne ha hb]

def compatibleColoringTransportLeft {n : ℕ} {α : Type*}
    (M N : PM n) (g : Equiv.Perm (Fin (2 * n)))
    (c : CompatibleMatchingColoring M N α)
    (hc : ∀ v, c.val (g v) = c.val v) :
    CompatibleMatchingColoring (transportPairPartition g M) N α :=
  ⟨c.val, by
    constructor
    · intro v
      rw [transportPairPartition_apply, hc, c.property.1]
      exact (hc (g.symm v)).symm.trans (congrArg c.val (g.apply_symm_apply v))
    · exact c.property.2⟩

def firstPairNormalizedColoring {q : ℕ} {α : Type*}
    (M : PM (q + 1)) (N : PM q)
    (c : CompatibleMatchingColoring M (firstPairEmbed q N) α) :
    CompatibleMatchingColoring (firstPairNormalize M) (firstPairEmbed q N) α := by
  have hc : c.val (firstVertex q) = c.val (M (secondVertex q)) := by
    calc
      _ = c.val (secondVertex q) := by
        simpa only [firstPairEmbed_first] using (c.property.2 (firstVertex q)).symm
      _ = _ := (c.property.1 (secondVertex q)).symm
  exact compatibleColoringTransportLeft M (firstPairEmbed q N)
    (Equiv.swap (firstVertex q) (M (secondVertex q))) c
    (coloring_swap_invariant c.val _ _ hc)

@[simp] theorem firstPairNormalizedColoring_val {q : ℕ} {α : Type*}
    (M : PM (q + 1)) (N : PM q)
    (c : CompatibleMatchingColoring M (firstPairEmbed q N) α) :
    (firstPairNormalizedColoring M N c).val = c.val := rfl

def firstPairDeletedColoring {q : ℕ} {α : Type*}
    (M : PM (q + 1)) (N : PM q)
    (c : CompatibleMatchingColoring M (firstPairEmbed q N) α) :
    CompatibleMatchingColoring (firstPairDelete M) N α :=
  ⟨fun i => c.val (remainingVertex q i), by
    constructor
    · intro i
      have hc := (firstPairNormalizedColoring M N c).property.1 (remainingVertex q i)
      change c.val (firstPairNormalize M (remainingVertex q i)) =
        c.val (remainingVertex q i) at hc
      rw [← firstPairEmbed_delete M, firstPairEmbed_remaining] at hc
      exact hc
    · intro i
      simpa only [firstPairEmbed_remaining] using c.property.2 (remainingVertex q i)⟩

@[simp] theorem firstPairDeletedColoring_val {q : ℕ} {α : Type*}
    (M : PM (q + 1)) (N : PM q)
    (c : CompatibleMatchingColoring M (firstPairEmbed q N) α) (i : Fin (2 * q)) :
    (firstPairDeletedColoring M N c).val i = c.val (remainingVertex q i) := rfl

def firstPairJoinedColoring {q : ℕ} {α : Type*}
    (M : PM (q + 1)) (N : PM q) (t : Fin (2 * q))
    (hM : M (secondVertex q) = remainingVertex q t)
    (c : CompatibleMatchingColoring (firstPairDelete M) N α) :
    CompatibleMatchingColoring M (firstPairEmbed q N) α :=
  ⟨firstPairColorExtension (c.val t) c.val, by
  let cE := firstPairEmbeddedColoring (firstPairDelete M) N (c.val t) c
  have hc : cE.val (firstVertex q) = cE.val (M (secondVertex q)) := by
    rw [hM]
    change firstPairColorExtension (c.val t) c.val (firstVertex q) =
      firstPairColorExtension (c.val t) c.val (remainingVertex q t)
    exact (firstPairColorExtension_first _ _).trans
      (firstPairColorExtension_remaining _ _ t).symm
  have hinv : ∀ v, cE.val ((firstPairSwitch q t) v) = cE.val v := by
    rw [hM] at hc
    exact coloring_swap_invariant cE.val _ _ hc
  let cN : CompatibleMatchingColoring (firstPairNormalize M) (firstPairEmbed q N) α :=
    ⟨cE.val, by
      constructor
      · intro v
        rw [← firstPairEmbed_delete M]
        exact cE.property.1 v
      · exact cE.property.2⟩
  let cM := compatibleColoringTransportLeft (firstPairNormalize M)
    (firstPairEmbed q N) (firstPairSwitch q t) cN hinv
  have hback : transportPairPartition (firstPairSwitch q t) (firstPairNormalize M) = M := by
    rw [← firstPairSwitch_normalizes M t hM, ← transportPairPartition_mul]
    simp [firstPairSwitch]
  have hprop := cM.property
  change (∀ v, firstPairColorExtension (c.val t) c.val
    (transportPairPartition (firstPairSwitch q t) (firstPairNormalize M) v) =
      firstPairColorExtension (c.val t) c.val v) ∧
    (∀ v, firstPairColorExtension (c.val t) c.val (firstPairEmbed q N v) =
      firstPairColorExtension (c.val t) c.val v) at hprop
  rw [hback] at hprop
  exact hprop⟩

@[simp] theorem firstPairJoinedColoring_val {q : ℕ} {α : Type*}
    (M : PM (q + 1)) (N : PM q) (t : Fin (2 * q))
    (hM : M (secondVertex q) = remainingVertex q t)
    (c : CompatibleMatchingColoring (firstPairDelete M) N α) :
    (firstPairJoinedColoring M N t hM c).val = firstPairColorExtension (c.val t) c.val := rfl

def firstPairDeletedColoringEquiv {q : ℕ} {α : Type*}
    (M : PM (q + 1)) (N : PM q) (t : Fin (2 * q))
    (hM : M (secondVertex q) = remainingVertex q t) :
    CompatibleMatchingColoring (firstPairDelete M) N α ≃
      CompatibleMatchingColoring M (firstPairEmbed q N) α where
  toFun := firstPairJoinedColoring M N t hM
  invFun := firstPairDeletedColoring M N
  left_inv c := by
    apply Subtype.ext
    funext i
    simp only [firstPairDeletedColoring_val, firstPairJoinedColoring_val,
      firstPairColorExtension_remaining]
  right_inv c := by
    apply Subtype.ext
    funext v
    simp only [firstPairJoinedColoring_val, firstPairDeletedColoring_val]
    change firstPairColorExtension (c.val (remainingVertex q t))
      (fun i => c.val (remainingVertex q i)) v = c.val v
    have hc : c.val (remainingVertex q t) = c.val (secondVertex q) :=
      hM ▸ c.property.1 (secondVertex q)
    have hc' : c.val (secondVertex q) = c.val (firstVertex q) := by
      simpa only [firstPairEmbed_first] using c.property.2 (firstVertex q)
    rcases firstPair_vertex_cases v with rfl | rfl | ⟨i, rfl⟩
    · exact (firstPairColorExtension_first _ _).trans (hc.trans hc')
    · exact (firstPairColorExtension_second _ _).trans hc
    · exact firstPairColorExtension_remaining _ _ i

theorem matchingKappa_firstPairDelete_of_partner {q : ℕ}
    (M : PM (q + 1)) (N : PM q) (t : Fin (2 * q))
    (hM : M (secondVertex q) = remainingVertex q t) :
    matchingKappa M (firstPairEmbed q N) = matchingKappa (firstPairDelete M) N := by
  have hcard := Fintype.card_congr
    (firstPairDeletedColoringEquiv (α := Fin 2) M N t hM)
  rw [card_compatibleMatchingColoring, card_compatibleMatchingColoring] at hcard
  exact Nat.pow_right_injective (by omega : 2 ≤ 2) hcard.symm

theorem matchingKappa_firstPairDelete_of_fixed {q : ℕ}
    (M : PM (q + 1)) (N : PM q) (hM : M (firstVertex q) = secondVertex q) :
    matchingKappa M (firstPairEmbed q N) = matchingKappa (firstPairDelete M) N + 1 := by
  calc
    _ = matchingKappa (firstPairNormalize M) (firstPairEmbed q N) := by
      rw [firstPairNormalize_of_fixed M hM]
    _ = _ := by rw [← firstPairEmbed_delete M, matchingKappa_firstPairEmbed]

end MatsumotoPaper
