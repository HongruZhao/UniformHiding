import A4.MatchingGramBinary

/-! The union components of two matchings are pairs of rotation cycles. -/

noncomputable section

namespace MatsumotoPaper

private abbrev PM (n : ℕ) := A4Standalone.GramHafnian.PerfectMatching n

theorem matchingRotation_reachable {n : ℕ} (M N : PM n) (i : Fin (2 * n)) :
    Relation.ReflTransGen (matchingAdjacent M N) i (matchingRotation M N i) := by
  have hN : Relation.ReflTransGen (matchingAdjacent M N) i (N i) := .single (Or.inr rfl)
  have hM : Relation.ReflTransGen (matchingAdjacent M N) (N i) (M (N i)) := .single (Or.inl rfl)
  exact hN.trans hM

theorem matchingRotation_pow_reachable {n : ℕ} (M N : PM n)
    (i : Fin (2 * n)) (k : ℕ) :
    Relation.ReflTransGen (matchingAdjacent M N) i ((matchingRotation M N ^ k) i) := by
  induction k with
  | zero => exact Relation.ReflTransGen.refl
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    exact ih.trans (matchingRotation_reachable M N _)

theorem matchingRotation_reachable_of_sameCycle {n : ℕ} (M N : PM n)
    {i j : Fin (2 * n)} (h : (matchingRotation M N).SameCycle i j) :
    Relation.ReflTransGen (matchingAdjacent M N) i j := by
  obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
  rw [← hk]
  exact matchingRotation_pow_reachable M N i k

theorem matching_reachable_iff_rotation_cycles {n : ℕ} (M N : PM n)
    (i j : Fin (2 * n)) :
    Relation.ReflTransGen (matchingAdjacent M N) i j ↔
      (matchingRotation M N).SameCycle i j ∨
        (matchingRotation M N).SameCycle (M i) j := by
  constructor
  · intro h
    induction h with
    | refl => exact Or.inl (Equiv.Perm.SameCycle.refl _ _)
    | @tail j k hij hjk ih =>
      rcases hjk with hM | hN
      · subst k
        rcases ih with h | h
        · exact Or.inr ((matchingRotation_sameCycle_mate M N i j).mpr h)
        · left
          simpa only [M.apply_apply] using
            (matchingRotation_sameCycle_mate M N (M i) j).mpr h
      · subst k
        have hMN := (matchingRotation_sameCycle_other_mate M N j).symm
        rcases ih with h | h
        · exact Or.inr (((matchingRotation_sameCycle_mate M N i j).mpr h).trans hMN)
        · left
          have h' := (matchingRotation_sameCycle_mate M N (M i) j).mpr h
          simpa only [M.apply_apply] using h'.trans hMN
  · rintro (h | h)
    · exact matchingRotation_reachable_of_sameCycle M N h
    · have hM : Relation.ReflTransGen (matchingAdjacent M N) i (M i) := .single (Or.inl rfl)
      exact hM.trans (matchingRotation_reachable_of_sameCycle M N h)

theorem alternatingBit_rotation_invariant {n : ℕ} (M N : PM n)
    (b : AlternatingBitColoring M N) (i : Fin (2 * n)) :
    b.val (matchingRotation M N i) = b.val i := by
  change b.val (M (N i)) = b.val i
  rw [b.property.1, b.property.2]
  simp only [finTwoSwap, Equiv.swap_apply_self]

theorem alternatingBit_rotation_pow_invariant {n : ℕ} (M N : PM n)
    (b : AlternatingBitColoring M N) (i : Fin (2 * n)) (k : ℕ) :
    b.val ((matchingRotation M N ^ k) i) = b.val i := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, alternatingBit_rotation_invariant]
    exact ih

theorem alternatingBit_eq_of_same_rotation_cycle {n : ℕ} (M N : PM n)
    (b : AlternatingBitColoring M N) {i j : Fin (2 * n)}
    (h : (matchingRotation M N).SameCycle i j) : b.val i = b.val j := by
  obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
  rw [← hk]
  exact (alternatingBit_rotation_pow_invariant M N b i k).symm

theorem matching_same_rotation_cycle_iff_component_bit {n : ℕ} (M N : PM n)
    (b : AlternatingBitColoring M N) (i j : Fin (2 * n)) :
    (matchingRotation M N).SameCycle i j ↔
      vertexMatchingComponent M N i = vertexMatchingComponent M N j ∧ b.val i = b.val j := by
  constructor
  · intro h
    constructor
    · apply Subtype.ext
      exact componentVertices_eq_of_reachable M N
        (matchingRotation_reachable_of_sameCycle M N h)
    · exact alternatingBit_eq_of_same_rotation_cycle M N b h
  · rintro ⟨hc, hb⟩
    have hreach := (componentVertices_eq_iff M N i j).mp (congrArg Subtype.val hc)
    rcases (matching_reachable_iff_rotation_cycles M N i j).mp hreach with h | h
    · exact h
    · exfalso
      have hbit := alternatingBit_eq_of_same_rotation_cycle M N b h
      rw [b.property.1, ← hb] at hbit
      have hswap : ∀ c : Fin 2, finTwoSwap c ≠ c := by
        intro c
        fin_cases c <;> decide
      exact hswap (b.val i) hbit

end MatsumotoPaper
