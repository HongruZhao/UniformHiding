import A4.MatchingGramColoring

/-! Alternating binary colorings of the union of two perfect matchings. -/

noncomputable section

namespace MatsumotoPaper

private abbrev PM (n : ℕ) := A4Standalone.GramHafnian.PerfectMatching n

@[simp] theorem matchingMate_mul_self {n : ℕ} (M : PM n) : M.mate * M.mate = 1 := by
  apply Equiv.ext
  intro i
  exact M.apply_apply i

@[simp] theorem matchingMate_inv {n : ℕ} (M : PM n) : M.mate⁻¹ = M.mate := by
  exact inv_eq_of_mul_eq_one_right (matchingMate_mul_self M)

def matchingRotation {n : ℕ} (M N : PM n) : Equiv.Perm (Fin (2 * n)) :=
  M.mate * N.mate

theorem matchingRotation_semiconj {n : ℕ} (M N : PM n) :
    SemiconjBy M.mate (matchingRotation M N) (matchingRotation M N)⁻¹ := by
  unfold matchingRotation
  change M.mate * (M.mate * N.mate) = (M.mate * N.mate)⁻¹ * M.mate
  rw [mul_inv_rev, matchingMate_inv, matchingMate_inv, ← mul_assoc,
    matchingMate_mul_self, one_mul, mul_assoc, matchingMate_mul_self, mul_one]

theorem matchingRotation_pow_ne_mate {n : ℕ} (M N : PM n)
    (i : Fin (2 * n)) (k : ℕ) : (matchingRotation M N ^ k) i ≠ M i := by
  intro h
  obtain ⟨l, hk | hk⟩ := Nat.even_or_odd' k
  · have hfixed : M ((matchingRotation M N ^ l) i) = (matchingRotation M N ^ l) i := by
      have hsemi := congrArg (fun p : Equiv.Perm (Fin (2 * n)) => p i)
        ((matchingRotation_semiconj M N).pow_right l).eq
      change M ((matchingRotation M N ^ l) i) =
        (((matchingRotation M N)⁻¹ ^ l) (M i)) at hsemi
      rw [inv_pow] at hsemi
      have hpow : matchingRotation M N ^ k = matchingRotation M N ^ l * matchingRotation M N ^ l := by
        rw [hk, show 2 * l = l + l by omega, pow_add]
      rw [hsemi, ← h, hpow]
      simp only [Equiv.Perm.mul_apply]
      exact (matchingRotation M N ^ l).symm_apply_apply _
    exact M.apply_ne _ hfixed
  · have hfixed : N ((matchingRotation M N ^ l) i) = (matchingRotation M N ^ l) i := by
      have hsemi := congrArg (fun p : Equiv.Perm (Fin (2 * n)) => p i)
        ((matchingRotation_semiconj M N).pow_right (l + 1)).eq
      change M ((matchingRotation M N ^ (l + 1)) i) =
        (((matchingRotation M N)⁻¹ ^ (l + 1)) (M i)) at hsemi
      rw [inv_pow] at hsemi
      have hN : N ((matchingRotation M N ^ l) i) =
          M ((matchingRotation M N ^ (l + 1)) i) := by
        rw [pow_succ']
        simp only [matchingRotation, Equiv.Perm.mul_apply, M.apply_apply]
      have hpow : matchingRotation M N ^ k =
          matchingRotation M N ^ (l + 1) * matchingRotation M N ^ l := by
        rw [hk, show 2 * l + 1 = (l + 1) + l by omega, pow_add]
      rw [hN, hsemi, ← h, hpow]
      exact (matchingRotation M N ^ (l + 1)).symm_apply_apply _
    exact N.apply_ne _ hfixed

theorem matchingRotation_not_sameCycle_mate {n : ℕ} (M N : PM n)
    (i : Fin (2 * n)) : ¬ (matchingRotation M N).SameCycle i (M i) := by
  intro h
  obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
  exact matchingRotation_pow_ne_mate M N i k hk

theorem matchingRotation_sameCycle_mate {n : ℕ} (M N : PM n)
    (i j : Fin (2 * n)) :
    (matchingRotation M N).SameCycle (M i) (M j) ↔
      (matchingRotation M N).SameCycle i j := by
  have hforward : ∀ a b, (matchingRotation M N).SameCycle (M a) (M b) →
      (matchingRotation M N).SameCycle a b := by
    intro a b hab
    obtain ⟨k, hk⟩ := hab
    refine ⟨-k, ?_⟩
    have hs := congrArg (fun p : Equiv.Perm (Fin (2 * n)) => p (M a))
      ((matchingRotation_semiconj M N).zpow_right k).eq
    change M ((matchingRotation M N ^ k) (M a)) =
      ((matchingRotation M N)⁻¹ ^ k) (M (M a)) at hs
    rw [hk, M.apply_apply, M.apply_apply, inv_zpow, ← zpow_neg] at hs
    exact hs.symm
  constructor
  · exact hforward i j
  · intro h
    apply hforward (M i) (M j)
    simpa only [M.apply_apply] using h

def matchingRotationCycle {n : ℕ} (M N : PM n) (i : Fin (2 * n)) :
    Finset (Fin (2 * n)) :=
  Finset.univ.filter ((matchingRotation M N).SameCycle i)

@[simp] theorem mem_matchingRotationCycle {n : ℕ} (M N : PM n)
    (i j : Fin (2 * n)) : j ∈ matchingRotationCycle M N i ↔
      (matchingRotation M N).SameCycle i j := by
  classical
  simp only [matchingRotationCycle, Finset.mem_filter, Finset.mem_univ, true_and]

theorem matchingRotationCycle_nonempty {n : ℕ} (M N : PM n) (i : Fin (2 * n)) :
    (matchingRotationCycle M N i).Nonempty :=
  ⟨i, (mem_matchingRotationCycle M N i i).mpr (Equiv.Perm.SameCycle.refl _ _)⟩

def matchingRotationCycleMin {n : ℕ} (M N : PM n) (i : Fin (2 * n)) : Fin (2 * n) :=
  (matchingRotationCycle M N i).min' (matchingRotationCycle_nonempty M N i)

theorem matchingRotationCycle_eq_of_sameCycle {n : ℕ} (M N : PM n)
    {i j : Fin (2 * n)} (h : (matchingRotation M N).SameCycle i j) :
    matchingRotationCycle M N i = matchingRotationCycle M N j := by
  classical
  ext k
  simp only [mem_matchingRotationCycle]
  exact ⟨fun hik => h.symm.trans hik, fun hjk => h.trans hjk⟩

theorem matchingRotationCycleMin_eq_iff {n : ℕ} (M N : PM n)
    (i j : Fin (2 * n)) :
    matchingRotationCycleMin M N i = matchingRotationCycleMin M N j ↔
      (matchingRotation M N).SameCycle i j := by
  constructor
  · intro h
    have hi := Finset.min'_mem (matchingRotationCycle M N i)
      (matchingRotationCycle_nonempty M N i)
    have hj := Finset.min'_mem (matchingRotationCycle M N j)
      (matchingRotationCycle_nonempty M N j)
    change matchingRotationCycleMin M N i ∈ matchingRotationCycle M N i at hi
    change matchingRotationCycleMin M N j ∈ matchingRotationCycle M N j at hj
    rw [← h] at hj
    exact ((mem_matchingRotationCycle M N i _).mp hi).trans
      ((mem_matchingRotationCycle M N j _).mp hj).symm
  · intro h
    unfold matchingRotationCycleMin
    simp only [matchingRotationCycle_eq_of_sameCycle M N h]

theorem matchingRotationCycleMin_ne_mate {n : ℕ} (M N : PM n)
    (i : Fin (2 * n)) : matchingRotationCycleMin M N i ≠ matchingRotationCycleMin M N (M i) := by
  intro h
  exact matchingRotation_not_sameCycle_mate M N i
    ((matchingRotationCycleMin_eq_iff M N i (M i)).mp h)

def matchingAlternatingBit {n : ℕ} (M N : PM n) (i : Fin (2 * n)) : Fin 2 :=
  if matchingRotationCycleMin M N i < matchingRotationCycleMin M N (M i) then 0 else 1

@[simp] theorem matchingAlternatingBit_mate_left {n : ℕ} (M N : PM n)
    (i : Fin (2 * n)) : matchingAlternatingBit M N (M i) =
      finTwoSwap (matchingAlternatingBit M N i) := by
  unfold matchingAlternatingBit
  rw [M.apply_apply]
  have hne := matchingRotationCycleMin_ne_mate M N i
  rcases lt_or_gt_of_ne hne with h | h
  · simp [h, not_lt_of_gt h, finTwoSwap]
  · simp [h, not_lt_of_gt h, finTwoSwap]

theorem matchingRotation_sameCycle_other_mate {n : ℕ} (M N : PM n)
    (i : Fin (2 * n)) : (matchingRotation M N).SameCycle (N i) (M i) := by
  have hrot : (matchingRotation M N).SameCycle (M (N i)) i := by
    exact (Equiv.Perm.SameCycle.refl (matchingRotation M N) i).apply_left
  simpa only [M.apply_apply] using
    (matchingRotation_sameCycle_mate M N (M (N i)) i).mpr hrot

@[simp] theorem matchingAlternatingBit_mate_right {n : ℕ} (M N : PM n)
    (i : Fin (2 * n)) : matchingAlternatingBit M N (N i) =
      finTwoSwap (matchingAlternatingBit M N i) := by
  have hfirst : matchingRotationCycleMin M N (N i) = matchingRotationCycleMin M N (M i) :=
    (matchingRotationCycleMin_eq_iff M N _ _).mpr (matchingRotation_sameCycle_other_mate M N i)
  have hsecond : matchingRotationCycleMin M N (M (N i)) = matchingRotationCycleMin M N i := by
    apply (matchingRotationCycleMin_eq_iff M N _ _).mpr
    exact (Equiv.Perm.SameCycle.refl (matchingRotation M N) i).apply_left
  rw [← matchingAlternatingBit_mate_left]
  unfold matchingAlternatingBit
  rw [hfirst, hsecond, M.apply_apply]

def AlternatingBitColoring {n : ℕ} (M N : PM n) :=
  {b : Fin (2 * n) → Fin 2 //
    (∀ i, b (M i) = finTwoSwap (b i)) ∧ (∀ i, b (N i) = finTwoSwap (b i))}

instance alternatingBitColoring_finite {n : ℕ} (M N : PM n) :
    Finite (AlternatingBitColoring M N) := by
  unfold AlternatingBitColoring
  infer_instance

instance alternatingBitColoring_fintype {n : ℕ} (M N : PM n) :
    Fintype (AlternatingBitColoring M N) := Fintype.ofFinite _

def standardAlternatingBitColoring {n : ℕ} (M N : PM n) : AlternatingBitColoring M N :=
  ⟨matchingAlternatingBit M N,
    ⟨matchingAlternatingBit_mate_left M N, matchingAlternatingBit_mate_right M N⟩⟩

theorem finTwoSwap_add_right (a b : Fin 2) :
    a + finTwoSwap b = finTwoSwap (a + b) := by
  fin_cases a <;> fin_cases b <;> decide

theorem finTwoSwap_add_finTwoSwap (a b : Fin 2) :
    finTwoSwap a + finTwoSwap b = a + b := by
  fin_cases a <;> fin_cases b <;> decide

theorem finTwo_add_cancel (a b : Fin 2) : (a + b) + b = a := by
  fin_cases a <;> fin_cases b <;> decide

/-- Every alternating binary coloring differs from the chosen one by one constant bit per component. -/
def alternatingBitColoringEquiv {n : ℕ} (M N : PM n) :
    CompatibleMatchingColoring M N (Fin 2) ≃ AlternatingBitColoring M N where
  toFun c := ⟨fun i => c.val i + matchingAlternatingBit M N i,
    ⟨fun i => by
      change c.val (M i) + matchingAlternatingBit M N (M i) =
        finTwoSwap (c.val i + matchingAlternatingBit M N i)
      rw [c.property.1 i, matchingAlternatingBit_mate_left, finTwoSwap_add_right],
     fun i => by
      change c.val (N i) + matchingAlternatingBit M N (N i) =
        finTwoSwap (c.val i + matchingAlternatingBit M N i)
      rw [c.property.2 i, matchingAlternatingBit_mate_right, finTwoSwap_add_right]⟩⟩
  invFun b := ⟨fun i => b.val i + matchingAlternatingBit M N i,
    ⟨fun i => by
      change b.val (M i) + matchingAlternatingBit M N (M i) =
        b.val i + matchingAlternatingBit M N i
      rw [b.property.1 i, matchingAlternatingBit_mate_left, finTwoSwap_add_finTwoSwap],
     fun i => by
      change b.val (N i) + matchingAlternatingBit M N (N i) =
        b.val i + matchingAlternatingBit M N i
      rw [b.property.2 i, matchingAlternatingBit_mate_right, finTwoSwap_add_finTwoSwap]⟩⟩
  left_inv c := by
    apply Subtype.ext
    funext i
    exact finTwo_add_cancel _ _
  right_inv b := by
    apply Subtype.ext
    funext i
    exact finTwo_add_cancel _ _

theorem card_alternatingBitColoring {n : ℕ} (M N : PM n) :
    Fintype.card (AlternatingBitColoring M N) = 2 ^ matchingKappa M N := by
  rw [← Fintype.card_congr (alternatingBitColoringEquiv M N), card_compatibleMatchingColoring]

end MatsumotoPaper
