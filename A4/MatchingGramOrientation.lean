import A4.MatchingGramSymplectic
import A4.MatchingGramPermutation

/-!
# Orienting a perfect matching by an alternating bit

The ordered-pair permutation sign is converted into the literal product of
the symplectic edge signs.  All permutations and pair orderings use the
exact definitions of the A4 matching operator.
-/

open scoped BigOperators

noncomputable section

namespace MatsumotoPaper

private abbrev PM (n : ℕ) := A4Standalone.GramHafnian.PerfectMatching n

def matchingBitTensor {n : ℕ} (M : PM n) (b : Fin (2 * n) → Fin 2) : ℝ :=
  ∏ i ∈ M.pairReps, if b i = 0 then 1 else -1

def matchingBitFlip {n : ℕ} (M : PM n) (b : Fin (2 * n) → Fin 2)
    (i : Fin n) : Equiv.Perm (Fin 2) :=
  if b (matchingPairOrder M i) = 0 then 1 else finTwoSwap

def orientedMatchingEquiv {n : ℕ} (M : PM n) (b : Fin (2 * n) → Fin 2) :
    Fin n × Fin 2 ≃ Fin (2 * n) :=
  (Equiv.prodCongrRight (matchingBitFlip M b)).trans (indexedMatchingEquiv M)

@[simp] theorem orientedMatchingEquiv_zero {n : ℕ} (M : PM n)
    (b : Fin (2 * n) → Fin 2) (i : Fin n) :
    orientedMatchingEquiv M b (i, 0) =
      if b (matchingPairOrder M i) = 0 then matchingPairOrder M i
      else M (matchingPairOrder M i) := by
  classical
  unfold orientedMatchingEquiv matchingBitFlip
  by_cases hi : b (matchingPairOrder M i) = 0
  · simp only [hi, if_pos, Equiv.trans_apply, Equiv.prodCongrRight_apply,
      Equiv.Perm.one_apply]
    exact indexedMatchingVertex_zero M i
  · simp only [hi, Equiv.trans_apply, Equiv.prodCongrRight_apply]
    change indexedMatchingVertex M (i, 1) = _
    exact indexedMatchingVertex_one M i

@[simp] theorem orientedMatchingEquiv_one {n : ℕ} (M : PM n)
    (b : Fin (2 * n) → Fin 2) (i : Fin n) :
    orientedMatchingEquiv M b (i, 1) =
      if b (matchingPairOrder M i) = 0 then M (matchingPairOrder M i)
      else matchingPairOrder M i := by
  classical
  unfold orientedMatchingEquiv matchingBitFlip
  by_cases hi : b (matchingPairOrder M i) = 0
  · simp only [hi, if_pos, Equiv.trans_apply, Equiv.prodCongrRight_apply,
      Equiv.Perm.one_apply]
    exact indexedMatchingVertex_one M i
  · simp only [hi, Equiv.trans_apply, Equiv.prodCongrRight_apply]
    change indexedMatchingVertex M (i, 0) = _
    exact indexedMatchingVertex_zero M i

theorem orientedMatchingEquiv_mate_zero {n : ℕ} (M : PM n)
    (b : Fin (2 * n) → Fin 2) (i : Fin n) :
    M (orientedMatchingEquiv M b (i, 0)) = orientedMatchingEquiv M b (i, 1) := by
  rw [orientedMatchingEquiv_zero, orientedMatchingEquiv_one]
  split_ifs <;> simp only [M.apply_apply]

theorem orientedMatchingEquiv_mate_one {n : ℕ} (M : PM n)
    (b : Fin (2 * n) → Fin 2) (i : Fin n) :
    M (orientedMatchingEquiv M b (i, 1)) = orientedMatchingEquiv M b (i, 0) := by
  rw [← orientedMatchingEquiv_mate_zero, M.apply_apply]

theorem orientedMatchingEquiv_color {n : ℕ} (M : PM n)
    (b : Fin (2 * n) → Fin 2) (hb : ∀ i, b (M i) = finTwoSwap (b i))
    (p : Fin n × Fin 2) : b (orientedMatchingEquiv M b p) = p.2 := by
  classical
  obtain ⟨i, c⟩ := p
  have hmate := hb (matchingPairOrder M i)
  have hbit : b (matchingPairOrder M i) = 0 ∨ b (matchingPairOrder M i) = 1 := by
    have hi := (b (matchingPairOrder M i)).isLt
    by_cases hz : (b (matchingPairOrder M i)).val = 0
    · exact Or.inl (Fin.ext hz)
    · right
      apply Fin.ext
      change (b (matchingPairOrder M i)).val = 1
      omega
  fin_cases c <;> rcases hbit with h | h
  · simp [orientedMatchingEquiv_zero, h]
  · simp [orientedMatchingEquiv_zero, h, hmate, finTwoSwap]
  · simp [orientedMatchingEquiv_one, h, hmate, finTwoSwap]
  · simp [orientedMatchingEquiv_one, h]

def MatchingZeroSide {n : ℕ} (b : Fin (2 * n) → Fin 2) :=
  {i : Fin (2 * n) // b i = 0}

instance matchingZeroSide_fintype {n : ℕ} (b : Fin (2 * n) → Fin 2) :
    Fintype (MatchingZeroSide b) := by
  classical
  unfold MatchingZeroSide
  infer_instance

def orientedMatchingZeroEquiv {n : ℕ} (M : PM n)
    (b : Fin (2 * n) → Fin 2) (hb : ∀ i, b (M i) = finTwoSwap (b i)) :
    Fin n ≃ MatchingZeroSide b :=
  Equiv.ofBijective
    (fun i => ⟨orientedMatchingEquiv M b (i, 0), orientedMatchingEquiv_color M b hb (i, 0)⟩)
    ⟨by
      intro i j h
      exact congrArg Prod.fst ((orientedMatchingEquiv M b).injective
        (congrArg Subtype.val h)),
      by
        intro v
        obtain ⟨⟨i, c⟩, hc⟩ := (orientedMatchingEquiv M b).surjective v.val
        have hc0 : c = 0 := by
          have hcolor := orientedMatchingEquiv_color M b hb (i, c)
          rw [hc, v.property] at hcolor
          exact hcolor.symm
        subst c
        exact ⟨i, Subtype.ext hc⟩⟩

def orientedMatchingPermutation {n : ℕ} (M : PM n)
    (b : Fin (2 * n) → Fin 2) : Equiv.Perm (Fin (2 * n)) :=
  (matchingSlotEquiv n).symm.trans (orientedMatchingEquiv M b)

theorem orientedMatchingPermutation_sign {n : ℕ} (M : PM n)
    (b : Fin (2 * n) → Fin 2) :
    Equiv.Perm.sign (orientedMatchingPermutation M b) =
      (∏ i : Fin n, if b (matchingPairOrder M i) = 0 then (1 : ℤˣ) else -1) *
        Equiv.Perm.sign (canonicalMatchingPermutation M) := by
  classical
  unfold orientedMatchingPermutation orientedMatchingEquiv
  rw [Equiv.Perm.sign_trans_trans, Equiv.Perm.sign_prodCongrRight]
  congr 1
  apply Fintype.prod_congr
  intro i
  unfold matchingBitFlip
  split_ifs
  · simp only [map_one]
  · exact Equiv.Perm.sign_swap (by decide : (0 : Fin 2) ≠ 1)

def realUnitSign : ℤˣ →* ℝ :=
  (Int.castRingHom ℝ).toMonoidHom.comp (Units.coeHom ℤ)

theorem realUnitSign_one : realUnitSign 1 = 1 := map_one _

theorem realUnitSign_neg_one : realUnitSign (-1) = -1 := by
  change ((-1 : ℤ) : ℝ) = -1
  norm_num

theorem orientedMatchingPermutation_real_sign {n : ℕ} (M : PM n)
    (b : Fin (2 * n) → Fin 2) :
    realUnitSign (Equiv.Perm.sign (orientedMatchingPermutation M b)) =
      matchingBitTensor M b * matchingOrientation M := by
  classical
  rw [orientedMatchingPermutation_sign, map_mul, map_prod]
  have hprod : (∏ i : Fin n,
      realUnitSign (if b (matchingPairOrder M i) = 0 then (1 : ℤˣ) else -1)) =
      matchingBitTensor M b := by
    unfold matchingBitTensor
    calc
      _ = ∏ i : Fin n, if b (matchingPairOrder M i) = 0 then (1 : ℝ) else -1 := by
        apply Fintype.prod_congr
        intro i
        split_ifs <;> simp only [realUnitSign_one, realUnitSign_neg_one]
      _ = ∏ i : M.pairReps, if b i = 0 then (1 : ℝ) else -1 :=
        by
          change (∏ i : Fin n, if b
            ((M.pairReps.orderIsoOfFin M.card_pairReps).toEquiv i).val = 0
              then (1 : ℝ) else -1) = _
          exact (M.pairReps.orderIsoOfFin M.card_pairReps).toEquiv.prod_comp
            (fun i => if b i.val = 0 then (1 : ℝ) else -1)
      _ = _ := Finset.prod_coe_sort M.pairReps (fun i => if b i = 0 then (1 : ℝ) else -1)
  rw [hprod]
  rfl

end MatsumotoPaper
