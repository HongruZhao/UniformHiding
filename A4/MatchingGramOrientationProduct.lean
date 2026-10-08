import A4.MatchingGramOrientation
import A4.MatchingGramRotation

/-! The exact two-matching binary orientation product. -/

open scoped BigOperators

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MatsumotoPaper

private abbrev PM (n : ℕ) := A4Standalone.GramHafnian.PerfectMatching n

instance matchingZeroSide_decidableEq {n : ℕ} (b : Fin (2 * n) → Fin 2) :
    DecidableEq (MatchingZeroSide b) := Classical.decEq _

def matchingZeroRotation {n : ℕ} (M N : PM n) (b : AlternatingBitColoring M N) :
    Equiv.Perm (MatchingZeroSide b.val) :=
  Equiv.Perm.subtypePerm (matchingRotation M N)
    (fun i => by
      change b.val (matchingRotation M N i) = 0 ↔ b.val i = 0
      rw [alternatingBit_rotation_invariant M N b i])

@[simp] theorem matchingZeroRotation_apply_val {n : ℕ} (M N : PM n)
    (b : AlternatingBitColoring M N) (i : MatchingZeroSide b.val) :
    (matchingZeroRotation M N b i).val = M (N i.val) := rfl

@[simp] theorem matchingZeroRotation_symm_apply_val {n : ℕ} (M N : PM n)
    (b : AlternatingBitColoring M N) (i : MatchingZeroSide b.val) :
    ((matchingZeroRotation M N b).symm i).val = N (M i.val) := by
  change ((matchingRotation M N)⁻¹ i.val) = N (M i.val)
  simp only [matchingRotation, mul_inv_rev, matchingMate_inv, Equiv.Perm.mul_apply]

theorem matchingZeroRotation_pow_apply_val {n : ℕ} (M N : PM n)
    (b : AlternatingBitColoring M N) (i : MatchingZeroSide b.val) (k : ℕ) :
    ((matchingZeroRotation M N b ^ k) i).val = ((matchingRotation M N ^ k) i.val) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, matchingZeroRotation_apply_val, ih]
    rw [pow_succ', Equiv.Perm.mul_apply]
    rfl

theorem matchingZeroRotation_sameCycle_iff {n : ℕ} (M N : PM n)
    (b : AlternatingBitColoring M N) (i j : MatchingZeroSide b.val) :
    (matchingZeroRotation M N b).SameCycle i j ↔
      vertexMatchingComponent M N i.val = vertexMatchingComponent M N j.val := by
  have hsc : (matchingZeroRotation M N b).SameCycle i j ↔
      (matchingRotation M N).SameCycle i.val j.val := by
    constructor
    · intro h
      obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
      have hv := congrArg Subtype.val hk
      rw [matchingZeroRotation_pow_apply_val] at hv
      exact ⟨k, by simpa only [zpow_natCast] using hv⟩
    · intro h
      obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
      have hv : (matchingZeroRotation M N b ^ k) i = j := by
        apply Subtype.ext
        rw [matchingZeroRotation_pow_apply_val]
        exact hk
      exact ⟨k, by simpa only [zpow_natCast] using hv⟩
  rw [hsc]
  constructor
  · intro h
    exact ((matching_same_rotation_cycle_iff_component_bit M N b i.val j.val).mp h).1
  · intro h
    exact (matching_same_rotation_cycle_iff_component_bit M N b i.val j.val).mpr
      ⟨h, i.property.trans j.property.symm⟩

theorem zeroSide_component_surjective {n : ℕ} (M N : PM n)
    (b : AlternatingBitColoring M N) :
    Function.Surjective (fun i : MatchingZeroSide b.val => vertexMatchingComponent M N i.val) := by
  intro C
  obtain ⟨i, hi⟩ := vertexMatchingComponent_surjective M N C
  by_cases hbi : b.val i = 0
  · exact ⟨⟨i, hbi⟩, hi⟩
  · have hbit : b.val i = 1 := by
      apply Fin.ext
      have hl := (b.val i).isLt
      have hn : (b.val i).val ≠ 0 := fun h => hbi (Fin.ext h)
      change (b.val i).val = 1
      omega
    have hbMi : b.val (M i) = 0 := by
      rw [b.property.1, hbit]
      decide
    refine ⟨⟨M i, hbMi⟩, ?_⟩
    change vertexMatchingComponent M N (M i) = C
    rw [vertexMatchingComponent_mate_left, hi]

def matchingZeroRotationCycleEquivComponent {n : ℕ} (M N : PM n)
    (b : AlternatingBitColoring M N) :
    PermutationCycle (matchingZeroRotation M N b) ≃ MatchingComponent M N :=
  Equiv.ofBijective
    (Quotient.lift (fun i : MatchingZeroSide b.val => vertexMatchingComponent M N i.val)
      (fun i j h => (matchingZeroRotation_sameCycle_iff M N b i j).mp h))
    ⟨by
      intro a c hac
      induction a using Quotient.inductionOn with
      | h i =>
        induction c using Quotient.inductionOn with
        | h j =>
          exact Quotient.sound ((matchingZeroRotation_sameCycle_iff M N b i j).mpr hac),
      by
        intro C
        obtain ⟨i, hi⟩ := zeroSide_component_surjective M N b C
        exact ⟨Quotient.mk _ i, hi⟩⟩

theorem matchingZeroRotation_sign {n : ℕ} (M N : PM n)
    (b : AlternatingBitColoring M N) :
    Equiv.Perm.sign (matchingZeroRotation M N b) = (-1 : ℤˣ) ^ (n + matchingKappa M N) := by
  classical
  rw [sign_eq_pow_card_add_cycles,
    Fintype.card_congr (matchingZeroRotationCycleEquivComponent M N b), card_matchingComponent]
  have hc : Fintype.card (MatchingZeroSide b.val) = n := by
    rw [← Fintype.card_congr (orientedMatchingZeroEquiv M b.val b.property.1), Fintype.card_fin]
  rw [hc]

@[simp] theorem orientedMatchingZeroEquiv_apply_val {n : ℕ} (M : PM n)
    (b : Fin (2 * n) → Fin 2) (hb : ∀ i, b (M i) = finTwoSwap (b i)) (i : Fin n) :
    (orientedMatchingZeroEquiv M b hb i).val = orientedMatchingEquiv M b (i, 0) := rfl

@[simp] theorem orientedMatchingZeroEquiv_symm_zero {n : ℕ} (M : PM n)
    (b : Fin (2 * n) → Fin 2) (hb : ∀ i, b (M i) = finTwoSwap (b i))
    (v : MatchingZeroSide b) :
    orientedMatchingEquiv M b ((orientedMatchingZeroEquiv M b hb).symm v, 0) = v.val :=
  congrArg Subtype.val ((orientedMatchingZeroEquiv M b hb).apply_symm_apply v)

def orientedMatchingSideZeroChange {n : ℕ} (M N : PM n) (b : AlternatingBitColoring M N) :
    Equiv.Perm (Fin n) :=
  (orientedMatchingZeroEquiv M b.val b.property.1).trans
    (orientedMatchingZeroEquiv N b.val b.property.2).symm

def orientedMatchingSideOneChange {n : ℕ} (M N : PM n) (b : AlternatingBitColoring M N) :
    Equiv.Perm (Fin n) :=
  (orientedMatchingZeroEquiv M b.val b.property.1).trans
    ((matchingZeroRotation M N b).symm.trans
      (orientedMatchingZeroEquiv N b.val b.property.2).symm)

theorem orientedMatchingChange_eq_prodCongrLeft {n : ℕ} (M N : PM n)
    (b : AlternatingBitColoring M N) :
    (orientedMatchingEquiv M b.val).trans (orientedMatchingEquiv N b.val).symm =
      Equiv.prodCongrLeft (fun c : Fin 2 => if c = 0 then
        orientedMatchingSideZeroChange M N b else orientedMatchingSideOneChange M N b) := by
  classical
  apply Equiv.ext
  rintro ⟨i, c⟩
  apply (orientedMatchingEquiv N b.val).injective
  rw [Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.prodCongrLeft_apply]
  fin_cases c
  · change orientedMatchingEquiv M b.val (i, 0) =
      orientedMatchingEquiv N b.val (orientedMatchingSideZeroChange M N b i, 0)
    simp only [orientedMatchingSideZeroChange, Equiv.trans_apply]
    rw [orientedMatchingZeroEquiv_symm_zero, orientedMatchingZeroEquiv_apply_val]
  · change orientedMatchingEquiv M b.val (i, 1) =
      orientedMatchingEquiv N b.val (orientedMatchingSideOneChange M N b i, 1)
    simp only [orientedMatchingSideOneChange, Equiv.trans_apply]
    rw [← orientedMatchingEquiv_mate_zero N, orientedMatchingZeroEquiv_symm_zero,
      matchingZeroRotation_symm_apply_val, N.apply_apply,
      orientedMatchingZeroEquiv_apply_val, orientedMatchingEquiv_mate_zero M]

theorem orientedMatching_sign_product_eq_rotation {n : ℕ} (M N : PM n)
    (b : AlternatingBitColoring M N) :
    Equiv.Perm.sign (orientedMatchingPermutation M b.val) *
      Equiv.Perm.sign (orientedMatchingPermutation N b.val) =
        Equiv.Perm.sign (matchingZeroRotation M N b) := by
  classical
  have hconj : Equiv.Perm.sign
      ((orientedMatchingEquiv M b.val).trans (orientedMatchingEquiv N b.val).symm) =
      Equiv.Perm.sign (orientedMatchingPermutation M b.val) *
        Equiv.Perm.sign (orientedMatchingPermutation N b.val) := by
    have he : (orientedMatchingEquiv M b.val).trans (orientedMatchingEquiv N b.val).symm =
        (matchingSlotEquiv n).symm.permCongr
          ((orientedMatchingPermutation N b.val)⁻¹ * orientedMatchingPermutation M b.val) := by
      apply Equiv.ext
      intro p
      simp [orientedMatchingPermutation, Equiv.permCongr_apply]
    rw [he, Equiv.Perm.sign_permCongr, map_mul, map_inv]
    rw [Int.units_inv_eq_self, mul_comm]
  rw [← hconj, orientedMatchingChange_eq_prodCongrLeft,
    Equiv.Perm.sign_prodCongrLeft, Fin.prod_univ_two]
  simp only [ite_true, show (1 : Fin 2) ≠ 0 by decide, if_false]
  have hone : Equiv.Perm.sign (orientedMatchingSideOneChange M N b) =
      Equiv.Perm.sign (matchingZeroRotation M N b) *
        Equiv.Perm.sign (orientedMatchingSideZeroChange M N b) := by
    unfold orientedMatchingSideOneChange
    rw [Equiv.Perm.sign_trans_trans]
    change Equiv.Perm.sign (matchingZeroRotation M N b)⁻¹ * _ = _
    rw [Equiv.Perm.sign_inv]
    rfl
  rw [hone, mul_left_comm, Int.units_mul_self, mul_one]

theorem matchingOrientation_mul_self {n : ℕ} (M : PM n) :
    matchingOrientation M * matchingOrientation M = 1 := by
  change realUnitSign (Equiv.Perm.sign (canonicalMatchingPermutation M)) *
    realUnitSign (Equiv.Perm.sign (canonicalMatchingPermutation M)) = 1
  rw [← map_mul, Int.units_mul_self, map_one]

theorem matchingBitTensor_product {n : ℕ} (M N : PM n)
    (b : AlternatingBitColoring M N) :
    matchingBitTensor M b.val * matchingBitTensor N b.val =
      matchingOrientation M * matchingOrientation N * (-1 : ℝ) ^ (n + matchingKappa M N) := by
  have hsign := congrArg realUnitSign (orientedMatching_sign_product_eq_rotation M N b)
  rw [map_mul, orientedMatchingPermutation_real_sign, orientedMatchingPermutation_real_sign,
    matchingZeroRotation_sign, map_pow, realUnitSign_neg_one] at hsign
  have hM := matchingOrientation_mul_self M
  have hN := matchingOrientation_mul_self N
  calc
    _ = matchingBitTensor M b.val * matchingBitTensor N b.val *
        (matchingOrientation M * matchingOrientation M) *
          (matchingOrientation N * matchingOrientation N) := by rw [hM, hN]; ring
    _ = (matchingBitTensor M b.val * matchingOrientation M *
        (matchingBitTensor N b.val * matchingOrientation N)) *
          (matchingOrientation M * matchingOrientation N) := by ring
    _ = _ := by rw [hsign]; ring

end MatsumotoPaper
