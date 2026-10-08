import A4.MatchingGramBinary

/-!
# Permutation sign and the number of whole cycles

The cycle count here includes fixed points.  The exact sign identity is
proved through mathlib's disjoint cycle factors, with no parity assumption.
-/

open scoped BigOperators

noncomputable section

namespace MatsumotoPaper

def PermutationCycle {α : Type*} (σ : Equiv.Perm α) :=
  Quotient (Equiv.Perm.SameCycle.setoid σ)

instance permutationCycle_finite {α : Type*} [Finite α] (σ : Equiv.Perm α) :
    Finite (PermutationCycle σ) := by
  unfold PermutationCycle
  infer_instance

instance permutationCycle_fintype {α : Type*} [Finite α] (σ : Equiv.Perm α) :
    Fintype (PermutationCycle σ) := Fintype.ofFinite _

def permutationCycleLabel {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (i : α) :
    σ.cycleFactorsFinset ⊕ Function.fixedPoints σ :=
  if hi : σ i = i then Sum.inr ⟨i, hi⟩ else
    Sum.inl ⟨σ.cycleOf i, Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr
      (Equiv.Perm.mem_support.mpr hi)⟩

theorem permutationCycleLabel_eq_iff {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (i j : α) :
    permutationCycleLabel σ i = permutationCycleLabel σ j ↔ σ.SameCycle i j := by
  classical
  unfold permutationCycleLabel
  by_cases hi : σ i = i <;> by_cases hj : σ j = j
  · simp only [dif_pos hi, dif_pos hj, Sum.inr.injEq]
    exact ⟨fun h => (Subtype.mk.inj h) ▸ Equiv.Perm.SameCycle.refl σ i,
      fun h => Subtype.ext (h.eq_of_left hi)⟩
  · simp only [dif_pos hi, dif_neg hj, Sum.inr_ne_inl, false_iff]
    exact fun h => hj ((h.apply_eq_self_iff).mp hi)
  · simp only [dif_neg hi, dif_pos hj, Sum.inl_ne_inr, false_iff]
    exact fun h => hi ((h.apply_eq_self_iff).mpr hj)
  · simp only [dif_neg hi, dif_neg hj, Sum.inl.injEq, Subtype.mk.injEq]
    exact (Equiv.Perm.sameCycle_iff_cycleOf_eq_of_mem_support
      (Equiv.Perm.mem_support.mpr hi) (Equiv.Perm.mem_support.mpr hj)).symm

theorem permutationCycleLabel_surjective {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) : Function.Surjective (permutationCycleLabel σ) := by
  classical
  rintro (p | i)
  · have hp := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp p.property).1
    obtain ⟨i, hpiMove, _⟩ := hp
    have hi : i ∈ p.val.support := Equiv.Perm.mem_support.mpr hpiMove
    have hσi : σ i ≠ i := Equiv.Perm.mem_support.mp
      (Equiv.Perm.mem_cycleFactorsFinset_support_le p.property hi)
    have hpi : σ.cycleOf i = p.val := by
      by_contra hne
      have hc := Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr
        (Equiv.Perm.mem_support.mpr hσi)
      have hd := σ.cycleFactorsFinset_pairwise_disjoint hc p.property hne
      have hmove := Equiv.Perm.mem_support.mp hi
      have hcMove : σ.cycleOf i i ≠ i := by
        rw [Equiv.Perm.cycleOf_apply_self]
        exact hσi
      exact (hd i).elim hcMove hmove
    refine ⟨i, ?_⟩
    simp only [permutationCycleLabel, dif_neg hσi, Sum.inl.injEq]
    exact Subtype.ext hpi
  · refine ⟨i.val, ?_⟩
    have hi : σ i.val = i.val := i.property
    simp only [permutationCycleLabel, dif_pos hi]

def permutationCycleEquivLabel {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) :
    PermutationCycle σ ≃ (σ.cycleFactorsFinset ⊕ Function.fixedPoints σ) :=
  Equiv.ofBijective
    (Quotient.lift (permutationCycleLabel σ)
      (fun i j h => (permutationCycleLabel_eq_iff σ i j).mpr h))
    ⟨by
      intro a b hab
      induction a using Quotient.inductionOn with
      | h i =>
        induction b using Quotient.inductionOn with
        | h j =>
          exact Quotient.sound ((permutationCycleLabel_eq_iff σ i j).mp hab),
      by
        intro c
        obtain ⟨i, rfl⟩ := permutationCycleLabel_surjective σ c
        exact ⟨Quotient.mk _ i, rfl⟩⟩

theorem card_permutationCycle {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) :
    Fintype.card (PermutationCycle σ) =
      σ.cycleType.card + Fintype.card (Function.fixedPoints σ) := by
  classical
  rw [Fintype.card_congr (permutationCycleEquivLabel σ), Fintype.card_sum]
  simp only [Fintype.card_coe, Equiv.Perm.cycleType_def, Multiset.card_map]
  rfl

theorem sign_eq_pow_card_add_cycles {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) :
    Equiv.Perm.sign σ =
      (-1 : ℤˣ) ^ (Fintype.card α + Fintype.card (PermutationCycle σ)) := by
  classical
  rw [card_permutationCycle, Equiv.Perm.card_fixedPoints]
  have hcard : Fintype.card α =
      σ.cycleType.sum + (Fintype.card α - σ.cycleType.sum) := by
    exact (Nat.add_sub_of_le (Equiv.Perm.sum_cycleType_le σ)).symm
  have hexp : Fintype.card α +
      (σ.cycleType.card + (Fintype.card α - σ.cycleType.sum)) =
      (σ.cycleType.sum + σ.cycleType.card) +
        2 * (Fintype.card α - σ.cycleType.sum) := by omega
  rw [hexp, pow_add, pow_mul, show (-1 : ℤˣ) ^ 2 = 1 by decide, one_pow, mul_one]
  exact Equiv.Perm.sign_of_cycleType σ

end MatsumotoPaper
