import A4.MatchingGramCanonical

/-!
# Pair products under an arbitrary permutation

A symmetric pair weight has exactly the same product whether its pairs are
listed in the source slots of an arbitrary permutation or by the smaller
endpoints of the transported involution.  No canonicality is required of
the permutation.
-/

open scoped BigOperators

noncomputable section

namespace MatsumotoPaper

private abbrev PM (n : ℕ) := A4Standalone.GramHafnian.PerfectMatching n

def transportedPairRepresentative {n : ℕ} (g : Equiv.Perm (Fin (2 * n)))
    (i : Fin n) : (transportedPairPartition g).pairReps :=
  ⟨matchingPairRep (transportedPairPartition g) (g (leftSlot i)),
    matchingPairRep_mem _ _⟩

theorem transportedPairRepresentative_injective {n : ℕ}
    (g : Equiv.Perm (Fin (2 * n))) :
    Function.Injective (transportedPairRepresentative g) := by
  intro i j hij
  have h := congrArg Subtype.val hij
  rcases (matchingPairRep_eq_iff _ _ _).mp h with h | h
  · have hs := congrArg Fin.val (g.injective h)
    apply Fin.ext
    simp only [leftSlot] at hs
    omega
  · rw [transportedPairPartition_left] at h
    have hs := congrArg Fin.val (g.injective h)
    simp only [leftSlot, rightSlot] at hs
    omega

def transportedPairRepresentativeEquiv {n : ℕ}
    (g : Equiv.Perm (Fin (2 * n))) :
    Fin n ≃ (transportedPairPartition g).pairReps :=
  Equiv.ofBijective (transportedPairRepresentative g)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨transportedPairRepresentative_injective g, by
        rw [Fintype.card_fin, Fintype.card_coe, (transportedPairPartition g).card_pairReps]⟩)

theorem symmetric_pairWeight_representative {n : ℕ} {R : Type*}
    (M : PM n) (F : Fin (2 * n) → Fin (2 * n) → R)
    (hF : ∀ i j, F i j = F j i) (i : Fin (2 * n)) :
    F (matchingPairRep M i) (M (matchingPairRep M i)) = F i (M i) := by
  rcases matchingPairRep_eq_or M i with h | h
  · rw [h]
  · rw [h, M.apply_apply, hF]

theorem prod_symmetric_pairWeight_transport {n : ℕ} {R : Type*} [CommMonoid R]
    (g : Equiv.Perm (Fin (2 * n)))
    (F : Fin (2 * n) → Fin (2 * n) → R)
    (hF : ∀ i j, F i j = F j i) :
    (∏ i : Fin n, F (g (leftSlot i)) (g (rightSlot i))) =
      ∏ i : (transportedPairPartition g).pairReps, F i (transportedPairPartition g i) := by
  classical
  calc
    _ = ∏ i : Fin n,
        F (transportedPairRepresentativeEquiv g i)
          (transportedPairPartition g (transportedPairRepresentativeEquiv g i)) := by
      apply Fintype.prod_congr
      intro i
      change F (g (leftSlot i)) (g (rightSlot i)) =
        F (matchingPairRep (transportedPairPartition g) (g (leftSlot i)))
          (transportedPairPartition g
            (matchingPairRep (transportedPairPartition g) (g (leftSlot i))))
      rw [symmetric_pairWeight_representative _ F hF, transportedPairPartition_left]
    _ = _ := (transportedPairRepresentativeEquiv g).prod_comp
      (fun i => F i (transportedPairPartition g i))

theorem prod_symmetric_pairWeight_transport_finset {n : ℕ} {R : Type*} [CommMonoid R]
    (g : Equiv.Perm (Fin (2 * n)))
    (F : Fin (2 * n) → Fin (2 * n) → R)
    (hF : ∀ i j, F i j = F j i) :
    (∏ i : Fin n, F (g (leftSlot i)) (g (rightSlot i))) =
      ∏ i ∈ (transportedPairPartition g).pairReps, F i (transportedPairPartition g i) := by
  rw [prod_symmetric_pairWeight_transport g F hF]
  exact Finset.prod_coe_sort (transportedPairPartition g).pairReps
    (fun i => F i (transportedPairPartition g i))

end MatsumotoPaper
