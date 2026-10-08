import A4.MatchingGramOrientationProduct
import A4.MatchingGramColorRank

/-!
# Exact contractions of the surjective symplectic color layers

For each rank, nonzero rows are exactly a surjective component-color map
and an alternating binary coloring.  Their orientation product is already
proved in every degree.
-/

open scoped BigOperators Matrix

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MatsumotoPaper

private abbrev PM (n : ℕ) := A4Standalone.GramHafnian.PerfectMatching n

theorem finTwo_ne_iff_flip (a b : Fin 2) : a ≠ b ↔ b = finTwoSwap a := by
  fin_cases a <;> fin_cases b <;> decide

theorem matchingSymplecticTensor_nonzero_bit {n r : ℕ} (M : PM n)
    (a : Fin (2 * n) → Fin r × Fin 2)
    (ha : matchingSymplecticTensor M a ≠ 0) (i : Fin (2 * n)) :
    (a (M i)).2 = finTwoSwap (a i).2 := by
  classical
  have hp : ∀ j ∈ M.pairReps, (a j).2 ≠ (a (M j)).2 := by
    intro j hj
    have hf := (Finset.prod_ne_zero_iff.mp ha) j hj
    by_contra h
    simp only [h, ne_self_iff_false, and_false, if_false] at hf
  apply (finTwo_ne_iff_flip _ _).mp
  rcases (M.exactly_one_mem_pairReps i).1 with hi | hi
  · exact hp i hi
  · simpa only [M.apply_apply, ne_comm] using hp (M i) hi

theorem matchingSymplecticTensor_eq_bitTensor {n r : ℕ} (M : PM n)
    (a : Fin (2 * n) → Fin r × Fin 2)
    (hc : ∀ i, (a (M i)).1 = (a i).1)
    (hb : ∀ i, (a (M i)).2 = finTwoSwap (a i).2) :
    matchingSymplecticTensor M a = matchingBitTensor M (fun i => (a i).2) := by
  classical
  unfold matchingSymplecticTensor matchingBitTensor
  apply Finset.prod_congr rfl
  intro i hi
  have hd : (a i).2 ≠ (a (M i)).2 := (finTwo_ne_iff_flip _ _).mpr (hb i)
  have hc' := (hc i).symm
  rw [if_pos ⟨hc', hd⟩]

def SymplecticCommonCompatibility {n r : ℕ} (M N : PM n)
    (a : Fin (2 * n) → Fin r × Fin 2) : Prop :=
  ((∀ i, (a (M i)).1 = (a i).1) ∧ (∀ i, (a (N i)).1 = (a i).1)) ∧
    ((∀ i, (a (M i)).2 = finTwoSwap (a i).2) ∧
      (∀ i, (a (N i)).2 = finTwoSwap (a i).2))

instance symplecticCommonCompatibility_decidable {n r : ℕ} (M N : PM n)
    (a : Fin (2 * n) → Fin r × Fin 2) : Decidable (SymplecticCommonCompatibility M N a) :=
  Classical.propDecidable _

theorem matchingSymplecticTensor_product {n r : ℕ} (M N : PM n)
    (a : Fin (2 * n) → Fin r × Fin 2) :
    matchingSymplecticTensor M a * matchingSymplecticTensor N a =
      if SymplecticCommonCompatibility M N a then
        matchingOrientation M * matchingOrientation N * (-1 : ℝ) ^ (n + matchingKappa M N)
      else 0 := by
  classical
  by_cases h : SymplecticCommonCompatibility M N a
  · rw [if_pos h, matchingSymplecticTensor_eq_bitTensor M a h.1.1 h.2.1,
      matchingSymplecticTensor_eq_bitTensor N a h.1.2 h.2.2]
    exact matchingBitTensor_product M N ⟨fun i => (a i).2, h.2⟩
  · rw [if_neg h]
    by_contra hp
    obtain ⟨hM, hN⟩ := mul_ne_zero_iff.mp hp
    apply h
    exact ⟨⟨matchingSymplecticTensor_nonzero_color M a hM,
        matchingSymplecticTensor_nonzero_color N a hN⟩,
      ⟨matchingSymplecticTensor_nonzero_bit M a hM,
        matchingSymplecticTensor_nonzero_bit N a hN⟩⟩

def CommonSymplecticColoring {n : ℕ} (M N : PM n) (r : ℕ) :=
  {a : SymplecticColoring n r // SymplecticCommonCompatibility M N a.val}

instance commonSymplecticColoring_finite {n : ℕ} (M N : PM n) (r : ℕ) :
    Finite (CommonSymplecticColoring M N r) := by
  unfold CommonSymplecticColoring
  infer_instance

instance commonSymplecticColoring_fintype {n : ℕ} (M N : PM n) (r : ℕ) :
    Fintype (CommonSymplecticColoring M N r) := by
  classical
  unfold CommonSymplecticColoring
  infer_instance

def componentBitToCommonSymplecticColoring {n r : ℕ} (M N : PM n)
    (p : SurjectiveFiniteMap (MatchingComponent M N) (Fin r) × AlternatingBitColoring M N) :
    CommonSymplecticColoring M N r :=
  ⟨⟨fun i => (p.1.val (vertexMatchingComponent M N i), p.2.val i),
    p.1.property.comp (vertexMatchingComponent_surjective M N)⟩,
    ⟨⟨fun i => congrArg p.1.val (vertexMatchingComponent_mate_left M N i),
      fun i => congrArg p.1.val (vertexMatchingComponent_mate_right M N i)⟩,
      p.2.property⟩⟩

def commonSymplecticVertexColoring {n r : ℕ} (M N : PM n)
    (a : CommonSymplecticColoring M N r) : CompatibleMatchingColoring M N (Fin r) :=
  ⟨fun i => (a.val.val i).1, a.property.1⟩

theorem commonSymplectic_representative_color {n r : ℕ} (M N : PM n)
    (a : CommonSymplecticColoring M N r) (i : Fin (2 * n)) :
    (a.val.val (matchingComponentRepresentative M N (vertexMatchingComponent M N i))).1 =
      (a.val.val i).1 :=
  compatibleMatchingColoring_eq_of_component M N (commonSymplecticVertexColoring M N a)
    (vertexMatchingComponent_representative M N _)

theorem componentBitToCommonSymplecticColoring_bijective {n r : ℕ} (M N : PM n) :
    Function.Bijective (componentBitToCommonSymplecticColoring (r := r) M N) := by
  classical
  constructor
  · intro p q h
    have hv := congrArg (fun a : CommonSymplecticColoring M N r => a.val.val) h
    apply Prod.ext
    · apply Subtype.ext
      funext C
      obtain ⟨i, hi⟩ := vertexMatchingComponent_surjective M N C
      have hrow := congrFun hv i
      change (p.1.val (vertexMatchingComponent M N i), p.2.val i) =
        (q.1.val (vertexMatchingComponent M N i), q.2.val i) at hrow
      have hc := congrArg Prod.fst hrow
      simpa only [hi] using hc
    · apply Subtype.ext
      funext i
      exact congrArg Prod.snd (congrFun hv i)
  · intro a
    let f : MatchingComponent M N → Fin r :=
      fun C => (a.val.val (matchingComponentRepresentative M N C)).1
    have hf : Function.Surjective f := by
      intro c
      obtain ⟨i, hi⟩ := a.val.property c
      refine ⟨vertexMatchingComponent M N i, ?_⟩
      exact (commonSymplectic_representative_color M N a i).trans hi
    let b : AlternatingBitColoring M N := ⟨fun i => (a.val.val i).2, a.property.2⟩
    refine ⟨(⟨f, hf⟩, b), ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    funext i
    exact Prod.ext (commonSymplectic_representative_color M N a i) rfl

def commonSymplecticColoringEquiv {n r : ℕ} (M N : PM n) :
    (SurjectiveFiniteMap (MatchingComponent M N) (Fin r) × AlternatingBitColoring M N) ≃
      CommonSymplecticColoring M N r :=
  Equiv.ofBijective (componentBitToCommonSymplecticColoring M N)
    (componentBitToCommonSymplecticColoring_bijective M N)

theorem card_commonSymplecticColoring {n r : ℕ} (M N : PM n) :
    Fintype.card (CommonSymplecticColoring M N r) =
      Fintype.card (SurjectiveFiniteMap (MatchingComponent M N) (Fin r)) *
        2 ^ matchingKappa M N := by
  rw [← Fintype.card_congr (commonSymplecticColoringEquiv M N), Fintype.card_prod,
    card_alternatingBitColoring]

theorem matchingSymplecticFeature_gram_entry {n r : ℕ} (M N : PM n) :
    ((matchingSymplecticFeature n r)ᴴ * matchingSymplecticFeature n r) M N =
      (matchingOrientation M * matchingOrientation N * (-1 : ℝ) ^ (n + matchingKappa M N)) *
        (2 : ℝ) ^ matchingKappa M N *
          (Fintype.card (SurjectiveFiniteMap (MatchingComponent M N) (Fin r)) : ℝ) := by
  classical
  have hcard : (Finset.univ.filter (fun a : SymplecticColoring n r =>
      SymplecticCommonCompatibility M N a.val)).card =
      Fintype.card (CommonSymplecticColoring M N r) := by
    unfold CommonSymplecticColoring
    exact (Fintype.card_of_subtype _ (fun a => by simp only [Finset.mem_filter,
      Finset.mem_univ, true_and])).symm
  calc
    _ = ∑ a : SymplecticColoring n r,
        matchingSymplecticTensor M a.val * matchingSymplecticTensor N a.val := by
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial,
        matchingSymplecticFeature]
    _ = ∑ a : SymplecticColoring n r,
        if SymplecticCommonCompatibility M N a.val then
          matchingOrientation M * matchingOrientation N * (-1 : ℝ) ^ (n + matchingKappa M N)
        else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      exact matchingSymplecticTensor_product M N a.val
    _ = (Fintype.card (CommonSymplecticColoring M N r) : ℝ) *
        (matchingOrientation M * matchingOrientation N * (-1 : ℝ) ^ (n + matchingKappa M N)) := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hcard]
    _ = _ := by
      rw [card_commonSymplecticColoring]
      push_cast
      ring

end MatsumotoPaper
