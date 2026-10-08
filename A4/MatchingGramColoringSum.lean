import A4.MatchingGramColoring
import A4.DirectMomentsWickRegrouping

/-! The exact loop factor for a Wick target matching in a source pair-color sum. -/

open scoped BigOperators Matrix

noncomputable section

namespace MatsumotoPaper

private abbrev PM (n : ℕ) := A4Standalone.GramHafnian.PerfectMatching n
open A4Standalone.GramHafnian

theorem matching_pairReps_color_iff {n k : ℕ} (N : PM n)
    (c : Fin (2 * n) → Fin k) :
    (∀ i : N.pairReps, c i.val = c (N i.val)) ↔ ∀ i, c (N i) = c i := by
  constructor
  · intro h i
    rcases (N.exactly_one_mem_pairReps i).1 with hi | hi
    · exact (h ⟨i, hi⟩).symm
    · simpa only [N.apply_apply] using h ⟨N i, hi⟩
  · intro h i
    exact (h i.val).symm

def CompatiblePairColoring {n k : ℕ} (M N : PM n) :=
  {c : PairColoring M k // ∀ i : N.pairReps,
    vertexColoringOfPairColoring M c i.val = vertexColoringOfPairColoring M c (N i.val)}

instance compatiblePairColoring_finite {n k : ℕ} (M N : PM n) :
    Finite (CompatiblePairColoring (k := k) M N) := by
  unfold CompatiblePairColoring PairColoring
  infer_instance

instance compatiblePairColoring_fintype {n k : ℕ} (M N : PM n) :
    Fintype (CompatiblePairColoring (k := k) M N) := by
  classical
  unfold CompatiblePairColoring
  infer_instance

def compatiblePairColoringEquiv {n k : ℕ} (M N : PM n) :
    CompatiblePairColoring (k := k) M N ≃ CompatibleMatchingColoring M N (Fin k) where
  toFun c := ⟨vertexColoringOfPairColoring M c.val,
    ⟨vertexColoringOfPairColoring_compatible M c.val,
     (matching_pairReps_color_iff N _).mp c.property⟩⟩
  invFun c :=
    ⟨fun i => c.val i.val, by
      intro i
      have heq : vertexColoringOfPairColoring M (fun j => c.val j.val) = c.val :=
        congrArg Subtype.val ((pairColoringEquivCompatibleVertexColoring M k).right_inv
          ⟨c.val, c.property.1⟩)
      rw [heq]
      exact (c.property.2 i.val).symm⟩
  left_inv c := by
    apply Subtype.ext
    funext i
    exact vertexColoringOfPairColoring_apply_rep M c.val i
  right_inv c := by
    apply Subtype.ext
    change vertexColoringOfPairColoring M (fun i => c.val i.val) = c.val
    exact congrArg Subtype.val ((pairColoringEquivCompatibleVertexColoring M k).right_inv
      ⟨c.val, c.property.1⟩)

theorem sum_pairColoring_compatible_eq_loop_power {n : ℕ} (M N : PM n) (k : ℕ) :
    (∑ c : PairColoring M k,
      if ∀ i : N.pairReps,
        vertexColoringOfPairColoring M c i.val = vertexColoringOfPairColoring M c (N i.val)
      then (1 : ℂ) else 0) = (k : ℂ) ^ matchingKappa M N := by
  classical
  let p : PairColoring M k → Prop := fun c => ∀ i : N.pairReps,
    vertexColoringOfPairColoring M c i.val = vertexColoringOfPairColoring M c (N i.val)
  have hcard : Fintype.card (CompatiblePairColoring (k := k) M N) =
      (Finset.univ.filter p).card :=
    Fintype.card_of_subtype _ (by intro c; simp only [p, Finset.mem_filter, Finset.mem_univ, true_and])
  calc
    _ = ((Finset.univ.filter p).card : ℂ) := by
      simpa only [Finset.mem_univ, if_true] using (Finset.sum_boole p Finset.univ :
        (∑ c ∈ Finset.univ, if p c then (1 : ℂ) else 0) = _)
    _ = (Fintype.card (CompatiblePairColoring (k := k) M N) : ℂ) := by rw [hcard]
    _ = (Fintype.card (CompatibleMatchingColoring M N (Fin k)) : ℂ) := by
      rw [Fintype.card_congr (compatiblePairColoringEquiv M N)]
    _ = (k : ℂ) ^ matchingKappa M N := by
      rw [card_compatibleMatchingColoring]
      norm_cast

end MatsumotoPaper
