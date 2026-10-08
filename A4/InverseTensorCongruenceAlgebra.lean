import A4.InverseMatchingRecurrenceTensor
import A4.DirectMomentsWickRegrouping

open scoped BigOperators Matrix

noncomputable section
namespace A4Research

open MatsumotoPaper
open A4Standalone.GramHafnian

set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

private abbrev PM (n : ℕ) := A4Standalone.GramHafnian.PerfectMatching n

def entryPairListVertexEquiv (d n : ℕ) :
    EntryPairList d n ≃ (Fin (2 * n) → Fin d) where
  toFun := entryPairListVertices
  invFun := vertexEntryPairList
  left_inv := vertexEntryPairList_vertices
  right_inv := entryPairListVertices_vertexEntryPairList

/-- The coefficient of one ordered entry product after a linear covariance
change on every vertex. -/
def entryCongruenceCoefficient {d n : ℕ} {R : Type*} [CommMonoid R]
    (B : Matrix (Fin d) (Fin d) R) (x y : EntryPairList d n) : R :=
  ∏ r : Fin n, B (x r).1 (y r).1 * B (x r).2 (y r).2

theorem entryCongruenceCoefficient_eq_vertexProduct {d n : ℕ}
    {R : Type*} [CommMonoid R] (B : Matrix (Fin d) (Fin d) R)
    (x y : EntryPairList d n) :
    entryCongruenceCoefficient B x y =
      ∏ v : Fin (2 * n), B (entryPairListVertices x v) (entryPairListVertices y v) := by
  classical
  rw [← (matchingSlotEquiv n).prod_comp
    (fun v ↦ B (entryPairListVertices x v) (entryPairListVertices y v)),
    Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro r _
  simp [Fin.prod_univ_two]

theorem congruence_matrix_entry {d : ℕ} {R : Type*} [CommSemiring R]
    (B X : Matrix (Fin d) (Fin d) R) (i j : Fin d) :
    (B * X * B.transpose) i j =
      ∑ p : Fin d × Fin d, (B i p.1 * B j p.2) * X p.1 p.2 := by
  classical
  rw [Fintype.sum_prod_type]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- The exact finite expansion of a full matrix-entry product under
congruence, in every degree. -/
theorem prod_entries_congruence {d n : ℕ} {R : Type*} [CommSemiring R]
    (B X : Matrix (Fin d) (Fin d) R) (x : EntryPairList d n) :
    (∏ r : Fin n, (B * X * B.transpose) (x r).1 (x r).2) =
      ∑ y : EntryPairList d n, entryCongruenceCoefficient B x y *
        ∏ r : Fin n, X (y r).1 (y r).2 := by
  classical
  simp_rw [congruence_matrix_entry]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [entryCongruenceCoefficient, ← Finset.prod_mul_distrib]

theorem matching_color_compatible_iff_representatives {n d : ℕ}
    (M : PM n) (c : Fin (2 * n) → Fin d) :
    (∀ v, c (M v) = c v) ↔ (∀ i : M.pairReps, c i.1 = c (M i.1)) := by
  constructor
  · intro h i
    exact (h i.1).symm
  · intro h v
    rcases (M.exactly_one_mem_pairReps v).1 with hv | hv
    · exact (h ⟨v, hv⟩).symm
    · simpa only [M.apply_apply] using h ⟨M v, hv⟩

/-- Contracting one literal matching of Kronecker deltas gives its Gram
monomial. The finite pair-coloring bijection discharges the entire sum. -/
theorem sum_vertexProduct_matching_delta {d n : ℕ}
    (X : Fin d → Fin (2 * n) → ℂ) (M : PM n) :
    (∑ c : Fin (2 * n) → Fin d,
      (∏ v : Fin (2 * n), X (c v) v) *
        ∏ i : M.pairReps, (if c i.1 = c (M i.1) then (1 : ℂ) else 0)) =
      ∏ i : M.pairReps, ∑ a : Fin d, X a i.1 * X a (M i.1) := by
  classical
  simp_rw [Fintype.prod_ite_zero]
  simp only [Finset.prod_const_one]
  change (∑ c : Fin (2 * n) → Fin d, complexColoringCoefficient X c *
    (if ∀ i : M.pairReps, c i.1 = c (M i.1) then (1 : ℂ) else 0)) = _
  have hpoint (c : Fin (2 * n) → Fin d) :
      complexColoringCoefficient X c *
          (if ∀ i : M.pairReps, c i.1 = c (M i.1) then (1 : ℂ) else 0) =
        if ∀ v, c (M v) = c v then complexColoringCoefficient X c else 0 := by
    by_cases h : ∀ v, c (M v) = c v
    · have hp := (matching_color_compatible_iff_representatives M c).mp h
      simp only [if_pos h, if_pos hp, mul_one]
    · have hp : ¬∀ i : M.pairReps, c i.1 = c (M i.1) :=
        mt (matching_color_compatible_iff_representatives M c).mpr h
      simp only [if_neg h, if_neg hp, mul_zero]
  simp_rw [hpoint]
  have hsub : (∑ c : Fin (2 * n) → Fin d,
      if ∀ v, c (M v) = c v then complexColoringCoefficient X c else 0) =
        ∑ c : CompatibleVertexColoring M d, complexColoringCoefficient X c.1 := by
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (fun c ↦ by simp only [Finset.mem_filter,
      Finset.mem_univ, true_and]) _
  rw [hsub, ← (pairColoringEquivCompatibleVertexColoring M d).sum_comp
    (fun c ↦ complexColoringCoefficient X c.1)]
  change (∑ p : PairColoring M d,
    complexColoringCoefficient X (vertexColoringOfPairColoring M p)) = _
  have hcoeff (p : PairColoring M d) :
      complexColoringCoefficient X (vertexColoringOfPairColoring M p) =
        coloredMatchingMonomial (Matrix.of X) M p :=
    complexColoringCoefficient_vertexColoringOfPairColoring (Matrix.of X) M p
  simp_rw [hcoeff]
  exact (Fintype.prod_sum (fun (i : M.pairReps) (a : Fin d) ↦
    X a i.1 * X a (M i.1))).symm

/-- The same contraction in the exact ordered-pair coordinates of the
inverse-entry recurrence. -/
theorem sum_entryCongruenceCoefficient_matching_delta {d n : ℕ}
    (B : Matrix (Fin d) (Fin d) ℂ) (x : EntryPairList d n) (M : PM n) :
    (∑ y : EntryPairList d n, entryCongruenceCoefficient B x y *
      matchingEntryWeight (fun a b ↦ if a = b then 1 else 0)
        (entryPairListVertices y) M) =
      matchingEntryWeight (fun a b ↦ (B * B.transpose) a b)
        (entryPairListVertices x) M := by
  classical
  let X : Matrix (Fin d) (Fin (2 * n)) ℂ :=
    Matrix.of fun a v ↦ B (entryPairListVertices x v) a
  calc
    _ = ∑ c : Fin (2 * n) → Fin d,
        (∏ v : Fin (2 * n), X (c v) v) *
          ∏ i : M.pairReps, (if c i.1 = c (M i.1) then (1 : ℂ) else 0) := by
      apply Fintype.sum_equiv (entryPairListVertexEquiv d n)
      intro y
      rw [entryCongruenceCoefficient_eq_vertexProduct]
      rfl
    _ = ∏ i : M.pairReps, ∑ a : Fin d, X a i.1 * X a (M i.1) :=
      sum_vertexProduct_matching_delta (fun a v ↦ X a v) M
    _ = _ := by
      simp only [matchingEntryWeight, Matrix.mul_apply, Matrix.transpose_apply, X,
        Matrix.of_apply]

/-- All modified inverse coefficients survive a common covariance change;
only each matching monomial changes its scale. -/
theorem sum_entryCongruenceCoefficient_weingarten {d n : ℕ}
    (gamma : ℝ) (B : Matrix (Fin d) (Fin d) ℂ) (x : EntryPairList d n) :
    (∑ y : EntryPairList d n, entryCongruenceCoefficient B x y *
      inverseWeingartenEntryTensor gamma (fun a b ↦ if a = b then 1 else 0) n y) =
      inverseWeingartenEntryTensor gamma (fun a b ↦ (B * B.transpose) a b) n x := by
  classical
  simp only [inverseWeingartenEntryTensor, inverseWeingartenVertexTensor, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro M _
  have hterm :
      (∑ y : EntryPairList d n,
        entryCongruenceCoefficient B x y *
          (modifiedGramInverse n gamma (standardPairPartition n) M *
            matchingEntryWeight (fun a b ↦ if a = b then 1 else 0)
              (entryPairListVertices y) M)) =
        modifiedGramInverse n gamma (standardPairPartition n) M *
          ∑ y : EntryPairList d n, entryCongruenceCoefficient B x y *
            matchingEntryWeight (fun a b ↦ if a = b then 1 else 0)
              (entryPairListVertices y) M := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    ring
  rw [hterm, sum_entryCongruenceCoefficient_matching_delta]

end A4Research
