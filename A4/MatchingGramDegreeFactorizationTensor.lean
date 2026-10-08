import A4.MatchingGramDegreeFactorizationSlots

open scoped BigOperators Matrix

noncomputable section

namespace A4Research

open MatsumotoPaper

private abbrev PM (n : ℕ) := A4Standalone.GramHafnian.PerfectMatching n

theorem inverseWeingartenVertexTensor_firstPairSwitch_expand {d q : ℕ}
    (gamma : ℝ) (A : Fin d → Fin d → ℂ) (hA : ∀ a b, A a b = A b a)
    (j : Fin (2 * (q + 1)) → Fin d) (t : Fin (2 * q)) :
    inverseWeingartenVertexTensor (q + 1) gamma A (j ∘ firstPairSwitch q t) =
      ∑ M : PM (q + 1), modifiedGramInverse (q + 1) gamma
        (standardPairPartition (q + 1))
        (transportPairPartition (firstPairSwitch q t) M) * matchingEntryWeight A j M := by
  classical
  rw [inverseWeingartenVertexTensor_relabel gamma A hA]
  apply Finset.sum_congr rfl
  intro M _
  have htwice : transportPairPartition (firstPairSwitch q t)
      (transportPairPartition (firstPairSwitch q t) M) = M := by
    rw [← transportPairPartition_mul]
    simp [firstPairSwitch]
  have h := modifiedGramInverse_relabel gamma (firstPairSwitch q t)
    (standardPairPartition (q + 1)) (transportPairPartition (firstPairSwitch q t) M)
  rw [htwice] at h
  exact congrArg (fun z : ℂ => z * matchingEntryWeight A j M) h

end A4Research
