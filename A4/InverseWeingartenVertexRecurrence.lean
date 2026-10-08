import A4.InverseWeingartenCoefficientContraction
import A4.MatchingGramDegreeFactorizationTensor
import A4.InverseMatchingRecurrenceEmbed
import A4.InverseVertexRecurrenceFamily
import A4.InverseMatchingRecurrenceActual

open scoped BigOperators Matrix

noncomputable section
namespace A4Research

open MatsumotoPaper

private abbrev PM (n : ℕ) := A4Standalone.GramHafnian.PerfectMatching n

/-- The literal modified Weingarten candidate satisfies the complete
first-vertex recurrence at the sharp degree threshold. -/
theorem inverseWeingartenVertexTensor_recurrence {d q : ℕ}
    (gamma : ℝ) (hgamma : (q : ℝ) < gamma)
    (A : Fin d → Fin d → ℂ) (hA : ∀ a b, A a b = A b a)
    (j : VertexArray d (q + 1)) :
    (gamma : ℂ) * inverseWeingartenVertexTensor (q + 1) gamma A j -
      (1 / 2 : ℂ) * ∑ r : Fin q,
        (inverseWeingartenVertexTensor (q + 1) gamma A
            (j ∘ firstPairSwitch q (leftSlot r)) +
          inverseWeingartenVertexTensor (q + 1) gamma A
            (j ∘ firstPairSwitch q (rightSlot r))) =
      A (j (firstVertex q)) (j (secondVertex q)) *
        inverseWeingartenVertexTensor q gamma A (fun t ↦ j (remainingVertex q t)) := by
  have hs := sum_remainingVertex_slots
    (fun t ↦ inverseWeingartenVertexTensor (q + 1) gamma A (j ∘ firstPairSwitch q t))
  rw [← hs]
  simp_rw [inverseWeingartenVertexTensor_firstPairSwitch_expand gamma A hA j]
  exact (modifiedGramInverse_weighted_firstPair_recurrence q gamma hgamma
    (matchingEntryWeight A j)).trans (sum_firstPair_fixed_weingarten gamma A j)

theorem inverseWeingartenVertexTensor_recurrenceThrough {d : ℕ}
    (n : ℕ) (gamma : ℝ) (hgap : (n : ℝ) - 1 < gamma)
    (A : Fin d → Fin d → ℂ) (hA : ∀ a b, A a b = A b a) :
    InverseVertexRecurrenceThrough n gamma A
      (fun k ↦ inverseWeingartenVertexTensor k gamma A) := by
  intro q hq j
  have hqgap : (q : ℝ) < gamma := by
    have hle : (q : ℝ) + 1 ≤ n := by exact_mod_cast hq
    linarith
  exact inverseWeingartenVertexTensor_recurrence gamma hqgap A hA j

@[simp] theorem inverseWeingartenVertexTensor_zero {d : ℕ} (gamma : ℝ)
    (A : Fin d → Fin d → ℂ) (j : VertexArray d 0) :
    inverseWeingartenVertexTensor 0 gamma A j = 1 := by
  simpa only [inverseWeingartenEntryTensor, entryPairListVertices_vertexEntryPairList]
    using inverseWeingartenEntryTensor_zero gamma A (vertexEntryPairList j)

end A4Research
