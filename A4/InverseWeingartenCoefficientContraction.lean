import A4.MatchingGramDegreeFactorizationStandard

open scoped BigOperators Matrix

noncomputable section
namespace A4Research

open MatsumotoPaper

private abbrev PM (n : ℕ) := A4Standalone.GramHafnian.PerfectMatching n

/-- Applying an arbitrary finite matching weight to the proved coefficient
recurrence. This is a finite sum identity, with no moment premise. -/
theorem modifiedGramInverse_weighted_firstPair_recurrence
    (q : ℕ) (gamma : ℝ) (hgamma : (q : ℝ) < gamma)
    (weight : PM (q + 1) → ℂ) :
    (gamma : ℂ) * (∑ M : PM (q + 1),
        modifiedGramInverse (q + 1) gamma (standardPairPartition (q + 1)) M * weight M) -
      (1 / 2 : ℂ) * (∑ t : Fin (2 * q), ∑ M : PM (q + 1),
        modifiedGramInverse (q + 1) gamma (standardPairPartition (q + 1))
          (transportPairPartition (firstPairSwitch q t) M) * weight M) =
      ∑ M : PM (q + 1),
        (if M (firstVertex q) = secondVertex q then
          modifiedGramInverse q gamma (standardPairPartition q) (firstPairDelete M)
        else 0) * weight M := by
  classical
  have hfirst : (gamma : ℂ) * (∑ M : PM (q + 1),
      modifiedGramInverse (q + 1) gamma (standardPairPartition (q + 1)) M * weight M) =
      ∑ M : PM (q + 1),
        ((gamma : ℂ) * modifiedGramInverse (q + 1) gamma
          (standardPairPartition (q + 1)) M) * weight M := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro M _
    ring
  have hswitch : (1 / 2 : ℂ) * (∑ t : Fin (2 * q), ∑ M : PM (q + 1),
      modifiedGramInverse (q + 1) gamma (standardPairPartition (q + 1))
        (transportPairPartition (firstPairSwitch q t) M) * weight M) =
      ∑ M : PM (q + 1),
        ((1 / 2 : ℂ) * ∑ t : Fin (2 * q),
          modifiedGramInverse (q + 1) gamma (standardPairPartition (q + 1))
            (transportPairPartition (firstPairSwitch q t) M)) * weight M := by
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro M _
    rw [← Finset.sum_mul]
    ring
  rw [hfirst, hswitch, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro M _
  rw [← sub_mul, modifiedGramInverse_standard_firstPair_recurrence q gamma hgamma M]

/-- The two slots of each old pair exhaust the remaining vertices. -/
theorem sum_remainingVertex_slots {q : ℕ} (f : Fin (2 * q) → ℂ) :
    (∑ t : Fin (2 * q), f t) =
      ∑ r : Fin q, (f (leftSlot r) + f (rightSlot r)) := by
  rw [← (matchingSlotEquiv q).sum_comp f, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro r _
  simp [Fin.sum_univ_two]

end A4Research
