import A4.MatchingGramDegreeFactorizationCoefficients
import A4.MatchingGramDegreeFactorizationSlots

open scoped BigOperators Matrix

noncomputable section

namespace MatsumotoPaper

private abbrev PM (n : ℕ) := A4Standalone.GramHafnian.PerfectMatching n

theorem modifiedGramInverse_standard_firstPair_recurrence (q : ℕ) (gamma : ℝ)
    (hgamma : (q : ℝ) < gamma) (M : PM (q + 1)) :
    (gamma : ℂ) * modifiedGramInverse (q + 1) gamma (standardPairPartition (q + 1)) M -
      (1 / 2 : ℂ) * ∑ t : Fin (2 * q),
        modifiedGramInverse (q + 1) gamma (standardPairPartition (q + 1))
          (transportPairPartition (firstPairSwitch q t) M) =
      if M (firstVertex q) = secondVertex q then
        modifiedGramInverse q gamma (standardPairPartition q) (firstPairDelete M) else 0 := by
  have h := modifiedGramInverse_firstPair_recurrence q gamma hgamma M (standardPairPartition q)
  rw [firstPairEmbed_standard] at h
  have hbig : ∀ P : PM (q + 1),
      modifiedGramInverse (q + 1) gamma P (standardPairPartition (q + 1)) =
        modifiedGramInverse (q + 1) gamma (standardPairPartition (q + 1)) P :=
    fun P => (modifiedGramInverse_isSymm (q + 1) gamma).apply _ P
  have hsmall : modifiedGramInverse q gamma (firstPairDelete M) (standardPairPartition q) =
      modifiedGramInverse q gamma (standardPairPartition q) (firstPairDelete M) :=
    (modifiedGramInverse_isSymm q gamma).apply _ _
  simpa only [hbig, hsmall] using h

end MatsumotoPaper
