import A4.DirectMomentsFull
import A4.InverseMomentsUnconditional

noncomputable section
namespace MatsumotoPaper

/-- The exact original A4 target, with both moment formulas proved. -/
theorem completedMatsumotoTheorem3 : Target := by
  intro d n beta gamma hd hn sigma W hgamma hgap m g
  exact ⟨W.direct_matching_moment m g, W.inverse_matching_moment hgamma hgap m g⟩

end MatsumotoPaper
