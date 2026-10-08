import A4.InverseSteinRealShape
import A4.InverseMatchingRecurrenceActual

open scoped BigOperators Matrix

noncomputable section
namespace MatsumotoPaper

open A4Research A4Research.InverseStein

/-- The actual inverse tensor satisfies its full degree-lowering recurrence
through every degree in the sharp original real-shape range. -/
theorem W_d.inverse_identity_tensor_recurrenceThrough
    {d n : ℕ} {beta gamma : ℝ} (W : W_d d beta (identityScale d))
    (hgamma : gamma = beta - ((d : ℝ) + 1) / 2) (hgap : (n : ℝ) - 1 < gamma) :
    InverseEntryRecurrenceThrough n gamma
      (fun a b ↦ ((identityScale d).1⁻¹ a b : ℂ)) (inverseEntryMomentTensor W) := by
  apply inverseEntryMomentTensor_recurrenceThrough W n gamma
  intro q hq indices a b
  have hqgap : (q : ℝ) < gamma := by
    have hle : (q : ℝ) + 1 ≤ n := by exact_mod_cast hq
    linarith
  exact W.inverse_entry_recurrence_identity hgamma hqgap indices a b

/-- Once the independently derived finite coefficient recurrence is supplied,
the exact identity-scale inverse tensor follows without further analytic
assumptions. -/
theorem W_d.inverse_identity_tensor_eq_of_candidate_recurrence
    {d n : ℕ} {beta gamma : ℝ} (W : W_d d beta (identityScale d))
    (hgamma : gamma = beta - ((d : ℝ) + 1) / 2) (hgap : (n : ℝ) - 1 < gamma)
    (hcandidate : InverseEntryRecurrenceThrough n gamma
      (fun a b ↦ ((identityScale d).1⁻¹ a b : ℂ))
      (inverseWeingartenEntryTensor gamma (fun a b ↦ ((identityScale d).1⁻¹ a b : ℂ)))) :
    inverseEntryMomentTensor W n =
      inverseWeingartenEntryTensor gamma (fun a b ↦ ((identityScale d).1⁻¹ a b : ℂ)) n :=
  inverseEntryMomentTensor_eq_of_recurrences W hgap
    (W.inverse_identity_tensor_recurrenceThrough hgamma hgap) hcandidate

end MatsumotoPaper
