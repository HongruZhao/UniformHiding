import A4.InverseSteinRealShape

#print axioms A4Research.InverseStein.inverseEntryProduct_steinHaff_halfGaussianMatrix
#print axioms A4Research.InverseStein.inverse_entry_recurrence_halfGaussianMatrix
#print axioms A4Research.InverseStein.inverse_entry_recurrence_half_integer
#print axioms MatsumotoPaper.W_d.inverse_entry_recurrence_identity

open MeasureTheory Matrix
open scoped BigOperators

noncomputable section
open MatsumotoPaper A4Research.InverseStein

example {d q : ℕ} {beta gamma : ℝ} (W : W_d d beta (identityScale d))
    (hgamma : gamma = beta - ((d : ℝ) + 1) / 2) (hgap : (q : ℝ) < gamma)
    (indices : Fin q → Fin d × Fin d) (a b : Fin d) :
    gamma * (∫ w, ∏ r : Fin (q + 1),
        w.1⁻¹ (prependInverseEntry indices a b r).1
          (prependInverseEntry indices a b r).2 ∂W.toMeasure) -
      (1 / 2 : ℝ) * ∑ r : Fin q,
        ((∫ w, ∏ s : Fin (q + 1), w.1⁻¹ (inverseSwapLeft indices a b r s).1
              (inverseSwapLeft indices a b r s).2 ∂W.toMeasure) +
          (∫ w, ∏ s : Fin (q + 1), w.1⁻¹ (inverseSwapRight indices a b r s).1
              (inverseSwapRight indices a b r s).2 ∂W.toMeasure)) =
      (identityScale d).1⁻¹ a b *
        (∫ w, ∏ r : Fin q, w.1⁻¹ (indices r).1 (indices r).2 ∂W.toMeasure) := by
  exact W.inverse_entry_recurrence_identity hgamma hgap indices a b
