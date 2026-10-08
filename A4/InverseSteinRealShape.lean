import A4.InverseSteinEntryRecurrence

open MeasureTheory Matrix
open scoped BigOperators

noncomputable section
namespace MatsumotoPaper

open A4Research.InverseStein

/-- The all-degree Stein--Haff inverse-entry recurrence follows from the
matrix Laplace characterization for every admissible real shape. The sharp
moment gap is `q < gamma`; the Gaussian sampling margin is fully eliminated
by rational continuation. -/
theorem W_d.inverse_entry_recurrence_identity
    {d q : ℕ} {beta gamma : ℝ} (W : W_d d beta (identityScale d))
    (hgamma : gamma = beta - ((d : ℝ) + 1) / 2) (hgap : (q : ℝ) < gamma)
    (indices : Fin q → Fin d × Fin d) (a b : Fin d) :
    gamma * inverseEntryMoment W (prependInverseEntry indices a b) -
        (1 / 2 : ℝ) * ∑ r : Fin q,
          (inverseEntryMoment W (inverseSwapLeft indices a b r) +
            inverseEntryMoment W (inverseSwapRight indices a b r)) =
      (identityScale d).1⁻¹ a b * inverseEntryMoment W indices := by
  exact inverse_entry_recurrence_of_nat (d + 64 * (q + 2) + 2)
    (fun k hk V indices a b ↦ inverse_entry_recurrence_half_integer V hk indices a b)
    W hgamma hgap indices a b

end MatsumotoPaper
