import LogdetLean.GramHafnian.ShiftedAnticoncentration.FinalTheorem

/-!
# Ordinary inverse integrability in the paper range

The production inverse-moment argument is deliberately formulated in
`ENNReal`, so it remains meaningful before finiteness is known.  This small
bridge records that its proved finite upper bound implies ordinary real
integrability of `V_n⁻¹` when `1 ≤ n` and `4 * n ≤ k`.  It also identifies the
ordinary integral with the real value of the production extended inverse
moment.

No new probabilistic or analytic input is used here.
-/

open MeasureTheory
open scoped ENNReal

namespace LogdetLean.GramHafnian

noncomputable section

/-- The production extended inverse moment is finite throughout the paper's
dimension range. -/
theorem pastCofactorVInverseMoment_ne_top_paperRange
    (k n : ℕ) (hn : 1 ≤ n) (hkn : 4 * n ≤ k) :
    pastCofactorVInverseMoment k n ≠ ⊤ := by
  have hle : pastCofactorVInverseMoment k n ≤
      ENNReal.ofReal (inverseVarianceBound k n) := by
    apply pastCofactorVInverseMoment_le_inverseVarianceBound_of_steps
      k n hn hkn
    · intro r hr2 hrn
      exact pastCofactorWInverseMoment_le_fourier k r hr2 (by omega)
    · intro r hr2 hrn
      exact Wishart.pastCofactorVInverseMoment_le_wishart k r hr2 (by omega)
  exact ne_top_of_le_ne_top (by finiteness) hle

/-- The reciprocal of the literal past cofactor variance is an ordinary
Bochner-integrable real random variable in the paper range. -/
theorem integrable_inv_pastCofactorV_paperRange
    (k n : ℕ) (hn : 1 ≤ n) (hkn : 4 * n ≤ k) :
    Integrable
      (fun A : OddCofactorIndex n hn → (Fin k → ℂ) ↦
        (pastCofactorV hn A)⁻¹)
      (Measure.pi fun _ : OddCofactorIndex n hn ↦ circularGaussianVector k) := by
  let μ : Measure (OddCofactorIndex n hn → (Fin k → ℂ)) :=
    Measure.pi fun _ : OddCofactorIndex n hn ↦ circularGaussianVector k
  have hnonneg :
      0 ≤ᵐ[μ] (fun A ↦ (pastCofactorV hn A)⁻¹) :=
    ae_of_all μ fun A ↦ inv_nonneg.mpr (pastCofactorV_nonneg hn A)
  have hmoment :
      ennInverseMoment μ (pastCofactorV hn) ≠ ⊤ := by
    rw [← pastCofactorVInverseMoment_eq hn]
    exact pastCofactorVInverseMoment_ne_top_paperRange k n hn hkn
  refine ⟨(measurable_pastCofactorV hn).inv.aestronglyMeasurable, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal hnonneg).2
  unfold ennInverseMoment at hmoment
  exact lt_top_iff_ne_top.mpr hmoment

/-- The ordinary real inverse moment is exactly the finite real value of the
production `ENNReal` inverse moment. -/
theorem integral_inv_pastCofactorV_eq_toReal_paperRange
    (k n : ℕ) (hn : 1 ≤ n) (hkn : 4 * n ≤ k) :
    (∫ A : OddCofactorIndex n hn → (Fin k → ℂ),
        (pastCofactorV hn A)⁻¹
      ∂(Measure.pi fun _ : OddCofactorIndex n hn ↦ circularGaussianVector k)) =
      (pastCofactorVInverseMoment k n).toReal := by
  let μ : Measure (OddCofactorIndex n hn → (Fin k → ℂ)) :=
    Measure.pi fun _ : OddCofactorIndex n hn ↦ circularGaussianVector k
  have hnonneg :
      0 ≤ᵐ[μ] (fun A ↦ (pastCofactorV hn A)⁻¹) :=
    ae_of_all μ fun A ↦ inv_nonneg.mpr (pastCofactorV_nonneg hn A)
  have hint := integrable_inv_pastCofactorV_paperRange k n hn hkn
  rw [integral_eq_lintegral_of_nonneg_ae hnonneg hint.aestronglyMeasurable]
  rw [pastCofactorVInverseMoment_eq hn]
  rfl

end

end LogdetLean.GramHafnian
