import LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep.TaylorTV

/-!
# Correlated scalar--orbital Taylor bridge

In the Haar one-column update the central increment and the traceless orbital
increment are functions of the **same** beta variable.  They cannot be
implemented by first averaging the central move and then applying an
independently averaged orbital move.

This file proves the eventwise Taylor estimate with a parameter-dependent
orbital path.  Its value at zero may therefore retain the central move made
with that same parameter.  No Haar, beta, COE, score, or hiding statement is
assumed.
-/

open MeasureTheory Set

namespace LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep

noncomputable section

/-- A centered orbital Taylor estimate in which the path itself depends on
the sampled parameter.  The two endpoint laws are mixtures using the same
parameter `p`; this is the correlation-safe form needed by the one-column
recursion. -/
theorem probabilityTVLE_of_correlated_centered_eventPath
    {State Param : Type*}
    [MeasurableSpace State] [MeasurableSpace Param]
    (mu nu : Measure State) (param : Measure Param)
    [IsProbabilityMeasure param]
    (amplitude : Param → ℝ)
    (eventPath : Param → Set State → ℝ → ℝ)
    (Ctwo Cthree : ℝ)
    (hCtwo : 0 ≤ Ctwo) (hCthree : 0 ≤ Cthree)
    (hmu : ∀ A, MeasurableSet A →
      ∫ p, eventPath p A 0 ∂param = mu.real A)
    (hnu : ∀ A, MeasurableSet A →
      ∫ p, eventPath p A (amplitude p) ∂param = nu.real A)
    (hsmooth : ∀ p A, MeasurableSet A → ContDiff ℝ 3 (eventPath p A))
    (hfirst : ∀ p A, MeasurableSet A →
      iteratedDeriv 1 (eventPath p A) 0 = 0)
    (hsecond : ∀ p A, MeasurableSet A →
      |iteratedDeriv 2 (eventPath p A) 0| ≤ Ctwo)
    (hthird : ∀ p A, MeasurableSet A → ∀ y ∈ uIcc 0 (amplitude p),
      |iteratedDeriv 3 (eventPath p A) y| ≤ Cthree)
    (hpathZeroIntegrable : ∀ A, MeasurableSet A →
      Integrable (fun p ↦ eventPath p A 0) param)
    (hpathMoveIntegrable : ∀ A, MeasurableSet A →
      Integrable (fun p ↦ eventPath p A (amplitude p)) param)
    (hsqIntegrable : Integrable (fun p ↦ amplitude p ^ 2) param)
    (hcubeIntegrable : Integrable (fun p ↦ |amplitude p| ^ 3) param) :
    Dense.ProbabilityTVLE mu nu
      (Ctwo * (∫ p, amplitude p ^ 2 ∂param) / 2 +
        Cthree * (∫ p, |amplitude p| ^ 3 ∂param) / 6) := by
  have hsqnonneg : 0 ≤ ∫ p, amplitude p ^ 2 ∂param :=
    integral_nonneg fun _ ↦ sq_nonneg _
  have hcubenonneg : 0 ≤ ∫ p, |amplitude p| ^ 3 ∂param :=
    integral_nonneg fun _ ↦ by positivity
  refine ⟨add_nonneg
      (div_nonneg (mul_nonneg hCtwo hsqnonneg) (by norm_num))
      (div_nonneg (mul_nonneg hCthree hcubenonneg) (by norm_num)), ?_⟩
  intro A hA
  have hdiff : Integrable
      (fun p ↦ eventPath p A (amplitude p) - eventPath p A 0) param :=
    (hpathMoveIntegrable A hA).sub (hpathZeroIntegrable A hA)
  have hmajorant : Integrable
      (fun p ↦ Ctwo * amplitude p ^ 2 / 2 +
        Cthree * |amplitude p| ^ 3 / 6) param :=
    ((hsqIntegrable.const_mul Ctwo).div_const 2).add
      ((hcubeIntegrable.const_mul Cthree).div_const 6)
  have hpoint : ∀ p,
      |eventPath p A (amplitude p) - eventPath p A 0| ≤
        Ctwo * amplitude p ^ 2 / 2 +
          Cthree * |amplitude p| ^ 3 / 6 := by
    intro p
    exact abs_centered_move_le (eventPath p A) (amplitude p) Ctwo Cthree
      hCtwo hCthree (hsmooth p A hA) (hfirst p A hA) (hsecond p A hA)
      (hthird p A hA)
  rw [← hnu A hA, ← hmu A hA, abs_sub_comm,
    ← integral_sub (hpathMoveIntegrable A hA) (hpathZeroIntegrable A hA)]
  calc
    |∫ p, eventPath p A (amplitude p) - eventPath p A 0 ∂param| ≤
        ∫ p, |eventPath p A (amplitude p) - eventPath p A 0| ∂param :=
      abs_integral_le_integral_abs
    _ ≤ ∫ p, (Ctwo * amplitude p ^ 2 / 2 +
          Cthree * |amplitude p| ^ 3 / 6) ∂param := by
      exact integral_mono hdiff.abs hmajorant hpoint
    _ = Ctwo * (∫ p, amplitude p ^ 2 ∂param) / 2 +
          Cthree * (∫ p, |amplitude p| ^ 3 ∂param) / 6 := by
      rw [integral_add ((hsqIntegrable.const_mul Ctwo).div_const 2)
          ((hcubeIntegrable.const_mul Cthree).div_const 6),
        integral_div, integral_const_mul, integral_div, integral_const_mul]

end

end LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep
