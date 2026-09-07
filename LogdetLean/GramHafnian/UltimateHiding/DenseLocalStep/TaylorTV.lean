import LogdetLean.GramHafnian.UltimateHiding.Dense.Telescoping
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Tactic

/-!
# Centered Taylor expansion to total variation

This file proves the analytic passage used after the COE score calculation.
The theorem is deliberately eventwise: a concrete density proof supplies the
event path and its derivatives, while the conclusion is the same
`ProbabilityTVLE` relation used by the dense telescope.

No Haar, COE, Wishart, or score estimate is postulated here.
-/

open MeasureTheory Set

namespace LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep

noncomputable section

/-- Taylor's theorem through degree two, with an explicit third-derivative
remainder valid for either sign of `s`. -/
theorem abs_sub_taylor_two_le
    (f : ℝ → ℝ) (s Cthree : ℝ)
    (hf : ContDiff ℝ 3 f)
    (hthree : ∀ y ∈ uIcc 0 s, |iteratedDeriv 3 f y| ≤ Cthree) :
    |f s - (f 0 + iteratedDeriv 1 f 0 * s +
      iteratedDeriv 2 f 0 * s ^ 2 / 2)| ≤
      Cthree * |s| ^ 3 / 6 := by
  by_cases hs : s = 0
  · subst s
    simp
  · have hs0 : (0 : ℝ) ≠ s := Ne.symm hs
    have hu : UniqueDiffOn ℝ (uIcc 0 s) := uniqueDiffOn_uIcc hs0
    have hpoly :
        taylorWithinEval f 2 (uIcc 0 s) 0 s =
          f 0 + iteratedDeriv 1 f 0 * s +
            iteratedDeriv 2 f 0 * s ^ 2 / 2 := by
      rw [taylor_within_apply]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero,
        Finset.sum_insert, Finset.mem_range, not_false_eq_true,
        Finset.sum_empty, zero_add, Nat.factorial_zero, Nat.cast_one,
        inv_one, sub_zero, pow_zero, one_smul, Nat.factorial_one, pow_one,
        Nat.factorial_two, Nat.cast_ofNat, smul_eq_mul]
      rw [iteratedDerivWithin_eq_iteratedDeriv hu (hf.of_le (by norm_num)).contDiffAt
          left_mem_uIcc,
        iteratedDerivWithin_eq_iteratedDeriv hu (hf.of_le (by norm_num)).contDiffAt
          left_mem_uIcc,
        iteratedDerivWithin_eq_iteratedDeriv hu (hf.of_le (by norm_num)).contDiffAt
          left_mem_uIcc]
      simp only [iteratedDeriv_zero, Pi.zero_apply]
      ring
    obtain ⟨y, hy, hrem⟩ :=
      taylor_mean_remainder_lagrange_iteratedDeriv hs0 hf.contDiffOn
    rw [hpoly] at hrem
    rw [hrem]
    have hy' : y ∈ uIcc 0 s := uIoo_subset_uIcc_self hy
    have hbound := hthree y hy'
    have hmul := mul_le_mul_of_nonneg_right hbound
      (pow_nonneg (abs_nonneg s) 3)
    have hdiv := div_le_div_of_nonneg_right hmul (by norm_num : (0 : ℝ) ≤ 6)
    simpa [Nat.factorial, abs_mul, abs_div, abs_pow] using hdiv

/-- Taylor's theorem through degree one with an explicit second-derivative
remainder.  This is the scalar-dilation companion of
`abs_sub_taylor_two_le`. -/
theorem abs_sub_taylor_one_le
    (f : ℝ → ℝ) (s Ctwo : ℝ)
    (hf : ContDiff ℝ 2 f)
    (htwo : ∀ y ∈ uIcc 0 s, |iteratedDeriv 2 f y| ≤ Ctwo) :
    |f s - (f 0 + iteratedDeriv 1 f 0 * s)| ≤
      Ctwo * s ^ 2 / 2 := by
  by_cases hs : s = 0
  · subst s
    simp
  · have hs0 : (0 : ℝ) ≠ s := Ne.symm hs
    have hu : UniqueDiffOn ℝ (uIcc 0 s) := uniqueDiffOn_uIcc hs0
    have hpoly :
        taylorWithinEval f 1 (uIcc 0 s) 0 s =
          f 0 + iteratedDeriv 1 f 0 * s := by
      rw [taylor_within_apply]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero,
        zero_add, Nat.factorial_zero, Nat.cast_one, inv_one, sub_zero,
        pow_zero, Nat.factorial_one, pow_one, smul_eq_mul]
      rw [iteratedDerivWithin_eq_iteratedDeriv hu (hf.of_le (by norm_num)).contDiffAt
          left_mem_uIcc,
        iteratedDerivWithin_eq_iteratedDeriv hu (hf.of_le (by norm_num)).contDiffAt
          left_mem_uIcc]
      simp only [iteratedDeriv_zero]
      ring
    obtain ⟨y, hy, hrem⟩ :=
      taylor_mean_remainder_lagrange_iteratedDeriv hs0 hf.contDiffOn
    rw [hpoly] at hrem
    rw [hrem]
    have hbound := htwo y (uIoo_subset_uIcc_self hy)
    have hmul := mul_le_mul_of_nonneg_right hbound (sq_nonneg s)
    have hdiv := div_le_div_of_nonneg_right hmul (by norm_num : (0 : ℝ) ≤ 2)
    simpa [Nat.factorial, abs_mul, abs_div, abs_pow, sq_abs] using hdiv

/-- First-order mean-value bound, phrased with `iteratedDeriv` so it can be
applied directly to the third score and its fourth derivative. -/
theorem abs_sub_taylor_zero_le
    (f : ℝ → ℝ) (s Cone : ℝ)
    (hf : ContDiff ℝ 1 f)
    (hone : ∀ y ∈ uIcc 0 s, |iteratedDeriv 1 f y| ≤ Cone) :
    |f s - f 0| ≤ Cone * |s| := by
  by_cases hs : s = 0
  · subst s
    simp
  · have hs0 : (0 : ℝ) ≠ s := Ne.symm hs
    obtain ⟨y, hy, hrem⟩ :=
      taylor_mean_remainder_lagrange_iteratedDeriv
        (n := 0) hs0 hf.contDiffOn
    have hpoly : taylorWithinEval f 0 (uIcc 0 s) 0 s = f 0 := by simp
    rw [hpoly] at hrem
    rw [hrem]
    have hbound := hone y (uIoo_subset_uIcc_self hy)
    have hmul := mul_le_mul_of_nonneg_right hbound (abs_nonneg s)
    simpa [Nat.factorial, abs_mul, abs_div, abs_pow] using hmul

/-- Centering removes the first-order term.  A second-score bound and a
third-score bound therefore control a finite orbital move by
`C₂ s²/2 + C₃ |s|³/6`. -/
theorem abs_centered_move_le
    (f : ℝ → ℝ) (s Ctwo Cthree : ℝ)
    (hCtwo : 0 ≤ Ctwo) (hCthree : 0 ≤ Cthree)
    (hf : ContDiff ℝ 3 f)
    (hfirst : iteratedDeriv 1 f 0 = 0)
    (hsecond : |iteratedDeriv 2 f 0| ≤ Ctwo)
    (hthree : ∀ y ∈ uIcc 0 s, |iteratedDeriv 3 f y| ≤ Cthree) :
    |f s - f 0| ≤ Ctwo * s ^ 2 / 2 + Cthree * |s| ^ 3 / 6 := by
  have hrem := abs_sub_taylor_two_le f s Cthree hf hthree
  rw [hfirst] at hrem
  simp only [zero_mul, add_zero] at hrem
  have hquad : |iteratedDeriv 2 f 0 * s ^ 2 / 2| ≤ Ctwo * s ^ 2 / 2 := by
    have hmul := mul_le_mul_of_nonneg_right hsecond (sq_nonneg s)
    have hdiv := div_le_div_of_nonneg_right hmul (by norm_num : (0 : ℝ) ≤ 2)
    simpa [abs_mul, abs_div, abs_pow, sq_abs] using hdiv
  calc
    |f s - f 0| =
        |(f s - (f 0 + iteratedDeriv 2 f 0 * s ^ 2 / 2)) +
          iteratedDeriv 2 f 0 * s ^ 2 / 2| := by ring_nf
    _ ≤ |f s - (f 0 + iteratedDeriv 2 f 0 * s ^ 2 / 2)| +
          |iteratedDeriv 2 f 0 * s ^ 2 / 2| := abs_add_le _ _
    _ ≤ Cthree * |s| ^ 3 / 6 + Ctwo * s ^ 2 / 2 := add_le_add hrem hquad
    _ = Ctwo * s ^ 2 / 2 + Cthree * |s| ^ 3 / 6 := by ring

/-- Eventwise centered Taylor control implies the probability total-variation
bound used by the hiding telescope.  This theorem is the formal
score-to-TV plug-in point: the remaining concrete obligation is precisely to
construct `eventPath` from the COE likelihood and prove the displayed score
bounds uniformly in measurable events. -/
theorem probabilityTVLE_of_centered_eventPath
    {State : Type*} [MeasurableSpace State]
    (mu nu : Measure State)
    (eventPath : Set State → ℝ → ℝ)
    (s Ctwo Cthree : ℝ)
    (hCtwo : 0 ≤ Ctwo) (hCthree : 0 ≤ Cthree)
    (hmu : ∀ A, MeasurableSet A → eventPath A 0 = mu.real A)
    (hnu : ∀ A, MeasurableSet A → eventPath A s = nu.real A)
    (hsmooth : ∀ A, MeasurableSet A → ContDiff ℝ 3 (eventPath A))
    (hfirst : ∀ A, MeasurableSet A →
      iteratedDeriv 1 (eventPath A) 0 = 0)
    (hsecond : ∀ A, MeasurableSet A →
      |iteratedDeriv 2 (eventPath A) 0| ≤ Ctwo)
    (hthird : ∀ A, MeasurableSet A → ∀ y ∈ uIcc 0 s,
      |iteratedDeriv 3 (eventPath A) y| ≤ Cthree) :
    Dense.ProbabilityTVLE mu nu
      (Ctwo * s ^ 2 / 2 + Cthree * |s| ^ 3 / 6) := by
  refine ⟨add_nonneg (div_nonneg (mul_nonneg hCtwo (sq_nonneg s)) (by norm_num))
      (div_nonneg (mul_nonneg hCthree (by positivity)) (by norm_num)), ?_⟩
  intro A hA
  rw [← hmu A hA, ← hnu A hA, abs_sub_comm]
  exact abs_centered_move_le (eventPath A) s Ctwo Cthree hCtwo hCthree
    (hsmooth A hA) (hfirst A hA) (hsecond A hA) (hthird A hA)

/-- Randomized centered orbital Taylor bound.

The theorem integrates the deterministic Taylor estimate only after the zero
first derivative has been used, yielding the exact moment budget
`C₂ E[b²]/2 + C₃ E[|b|³]/6`.  The parameter law is arbitrary, so the
one-column beta law can be plugged in without changing this argument. -/
theorem probabilityTVLE_of_random_centered_eventPath
    {State Param : Type*}
    [MeasurableSpace State] [MeasurableSpace Param]
    (mu nu : Measure State) (param : Measure Param)
    [IsProbabilityMeasure param]
    (amplitude : Param → ℝ)
    (eventPath : Set State → ℝ → ℝ)
    (Ctwo Cthree : ℝ)
    (hCtwo : 0 ≤ Ctwo) (hCthree : 0 ≤ Cthree)
    (hmu : ∀ A, MeasurableSet A → eventPath A 0 = mu.real A)
    (hnu : ∀ A, MeasurableSet A →
      ∫ p, eventPath A (amplitude p) ∂param = nu.real A)
    (hsmooth : ∀ A, MeasurableSet A → ContDiff ℝ 3 (eventPath A))
    (hfirst : ∀ A, MeasurableSet A →
      iteratedDeriv 1 (eventPath A) 0 = 0)
    (hsecond : ∀ A, MeasurableSet A →
      |iteratedDeriv 2 (eventPath A) 0| ≤ Ctwo)
    (hthird : ∀ A, MeasurableSet A → ∀ p, ∀ y ∈ uIcc 0 (amplitude p),
      |iteratedDeriv 3 (eventPath A) y| ≤ Cthree)
    (hpathIntegrable : ∀ A, MeasurableSet A →
      Integrable (fun p ↦ eventPath A (amplitude p)) param)
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
  have hconst : Integrable (fun _ : Param ↦ eventPath A 0) param :=
    integrable_const _
  have hdiff : Integrable
      (fun p ↦ eventPath A (amplitude p) - eventPath A 0) param :=
    (hpathIntegrable A hA).sub hconst
  have hmajorant : Integrable
      (fun p ↦ Ctwo * amplitude p ^ 2 / 2 +
        Cthree * |amplitude p| ^ 3 / 6) param :=
    ((hsqIntegrable.const_mul Ctwo).div_const 2).add
      ((hcubeIntegrable.const_mul Cthree).div_const 6)
  have hpoint : ∀ p,
      |eventPath A (amplitude p) - eventPath A 0| ≤
        Ctwo * amplitude p ^ 2 / 2 +
          Cthree * |amplitude p| ^ 3 / 6 := by
    intro p
    exact abs_centered_move_le (eventPath A) (amplitude p) Ctwo Cthree
      hCtwo hCthree (hsmooth A hA) (hfirst A hA) (hsecond A hA)
      (hthird A hA p)
  rw [← hnu A hA, ← hmu A hA]
  have hconstIntegral :
      ∫ _ : Param, eventPath A 0 ∂param = eventPath A 0 := by simp
  rw [← hconstIntegral, abs_sub_comm,
    ← integral_sub (hpathIntegrable A hA) hconst]
  calc
    |∫ p, eventPath A (amplitude p) - eventPath A 0 ∂param| ≤
        ∫ p, |eventPath A (amplitude p) - eventPath A 0| ∂param :=
      abs_integral_le_integral_abs
    _ ≤ ∫ p, (Ctwo * amplitude p ^ 2 / 2 +
          Cthree * |amplitude p| ^ 3 / 6) ∂param := by
      exact integral_mono hdiff.abs hmajorant hpoint
    _ = Ctwo * (∫ p, amplitude p ^ 2 ∂param) / 2 +
          Cthree * (∫ p, |amplitude p| ^ 3 ∂param) / 6 := by
      rw [integral_add ((hsqIntegrable.const_mul Ctwo).div_const 2)
          ((hcubeIntegrable.const_mul Cthree).div_const 6),
        integral_div, integral_const_mul, integral_div, integral_const_mul]

/-- Random scalar Taylor bound with first-order cancellation performed at the
level of the parameter expectation.  In particular, the first-order term is
`C₁ |E[c]|`, not `C₁ E|c|`. -/
theorem probabilityTVLE_of_random_scalar_eventPath
    {State Param : Type*}
    [MeasurableSpace State] [MeasurableSpace Param]
    (mu nu : Measure State) (param : Measure Param)
    [IsProbabilityMeasure param]
    (amplitude : Param → ℝ)
    (eventPath : Set State → ℝ → ℝ)
    (Cone Ctwo : ℝ)
    (hCone : 0 ≤ Cone) (hCtwo : 0 ≤ Ctwo)
    (hmu : ∀ A, MeasurableSet A → eventPath A 0 = mu.real A)
    (hnu : ∀ A, MeasurableSet A →
      ∫ p, eventPath A (amplitude p) ∂param = nu.real A)
    (hsmooth : ∀ A, MeasurableSet A → ContDiff ℝ 2 (eventPath A))
    (hfirst : ∀ A, MeasurableSet A →
      |iteratedDeriv 1 (eventPath A) 0| ≤ Cone)
    (hsecond : ∀ A, MeasurableSet A → ∀ p, ∀ y ∈ uIcc 0 (amplitude p),
      |iteratedDeriv 2 (eventPath A) y| ≤ Ctwo)
    (hpathIntegrable : ∀ A, MeasurableSet A →
      Integrable (fun p ↦ eventPath A (amplitude p)) param)
    (hampIntegrable : Integrable amplitude param)
    (hsqIntegrable : Integrable (fun p ↦ amplitude p ^ 2) param) :
    Dense.ProbabilityTVLE mu nu
      (Cone * |∫ p, amplitude p ∂param| +
        Ctwo * (∫ p, amplitude p ^ 2 ∂param) / 2) := by
  have hsqnonneg : 0 ≤ ∫ p, amplitude p ^ 2 ∂param :=
    integral_nonneg fun _ ↦ sq_nonneg _
  refine ⟨add_nonneg (mul_nonneg hCone (abs_nonneg _))
      (div_nonneg (mul_nonneg hCtwo hsqnonneg) (by norm_num)), ?_⟩
  intro A hA
  let d : ℝ := iteratedDeriv 1 (eventPath A) 0
  let rem : Param → ℝ := fun p ↦
    eventPath A (amplitude p) - eventPath A 0 - d * amplitude p
  have hconst : Integrable (fun _ : Param ↦ eventPath A 0) param :=
    integrable_const _
  have hlin : Integrable (fun p ↦ d * amplitude p) param :=
    hampIntegrable.const_mul d
  have hremInt : Integrable rem param := by
    exact ((hpathIntegrable A hA).sub hconst).sub hlin
  have hmajorant : Integrable (fun p ↦ Ctwo * amplitude p ^ 2 / 2) param :=
    (hsqIntegrable.const_mul Ctwo).div_const 2
  have hremPoint : ∀ p, |rem p| ≤ Ctwo * amplitude p ^ 2 / 2 := by
    intro p
    dsimp [rem, d]
    convert abs_sub_taylor_one_le (eventPath A) (amplitude p) Ctwo
        (hsmooth A hA) (hsecond A hA p) using 1 <;> ring
  have hdecomp :
      ∫ p, eventPath A (amplitude p) - eventPath A 0 ∂param =
        d * (∫ p, amplitude p ∂param) + ∫ p, rem p ∂param := by
    calc
      ∫ p, eventPath A (amplitude p) - eventPath A 0 ∂param =
          ∫ p, d * amplitude p + rem p ∂param := by
            apply integral_congr_ae
            filter_upwards [] with p
            dsimp [rem]
            ring
      _ = ∫ p, d * amplitude p ∂param + ∫ p, rem p ∂param := by
            rw [integral_add hlin hremInt]
      _ = d * (∫ p, amplitude p ∂param) + ∫ p, rem p ∂param := by
            rw [integral_const_mul]
  have hremBound : |∫ p, rem p ∂param| ≤
      Ctwo * (∫ p, amplitude p ^ 2 ∂param) / 2 := by
    calc
      |∫ p, rem p ∂param| ≤ ∫ p, |rem p| ∂param :=
        abs_integral_le_integral_abs
      _ ≤ ∫ p, Ctwo * amplitude p ^ 2 / 2 ∂param := by
        exact integral_mono hremInt.abs hmajorant hremPoint
      _ = Ctwo * (∫ p, amplitude p ^ 2 ∂param) / 2 := by
        rw [integral_div, integral_const_mul]
  rw [← hnu A hA, ← hmu A hA]
  have hconstIntegral :
      ∫ _ : Param, eventPath A 0 ∂param = eventPath A 0 := by simp
  rw [← hconstIntegral, abs_sub_comm,
    ← integral_sub (hpathIntegrable A hA) hconst, hdecomp]
  calc
    |d * (∫ p, amplitude p ∂param) + ∫ p, rem p ∂param| ≤
        |d * (∫ p, amplitude p ∂param)| +
          |∫ p, rem p ∂param| := abs_add_le _ _
    _ ≤ Cone * |∫ p, amplitude p ∂param| +
          Ctwo * (∫ p, amplitude p ^ 2 ∂param) / 2 := by
      apply add_le_add
      · rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hfirst A hA) (abs_nonneg _)
      · exact hremBound

end

end LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep
