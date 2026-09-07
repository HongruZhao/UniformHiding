import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CenteredLikelihoodBellCalculus
import Mathlib.Tactic

/-!
# Low-order Bell identities for the literal centered likelihood

The fourth-order calculus file already proves that the literal likelihood is
`C^4` and positive near the origin.  This file records the corresponding
first-, second-, and third-order Bell identities.  They are ordinary
one-variable calculus and introduce no analytic or probabilistic input.
-/

open Function

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

private theorem iteratedDeriv_one_exp_comp_at (g : ℝ → ℝ) {x : ℝ}
    (hg : ContDiffAt ℝ 1 g x) :
    iteratedDeriv 1 (Real.exp ∘ g) x =
      Real.exp (g x) * iteratedDeriv 1 g x := by
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  have hg' : HasDerivAt g (deriv g x) x :=
    (hg.differentiableAt (by norm_num)).hasDerivAt
  simpa [Function.comp_def] using hg'.exp.deriv

private theorem iteratedDeriv_two_exp_comp_at (g : ℝ → ℝ) {x : ℝ}
    (hg : ContDiffAt ℝ 2 g x) :
    iteratedDeriv 2 (Real.exp ∘ g) x =
      Real.exp (g x) *
        (iteratedDeriv 1 g x ^ 2 + iteratedDeriv 2 g x) := by
  rw [iteratedDeriv_comp_two Real.contDiff_exp.contDiffAt hg]
  simp only [iteratedDeriv_eq_iterate, Real.iter_deriv_exp, Real.deriv_exp,
    iterate_one]
  ring

private theorem iteratedDeriv_three_exp_comp_at (g : ℝ → ℝ) {x : ℝ}
    (hg : ContDiffAt ℝ 3 g x) :
    iteratedDeriv 3 (Real.exp ∘ g) x =
      Real.exp (g x) * densityBellThree
        (iteratedDeriv 1 g x) (iteratedDeriv 2 g x)
        (iteratedDeriv 3 g x) := by
  rw [iteratedDeriv_comp_three Real.contDiff_exp.contDiffAt hg]
  simp only [iteratedDeriv_eq_iterate, Real.iter_deriv_exp, Real.deriv_exp,
    densityBellThree, iterate_one]
  ring

private theorem concreteCenteredLikelihoodCore_eq_exp_log_eventually
    {N K : ℕ} (hN : 1 ≤ N) (v : ComplexUnitSphere N)
    (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    let f : ℝ → ℝ := fun t ↦ concreteCenteredLikelihoodCore K v t A
    let g : ℝ → ℝ := fun t ↦ Real.log (f t)
    f =ᶠ[nhds 0] Real.exp ∘ g := by
  dsimp only
  let f : ℝ → ℝ := fun t ↦ concreteCenteredLikelihoodCore K v t A
  have hf : ContDiffAt ℝ 4 f 0 :=
    concreteCenteredLikelihoodCore_contDiffAt_four hN v A hsupport
  have hf0 : f 0 = 1 :=
    concreteCenteredLikelihoodCore_zero_on_support v A hsupport
  have hpos : ∀ᶠ t in nhds 0, 0 < f t :=
    continuousAt_const.eventually_lt hf.continuousAt (by simp [hf0])
  filter_upwards [hpos] with t ht
  simp only [Function.comp_apply]
  exact (Real.exp_log ht).symm

/-- First density derivative equals the first logarithmic derivative on the
open COE support. -/
theorem coeCorner_centeredDensityScore_one_eq_logScore
    {N K : ℕ} (hN : 1 ≤ N) (v : ComplexUnitSphere N)
    (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    concreteCenteredDensityScore 1 N K v A =
      concreteCenteredLogScore 1 N K v A := by
  let f : ℝ → ℝ := fun t ↦ concreteCenteredLikelihoodCore K v t A
  let g : ℝ → ℝ := fun t ↦ Real.log (f t)
  have hf : ContDiffAt ℝ 4 f 0 :=
    concreteCenteredLikelihoodCore_contDiffAt_four hN v A hsupport
  have hf0 : f 0 = 1 :=
    concreteCenteredLikelihoodCore_zero_on_support v A hsupport
  have hg : ContDiffAt ℝ 4 g 0 := hf.log (by simp [hf0])
  have hfg : f =ᶠ[nhds 0] Real.exp ∘ g :=
    concreteCenteredLikelihoodCore_eq_exp_log_eventually hN v A hsupport
  have hbell := iteratedDeriv_one_exp_comp_at g (hg.of_le (by norm_num))
  rw [← hfg.iteratedDeriv_eq 1] at hbell
  simp only [g, hf0, Real.log_one, Real.exp_zero, one_mul] at hbell
  simpa [concreteCenteredDensityScore, concreteCenteredLogScore, f, g]
    using hbell

/-- Second density derivative is the second Bell polynomial on support. -/
theorem coeCorner_centeredDensityScore_two_eq_Bell
    {N K : ℕ} (hN : 1 ≤ N) (v : ComplexUnitSphere N)
    (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    concreteCenteredDensityScore 2 N K v A =
      concreteCenteredLogScore 1 N K v A ^ 2 +
        concreteCenteredLogScore 2 N K v A := by
  let f : ℝ → ℝ := fun t ↦ concreteCenteredLikelihoodCore K v t A
  let g : ℝ → ℝ := fun t ↦ Real.log (f t)
  have hf : ContDiffAt ℝ 4 f 0 :=
    concreteCenteredLikelihoodCore_contDiffAt_four hN v A hsupport
  have hf0 : f 0 = 1 :=
    concreteCenteredLikelihoodCore_zero_on_support v A hsupport
  have hg : ContDiffAt ℝ 4 g 0 := hf.log (by simp [hf0])
  have hfg : f =ᶠ[nhds 0] Real.exp ∘ g :=
    concreteCenteredLikelihoodCore_eq_exp_log_eventually hN v A hsupport
  have hbell := iteratedDeriv_two_exp_comp_at g (hg.of_le (by norm_num))
  rw [← hfg.iteratedDeriv_eq 2] at hbell
  simp only [g, hf0, Real.log_one, Real.exp_zero, one_mul] at hbell
  simpa [concreteCenteredDensityScore, concreteCenteredLogScore, f, g]
    using hbell

/-- Third density derivative is the third Bell polynomial on support. -/
theorem coeCorner_centeredDensityScore_three_eq_Bell
    {N K : ℕ} (hN : 1 ≤ N) (v : ComplexUnitSphere N)
    (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    concreteCenteredDensityScore 3 N K v A =
      densityBellThree
        (concreteCenteredLogScore 1 N K v A)
        (concreteCenteredLogScore 2 N K v A)
        (concreteCenteredLogScore 3 N K v A) := by
  let f : ℝ → ℝ := fun t ↦ concreteCenteredLikelihoodCore K v t A
  let g : ℝ → ℝ := fun t ↦ Real.log (f t)
  have hf : ContDiffAt ℝ 4 f 0 :=
    concreteCenteredLikelihoodCore_contDiffAt_four hN v A hsupport
  have hf0 : f 0 = 1 :=
    concreteCenteredLikelihoodCore_zero_on_support v A hsupport
  have hg : ContDiffAt ℝ 4 g 0 := hf.log (by simp [hf0])
  have hfg : f =ᶠ[nhds 0] Real.exp ∘ g :=
    concreteCenteredLikelihoodCore_eq_exp_log_eventually hN v A hsupport
  have hbell := iteratedDeriv_three_exp_comp_at g (hg.of_le (by norm_num))
  rw [← hfg.iteratedDeriv_eq 3] at hbell
  simp only [g, hf0, Real.log_one, Real.exp_zero, one_mul] at hbell
  simpa [concreteCenteredDensityScore, concreteCenteredLogScore, f, g]
    using hbell

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
