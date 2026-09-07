import LogdetLean.GramHafnian.UltimateHiding.DenseScore.COELikelihoodAlgebra
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-!
# Generic scalar Bell bridge for H7

This is an assumption-free one-variable calculus layer shared by the
rank-one and central H7 lines.  It turns logarithmic jets through order four
into the corresponding density derivatives.  No COE, determinant, or
project-specific scientific input occurs here.

The file was written after the host resource stop and remains UNVERIFIED
until an exact single-module build is permitted.
-/

open Function
open scoped Topology

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

private theorem h7_iteratedDeriv_three_exp_comp_at
    (g : ℝ → ℝ) {x : ℝ} (hg : ContDiffAt ℝ 3 g x) :
    iteratedDeriv 3 (Real.exp ∘ g) x =
      Real.exp (g x) * densityBellThree
        (iteratedDeriv 1 g x)
        (iteratedDeriv 2 g x)
        (iteratedDeriv 3 g x) := by
  rw [iteratedDeriv_comp_three Real.contDiff_exp.contDiffAt hg]
  simp only [iteratedDeriv_eq_iterate, Real.iter_deriv_exp,
    Real.deriv_exp, densityBellThree, iterate_one]
  ring

private theorem h7_contDiffAt_iteratedDeriv_right_real {f : ℝ → ℝ}
    {n : WithTop ℕ∞} {m i : ℕ} {x : ℝ} (hf : ContDiffAt ℝ n f x)
    (hmi : m + i ≤ n) : ContDiffAt ℝ m (iteratedDeriv i f) x := by
  rw [iteratedDeriv_eq_equiv_comp]
  exact (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin i) ℝ).symm.contDiff.contDiffAt.comp x
    (hf.iteratedFDeriv_right hmi)

private theorem h7_iteratedDeriv_four_exp_comp_at
    (g : ℝ → ℝ) {x : ℝ} (hg : ContDiffAt ℝ 4 g x) :
    iteratedDeriv 4 (Real.exp ∘ g) x =
      Real.exp (g x) * densityBellFour
        (iteratedDeriv 1 g x)
        (iteratedDeriv 2 g x)
        (iteratedDeriv 3 g x)
        (iteratedDeriv 4 g x) := by
  have h3 : iteratedDeriv 3 (Real.exp ∘ g) =ᶠ[nhds x] fun y ↦
      Real.exp (g y) * deriv g y ^ 3 +
      3 * Real.exp (g y) * iteratedDeriv 2 g y * deriv g y +
      Real.exp (g y) * iteratedDeriv 3 g y := by
    filter_upwards [hg.eventually (by norm_num)] with y hy
    rw [iteratedDeriv_comp_three Real.contDiff_exp.contDiffAt
      (hy.of_le (by norm_num))]
    simp only [iteratedDeriv_eq_iterate, Real.iter_deriv_exp,
      Real.deriv_exp]
  rw [show 4 = 3 + 1 by norm_num, iteratedDeriv_succ, h3.deriv_eq]
  have hg0 : DifferentiableAt ℝ g x := hg.differentiableAt (by norm_num)
  have hg1 : DifferentiableAt ℝ (iteratedDeriv 1 g) x :=
    (h7_contDiffAt_iteratedDeriv_right_real hg (m := 1) (i := 1)
      (by norm_num)).differentiableAt (by norm_num)
  have hg2 : DifferentiableAt ℝ (iteratedDeriv 2 g) x :=
    (h7_contDiffAt_iteratedDeriv_right_real hg (m := 1) (i := 2)
      (by norm_num)).differentiableAt (by norm_num)
  have hg3 : DifferentiableAt ℝ (iteratedDeriv 3 g) x :=
    (h7_contDiffAt_iteratedDeriv_right_real hg (m := 1) (i := 3)
      (by norm_num)).differentiableAt (by norm_num)
  have he : HasDerivAt (fun y ↦ Real.exp (g y))
      (Real.exp (g x) * deriv g x) x := hg0.hasDerivAt.exp
  have hd1 : HasDerivAt (deriv g) (deriv (deriv g) x) x := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hg1.hasDerivAt
  have hd2 : HasDerivAt (deriv (deriv g))
      (deriv (deriv (deriv g)) x) x := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hg2.hasDerivAt
  have hd3 : HasDerivAt (deriv (deriv (deriv g)))
      (deriv (deriv (deriv (deriv g))) x) x := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hg3.hasDerivAt
  have hcalc := ((he.mul (hd1.pow 3)).add
      (((he.const_mul 3).mul hd2).mul hd1)).add (he.mul hd3)
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  have hfun :
      (fun y ↦ Real.exp (g y) * deriv g y ^ 3 +
        3 * Real.exp (g y) * deriv (deriv g) y * deriv g y +
        Real.exp (g y) * deriv (deriv (deriv g)) y) =
      ((fun y ↦ Real.exp (g y)) * deriv g ^ 3 +
        (fun y ↦ 3 * Real.exp (g y)) * deriv (deriv g) * deriv g +
        (fun y ↦ Real.exp (g y)) * deriv (deriv (deriv g))) := by
    funext y
    simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply]
  rw [hfun, hcalc.deriv]
  simp only [Pi.mul_apply, Pi.pow_apply, densityBellFour]
  norm_num
  ring

/-- For any positive `C^3` scalar density, the third derivative is its value
times the third Bell polynomial in the logarithmic derivatives. -/
theorem iteratedDeriv_three_eq_densityBell_log_of_contDiffAt
    (f : ℝ → ℝ) {x : ℝ} (hf : ContDiffAt ℝ 3 f x)
    (hfx : 0 < f x) :
    iteratedDeriv 3 f x =
      f x * densityBellThree
        (iteratedDeriv 1 (fun t ↦ Real.log (f t)) x)
        (iteratedDeriv 2 (fun t ↦ Real.log (f t)) x)
        (iteratedDeriv 3 (fun t ↦ Real.log (f t)) x) := by
  let g : ℝ → ℝ := fun t ↦ Real.log (f t)
  have hg : ContDiffAt ℝ 3 g x := hf.log hfx.ne'
  have hpos : ∀ᶠ t in nhds x, 0 < f t :=
    continuousAt_const.eventually_lt hf.continuousAt hfx
  have hfg : f =ᶠ[nhds x] Real.exp ∘ g := by
    filter_upwards [hpos] with t ht
    simp only [Function.comp_apply, g]
    exact (Real.exp_log ht).symm
  have hbell := h7_iteratedDeriv_three_exp_comp_at g hg
  rw [← hfg.iteratedDeriv_eq 3] at hbell
  simpa only [g, Real.exp_log hfx] using hbell

/-- Normalized version used by likelihood ratios, whose value at the origin
is one. -/
theorem iteratedDeriv_three_eq_densityBell_log_of_contDiffAt_one
    (f : ℝ → ℝ) {x : ℝ} (hf : ContDiffAt ℝ 3 f x)
    (hfx : f x = 1) :
    iteratedDeriv 3 f x =
      densityBellThree
        (iteratedDeriv 1 (fun t ↦ Real.log (f t)) x)
        (iteratedDeriv 2 (fun t ↦ Real.log (f t)) x)
        (iteratedDeriv 3 (fun t ↦ Real.log (f t)) x) := by
  have hpos : 0 < f x := by rw [hfx]; norm_num
  simpa only [hfx, one_mul] using
    iteratedDeriv_three_eq_densityBell_log_of_contDiffAt f hf hpos

/-- For any positive `C^4` scalar density, the fourth derivative is its value
times the fourth Bell polynomial in the logarithmic derivatives. -/
theorem iteratedDeriv_four_eq_densityBell_log_of_contDiffAt
    (f : ℝ → ℝ) {x : ℝ} (hf : ContDiffAt ℝ 4 f x)
    (hfx : 0 < f x) :
    iteratedDeriv 4 f x =
      f x * densityBellFour
        (iteratedDeriv 1 (fun t ↦ Real.log (f t)) x)
        (iteratedDeriv 2 (fun t ↦ Real.log (f t)) x)
        (iteratedDeriv 3 (fun t ↦ Real.log (f t)) x)
        (iteratedDeriv 4 (fun t ↦ Real.log (f t)) x) := by
  let g : ℝ → ℝ := fun t ↦ Real.log (f t)
  have hg : ContDiffAt ℝ 4 g x := hf.log hfx.ne'
  have hpos : ∀ᶠ t in nhds x, 0 < f t :=
    continuousAt_const.eventually_lt hf.continuousAt hfx
  have hfg : f =ᶠ[nhds x] Real.exp ∘ g := by
    filter_upwards [hpos] with t ht
    simp only [Function.comp_apply, g]
    exact (Real.exp_log ht).symm
  have hbell := h7_iteratedDeriv_four_exp_comp_at g hg
  rw [← hfg.iteratedDeriv_eq 4] at hbell
  simpa only [g, Real.exp_log hfx] using hbell

/-- Normalized fourth-order version used by likelihood ratios. -/
theorem iteratedDeriv_four_eq_densityBell_log_of_contDiffAt_one
    (f : ℝ → ℝ) {x : ℝ} (hf : ContDiffAt ℝ 4 f x)
    (hfx : f x = 1) :
    iteratedDeriv 4 f x =
      densityBellFour
        (iteratedDeriv 1 (fun t ↦ Real.log (f t)) x)
        (iteratedDeriv 2 (fun t ↦ Real.log (f t)) x)
        (iteratedDeriv 3 (fun t ↦ Real.log (f t)) x)
        (iteratedDeriv 4 (fun t ↦ Real.log (f t)) x) := by
  have hpos : 0 < f x := by rw [hfx]; norm_num
  simpa only [hfx, one_mul] using
    iteratedDeriv_four_eq_densityBell_log_of_contDiffAt f hf hpos

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
