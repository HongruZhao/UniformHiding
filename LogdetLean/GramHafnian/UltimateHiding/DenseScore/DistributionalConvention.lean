import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Congruence
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Forward distributional score convention

We fix one sign convention and use it throughout the dense score branch.
For an orbit `rho_t` and a measure `mu`, the forward distributional generator
is

`X mu = d/dt|_(t=0) (rho_t)_* mu`.

A function `s` is its density score when, for every real test function `phi`,

`d/dt|_0 integral phi(rho_t x) dmu(x) = integral phi(x) * s(x) dmu(x)`.

Thus the notation `X mu = s mu` has a **plus** sign.  The inverse-time orbit
has score `-s`; this is proved below.  These are definitions and consequences,
not existence claims for the COE law.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

/-- Test-function definition of the forward distributional score. -/
def HasForwardDistributionalScore
    {Omega : Type*} [MeasurableSpace Omega]
    (orbit : ℝ → Omega → Omega) (mu : Measure Omega)
    (score : Omega → ℝ) : Prop :=
  ∀ phi : Omega → ℝ,
    HasDerivAt
      (fun t ↦ ∫ x, phi (orbit t x) ∂mu)
      (∫ x, phi x * score x ∂mu) 0

/-- Reversing the time parameter reverses the score sign. -/
theorem HasForwardDistributionalScore.timeReversal
    {Omega : Type*} [MeasurableSpace Omega]
    {orbit : ℝ → Omega → Omega} {mu : Measure Omega}
    {score : Omega → ℝ}
    (h : HasForwardDistributionalScore orbit mu score) :
    HasForwardDistributionalScore
      (fun t x ↦ orbit (-t) x) mu (fun x ↦ -score x) := by
  intro phi
  have hneg : HasDerivAt (fun t : ℝ ↦ -t) (-1) 0 :=
    (hasDerivAt_id (x := (0 : ℝ))).neg
  have hcomp := HasDerivAt.comp_of_eq (𝕜 := ℝ) (𝕜' := ℝ) (0 : ℝ)
    (h phi) hneg (by norm_num)
  simpa only [Function.comp_def, neg_zero, mul_neg, integral_neg, neg_mul,
    mul_one, mul_neg_one] using hcomp

/-- A pointwise invariant test integral has zero forward score. -/
theorem hasForwardDistributionalScore_zero_of_integral_invariant
    {Omega : Type*} [MeasurableSpace Omega]
    {orbit : ℝ → Omega → Omega} {mu : Measure Omega}
    (hinv : ∀ (phi : Omega → ℝ) (t : ℝ),
      ∫ x, phi (orbit t x) ∂mu = ∫ x, phi x ∂mu) :
    HasForwardDistributionalScore orbit mu (fun _ ↦ 0) := by
  intro phi
  have hconst :
      HasDerivAt (fun _ : ℝ ↦ ∫ x, phi x ∂mu) 0 0 :=
    hasDerivAt_const 0 _
  have horbit := hconst.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun t ↦ hinv phi t)
  simpa only [mul_zero, integral_zero] using horbit

/-- The fixed forward score convention specialized to the literal
transpose-congruence exponential flow. -/
def HasForwardCongruenceScore {N : ℕ}
    (A : ComplexSquareMatrix N)
    (mu : Measure (ComplexSquareMatrix N))
    (score : ComplexSquareMatrix N → ℝ) : Prop :=
  HasForwardDistributionalScore (transposeCongruenceFlow A) mu score

/-- The same matrix orbit with `t` replaced by `-t` has the opposite score. -/
theorem HasForwardCongruenceScore.timeReversal {N : ℕ}
    {A : ComplexSquareMatrix N}
    {mu : Measure (ComplexSquareMatrix N)}
    {score : ComplexSquareMatrix N → ℝ}
    (h : HasForwardCongruenceScore A mu score) :
    HasForwardDistributionalScore
      (fun t C ↦ transposeCongruenceFlow A (-t) C)
      mu (fun C ↦ -score C) := by
  exact HasForwardDistributionalScore.timeReversal h

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
