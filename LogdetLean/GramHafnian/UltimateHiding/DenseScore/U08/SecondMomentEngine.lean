import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.Tactic

/-!
# Axiom-free centering and second-moment engine for U08

This module contains only general measure-theoretic algebra.  In particular,
it contains no Wishart, beta-prime, COE, or project-specific scientific input.
The two closure lemmas isolate exactly what must be supplied by the missing
fourth inverse-Wishart moment layer.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]
variable {mu : Measure Omega}

/-- Monotonicity of the real `L^p` seminorm on a probability space. -/
theorem lpNorm_le_lpNorm_of_exponent_le_probability
    [IsProbabilityMeasure mu]
    {p q : ENNReal} {f : Omega → ℝ}
    (hf : MemLp f q mu) (hpq : p ≤ q) :
    lpNorm f p mu ≤ lpNorm f q mu := by
  rw [← toReal_eLpNorm (hf.mono_exponent hpq).aestronglyMeasurable,
    ← toReal_eLpNorm hf.aestronglyMeasurable]
  exact ENNReal.toReal_mono hf.eLpNorm_ne_top
    (eLpNorm_le_eLpNorm_of_exponent_le hpq hf.aestronglyMeasurable)

/-- Squaring sends `L^4` to `L^2`. -/
theorem memLp_sq_two_of_memLp_four {f : Omega → ℝ}
    (hf : MemLp f 4 mu) :
    MemLp (fun omega ↦ f omega ^ 2) 2 mu := by
  have htriple : ENNReal.HolderTriple 4 4 2 :=
    ENNReal.HolderTriple.of_toReal (by constructor <;> norm_num)
  let _ := htriple
  simpa only [pow_two] using hf.mul' hf

/-- The elementary identity behind H8, separated from all integration. -/
theorem centered_square_scalar_identity
    {t x mean secondMoment centeredSecondMoment : ℝ}
    (ht : t = x + mean)
    (hsecond : secondMoment = centeredSecondMoment + mean ^ 2) :
    t ^ 2 - secondMoment =
      (x ^ 2 - centeredSecondMoment) + 2 * mean * x := by
  rw [ht, hsecond]
  ring

/-- The elementary two-level fluctuation decomposition behind H10. -/
theorem centered_two_level_scalar_identity
    {value conditionalMean totalMean : ℝ} :
    value - totalMean =
      (value - conditionalMean) + (conditionalMean - totalMean) := by
  ring

/-- If a quantity is the sum of two square-integrable fluctuation pieces,
then it is square-integrable. -/
theorem memLp_two_of_eq_add
    {f innovation drift : Omega → ℝ}
    (hinnovation : MemLp innovation 2 mu)
    (hdrift : MemLp drift 2 mu)
    (hdecomp : f = innovation + drift) :
    MemLp f 2 mu := by
  rw [hdecomp]
  exact hinnovation.add hdrift

/-- Minkowski closure for a two-level fluctuation decomposition. -/
theorem lpNorm_two_le_of_eq_add
    {f innovation drift : Omega → ℝ}
    (hinnovation : MemLp innovation 2 mu)
    (_hdrift : MemLp drift 2 mu)
    (hdecomp : f = innovation + drift) :
    lpNorm f 2 mu ≤ lpNorm innovation 2 mu + lpNorm drift 2 mu := by
  rw [hdecomp]
  exact lpNorm_add_le hinnovation (by norm_num)

/-- Dimension-explicit H10 arithmetic: the two human-proof components
`2^23 N^2` and `2^28 N^2` fit below `2^29 N^2`. -/
theorem h10_component_constants_le
    {N : ℕ} :
    (2 : ℝ) ^ 23 * (N : ℝ) ^ 2 +
        (2 : ℝ) ^ 28 * (N : ℝ) ^ 2 ≤
      (2 : ℝ) ^ 29 * (N : ℝ) ^ 2 := by
  norm_num
  nlinarith [sq_nonneg (N : ℝ)]

/-- The `2^12` first inverse-trace fluctuation implies the human-proof
`2^26 N` bound for the centered square of that trace. -/
theorem h10_denominator_trace_square_constant
    {N A : ℝ} (hN : 1 ≤ N) (hA : 0 ≤ A)
    (hA_le : A ≤ (2 : ℝ) ^ 12) :
    2 * A ^ 2 + 2 * N * A ≤ (2 : ℝ) ^ 26 * N := by
  have hsq : A ^ 2 ≤ ((2 : ℝ) ^ 12) ^ 2 := by nlinarith
  have hmul : N * A ≤ N * (2 : ℝ) ^ 12 := by
    exact mul_le_mul_of_nonneg_left hA_le (by linarith)
  norm_num at hsq hmul ⊢
  nlinarith

/-- Exact H10 denominator arithmetic after the two inverse-trace bounds:
`n(n+1) 2^16 N⁰ + n 2^26 N`, with `n=N+1`, fits below
`2^28 N²`. -/
theorem h10_denominator_drift_constant
    {N : ℝ} (hN : 1 ≤ N) :
    (N + 1) * (N + 2) * (2 : ℝ) ^ 16 +
        (N + 1) * ((2 : ℝ) ^ 26 * N) ≤
      (2 : ℝ) ^ 28 * N ^ 2 := by
  norm_num
  nlinarith [sq_nonneg (N - 1)]

/-- The intermediate H10 constant is below the exposed `2^40` constant. -/
theorem h10_intermediate_constant_le_dense_constant
    {N : ℕ} :
    (2 : ℝ) ^ 29 * (N : ℝ) ^ 2 ≤
      (2 : ℝ) ^ 40 * (N : ℝ) ^ 2 := by
  norm_num
  nlinarith [sq_nonneg (N : ℝ)]

/-- Dimension-explicit H8 arithmetic after the centered-square identity.
The hypotheses are exactly the numerical consequences
`||X||_4 ≤ 2^14 N` and `mean ≤ 2 N^2`. -/
theorem h8_numeric_closure
    {N A mean : ℝ}
    (hN : 1 ≤ N)
    (hA : 0 ≤ A)
    (hA_le : A ≤ (2 : ℝ) ^ 14 * N)
    (hmean : 0 ≤ mean)
    (hmean_le : mean ≤ 2 * N ^ 2) :
    2 * A ^ 2 + 2 * mean * A ≤ (2 : ℝ) ^ 30 * N ^ 3 := by
  have hsq : A ^ 2 ≤ ((2 : ℝ) ^ 14 * N) ^ 2 := by nlinarith
  have hmul : mean * A ≤ (2 * N ^ 2) * ((2 : ℝ) ^ 14 * N) :=
    mul_le_mul hmean_le hA_le hA (by positivity)
  have hterm1 : 2 * A ^ 2 ≤ 2 * ((2 : ℝ) ^ 14 * N) ^ 2 :=
    mul_le_mul_of_nonneg_left hsq (by norm_num)
  have hterm2 : 2 * (mean * A) ≤
      2 * ((2 * N ^ 2) * ((2 : ℝ) ^ 14 * N)) :=
    mul_le_mul_of_nonneg_left hmul (by norm_num)
  calc
    2 * A ^ 2 + 2 * mean * A ≤
        2 * ((2 : ℝ) ^ 14 * N) ^ 2 +
          2 * ((2 * N ^ 2) * ((2 : ℝ) ^ 14 * N)) := by
      exact add_le_add hterm1 (by simpa [mul_assoc] using hterm2)
    _ ≤ (2 : ℝ) ^ 30 * N ^ 3 := by
      nlinarith [sq_nonneg (N - 1)]

/-- The intermediate H8 constant is below the exposed `2^40` constant. -/
theorem h8_intermediate_constant_le_dense_constant
    {N : ℕ} :
    (2 : ℝ) ^ 30 * (N : ℝ) ^ 3 ≤
      (2 : ℝ) ^ 40 * (N : ℝ) ^ 3 := by
  norm_num
  have hcube : 0 ≤ (N : ℝ) ^ 3 := by positivity
  nlinarith

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08
