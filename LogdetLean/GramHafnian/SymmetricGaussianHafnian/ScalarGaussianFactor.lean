import LogdetLean.GramHafnian.SymmetricGaussianHafnian.WeightedCompression
import LogdetLean.GramHafnian.ShiftedAnticoncentration.GaussianDisk

/-!
# The additional independent Gaussian edge

These identities integrate an actual independent `CN(0,1)` scalar, rather
than postulating the positive weight used by the interpolation argument.
The complex variance and Fourier normalization are exactly those of the
existing literal `circularGaussian` measure.
-/

open MeasureTheory ProbabilityTheory Complex
open scoped ENNReal BigOperators Real ComplexConjugate

namespace LogdetLean.GramHafnian.SymmetricGaussianHafnian

noncomputable section

/-- The positive characteristic factor of the edge joining the two
exposed vertices. -/
def scalarGaussianWeight (ell : ℂ) : ℝ :=
  Real.exp (-Complex.normSq ell / 4)

theorem scalarGaussianWeight_pos (ell : ℂ) :
    0 < scalarGaussianWeight ell := Real.exp_pos _

theorem scalarGaussianWeight_le_one (ell : ℂ) :
    scalarGaussianWeight ell ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  exact div_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr (Complex.normSq_nonneg ell)) (by norm_num)

@[fun_prop]
theorem continuous_scalarGaussianWeight : Continuous scalarGaussianWeight := by
  unfold scalarGaussianWeight
  fun_prop

@[fun_prop]
theorem measurable_scalarGaussianWeight : Measurable scalarGaussianWeight :=
  continuous_scalarGaussianWeight.measurable

/-- Exact integration over one standard circular Gaussian edge. -/
theorem integral_scalarGaussian_phase (ell : ℂ) :
    (∫ u : ℂ, Complex.exp ((((u * ell).re : ℝ) : ℂ) * Complex.I)
      ∂circularGaussian) = (scalarGaussianWeight ell : ℂ) := by
  have hphase (u : ℂ) : (u * ell).re = inner ℝ u (conj ell) := by
    simp [real_inner_eq_re_inner ℂ, Complex.mul_re]
    ring
  calc
    (∫ u : ℂ, Complex.exp ((((u * ell).re : ℝ) : ℂ) * Complex.I)
      ∂circularGaussian) = charFun circularGaussian (conj ell) := by
      rw [charFun_apply]
      apply integral_congr_ae
      filter_upwards [] with u
      rw [hphase]
    _ = (scalarGaussianWeight ell : ℂ) := by
      rw [charFun_circularGaussian, Complex.norm_conj]
      simp [scalarGaussianWeight, Complex.normSq_eq_norm_sq,
        Complex.ofReal_exp]

/-- Any independent remainder phase factors from the additional Gaussian
edge.  In the symmetric cofactor application the coefficient `ell` depends
only on the fixed background and its uncompressed Fourier weights. -/
theorem integral_independent_scalarGaussian_phase
    {P : Type*} [MeasurableSpace P]
    (mu : Measure P) [SFinite mu] (ell : ℂ) (phase : P → ℝ) :
    (∫ p : ℂ × P,
      Complex.exp (((((p.1 * ell).re + phase p.2) : ℝ) : ℂ) * Complex.I)
      ∂(circularGaussian.prod mu)) =
      (scalarGaussianWeight ell : ℂ) *
        ∫ p : P, Complex.exp (((phase p : ℝ) : ℂ) * Complex.I) ∂mu := by
  have hsplit :
      (fun p : ℂ × P ↦ Complex.exp
        (((((p.1 * ell).re + phase p.2) : ℝ) : ℂ) * Complex.I)) =
      (fun p : ℂ × P ↦
        Complex.exp ((((p.1 * ell).re : ℝ) : ℂ) * Complex.I) *
          Complex.exp (((phase p.2 : ℝ) : ℂ) * Complex.I)) := by
    funext p
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hsplit, integral_prod_mul
    (fun u : ℂ ↦ Complex.exp ((((u * ell).re : ℝ) : ℂ) * Complex.I))
    (fun p : P ↦ Complex.exp (((phase p : ℝ) : ℂ) * Complex.I)),
    integral_scalarGaussian_phase]

/-- Literal Gaussian product integral for a scalar-plus-bilinear phase. -/
theorem integral_scalar_plus_bilinearGaussian_phase
    {E A : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup A] [InnerProductSpace ℝ A]
    (ell : ℂ) (T : E →L[ℝ] E) (L : A →L[ℝ] E) (a b : A) :
    (∫ p : ℂ × (E × E), Complex.exp
      (((((p.1 * ell).re + (inner ℝ p.2.1 (T p.2.2) +
        inner ℝ p.2.1 (L b) + inner ℝ p.2.2 (L a))) : ℝ) : ℂ) * Complex.I)
      ∂(circularGaussian.prod ((stdGaussian E).prod (stdGaussian E)))) =
      weightedBilinearGaussianIntegral (scalarGaussianWeight ell) T L a b := by
  exact integral_independent_scalarGaussian_phase
    ((stdGaussian E).prod (stdGaussian E)) ell
    (fun p : E × E ↦ inner ℝ p.1 (T p.2) +
      inner ℝ p.1 (L b) + inner ℝ p.2 (L a))

end

end LogdetLean.GramHafnian.SymmetricGaussianHafnian
