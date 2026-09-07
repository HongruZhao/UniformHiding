import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H11_FourthBellNormalizationReducer
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# One-sided fourth-Bell normalization

The fourth density score has zero integral in every fixed projective fibre,
while the fourth logarithmic score is nonpositive on the COE support.  Hence
only the positive part of the lower Bell polynomial can contribute to the
positive part of the density score.  The zero-mean identity then gives

`integral |density score| = 2 * integral (density score)^+`.

This file isolates that measure-theoretic reduction and the exact scalar
sum-of-squares envelope used by the sharper fourth-score assembly.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- A one-sided version of the fixed-fibre Bell normalization reducer.

Unlike the symmetric triangle-inequality reduction, this theorem controls
the complete Bell score by twice an envelope for only the positive part of
the lower Bell polynomial. -/
theorem integrable_and_lpNorm_one_le_two_mul_integral_envelope_of_fiber_normalization_nonpos
    {Alpha Beta : Type*} [MeasurableSpace Alpha] [MeasurableSpace Beta]
    {mu : Measure Alpha} {nu : Measure Beta} [SFinite mu] [SFinite nu]
    {density score lower envelope : Alpha × Beta → ℝ}
    (hscoreMeas : AEStronglyMeasurable score (mu.prod nu))
    (hlower : Integrable lower (mu.prod nu))
    (henvelope : Integrable envelope (mu.prod nu))
    (hdensityInt : ∀ b, Integrable (fun a ↦ density (a, b)) mu)
    (hdensityZero : ∀ b, (∫ a, density (a, b) ∂mu) = 0)
    (hBell : ∀ b, (fun a ↦ density (a, b)) =ᵐ[mu]
      (fun a ↦ lower (a, b) + score (a, b)))
    (hscoreNonpos : ∀ b, ∀ᵐ a ∂mu, score (a, b) ≤ 0)
    (hlowerPosPartLe : ∀ b, ∀ᵐ a ∂mu,
      max (lower (a, b)) 0 ≤ envelope (a, b)) :
    Integrable (lower + score) (mu.prod nu) ∧
      lpNorm (lower + score) 1 (mu.prod nu) ≤
        2 * ∫ z, envelope z ∂(mu.prod nu) := by
  have hscoreInt :=
    (integrable_and_lpNorm_one_le_of_fiber_normalization_nonpos
      hscoreMeas hlower hdensityInt hdensityZero hBell hscoreNonpos).1
  have hbellInt : Integrable (lower + score) (mu.prod nu) :=
    hlower.add hscoreInt
  have hbellFiberNormInt : Integrable
      (fun b ↦ ∫ a, ‖(lower + score) (a, b)‖ ∂mu) nu :=
    hbellInt.integral_norm_prod_right
  have henvelopeFiberInt : Integrable
      (fun b ↦ ∫ a, envelope (a, b) ∂mu) nu :=
    henvelope.integral_prod_right
  have hfiberLe : ∀ᵐ b ∂nu,
      (∫ a, ‖(lower + score) (a, b)‖ ∂mu) ≤
        2 * ∫ a, envelope (a, b) ∂mu := by
    filter_upwards [hbellInt.prod_left_ae, henvelope.prod_left_ae] with b hbellB henvB
    have hbellEq : (fun a ↦ (lower + score) (a, b)) =ᵐ[mu]
        (fun a ↦ density (a, b)) := by
      filter_upwards [hBell b] with a ha
      simpa only [Pi.add_apply] using ha.symm
    have hbellZero : (∫ a, (lower + score) (a, b) ∂mu) = 0 := by
      rw [integral_congr_ae hbellEq]
      exact hdensityZero b
    have hposLe : ∀ᵐ a ∂mu,
        max ((lower + score) (a, b)) 0 ≤ envelope (a, b) := by
      filter_upwards [hscoreNonpos b, hlowerPosPartLe b] with a hscore henv
      have hsum : (lower + score) (a, b) ≤ lower (a, b) := by
        simp only [Pi.add_apply]
        linarith
      exact (max_le_max_right 0 hsum).trans henv
    calc
      (∫ a, ‖(lower + score) (a, b)‖ ∂mu) =
          ∫ a, |(lower + score) (a, b)| ∂mu := by
            simp only [Real.norm_eq_abs]
      _ = 2 * ∫ a, max ((lower + score) (a, b)) 0 ∂mu := by
        rw [integral_abs_eq_two_mul_integral_posPart_sub_integral hbellB,
          hbellZero]
        simp only [PosPart.posPart]
        ring
      _ ≤ 2 * ∫ a, envelope (a, b) ∂mu := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        simpa only [Real.coe_toNNReal'] using
          integral_mono_ae hbellB.real_toNNReal henvB hposLe
  refine ⟨hbellInt, ?_⟩
  rw [lpNorm_one_eq_integral_norm hbellInt.aestronglyMeasurable]
  calc
    (∫ z, ‖(lower + score) z‖ ∂(mu.prod nu)) =
        ∫ b, ∫ a, ‖(lower + score) (a, b)‖ ∂mu ∂nu := by
      exact integral_prod_symm (fun z ↦ ‖(lower + score) z‖) hbellInt.norm
    _ ≤ ∫ b, 2 * ∫ a, envelope (a, b) ∂mu ∂nu := by
      exact integral_mono_ae hbellFiberNormInt
        (henvelopeFiberInt.const_mul 2) hfiberLe
    _ = 2 * ∫ b, ∫ a, envelope (a, b) ∂mu ∂nu := by
      rw [integral_const_mul]
    _ = 2 * ∫ z, envelope z ∂(mu.prod nu) := by
      rw [integral_prod_symm envelope henvelope]

/-- The exact rational SOS envelope for the positive part of the lower
fourth Bell polynomial.  The coefficient choice is certified by

`48 * (envelope - polynomial without 4*x*z) = (16*x^2 - 9*y)^2`.
-/
theorem fourthBellLower_posPart_le_sos
    (x y z : ℝ) :
    max (x ^ 4 + 6 * x ^ 2 * y + 3 * y ^ 2 + 4 * x * z) 0 ≤
      (19 / 3 : ℝ) * x ^ 4 + (75 / 16 : ℝ) * y ^ 2 +
        4 * |x * z| := by
  have hbase :
      x ^ 4 + 6 * x ^ 2 * y + 3 * y ^ 2 ≤
        (19 / 3 : ℝ) * x ^ 4 + (75 / 16 : ℝ) * y ^ 2 := by
    nlinarith [sq_nonneg (16 * x ^ 2 - 9 * y)]
  apply max_le
  · calc
      x ^ 4 + 6 * x ^ 2 * y + 3 * y ^ 2 + 4 * x * z ≤
          (19 / 3 : ℝ) * x ^ 4 + (75 / 16 : ℝ) * y ^ 2 +
            4 * x * z := by linarith
      _ ≤ (19 / 3 : ℝ) * x ^ 4 + (75 / 16 : ℝ) * y ^ 2 +
            4 * |x * z| := by
        nlinarith [le_abs_self (x * z)]
  · positivity

/-- Concrete positive-part envelope used by the sharper fourth-score
assembly. -/
def concreteCenteredBellFourPositiveSOSEnvelope (N K : ℕ) :
    ConcreteMatrixState N × ComplexUnitSphere N → ℝ :=
  fun p ↦
    (19 / 3 : ℝ) * concreteCenteredEll 1 N K p ^ 4 +
      (75 / 16 : ℝ) * concreteCenteredEll 2 N K p ^ 2 +
      4 * |concreteCenteredEll 1 N K p * concreteCenteredEll 3 N K p|

theorem concreteCenteredBellFourLowerProduct_posPart_le_sosEnvelope
    {N K : ℕ} (p : ConcreteMatrixState N × ComplexUnitSphere N) :
    max (concreteCenteredBellFourLowerProduct N K p) 0 ≤
      concreteCenteredBellFourPositiveSOSEnvelope N K p := by
  simpa only [concreteCenteredBellFourLowerProduct,
    concreteCenteredBellFourPositiveSOSEnvelope] using
      fourthBellLower_posPart_le_sos
        (concreteCenteredEll 1 N K p)
        (concreteCenteredEll 2 N K p)
        (concreteCenteredEll 3 N K p)

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
