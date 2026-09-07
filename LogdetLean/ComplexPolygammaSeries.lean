import LogdetLean.HigherCumulants
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Complex reciprocal-cube series on vertical lines

This module supplies the exact cancellation needed in the identity part of
the general-correlation Wishart transform.  It is the series form of the
complex tetragamma estimate used in Appendix `app:wishart` of the manuscript.

The mathematical identity is NIST DLMF 5.15.1, differentiated once.  The
inequality on a vertical line follows directly from the fundamental theorem
of calculus in the positive real parameter.  The proof is included here, so
no complex-polygamma library theorem is assumed.
-/

namespace LogdetLean

open Complex Set MeasureTheory
open scoped BigOperators Interval

noncomputable section

/-- The positive complex reciprocal-cube series.  Its negative is the usual
complex second polygamma function on the right half-plane. -/
def complexNegPsiTwoAxis (x u : ℝ) : ℂ :=
  2 * ∑' l : ℕ,
    (((x + (l : ℝ) : ℝ) : ℂ) + (u : ℂ) * Complex.I)⁻¹ ^ 3

private theorem norm_axis_affine_ge
    {x : ℝ} (hx : 0 < x) (u : ℝ) (l : ℕ) :
    x + (l : ℝ) ≤
      ‖((x + (l : ℝ) : ℝ) : ℂ) + (u : ℂ) * Complex.I‖ := by
  have h := Complex.abs_re_le_norm
    (((x + (l : ℝ) : ℝ) : ℂ) + (u : ℂ) * Complex.I)
  simpa [abs_of_pos (add_pos_of_pos_of_nonneg hx (Nat.cast_nonneg l))] using h

private theorem norm_axis_inv_pow_le
    {x : ℝ} (hx : 0 < x) (u : ℝ) (l r : ℕ) :
    ‖((((x + (l : ℝ) : ℝ) : ℂ) + (u : ℂ) * Complex.I)⁻¹ ^ r)‖ ≤
      1 / (x + (l : ℝ)) ^ r := by
  rw [norm_pow, norm_inv]
  have hpos : 0 < x + (l : ℝ) :=
    add_pos_of_pos_of_nonneg hx (Nat.cast_nonneg l)
  have hnormpos : 0 <
      ‖((x + (l : ℝ) : ℝ) : ℂ) + (u : ℂ) * Complex.I‖ := by
    exact lt_of_lt_of_le hpos (norm_axis_affine_ge hx u l)
  rw [one_div]
  simpa only [inv_pow] using
    (pow_le_pow_left₀ (inv_nonneg.mpr hnormpos.le)
      ((inv_le_inv₀ hnormpos hpos).2 (norm_axis_affine_ge hx u l)) r)

theorem summable_complex_axis_inv_cube
    {x : ℝ} (hx : 0 < x) (u : ℝ) :
    Summable (fun l : ℕ ↦
      ((((x + (l : ℝ) : ℝ) : ℂ) + (u : ℂ) * Complex.I)⁻¹ ^ 3)) := by
  apply Summable.of_norm_bounded
    (summable_shifted_reciprocal_pow hx (by norm_num : 1 < 3))
  intro l
  simpa [one_div] using norm_axis_inv_pow_le hx u l 3

@[simp]
theorem complexNegPsiTwoAxis_zero
    {x : ℝ} (_hx : 0 < x) :
    complexNegPsiTwoAxis x 0 = (negPsiTwoSeries x : ℂ) := by
  unfold complexNegPsiTwoAxis negPsiTwoSeries
  rw [Complex.ofReal_mul, Complex.ofReal_tsum]
  congr 1
  apply tsum_congr
  intro l
  push_cast
  simp [one_div]

private theorem hasDerivAt_axis_inv_cube_shape
    (u s : ℝ) (hs : 0 < s) :
    HasDerivAt
      (fun y : ℝ ↦
        ((((y : ℂ) + (u : ℂ) * Complex.I)⁻¹) ^ 3))
      (-3 * ((((s : ℂ) + (u : ℂ) * Complex.I)⁻¹) ^ 4)) s := by
  have hz : (s : ℂ) + (u : ℂ) * Complex.I ≠ 0 := by
    intro hzero
    have := congrArg Complex.re hzero
    simp at this
    linarith
  have hbase : HasDerivAt
      (fun y : ℝ ↦ (y : ℂ) + (u : ℂ) * Complex.I) 1 s :=
    ((hasDerivAt_id s).ofReal_comp.add_const _)
  have hinv := hbase.inv hz
  convert hinv.pow 3 using 1 <;> try rfl
  simp only [Nat.cast_ofNat, Nat.reduceSub, Pi.inv_apply]
  field_simp [hz]

private theorem hasDerivAt_axis_inv_four_shape
    (u s : ℝ) (hs : 0 < s) :
    HasDerivAt
      (fun y : ℝ ↦
        ((((y : ℂ) + (u : ℂ) * Complex.I)⁻¹) ^ 4))
      (-4 * ((((s : ℂ) + (u : ℂ) * Complex.I)⁻¹) ^ 5)) s := by
  have hz : (s : ℂ) + (u : ℂ) * Complex.I ≠ 0 := by
    intro hzero
    have := congrArg Complex.re hzero
    simp at this
    linarith
  have hbase : HasDerivAt
      (fun y : ℝ ↦ (y : ℂ) + (u : ℂ) * Complex.I) 1 s :=
    ((hasDerivAt_id s).ofReal_comp.add_const _)
  have hinv := hbase.inv hz
  convert hinv.pow 4 using 1 <;> try rfl
  simp only [Nat.cast_ofNat, Nat.reduceSub, Pi.inv_apply]
  field_simp [hz]

private theorem intervalIntegral_three_div_pow_four
    {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    (∫ s in x..y, 3 / s ^ 4) = 1 / x ^ 3 - 1 / y ^ 3 := by
  let f : ℝ → ℝ := fun s ↦ -(1 / s ^ 3)
  let f' : ℝ → ℝ := fun s ↦ 3 / s ^ 4
  have hderiv : ∀ s ∈ uIcc x y, HasDerivAt f (f' s) s := by
    intro s hs
    have hsxy : x ≤ s ∧ s ≤ y := by simpa [uIcc_of_le hxy] using hs
    have hs0 : s ≠ 0 := ne_of_gt (hx.trans_le hsxy.1)
    dsimp [f, f']
    have hbase : HasDerivAt (fun y : ℝ ↦ y) 1 s := hasDerivAt_id s
    have hinv := hbase.inv hs0
    have hraw := (hinv.pow 3).neg
    have hfunc : HasDerivAt (fun y : ℝ ↦ -(1 / y ^ 3))
        (-(3 * s⁻¹ ^ 2 * (-1 / s ^ 2))) s := by
      apply hraw.congr_of_eventuallyEq
      filter_upwards with y
      simp [one_div, inv_pow]
    apply hfunc.congr_deriv
    field_simp [hs0]
  have hcont : ContinuousOn f' (uIcc x y) := by
    apply continuousOn_of_forall_continuousAt
    intro s hs
    have hsxy : x ≤ s ∧ s ≤ y := by simpa [uIcc_of_le hxy] using hs
    have hs0 : s ≠ 0 := ne_of_gt (hx.trans_le hsxy.1)
    exact ((continuousAt_const.div (continuousAt_id.pow 4) (pow_ne_zero 4 hs0)))
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    hcont.intervalIntegrable
  dsimp [f, f'] at hFTC
  linarith

/-- A complex reciprocal-cube difference on a vertical line is no larger
than its positive-real-axis counterpart. -/
theorem norm_axis_inv_cube_sub_le_real
    {x y u : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    ‖((((x : ℂ) + (u : ℂ) * Complex.I)⁻¹) ^ 3) -
        ((((y : ℂ) + (u : ℂ) * Complex.I)⁻¹) ^ 3)‖ ≤
      1 / x ^ 3 - 1 / y ^ 3 := by
  let f : ℝ → ℂ := fun s ↦
    ((((s : ℂ) + (u : ℂ) * Complex.I)⁻¹) ^ 3)
  let f' : ℝ → ℂ := fun s ↦
    -3 * ((((s : ℂ) + (u : ℂ) * Complex.I)⁻¹) ^ 4)
  have hderiv : ∀ s ∈ uIcc x y, HasDerivAt f (f' s) s := by
    intro s hs
    have hsxy : x ≤ s ∧ s ≤ y := by simpa [uIcc_of_le hxy] using hs
    exact hasDerivAt_axis_inv_cube_shape u s (hx.trans_le hsxy.1)
  have hcont : ContinuousOn f' (uIcc x y) := by
    exact continuousOn_of_forall_continuousAt fun s hs ↦ by
      have hsxy : x ≤ s ∧ s ≤ y := by simpa [uIcc_of_le hxy] using hs
      dsimp [f']
      exact (hasDerivAt_axis_inv_four_shape u s
        (hx.trans_le hsxy.1)).continuousAt.const_mul (-3)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    hcont.intervalIntegrable
  have hnorm :
      ‖∫ s in x..y, f' s‖ ≤ ∫ s in x..y, 3 / s ^ 4 := by
    calc
      ‖∫ s in x..y, f' s‖ ≤ ∫ s in x..y, ‖f' s‖ :=
        intervalIntegral.norm_integral_le_integral_norm hxy
      _ ≤ ∫ s in x..y, 3 / s ^ 4 := by
        apply intervalIntegral.integral_mono_on hxy
        · exact hcont.norm.intervalIntegrable
        · exact (continuousOn_of_forall_continuousAt fun s hs ↦ by
            have hsxy : x ≤ s ∧ s ≤ y := by
              simpa [uIcc_of_le hxy] using hs
            have hs0 : s ≠ 0 := ne_of_gt (hx.trans_le hsxy.1)
            exact continuousAt_const.div (continuousAt_id.pow 4)
              (pow_ne_zero 4 hs0)).intervalIntegrable
        · intro s hs
          dsimp [f']
          rw [norm_mul, norm_neg, norm_pow, norm_inv]
          have hpos : 0 < s := hx.trans_le hs.1
          have hge : s ≤ ‖(s : ℂ) + (u : ℂ) * Complex.I‖ := by
            have h := Complex.abs_re_le_norm
              ((s : ℂ) + (u : ℂ) * Complex.I)
            simpa [abs_of_pos hpos] using h
          rw [div_eq_mul_inv]
          apply mul_le_mul
          · simp
          · have hnormpos : 0 < ‖(s : ℂ) + (u : ℂ) * Complex.I‖ :=
              hpos.trans_le hge
            simpa only [inv_pow] using
              (pow_le_pow_left₀ (inv_nonneg.mpr hnormpos.le)
                ((inv_le_inv₀ hnormpos hpos).2 hge) 4)
          · positivity
          · positivity
  rw [intervalIntegral_three_div_pow_four hx hxy] at hnorm
  rw [hFTC] at hnorm
  dsimp [f] at hnorm
  have hsymm :
      ‖((((x : ℂ) + (u : ℂ) * Complex.I)⁻¹) ^ 3) -
          ((((y : ℂ) + (u : ℂ) * Complex.I)⁻¹) ^ 3)‖ =
        ‖((((y : ℂ) + (u : ℂ) * Complex.I)⁻¹) ^ 3) -
          ((((x : ℂ) + (u : ℂ) * Complex.I)⁻¹) ^ 3)‖ := by
    rw [← norm_neg]
    congr 1
    ring
  rw [hsymm]
  exact hnorm

/-- Exact vertical-line cancellation for the complex second-polygamma
difference. -/
theorem norm_complexNegPsiTwoAxis_sub_le
    {x y u : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    ‖complexNegPsiTwoAxis x u - complexNegPsiTwoAxis y u‖ ≤
      negPsiTwoSeries x - negPsiTwoSeries y := by
  have hy : 0 < y := hx.trans_le hxy
  have hsx := summable_complex_axis_inv_cube hx u
  have hsy := summable_complex_axis_inv_cube hy u
  unfold complexNegPsiTwoAxis
  rw [← mul_sub, ← hsx.tsum_sub hsy]
  rw [norm_mul, norm_ofNat]
  have hnormsum : Summable (fun l : ℕ ↦
      ‖((((x + (l : ℝ) : ℝ) : ℂ) + (u : ℂ) * Complex.I)⁻¹ ^ 3) -
        ((((y + (l : ℝ) : ℝ) : ℂ) + (u : ℂ) * Complex.I)⁻¹ ^ 3)‖) := by
    apply Summable.of_nonneg_of_le
      (fun l ↦ norm_nonneg _)
      (fun l ↦ norm_axis_inv_cube_sub_le_real
        (add_pos_of_pos_of_nonneg hx (Nat.cast_nonneg l))
        (by linarith))
    exact ((summable_shifted_reciprocal_pow hx (by norm_num : 1 < 3)).sub
      (summable_shifted_reciprocal_pow hy (by norm_num : 1 < 3)))
  calc
    2 * ‖∑' l : ℕ,
        (((((x + (l : ℝ) : ℝ) : ℂ) + (u : ℂ) * Complex.I)⁻¹ ^ 3) -
          ((((y + (l : ℝ) : ℝ) : ℂ) + (u : ℂ) * Complex.I)⁻¹ ^ 3))‖ ≤
        2 * ∑' l : ℕ,
          ‖((((x + (l : ℝ) : ℝ) : ℂ) + (u : ℂ) * Complex.I)⁻¹ ^ 3) -
            ((((y + (l : ℝ) : ℝ) : ℂ) + (u : ℂ) * Complex.I)⁻¹ ^ 3)‖ := by
      gcongr
      exact norm_tsum_le_tsum_norm hnormsum
    _ ≤ 2 * ∑' l : ℕ,
          (1 / (x + (l : ℝ)) ^ 3 - 1 / (y + (l : ℝ)) ^ 3) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Summable.tsum_le_tsum
          (fun l ↦ norm_axis_inv_cube_sub_le_real
            (add_pos_of_pos_of_nonneg hx (Nat.cast_nonneg l))
            (by linarith))
          hnormsum
          ((summable_shifted_reciprocal_pow hx (by norm_num : 1 < 3)).sub
            (summable_shifted_reciprocal_pow hy (by norm_num : 1 < 3)))
    _ = negPsiTwoSeries x - negPsiTwoSeries y := by
      unfold negPsiTwoSeries
      rw [(summable_shifted_reciprocal_pow hx (by norm_num : 1 < 3)).tsum_sub
        (summable_shifted_reciprocal_pow hy (by norm_num : 1 < 3))]
      ring

private theorem norm_three_axis_add_two_le
    {y u : ℝ} (hy : 0 < y) :
    y * ‖3 * ((y : ℂ) + (u : ℂ) * Complex.I) + 2‖ ≤
      (3 * y + 2) * ‖(y : ℂ) + (u : ℂ) * Complex.I‖ := by
  apply (sq_le_sq₀ (mul_nonneg hy.le (norm_nonneg _))
    (mul_nonneg (by linarith) (norm_nonneg _))).mp
  rw [mul_pow, mul_pow, Complex.sq_norm, Complex.sq_norm]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.I_re, Complex.ofReal_im, Complex.I_im,
    mul_zero, sub_zero, mul_one, Complex.add_im, add_zero]
  norm_num at *
  ring_nf
  nlinarith [sq_nonneg u]

/-- One Euler--Maclaurin remainder term for the complex reciprocal-cube
series is bounded by the corresponding positive real term. -/
theorem norm_complex_axis_cube_residual_term_le
    {y u : ℝ} (hy : 0 < y) :
    ‖2 * ((((y : ℂ) + (u : ℂ) * Complex.I)⁻¹) ^ 3) -
      (((((y : ℂ) + (u : ℂ) * Complex.I)⁻¹) ^ 2) -
        (((((y + 1 : ℝ) : ℂ) + (u : ℂ) * Complex.I)⁻¹) ^ 2))‖ ≤
      2 / y ^ 3 - (1 / y ^ 2 - 1 / (y + 1) ^ 2) := by
  let z : ℂ := (y : ℂ) + (u : ℂ) * Complex.I
  have hz : z ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    dsimp [z] at hre
    simp at hre
    linarith
  have hz1 : z + 1 ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    dsimp [z] at hre
    norm_num at hre
    linarith
  have heq :
      2 * z⁻¹ ^ 3 - (z⁻¹ ^ 2 - (z + 1)⁻¹ ^ 2) =
        (3 * z + 2) / (z ^ 3 * (z + 1) ^ 2) := by
    field_simp [hz, hz1]
    ring
  rw [show ((((y + 1 : ℝ) : ℂ) + (u : ℂ) * Complex.I)) = z + 1 by
    dsimp [z]
    push_cast
    ring]
  rw [heq, norm_div, norm_mul, norm_pow, norm_pow]
  have hnum : y * ‖3 * z + 2‖ ≤ (3 * y + 2) * ‖z‖ := by
    simpa [z] using norm_three_axis_add_two_le hy (u := u)
  have hzge : y ≤ ‖z‖ := by
    have hre := Complex.abs_re_le_norm z
    simpa [z, abs_of_pos hy] using hre
  have hz1ge : y + 1 ≤ ‖z + 1‖ := by
    have hpos1 : 0 < y + 1 := by linarith
    have hre := Complex.abs_re_le_norm (z + 1)
    simpa [z, abs_of_pos hpos1] using hre
  have hnormz : 0 < ‖z‖ := hy.trans_le hzge
  have hnormz1 : 0 < ‖z + 1‖ :=
    (by linarith : 0 < y + 1).trans_le hz1ge
  have hrealEq :
      (3 * y + 2) / (y ^ 3 * (y + 1) ^ 2) =
        2 / y ^ 3 - (1 / y ^ 2 - 1 / (y + 1) ^ 2) := by
    field_simp [hy.ne', (by linarith : y + 1 ≠ 0)]
    ring
  rw [← hrealEq]
  have hnum' : ‖3 * z + 2‖ ≤ ((3 * y + 2) / y) * ‖z‖ := by
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ hy).2 (by simpa [mul_comm] using hnum)
  calc
    ‖3 * z + 2‖ / (‖z‖ ^ 3 * ‖z + 1‖ ^ 2) ≤
        (((3 * y + 2) / y) * ‖z‖) /
          (‖z‖ ^ 3 * ‖z + 1‖ ^ 2) := by
      exact div_le_div_of_nonneg_right hnum' (by positivity)
    _ = ((3 * y + 2) / y) / (‖z‖ ^ 2 * ‖z + 1‖ ^ 2) := by
      field_simp [hnormz.ne', hnormz1.ne']
    _ ≤ ((3 * y + 2) / y) / (y ^ 2 * (y + 1) ^ 2) := by
      apply div_le_div_of_nonneg_left
      · positivity
      · positivity
      · gcongr
    _ = (3 * y + 2) / (y ^ 3 * (y + 1) ^ 2) := by
      field_simp [hy.ne']

private def complexAxisSquareTerm (x u : ℝ) (l : ℕ) : ℂ :=
  ((((x + (l : ℝ) : ℝ) : ℂ) + (u : ℂ) * Complex.I)⁻¹) ^ 2

private theorem summable_complexAxisSquareTerm
    {x : ℝ} (hx : 0 < x) (u : ℝ) :
    Summable (complexAxisSquareTerm x u) := by
  apply Summable.of_norm_bounded
    (summable_shifted_reciprocal_pow hx (by norm_num : 1 < 2))
  intro l
  simpa [complexAxisSquareTerm, one_div] using
    norm_axis_inv_pow_le hx u l 2

private theorem tsum_complexAxisSquareTerm_sub_succ
    {x : ℝ} (hx : 0 < x) (u : ℝ) :
    ∑' l : ℕ, (complexAxisSquareTerm x u l -
      complexAxisSquareTerm x u (l + 1)) =
      ((((x : ℂ) + (u : ℂ) * Complex.I)⁻¹) ^ 2) := by
  have hs := summable_complexAxisSquareTerm hx u
  have hshift : Summable (fun l : ℕ ↦ complexAxisSquareTerm x u (l + 1)) :=
    hs.comp_injective (fun _ _ h ↦ Nat.add_right_cancel h)
  rw [hs.tsum_sub hshift]
  have hsplit := hs.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hsplit
  have hzero : complexAxisSquareTerm x u 0 =
      ((((x : ℂ) + (u : ℂ) * Complex.I)⁻¹) ^ 2) := by
    simp [complexAxisSquareTerm]
  rw [← hzero]
  exact sub_eq_iff_eq_add.mpr hsplit.symm

private def complexAxisCubeResidualTerm (x u : ℝ) (l : ℕ) : ℂ :=
  2 * ((((x + (l : ℝ) : ℝ) : ℂ) + (u : ℂ) * Complex.I)⁻¹) ^ 3 -
    (complexAxisSquareTerm x u l - complexAxisSquareTerm x u (l + 1))

private def realAxisCubeResidualTerm (x : ℝ) (l : ℕ) : ℝ :=
  2 / (x + (l : ℝ)) ^ 3 -
    (1 / (x + (l : ℝ)) ^ 2 - 1 / (x + (l : ℝ) + 1) ^ 2)

private theorem realAxisCubeResidualTerm_nonneg
    {x : ℝ} (hx : 0 < x) (l : ℕ) :
    0 ≤ realAxisCubeResidualTerm x l := by
  have hy : 0 < x + (l : ℝ) :=
    add_pos_of_pos_of_nonneg hx (Nat.cast_nonneg l)
  unfold realAxisCubeResidualTerm
  have heq :
      2 / (x + (l : ℝ)) ^ 3 -
        (1 / (x + (l : ℝ)) ^ 2 - 1 / (x + (l : ℝ) + 1) ^ 2) =
      (3 * (x + (l : ℝ)) + 2) /
        ((x + (l : ℝ)) ^ 3 * (x + (l : ℝ) + 1) ^ 2) := by
    field_simp [hy.ne', (by linarith : x + (l : ℝ) + 1 ≠ 0)]
    ring
  rw [heq]
  positivity

private theorem summable_realAxisCubeResidualTerm
    {x : ℝ} (hx : 0 < x) :
    Summable (realAxisCubeResidualTerm x) := by
  exact Summable.of_nonneg_of_le
    (realAxisCubeResidualTerm_nonneg hx)
    (fun l ↦ by
      unfold realAxisCubeResidualTerm
      have hy : 0 < x + (l : ℝ) :=
        add_pos_of_pos_of_nonneg hx (Nat.cast_nonneg l)
      have hsq : 0 ≤
          1 / (x + (l : ℝ)) ^ 2 -
            1 / (x + (l : ℝ) + 1) ^ 2 := by
        apply sub_nonneg.mpr
        apply one_div_le_one_div_of_le
        · exact pow_pos hy 2
        · nlinarith [sq_nonneg (x + (l : ℝ))]
      rw [show 2 * (1 / (x + (l : ℝ)) ^ 3) =
          2 / (x + (l : ℝ)) ^ 3 by ring]
      exact sub_le_self _ hsq)
    ((summable_shifted_reciprocal_pow hx
      (by norm_num : 1 < 3)).mul_left 2)

private theorem summable_complexAxisCubeResidualTerm
    {x : ℝ} (hx : 0 < x) (u : ℝ) :
    Summable (complexAxisCubeResidualTerm x u) := by
  apply Summable.of_norm_bounded
    (summable_realAxisCubeResidualTerm hx)
  intro l
  unfold complexAxisCubeResidualTerm complexAxisSquareTerm
    realAxisCubeResidualTerm
  simpa [add_assoc] using
    norm_complex_axis_cube_residual_term_le
      (add_pos_of_pos_of_nonneg hx (Nat.cast_nonneg l)) (u := u)

private theorem tsum_realAxisCubeResidualTerm
    {x : ℝ} (hx : 0 < x) :
    ∑' l : ℕ, realAxisCubeResidualTerm x l =
      negPsiTwoSeries x - 1 / x ^ 2 := by
  have hcub := summable_shifted_reciprocal_pow hx (by norm_num : 1 < 3)
  have hsq := summable_shifted_reciprocal_pow hx (by norm_num : 1 < 2)
  let squareTerm : ℕ → ℝ := fun l ↦ 1 / (x + (l : ℝ)) ^ 2
  have hsq' : Summable squareTerm := by simpa [squareTerm] using hsq
  have hshift : Summable (fun l : ℕ ↦ squareTerm (l + 1)) :=
    hsq'.comp_injective (fun _ _ h ↦ Nat.add_right_cancel h)
  have htelescope :
      ∑' l : ℕ, (squareTerm l - squareTerm (l + 1)) = 1 / x ^ 2 := by
    rw [hsq'.tsum_sub hshift]
    have hsplit := hsq'.sum_add_tsum_nat_add 1
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hsplit
    have hzero : squareTerm 0 = 1 / x ^ 2 := by simp [squareTerm]
    rw [← hzero]
    exact sub_eq_iff_eq_add.mpr hsplit.symm
  unfold realAxisCubeResidualTerm negPsiTwoSeries
  have hdiff : Summable (fun l : ℕ ↦
      squareTerm l - squareTerm (l + 1)) := hsq'.sub hshift
  rw [show (fun l : ℕ ↦ 2 / (x + (l : ℝ)) ^ 3 -
      (1 / (x + (l : ℝ)) ^ 2 - 1 / (x + (l : ℝ) + 1) ^ 2)) =
      (fun l : ℕ ↦ 2 * (1 / (x + (l : ℝ)) ^ 3) -
        (squareTerm l - squareTerm (l + 1))) by
    funext l
    simp only [squareTerm, Nat.cast_add, Nat.cast_one]
    ring]
  rw [(hcub.mul_left 2).tsum_sub hdiff, tsum_mul_left, htelescope]

private theorem tsum_complexAxisCubeResidualTerm
    {x : ℝ} (hx : 0 < x) (u : ℝ) :
    ∑' l : ℕ, complexAxisCubeResidualTerm x u l =
      complexNegPsiTwoAxis x u -
        ((((x : ℂ) + (u : ℂ) * Complex.I)⁻¹) ^ 2) := by
  have hcub := summable_complex_axis_inv_cube hx u
  have hsquare := summable_complexAxisSquareTerm hx u
  have hshift : Summable (fun l : ℕ ↦ complexAxisSquareTerm x u (l + 1)) :=
    hsquare.comp_injective (fun _ _ h ↦ Nat.add_right_cancel h)
  have hdiff : Summable (fun l : ℕ ↦
      complexAxisSquareTerm x u l - complexAxisSquareTerm x u (l + 1)) :=
    hsquare.sub hshift
  unfold complexAxisCubeResidualTerm complexNegPsiTwoAxis
  rw [(hcub.mul_left 2).tsum_sub hdiff, tsum_mul_left,
    tsum_complexAxisSquareTerm_sub_succ hx u]

/-- The complex Euler residual is bounded by the exact real residual. -/
theorem norm_complexNegPsiTwoAxis_sub_invSq_le
    {x u : ℝ} (hx : 0 < x) :
    ‖complexNegPsiTwoAxis x u -
      ((((x : ℂ) + (u : ℂ) * Complex.I)⁻¹) ^ 2)‖ ≤
      negPsiTwoSeries x - 1 / x ^ 2 := by
  rw [← tsum_complexAxisCubeResidualTerm hx u,
    ← tsum_realAxisCubeResidualTerm hx]
  exact (norm_tsum_le_tsum_norm
      (summable_complexAxisCubeResidualTerm hx u).norm).trans
    (Summable.tsum_le_tsum
      (fun l ↦ by
        unfold complexAxisCubeResidualTerm complexAxisSquareTerm
          realAxisCubeResidualTerm
        simpa [add_assoc] using
          norm_complex_axis_cube_residual_term_le
            (add_pos_of_pos_of_nonneg hx (Nat.cast_nonneg l)) (u := u))
      (summable_complexAxisCubeResidualTerm hx u).norm
      (summable_realAxisCubeResidualTerm hx))

/-- Explicit form of the preceding residual bound. -/
theorem norm_complexNegPsiTwoAxis_sub_invSq_le_two_div_cube
    {x u : ℝ} (hx : 0 < x) :
    ‖complexNegPsiTwoAxis x u -
      ((((x : ℂ) + (u : ℂ) * Complex.I)⁻¹) ^ 2)‖ ≤ 2 / x ^ 3 := by
  exact (norm_complexNegPsiTwoAxis_sub_invSq_le hx).trans
    (by linarith [negPsiTwoSeries_le_one_div_sq_add_two_div_cube hx])

/-- Third derivative of the identity-correlation Wishart logarithm, written
directly on the imaginary axis in a cancellation-preserving form. -/
def wishartIdentityThirdAxis (m p : ℕ) (u : ℝ) : ℂ :=
  ∑ j ∈ Finset.Icc 2 p,
      (-complexNegPsiTwoAxis (betaShapeA m j) u +
        complexNegPsiTwoAxis (betaShapeTotal m) u) +
    (p : ℂ) *
      (-complexNegPsiTwoAxis (betaShapeTotal m) u +
        (((betaShapeTotal m : ℂ) + (u : ℂ) * Complex.I)⁻¹) ^ 2)

/-- Exact global identity-part envelope from the manuscript:
`A_{m,p}+16p/m^3`. -/
theorem norm_wishartIdentityThirdAxis_le
    {m p : ℕ} (h : Admissible m p) (u : ℝ) :
    ‖wishartIdentityThirdAxis m p u‖ ≤
      nullASeries m p + 16 * (p : ℝ) / (m : ℝ) ^ 3 := by
  have hp : 2 ≤ p := h.1
  have hpm : p ≤ m := h.2
  have hmpos : 0 < m := by omega
  have hM : 0 < betaShapeTotal m := betaShapeTotal_pos h
  have hfinite :
      ‖∑ j ∈ Finset.Icc 2 p,
          (-complexNegPsiTwoAxis (betaShapeA m j) u +
            complexNegPsiTwoAxis (betaShapeTotal m) u)‖ ≤
        nullASeries m p := by
    calc
      ‖∑ j ∈ Finset.Icc 2 p,
          (-complexNegPsiTwoAxis (betaShapeA m j) u +
            complexNegPsiTwoAxis (betaShapeTotal m) u)‖ ≤
          ∑ j ∈ Finset.Icc 2 p,
            ‖-complexNegPsiTwoAxis (betaShapeA m j) u +
              complexNegPsiTwoAxis (betaShapeTotal m) u‖ :=
        norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.Icc 2 p,
          (negPsiTwoSeries (betaShapeA m j) -
            negPsiTwoSeries (betaShapeTotal m)) := by
        apply Finset.sum_le_sum
        intro j hj
        have haj := betaShapeA_pos_of_mem_Icc h.2 hj
        have hajM := betaShapeA_lt_total (m := m) (Finset.mem_Icc.mp hj).1
        calc
          ‖-complexNegPsiTwoAxis (betaShapeA m j) u +
              complexNegPsiTwoAxis (betaShapeTotal m) u‖ =
              ‖complexNegPsiTwoAxis (betaShapeA m j) u -
                complexNegPsiTwoAxis (betaShapeTotal m) u‖ := by
            rw [← norm_neg]
            congr 1
            ring
          _ ≤ negPsiTwoSeries (betaShapeA m j) -
                negPsiTwoSeries (betaShapeTotal m) :=
            norm_complexNegPsiTwoAxis_sub_le haj hajM.le (u := u)
      _ = nullASeries m p := rfl
  have hres :
      ‖-complexNegPsiTwoAxis (betaShapeTotal m) u +
          (((betaShapeTotal m : ℂ) + (u : ℂ) * Complex.I)⁻¹) ^ 2‖ ≤
        2 / (betaShapeTotal m) ^ 3 := by
    rw [show -complexNegPsiTwoAxis (betaShapeTotal m) u +
          (((betaShapeTotal m : ℂ) + (u : ℂ) * Complex.I)⁻¹) ^ 2 =
        -(complexNegPsiTwoAxis (betaShapeTotal m) u -
          (((betaShapeTotal m : ℂ) + (u : ℂ) * Complex.I)⁻¹) ^ 2) by ring,
      norm_neg]
    exact norm_complexNegPsiTwoAxis_sub_invSq_le_two_div_cube hM (u := u)
  unfold wishartIdentityThirdAxis
  calc
    ‖(∑ j ∈ Finset.Icc 2 p,
        (-complexNegPsiTwoAxis (betaShapeA m j) u +
          complexNegPsiTwoAxis (betaShapeTotal m) u)) +
      (p : ℂ) *
        (-complexNegPsiTwoAxis (betaShapeTotal m) u +
          (((betaShapeTotal m : ℂ) + (u : ℂ) * Complex.I)⁻¹) ^ 2)‖ ≤
        ‖∑ j ∈ Finset.Icc 2 p,
          (-complexNegPsiTwoAxis (betaShapeA m j) u +
            complexNegPsiTwoAxis (betaShapeTotal m) u)‖ +
        ‖(p : ℂ) *
          (-complexNegPsiTwoAxis (betaShapeTotal m) u +
            (((betaShapeTotal m : ℂ) + (u : ℂ) * Complex.I)⁻¹) ^ 2)‖ :=
      norm_add_le _ _
    _ ≤ nullASeries m p + (p : ℝ) *
        (2 / (betaShapeTotal m) ^ 3) := by
      rw [norm_mul, Complex.norm_natCast]
      gcongr
    _ = nullASeries m p + 16 * (p : ℝ) / (m : ℝ) ^ 3 := by
      unfold betaShapeTotal
      field_simp [show (m : ℝ) ≠ 0 by exact_mod_cast hmpos.ne']
      ring

end

end LogdetLean
