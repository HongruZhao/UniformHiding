import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.SecondMomentEngine

/-!
# Axiom-free H8 centering closure

This file proves all measure-theoretic and numerical algebra needed for H8.
The only later probability input is a centered `L^4` estimate for the first
beta-prime trace on its literal Gaussian source law.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]
variable {mu : Measure Omega}

/-- Exact power conversion `||X^2||_2 = ||X||_4^2`. -/
theorem lpNorm_sq_two_eq_sq_lpNorm_four
    {f : Omega → ℝ} (hf : MemLp f 4 mu) :
    lpNorm (fun omega ↦ f omega ^ 2) 2 mu = lpNorm f 4 mu ^ 2 := by
  have hsq := memLp_sq_two_of_memLp_four hf
  rw [lpNorm_eq_integral_norm_rpow_toReal (p := (2 : ENNReal))
      (by norm_num) (by norm_num) hsq.aestronglyMeasurable]
  rw [lpNorm_eq_integral_norm_rpow_toReal (p := (4 : ENNReal))
      (by norm_num) (by norm_num) hf.aestronglyMeasurable]
  norm_num
  have hintegral :
      (∫ omega, (f omega ^ 2) ^ 2 ∂mu) =
        ∫ omega, |f omega| ^ 4 ∂mu := by
    apply integral_congr_ae
    filter_upwards [] with omega
    rw [show |f omega| ^ 4 = (f omega ^ 2) ^ 2 by
      calc
        |f omega| ^ 4 = (|f omega| ^ 2) ^ 2 := by ring
        _ = (f omega ^ 2) ^ 2 := by rw [sq_abs]]
  rw [hintegral]
  have hnonneg : 0 ≤ ∫ omega, |f omega| ^ (4 : ℕ) ∂mu :=
    integral_nonneg fun _ ↦ by positivity
  simpa only [show (1 / 4 : ℝ) * (2 : ℕ) = 1 / 2 by norm_num] using
    Real.rpow_mul_natCast hnonneg (1 / 4 : ℝ) 2

/-- On a probability space, the raw second moment is the centered second
moment plus the square of the mean.  The only moment hypothesis is the
centered `L^4` condition later supplied by the Wishart layer. -/
theorem integral_sq_eq_integral_centered_sq_add_sq
    [IsProbabilityMeasure mu]
    {f : Omega → ℝ} {mean : ℝ}
    (hx : MemLp (fun omega ↦ f omega - mean) 4 mu)
    (hmean : (∫ omega, f omega ∂mu) = mean) :
    (∫ omega, f omega ^ 2 ∂mu) =
      (∫ omega, (f omega - mean) ^ 2 ∂mu) + mean ^ 2 := by
  let x : Omega → ℝ := fun omega ↦ f omega - mean
  have hxInt : Integrable x mu :=
    memLp_one_iff_integrable.mp (hx.mono_exponent (by norm_num))
  have hfInt : Integrable f mu := by
    refine (hxInt.add (integrable_const mean)).congr ?_
    filter_upwards [] with omega
    simp [x]
  have hxMean : (∫ omega, x omega ∂mu) = 0 := by
    dsimp only [x]
    rw [integral_sub hfInt (integrable_const mean), hmean]
    simp
  have hxSq : MemLp (fun omega ↦ x omega ^ 2) 2 mu :=
    memLp_sq_two_of_memLp_four hx
  have hxSqInt : Integrable (fun omega ↦ x omega ^ 2) mu :=
    memLp_one_iff_integrable.mp (hxSq.mono_exponent (by norm_num))
  have hlinearInt : Integrable (fun omega ↦ (2 * mean) * x omega) mu :=
    hxInt.const_mul (2 * mean)
  have hpoint : (fun omega ↦ f omega ^ 2) =
      fun omega ↦ x omega ^ 2 + (2 * mean) * x omega + mean ^ 2 := by
    funext omega
    dsimp only [x]
    ring
  rw [hpoint]
  rw [integral_add (f := fun z ↦ x z ^ 2 + (2 * mean) * x z)
      (g := fun _ ↦ mean ^ 2) (hxSqInt.add hlinearInt)
      (integrable_const (mean ^ 2)),
    integral_add (f := fun z ↦ x z ^ 2)
      (g := fun z ↦ (2 * mean) * x z) hxSqInt hlinearInt,
    integral_const_mul, hxMean]
  simp [x]

/-- Complete axiom-free H8 closure: a centered `L^4` estimate for `f`
implies both square-integrability and the explicit `L^2` estimate for the
centered raw square. -/
theorem centered_square_two_momentPackage_of_centered_four
    [IsProbabilityMeasure mu]
    {f : Omega → ℝ} {mean : ℝ}
    (hx : MemLp (fun omega ↦ f omega - mean) 4 mu)
    (hmean : (∫ omega, f omega ∂mu) = mean) :
    MemLp (fun omega ↦ f omega ^ 2 -
        ∫ z, f z ^ 2 ∂mu) 2 mu ∧
      lpNorm (fun omega ↦ f omega ^ 2 -
          ∫ z, f z ^ 2 ∂mu) 2 mu ≤
        2 * lpNorm (fun omega ↦ f omega - mean) 4 mu ^ 2 +
          2 * |mean| * lpNorm (fun omega ↦ f omega - mean) 4 mu := by
  let x : Omega → ℝ := fun omega ↦ f omega - mean
  let centeredSq : Omega → ℝ := fun omega ↦
    x omega ^ 2 - ∫ z, x z ^ 2 ∂mu
  let linear : Omega → ℝ := fun omega ↦ 2 * mean * x omega
  let target : Omega → ℝ := fun omega ↦
    f omega ^ 2 - ∫ z, f z ^ 2 ∂mu
  have hxSq : MemLp (fun omega ↦ x omega ^ 2) 2 mu :=
    memLp_sq_two_of_memLp_four hx
  have hcenteredSq : MemLp centeredSq 2 mu := by
    dsimp only [centeredSq]
    exact hxSq.sub (memLp_const _)
  have hxTwo : MemLp x 2 mu := hx.mono_exponent (by norm_num)
  have hlinear : MemLp linear 2 mu := by
    change MemLp ((2 * mean) • x) 2 mu
    exact hxTwo.const_smul (2 * mean)
  have hsecond := integral_sq_eq_integral_centered_sq_add_sq hx hmean
  have hdecomp : target = centeredSq + linear := by
    funext omega
    dsimp only [target, centeredSq, linear, x]
    exact centered_square_scalar_identity (by ring) hsecond
  have htarget : MemLp target 2 mu :=
    memLp_two_of_eq_add hcenteredSq hlinear hdecomp
  have hIntegralSq :
      |∫ z, x z ^ 2 ∂mu| ≤ lpNorm (fun z ↦ x z ^ 2) 2 mu := by
    calc
      |∫ z, x z ^ 2 ∂mu| ≤ ∫ z, |x z ^ 2| ∂mu :=
        abs_integral_le_integral_abs
      _ = lpNorm (fun z ↦ x z ^ 2) 1 mu := by
        rw [lpNorm_one_eq_integral_norm hxSq.aestronglyMeasurable]
        simp only [Real.norm_eq_abs]
      _ ≤ lpNorm (fun z ↦ x z ^ 2) 2 mu :=
        lpNorm_le_lpNorm_of_exponent_le_probability hxSq (by norm_num)
  have hcenteredSqNorm : lpNorm centeredSq 2 mu ≤
      2 * lpNorm x 4 mu ^ 2 := by
    calc
      lpNorm centeredSq 2 mu ≤
          lpNorm (fun z ↦ x z ^ 2) 2 mu +
            lpNorm (fun _ : Omega ↦ ∫ z, x z ^ 2 ∂mu) 2 mu := by
        dsimp only [centeredSq]
        exact lpNorm_sub_le hxSq (by norm_num)
      _ = lpNorm (fun z ↦ x z ^ 2) 2 mu +
          |∫ z, x z ^ 2 ∂mu| := by simp
      _ ≤ lpNorm (fun z ↦ x z ^ 2) 2 mu +
          lpNorm (fun z ↦ x z ^ 2) 2 mu := by gcongr
      _ = 2 * lpNorm x 4 mu ^ 2 := by
        rw [lpNorm_sq_two_eq_sq_lpNorm_four hx]
        ring
  have hxTwoFour : lpNorm x 2 mu ≤ lpNorm x 4 mu :=
    lpNorm_le_lpNorm_of_exponent_le_probability hx (by norm_num)
  have hlinearNorm : lpNorm linear 2 mu ≤
      2 * |mean| * lpNorm x 4 mu := by
    calc
      lpNorm linear 2 mu = |2 * mean| * lpNorm x 2 mu := by
        change lpNorm ((2 * mean) • x) 2 mu = _
        rw [lpNorm_const_smul]
        change ‖2 * mean‖ * lpNorm x 2 mu = _
        rw [Real.norm_eq_abs]
      _ = 2 * |mean| * lpNorm x 2 mu := by rw [abs_mul]; norm_num
      _ ≤ 2 * |mean| * lpNorm x 4 mu := by
        exact mul_le_mul_of_nonneg_left hxTwoFour (by positivity)
  refine ⟨by simpa only [target] using htarget, ?_⟩
  calc
    lpNorm (fun omega ↦ f omega ^ 2 -
        ∫ z, f z ^ 2 ∂mu) 2 mu = lpNorm target 2 mu := rfl
    _ ≤ lpNorm centeredSq 2 mu + lpNorm linear 2 mu :=
      lpNorm_two_le_of_eq_add hcenteredSq hlinear hdecomp
    _ ≤ 2 * lpNorm x 4 mu ^ 2 +
        2 * |mean| * lpNorm x 4 mu :=
      add_le_add hcenteredSqNorm hlinearNorm
    _ = 2 * lpNorm (fun omega ↦ f omega - mean) 4 mu ^ 2 +
        2 * |mean| * lpNorm (fun omega ↦ f omega - mean) 4 mu := rfl

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08
