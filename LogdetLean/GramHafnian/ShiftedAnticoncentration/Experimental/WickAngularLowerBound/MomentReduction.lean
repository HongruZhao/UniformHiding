import LogdetLean.GramHafnian.ShiftedAnticoncentration.Experimental.RadialLowerBound.LiteralEndpointAlt
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# The rigorous moment reduction behind the Wick angular lower bound

This file contains only consequences that are already available for the
literal angular law.  In particular, it does **not** postulate the new Wick
square-root estimate.  The final theorem makes that one still-missing
analytic estimate an explicit hypothesis.

This separation is useful for auditing: once the square-root estimate is
proved for `angularMeasure` and `angularEnergy`, the desired angular
condition-number lower bound follows without any further probabilistic
assumption.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Real

namespace LogdetLean.GramHafnian

noncomputable section

namespace WickAngularLowerBound

/-- The scalar appearing as the mean absolute coordinate of a uniform point
on the complex unit sphere. -/
def sphereCoordinateAbsMean (k : ℕ) : ℝ :=
  Real.Gamma (3 / 2) * Real.Gamma k / Real.Gamma (k + 1 / 2)

/-- The proposed Wick upper bound on the first square-root moment of the
literal angular cofactor energy. -/
def wickSqrtMomentBound (k n : ℕ) : ℝ :=
  sphereCoordinateAbsMean k ^ (2 * n - 1) *
    2 ^ n * Real.Gamma (n + (k : ℝ) / 2) / Real.Gamma ((k : ℝ) / 2)

/-- The multiplicative lower-bound expression before taking logarithms. -/
def wickAngularRatio (k n : ℕ) : ℝ :=
  (closedFirstMoment k n / (k : ℝ) ^ (2 * n - 1)) /
    wickSqrtMomentBound k n ^ 2

/-- Extended-valued version of the angular condition number.  The inverse
moment is deliberately a `lintegral`, so divergence is represented by `⊤`
rather than by the default value of a nonintegrable Bochner integral. -/
def angularConditionNumberENN {n k : ℕ} (hn : 1 ≤ n) : ENNReal :=
  (∫⁻ u, ENNReal.ofReal
      (RadialLowerBoundAlt.angularEnergy (n := n) (k := k) hn u)
      ∂(RadialLowerBoundAlt.angularMeasure hn)) *
    ∫⁻ u, (ENNReal.ofReal
      (RadialLowerBoundAlt.angularEnergy (n := n) (k := k) hn u))⁻¹
      ∂(RadialLowerBoundAlt.angularMeasure hn)

/-- Extended-valued Wick lower-bound expression. -/
def wickAngularRatioENN (k n : ℕ) : ENNReal :=
  ENNReal.ofReal
      (closedFirstMoment k n / (k : ℝ) ^ (2 * n - 1)) /
    ENNReal.ofReal (wickSqrtMomentBound k n) ^ 2

/-- Exact first moment of the literal angular energy. -/
theorem integral_angularEnergy_eq_closedFirstMoment_div_pow
    {n k : ℕ} (hn : 1 ≤ n) (hk : 0 < k) :
    (∫ u, RadialLowerBoundAlt.angularEnergy (n := n) (k := k) hn u
        ∂(RadialLowerBoundAlt.angularMeasure hn)) =
      closedFirstMoment k n / (k : ℝ) ^ (2 * n - 1) := by
  have hsplit :=
    RadialLowerBoundAlt.integral_pastCofactorV_eq_angular_mul_radial hn hk
  rw [integral_pastCofactorV_eq_closedFirstMoment hn hk,
    RadialLowerBoundAlt.integral_squaredRadiusProduct hn hk] at hsplit
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  rw [hsplit]
  field_simp

/-- The exact first angular moment in nonnegative-integral form. -/
theorem lintegral_angularEnergy_eq_closedFirstMoment_div_pow
    {n k : ℕ} (hn : 1 ≤ n) (hk : 0 < k) :
    (∫⁻ u, ENNReal.ofReal
        (RadialLowerBoundAlt.angularEnergy (n := n) (k := k) hn u)
        ∂(RadialLowerBoundAlt.angularMeasure hn)) =
      ENNReal.ofReal
        (closedFirstMoment k n / (k : ℝ) ^ (2 * n - 1)) := by
  have hW := RadialLowerBoundAlt.integrable_angularEnergy hn hk
  have hnonneg : 0 ≤ᵐ[RadialLowerBoundAlt.angularMeasure
      (n := n) (k := k) hn]
      RadialLowerBoundAlt.angularEnergy (n := n) (k := k) hn := by
    exact ae_of_all _ fun u ↦ pastCofactorV_nonneg hn _
  rw [← ofReal_integral_eq_lintegral_ofReal hW hnonneg,
    integral_angularEnergy_eq_closedFirstMoment_div_pow hn hk]

/-- The square root of the literal angular energy is integrable. -/
theorem integrable_sqrt_angularEnergy
    {n k : ℕ} (hn : 1 ≤ n) (hk : 0 < k) :
    Integrable
      (fun u ↦ Real.sqrt
        (RadialLowerBoundAlt.angularEnergy (n := n) (k := k) hn u))
      (RadialLowerBoundAlt.angularMeasure hn) := by
  letI : ∀ _ : RadialLowerBoundAlt.CofactorIdx n hn,
      IsProbabilityMeasure (circularGaussianSphereProbability k) :=
    fun _ ↦ ⟨circularGaussianSphereProbability_apply_univ hk⟩
  letI : IsProbabilityMeasure
      (RadialLowerBoundAlt.angularMeasure (k := k) hn) := by
    unfold RadialLowerBoundAlt.angularMeasure
    infer_instance
  have hW := RadialLowerBoundAlt.integrable_angularEnergy hn hk
  apply Integrable.mono' (integrable_const (1 : ℝ) |>.add hW)
    (Real.continuous_sqrt.comp_aestronglyMeasurable
      (RadialLowerBoundAlt.measurable_angularEnergy hn).aestronglyMeasurable)
  filter_upwards [] with u
  have hw := pastCofactorV_nonneg hn
    (RadialLowerBoundAlt.directionColumns hn u)
  change 0 ≤ RadialLowerBoundAlt.angularEnergy hn u at hw
  change |Real.sqrt (RadialLowerBoundAlt.angularEnergy hn u)| ≤
    1 + RadialLowerBoundAlt.angularEnergy hn u
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  nlinarith [Real.sq_sqrt hw,
    sq_nonneg (Real.sqrt (RadialLowerBoundAlt.angularEnergy hn u) - 1)]

/-- The square-root angular moment is strictly positive; this follows from
the already verified positive first angular moment and does not require an
inverse-moment theorem. -/
theorem integral_sqrt_angularEnergy_pos
    {n k : ℕ} (hn : 1 ≤ n) (hk : 0 < k) :
    0 < ∫ u, Real.sqrt
      (RadialLowerBoundAlt.angularEnergy (n := n) (k := k) hn u)
      ∂(RadialLowerBoundAlt.angularMeasure hn) := by
  have hsqrtInt := integrable_sqrt_angularEnergy hn hk
  have hsqrtNonneg : 0 ≤ᵐ[RadialLowerBoundAlt.angularMeasure
      (n := n) (k := k) hn]
      (fun u ↦ Real.sqrt (RadialLowerBoundAlt.angularEnergy hn u)) :=
    ae_of_all _ fun _ ↦ Real.sqrt_nonneg _
  have hmeanPos : 0 <
      ∫ u, RadialLowerBoundAlt.angularEnergy (n := n) (k := k) hn u
        ∂(RadialLowerBoundAlt.angularMeasure hn) := by
    rw [integral_angularEnergy_eq_closedFirstMoment_div_pow hn hk]
    exact div_pos (closedFirstMoment_pos k n hk) (by positivity)
  apply lt_of_le_of_ne
    (integral_nonneg_of_ae hsqrtNonneg)
  intro hzero
  have hae := (integral_eq_zero_iff_of_nonneg_ae hsqrtNonneg hsqrtInt).mp
    hzero.symm
  have hWzero :
      RadialLowerBoundAlt.angularEnergy (n := n) (k := k) hn =ᵐ[
        RadialLowerBoundAlt.angularMeasure hn] 0 := by
    filter_upwards [hae] with u hu
    have hw := pastCofactorV_nonneg hn
      (RadialLowerBoundAlt.directionColumns hn u)
    change 0 ≤ RadialLowerBoundAlt.angularEnergy hn u at hw
    have hsquare := Real.sq_sqrt hw
    rw [hu] at hsquare
    simpa using hsquare.symm
  have : (∫ u, RadialLowerBoundAlt.angularEnergy
      (n := n) (k := k) hn u
      ∂(RadialLowerBoundAlt.angularMeasure hn)) = 0 :=
    integral_eq_zero_of_ae hWzero
  exact hmeanPos.ne' this

/-- The square-root moment written as a `lintegral` of the `ENNReal`
square root. -/
theorem lintegral_rpow_half_angularEnergy_eq_ofReal_integral_sqrt
    {n k : ℕ} (hn : 1 ≤ n) (hk : 0 < k) :
    (∫⁻ u, (ENNReal.ofReal
        (RadialLowerBoundAlt.angularEnergy (n := n) (k := k) hn u)) ^
          (1 / 2 : ℝ)
        ∂(RadialLowerBoundAlt.angularMeasure hn)) =
      ENNReal.ofReal
        (∫ u, Real.sqrt (RadialLowerBoundAlt.angularEnergy
          (n := n) (k := k) hn u)
          ∂(RadialLowerBoundAlt.angularMeasure hn)) := by
  have hsqrtInt := integrable_sqrt_angularEnergy hn hk
  have hsqrtNonneg : 0 ≤ᵐ[RadialLowerBoundAlt.angularMeasure
      (n := n) (k := k) hn]
      (fun u ↦ Real.sqrt (RadialLowerBoundAlt.angularEnergy hn u)) :=
    ae_of_all _ fun _ ↦ Real.sqrt_nonneg _
  rw [ofReal_integral_eq_lintegral_ofReal hsqrtInt hsqrtNonneg]
  apply lintegral_congr
  intro u
  have hw := pastCofactorV_nonneg hn
    (RadialLowerBoundAlt.directionColumns hn u)
  change 0 ≤ RadialLowerBoundAlt.angularEnergy hn u at hw
  rw [ENNReal.ofReal_rpow_of_nonneg hw (by norm_num),
    ← Real.sqrt_eq_rpow]

/-- A probability-space inequality used in the Wick argument.  If `W` and
`W⁻¹` are integrable and `W>0` almost surely, then

`(E sqrt W)^2 * E(W⁻¹) ≥ 1`.

This is the combination of Cauchy--Schwarz for `sqrt W` and `1/sqrt W`
with Cauchy--Schwarz for `1/sqrt W` and `1`. -/
theorem one_le_sq_integral_sqrt_mul_integral_inv
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (W : Omega → ℝ)
    (hWmeas : AEStronglyMeasurable W mu)
    (hWpos : ∀ᵐ w ∂mu, 0 < W w)
    (hW : Integrable W mu)
    (hWinv : Integrable (fun w ↦ (W w)⁻¹) mu) :
    1 ≤ (∫ w, Real.sqrt (W w) ∂mu) ^ 2 *
      ∫ w, (W w)⁻¹ ∂mu := by
  let Y : Omega → ℝ := fun w ↦ Real.sqrt (W w)
  have hYmeas : AEStronglyMeasurable Y mu :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hWmeas
  have hYpos : ∀ᵐ w ∂mu, 0 < Y w := by
    filter_upwards [hWpos] with w hw
    exact Real.sqrt_pos.2 hw
  have hY : Integrable Y mu := by
    apply Integrable.mono' (integrable_const (1 : ℝ) |>.add hW)
      hYmeas
    filter_upwards [hWpos] with w hw
    change |Real.sqrt (W w)| ≤ 1 + W w
    rw [abs_of_pos (Real.sqrt_pos.2 hw)]
    nlinarith [Real.sq_sqrt hw.le,
      sq_nonneg (Real.sqrt (W w) - 1)]
  have hYinv : Integrable (fun w ↦ (Y w)⁻¹) mu := by
    apply Integrable.mono' (integrable_const (1 : ℝ) |>.add hWinv)
      hYmeas.aemeasurable.inv.aestronglyMeasurable
    filter_upwards [hWpos] with w hw
    have hs : 0 < Real.sqrt (W w) := Real.sqrt_pos.2 hw
    have hinv : 0 ≤ (W w)⁻¹ := inv_nonneg.mpr hw.le
    change |(Real.sqrt (W w))⁻¹| ≤ 1 + (W w)⁻¹
    rw [abs_of_pos (inv_pos.mpr hs)]
    have hsquare : (Real.sqrt (W w))⁻¹ ^ 2 = (W w)⁻¹ := by
      rw [inv_pow, Real.sq_sqrt hw.le]
    nlinarith [sq_nonneg ((Real.sqrt (W w))⁻¹ - 1), hsquare]
  have hfirst : 1 ≤ (∫ w, Y w ∂mu) * ∫ w, (Y w)⁻¹ ∂mu :=
    one_le_integral_mul_integral_inv mu Y hYmeas hYpos hY hYinv
  have hsqInv : Integrable (fun w ↦ ((Y w)⁻¹) ^ 2) mu := by
    apply hWinv.congr
    filter_upwards [hWpos] with w hw
    dsimp [Y]
    rw [inv_pow, Real.sq_sqrt hw.le]
  have hconst : MemLp (fun _w : Omega ↦ (1 : ℝ)) 2 mu := by
    simpa using (memLp_const (μ := mu) (1 : ℝ) :
      MemLp (fun _w : Omega ↦ (1 : ℝ)) 2 mu)
  have hinvLp : MemLp (fun w ↦ (Y w)⁻¹) 2 mu :=
    (memLp_two_iff_integrable_sq
      hYmeas.aemeasurable.inv.aestronglyMeasurable).2 hsqInv
  have hholder : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := mu) (f := fun w ↦ (Y w)⁻¹) (g := fun _w ↦ (1 : ℝ))
    hholder
    (hYpos.mono fun _ hw ↦ inv_nonneg.mpr hw.le)
    (ae_of_all mu fun _ ↦ by norm_num)
    (by simpa using hinvLp) (by simpa using hconst)
  have hInvNonneg : 0 ≤ ∫ w, (Y w)⁻¹ ∂mu :=
    integral_nonneg_of_ae (hYpos.mono fun _ hw ↦ inv_nonneg.mpr hw.le)
  have hYmeanNonneg : 0 ≤ ∫ w, Y w ∂mu :=
    integral_nonneg_of_ae (hYpos.mono fun _ hw ↦ hw.le)
  have hcs' : (∫ w, (Y w)⁻¹ ∂mu) ^ 2 ≤
      ∫ w, (W w)⁻¹ ∂mu := by
    have hmu : (∫ _w : Omega, (1 : ℝ) ∂mu) = 1 := by simp
    have hpow : (∫ w, ((Y w)⁻¹) ^ (2 : ℝ) ∂mu) =
        ∫ w, (W w)⁻¹ ∂mu := by
      simp_rw [Real.rpow_two]
      exact integral_congr_ae (hWpos.mono fun w hw ↦ by
        dsimp [Y]
        rw [inv_pow, Real.sq_sqrt hw.le])
    simp only [mul_one] at hcs
    have hcsSimplified :
        (∫ w, (Y w)⁻¹ ∂mu) ≤
          Real.sqrt (∫ w, (W w)⁻¹ ∂mu) := by
      rw [hpow] at hcs
      simpa [Real.sqrt_eq_rpow] using hcs
    have hInvMomentNonneg : 0 ≤ ∫ w, (W w)⁻¹ ∂mu :=
      integral_nonneg_of_ae (hWpos.mono fun _ hw ↦ inv_nonneg.mpr hw.le)
    have hrhsNonneg : 0 ≤ Real.sqrt
        (∫ w, (W w)⁻¹ ∂mu) := Real.sqrt_nonneg _
    have hsq := (sq_le_sq₀ hInvNonneg hrhsNonneg).2 (by
      simpa [abs_of_nonneg hInvNonneg] using hcsSimplified)
    simpa [Real.sq_sqrt hInvMomentNonneg] using hsq
  have hfirstSq := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hfirst 2
  rw [one_pow, mul_pow] at hfirstSq
  calc
    1 ≤ (∫ w, Y w ∂mu) ^ 2 * (∫ w, (Y w)⁻¹ ∂mu) ^ 2 := hfirstSq
    _ ≤ (∫ w, Y w ∂mu) ^ 2 * ∫ w, (W w)⁻¹ ∂mu :=
      mul_le_mul_of_nonneg_left hcs' (sq_nonneg _)

/-- Cauchy--Schwarz for an `ENNReal` observable on a probability space. -/
theorem sq_lintegral_le_lintegral_sq
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (Z : Omega → ENNReal) (hZ : AEMeasurable Z mu) :
    (∫⁻ w, Z w ∂mu) ^ 2 ≤ ∫⁻ w, Z w ^ 2 ∂mu := by
  have hholder : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq
    (μ := mu) (f := Z) (g := fun _w ↦ (1 : ENNReal))
    hholder hZ aemeasurable_const
  have hsimp : (∫⁻ w, Z w ∂mu) ≤
      (∫⁻ w, Z w ^ 2 ∂mu) ^ (1 / 2 : ℝ) := by
    simpa using h
  have hsquare := pow_le_pow_left₀
    (show (0 : ENNReal) ≤ ∫⁻ w, Z w ∂mu by positivity) hsimp 2
  have hrpow_sq (x : ENNReal) : (x ^ (1 / 2 : ℝ)) ^ (2 : ℕ) = x := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  calc
    (∫⁻ w, Z w ∂mu) ^ 2 ≤
        ((∫⁻ w, Z w ^ 2 ∂mu) ^ (1 / 2 : ℝ)) ^ 2 := hsquare
    _ = ∫⁻ w, Z w ^ 2 ∂mu := hrpow_sq _

/-- Extended-valued square-root reduction.  The reciprocal moment may be
infinite; no integrability hypothesis is used. -/
theorem one_le_sq_lintegral_sqrt_mul_lintegral_inv
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (X : Omega → ENNReal) (hX : AEMeasurable X mu)
    (hXtop : ∀ᵐ w ∂mu, X w ≠ ⊤)
    (hEsqrt0 : (∫⁻ w, (X w) ^ (1 / 2 : ℝ) ∂mu) ≠ 0) :
    1 ≤ (∫⁻ w, (X w) ^ (1 / 2 : ℝ) ∂mu) ^ 2 *
      ∫⁻ w, (X w)⁻¹ ∂mu := by
  let Y : Omega → ENNReal := fun w ↦ (X w) ^ (1 / 2 : ℝ)
  have hY : AEMeasurable Y mu := hX.pow_const _
  have hYtop : ∀ᵐ w ∂mu, Y w ≠ ⊤ := by
    filter_upwards [hXtop] with w hw
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) hw
  have hfirst := measure_sq_le_lintegral_mul_lintegral_inv
    mu Y hY hYtop hEsqrt0
  have hmu : mu Set.univ = 1 := measure_univ
  rw [hmu, one_pow] at hfirst
  have hsecond := sq_lintegral_le_lintegral_sq mu (fun w ↦ (Y w)⁻¹) hY.inv
  have hsq : (fun w ↦ (Y w)⁻¹ ^ 2) = (fun w ↦ (X w)⁻¹) := by
    funext w
    dsimp [Y]
    rw [← ENNReal.rpow_neg, ← ENNReal.rpow_natCast,
      ← ENNReal.rpow_mul]
    norm_num
    exact ENNReal.rpow_neg_one _
  rw [hsq] at hsecond
  have hsquare := pow_le_pow_left₀ (show (0 : ENNReal) ≤ 1 by positivity)
    hfirst 2
  rw [one_pow, mul_pow] at hsquare
  calc
    1 ≤ (∫⁻ w, Y w ∂mu) ^ 2 * (∫⁻ w, (Y w)⁻¹ ∂mu) ^ 2 := hsquare
    _ ≤ (∫⁻ w, Y w ∂mu) ^ 2 * ∫⁻ w, (X w)⁻¹ ∂mu :=
      mul_le_mul_of_nonneg_left hsecond (by positivity)

/-- Unconditional-in-integrability reduction for the literal angular law.
The reciprocal moment is extended valued, so the conclusion remains valid
when it diverges.  The sole analytic input is the displayed Wick square-root
bound. -/
theorem wickAngularRatioENN_le_angularConditionNumberENN_of_sqrt_bound
    {n k : ℕ} (hn : 1 ≤ n) (hk : 0 < k)
    (hsqrt :
      (∫ u, Real.sqrt (RadialLowerBoundAlt.angularEnergy
          (n := n) (k := k) hn u)
        ∂(RadialLowerBoundAlt.angularMeasure hn)) ≤
        wickSqrtMomentBound k n)
    (hbound : 0 < wickSqrtMomentBound k n) :
    wickAngularRatioENN k n ≤ angularConditionNumberENN (k := k) hn := by
  letI : ∀ _ : RadialLowerBoundAlt.CofactorIdx n hn,
      IsProbabilityMeasure (circularGaussianSphereProbability k) :=
    fun _ ↦ ⟨circularGaussianSphereProbability_apply_univ hk⟩
  letI : IsProbabilityMeasure
      (RadialLowerBoundAlt.angularMeasure (k := k) hn) := by
    unfold RadialLowerBoundAlt.angularMeasure
    infer_instance
  let X : (RadialLowerBoundAlt.CofactorIdx n hn →
      RadialLowerBoundAlt.Direction k) → ENNReal :=
    fun u ↦ ENNReal.ofReal (RadialLowerBoundAlt.angularEnergy hn u)
  have hX : AEMeasurable X (RadialLowerBoundAlt.angularMeasure hn) :=
    (RadialLowerBoundAlt.measurable_angularEnergy hn).ennreal_ofReal.aemeasurable
  have hXtop : ∀ᵐ u ∂(RadialLowerBoundAlt.angularMeasure
      (n := n) (k := k) hn), X u ≠ ⊤ :=
    ae_of_all _ fun _ ↦ ENNReal.ofReal_ne_top
  have hEsqrt0 :
      (∫⁻ u, (X u) ^ (1 / 2 : ℝ)
        ∂(RadialLowerBoundAlt.angularMeasure hn)) ≠ 0 := by
    rw [show (∫⁻ u, (X u) ^ (1 / 2 : ℝ)
        ∂(RadialLowerBoundAlt.angularMeasure hn)) =
      ENNReal.ofReal
        (∫ u, Real.sqrt (RadialLowerBoundAlt.angularEnergy hn u)
          ∂(RadialLowerBoundAlt.angularMeasure hn)) by
      simpa [X] using
        lintegral_rpow_half_angularEnergy_eq_ofReal_integral_sqrt hn hk]
    exact (ENNReal.ofReal_pos.mpr
      (integral_sqrt_angularEnergy_pos hn hk)).ne'
  have hcore := one_le_sq_lintegral_sqrt_mul_lintegral_inv
    (RadialLowerBoundAlt.angularMeasure (n := n) (k := k) hn)
    X hX hXtop hEsqrt0
  have hEsqrtLe :
      (∫⁻ u, (X u) ^ (1 / 2 : ℝ)
        ∂(RadialLowerBoundAlt.angularMeasure hn)) ≤
      ENNReal.ofReal (wickSqrtMomentBound k n) := by
    rw [show (∫⁻ u, (X u) ^ (1 / 2 : ℝ)
        ∂(RadialLowerBoundAlt.angularMeasure hn)) =
      ENNReal.ofReal
        (∫ u, Real.sqrt (RadialLowerBoundAlt.angularEnergy hn u)
          ∂(RadialLowerBoundAlt.angularMeasure hn)) by
      simpa [X] using
        lintegral_rpow_half_angularEnergy_eq_ofReal_integral_sqrt hn hk]
    exact ENNReal.ofReal_le_ofReal hsqrt
  have hsq :
      (∫⁻ u, (X u) ^ (1 / 2 : ℝ)
        ∂(RadialLowerBoundAlt.angularMeasure hn)) ^ 2 ≤
      ENNReal.ofReal (wickSqrtMomentBound k n) ^ 2 :=
    pow_le_pow_left' hEsqrtLe 2
  let hInv : ENNReal :=
    ∫⁻ u, (X u)⁻¹ ∂(RadialLowerBoundAlt.angularMeasure hn)
  have hone : 1 ≤ ENNReal.ofReal (wickSqrtMomentBound k n) ^ 2 * hInv := by
    dsimp [hInv]
    exact hcore.trans (by
      simpa [mul_comm] using
        (mul_le_mul_right hsq
          (∫⁻ u, (X u)⁻¹ ∂(RadialLowerBoundAlt.angularMeasure hn))))
  have hB0 : ENNReal.ofReal (wickSqrtMomentBound k n) ^ 2 ≠ 0 := by
    exact pow_ne_zero _ (ENNReal.ofReal_pos.mpr hbound).ne'
  have hBtop : ENNReal.ofReal (wickSqrtMomentBound k n) ^ 2 ≠ ⊤ := by
    exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hinvle :
      (ENNReal.ofReal (wickSqrtMomentBound k n) ^ 2)⁻¹ ≤ hInv := by
    rw [← one_div]
    apply (ENNReal.div_le_iff_le_mul (Or.inl hB0) (Or.inl hBtop)).2
    simpa [mul_comm] using hone
  unfold wickAngularRatioENN angularConditionNumberENN
  rw [lintegral_angularEnergy_eq_closedFirstMoment_div_pow hn hk,
    ENNReal.div_eq_inv_mul]
  calc
    (ENNReal.ofReal (wickSqrtMomentBound k n) ^ 2)⁻¹ *
        ENNReal.ofReal
          (closedFirstMoment k n / (k : ℝ) ^ (2 * n - 1)) ≤
      hInv * ENNReal.ofReal
          (closedFirstMoment k n / (k : ℝ) ^ (2 * n - 1)) :=
        by simpa [mul_comm] using
          (mul_le_mul_right hinvle
            (ENNReal.ofReal
              (closedFirstMoment k n / (k : ℝ) ^ (2 * n - 1))))
    _ = ENNReal.ofReal
          (closedFirstMoment k n / (k : ℝ) ^ (2 * n - 1)) *
        (∫⁻ u, (ENNReal.ofReal
          (RadialLowerBoundAlt.angularEnergy (n := n) (k := k) hn u))⁻¹
          ∂(RadialLowerBoundAlt.angularMeasure hn)) := by
      simp only [hInv, X]
      exact mul_comm _ _

/-- Honest reduction of the Wick angular theorem to its one missing
square-root estimate.  No assumption on the numerical value of the inverse
moment is made beyond its finiteness. -/
theorem wickAngularRatio_le_literalAngularMomentProduct_of_sqrt_bound
    {n k : ℕ} (hn : 1 ≤ n) (hk : 0 < k)
    (hpos : ∀ᵐ u ∂(RadialLowerBoundAlt.angularMeasure (n := n) (k := k) hn),
      0 < RadialLowerBoundAlt.angularEnergy hn u)
    (hinv : Integrable
      (fun u ↦ (RadialLowerBoundAlt.angularEnergy
        (n := n) (k := k) hn u)⁻¹)
      (RadialLowerBoundAlt.angularMeasure hn))
    (hsqrt :
      (∫ u, Real.sqrt (RadialLowerBoundAlt.angularEnergy
          (n := n) (k := k) hn u)
        ∂(RadialLowerBoundAlt.angularMeasure hn)) ≤
        wickSqrtMomentBound k n)
    (hbound : 0 < wickSqrtMomentBound k n) :
    wickAngularRatio k n ≤
      (∫ u, RadialLowerBoundAlt.angularEnergy
          (n := n) (k := k) hn u
        ∂(RadialLowerBoundAlt.angularMeasure hn)) *
      (∫ u, (RadialLowerBoundAlt.angularEnergy
          (n := n) (k := k) hn u)⁻¹
        ∂(RadialLowerBoundAlt.angularMeasure hn)) := by
  have hkpos : 0 < k := hk
  letI : ∀ _ : RadialLowerBoundAlt.CofactorIdx n hn,
      IsProbabilityMeasure
        (circularGaussianSphereProbability k) :=
    fun _ ↦ ⟨circularGaussianSphereProbability_apply_univ hkpos⟩
  letI : IsProbabilityMeasure
      (RadialLowerBoundAlt.angularMeasure (k := k) hn) := by
    unfold RadialLowerBoundAlt.angularMeasure
    infer_instance
  have hW := RadialLowerBoundAlt.integrable_angularEnergy hn hk
  have hcore := one_le_sq_integral_sqrt_mul_integral_inv
    (RadialLowerBoundAlt.angularMeasure (n := n) (k := k) hn)
    (RadialLowerBoundAlt.angularEnergy (n := n) (k := k) hn)
    (RadialLowerBoundAlt.measurable_angularEnergy hn).aestronglyMeasurable
    hpos hW hinv
  have hInvNonneg : 0 ≤
      ∫ u, (RadialLowerBoundAlt.angularEnergy
        (n := n) (k := k) hn u)⁻¹
        ∂(RadialLowerBoundAlt.angularMeasure hn) :=
    integral_nonneg_of_ae (hpos.mono fun _ hu ↦ inv_nonneg.mpr hu.le)
  have hsqrtNonneg : 0 ≤
      ∫ u, Real.sqrt (RadialLowerBoundAlt.angularEnergy
        (n := n) (k := k) hn u)
        ∂(RadialLowerBoundAlt.angularMeasure hn) :=
    integral_nonneg fun _ ↦ Real.sqrt_nonneg _
  have hsquare :
      (∫ u, Real.sqrt (RadialLowerBoundAlt.angularEnergy
        (n := n) (k := k) hn u)
        ∂(RadialLowerBoundAlt.angularMeasure hn)) ^ 2 ≤
        wickSqrtMomentBound k n ^ 2 :=
    (sq_le_sq₀ hsqrtNonneg hbound.le).2 hsqrt
  have hone : 1 ≤ wickSqrtMomentBound k n ^ 2 *
      ∫ u, (RadialLowerBoundAlt.angularEnergy
        (n := n) (k := k) hn u)⁻¹
        ∂(RadialLowerBoundAlt.angularMeasure hn) :=
    hcore.trans (mul_le_mul_of_nonneg_right hsquare hInvNonneg)
  have hratio : (wickSqrtMomentBound k n ^ 2)⁻¹ ≤
      ∫ u, (RadialLowerBoundAlt.angularEnergy
        (n := n) (k := k) hn u)⁻¹
        ∂(RadialLowerBoundAlt.angularMeasure hn) := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ (sq_pos_of_pos hbound)).2
    simpa [mul_comm] using hone
  rw [wickAngularRatio, integral_angularEnergy_eq_closedFirstMoment_div_pow hn hk]
  rw [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left hratio
    (div_nonneg (closedFirstMoment_pos k n hk).le (by positivity))

end WickAngularLowerBound

end

end LogdetLean.GramHafnian
