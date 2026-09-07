import LogdetLean.GramHafnian.ShiftedAnticoncentration.LaplaceOrder
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Real

/-!
# Reciprocal-kernel Laplace bounds imply small-ball bounds

This module records the generic final transfer used after a Laplace comparison.
At the single scale `t = epsilon⁻²`, the small-ball indicator is bounded by
`exp(1) * exp (-t * ‖Y - z‖²)`, while positivity of `V` gives
`(1 + t * V)⁻¹ ≤ epsilon² * V⁻¹`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace LogdetLean.GramHafnian

noncomputable section

variable {Omega Omega' : Type*}
  [MeasurableSpace Omega] [MeasurableSpace Omega']

/-- The finite radius reciprocal kernel before it is bounded by the full
inverse moment.  This is the sharper intermediate inequality used in the
proof of the independent factor shift corollary. -/
theorem measure_norm_sub_le_exp_one_mul_reciprocalKernel_of_reciprocalLaplace_le
    (mu : Measure Omega) (nu : Measure Omega')
    (Y : Omega -> ℂ) (hY : Measurable Y)
    (V : Omega' -> ℝ)
    (z : ℂ) (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hLap : ∀ t : ℝ, 0 ≤ t ->
      ennLaplaceTransform mu (fun w => ‖Y w - z‖ ^ 2) t ≤
        ∫⁻ w, ENNReal.ofReal ((1 + t * V w)⁻¹) ∂nu) :
    mu {w | ‖Y w - z‖ ≤ epsilon} ≤
      ENNReal.ofReal (Real.exp 1) *
        ∫⁻ w, ENNReal.ofReal
          ((1 + (epsilon ^ 2)⁻¹ * V w)⁻¹) ∂nu := by
  let U : Omega -> ℝ := fun w => ‖Y w - z‖ ^ 2
  let t : ℝ := (epsilon ^ 2)⁻¹
  let F : Omega -> ENNReal := fun w =>
    ENNReal.ofReal (Real.exp 1) *
      ENNReal.ofReal (Real.exp (-t * U w))
  have hepsilon_sq : 0 < epsilon ^ 2 := by positivity
  have ht : 0 < t := by
    dsimp [t]
    positivity
  have hU : Measurable U := by
    dsimp [U]
    fun_prop
  have hF : AEMeasurable F mu := by
    apply Measurable.aemeasurable
    dsimp [F]
    exact measurable_const.mul
      ((hU.const_mul (-t)).exp.ennreal_ofReal)
  have hindicator :
      mu {w | ‖Y w - z‖ ≤ epsilon} ≤ ∫⁻ w, F w ∂mu := by
    apply meas_le_lintegral₀ hF
    intro w hw
    have hUle : U w ≤ epsilon ^ 2 := by
      dsimp [U]
      exact (sq_le_sq₀ (norm_nonneg _) hepsilon.le).2 hw
    have htu : t * U w ≤ 1 := by
      calc
        t * U w ≤ t * epsilon ^ 2 :=
          mul_le_mul_of_nonneg_left hUle ht.le
        _ = 1 := by simp [t, hepsilon_sq.ne']
    have hreal :
        (1 : ℝ) ≤ Real.exp 1 * Real.exp (-t * U w) := by
      rw [← Real.exp_add]
      have hexponent : 0 ≤ 1 + -t * U w := by linarith
      simpa using (Real.exp_le_exp.mpr hexponent)
    have henn :
        ENNReal.ofReal 1 ≤
          ENNReal.ofReal (Real.exp 1 * Real.exp (-t * U w)) :=
      ENNReal.ofReal_le_ofReal hreal
    simpa [F, ENNReal.ofReal_mul (Real.exp_pos 1).le] using henn
  have hF_integral :
      (∫⁻ w, F w ∂mu) =
        ENNReal.ofReal (Real.exp 1) * ennLaplaceTransform mu U t := by
    dsimp [F]
    rw [lintegral_const_mul]
    · rfl
    · exact (hU.const_mul (-t)).exp.ennreal_ofReal
  calc
    mu {w | ‖Y w - z‖ ≤ epsilon} ≤
        ENNReal.ofReal (Real.exp 1) * ennLaplaceTransform mu U t := by
      rw [← hF_integral]
      exact hindicator
    _ ≤ ENNReal.ofReal (Real.exp 1) *
        (∫⁻ w, ENNReal.ofReal ((1 + t * V w)⁻¹) ∂nu) :=
      mul_le_mul le_rfl (by simpa [U] using hLap t ht.le) bot_le bot_le
    _ = ENNReal.ofReal (Real.exp 1) *
        ∫⁻ w, ENNReal.ofReal
          ((1 + (epsilon ^ 2)⁻¹ * V w)⁻¹) ∂nu := by
      rfl

/-- The finite radius reciprocal kernel is bounded by the corresponding
scaled extended inverse moment. -/
theorem reciprocalKernel_lintegral_le_sq_mul_ennInverseMoment
    (nu : Measure Omega') (V : Omega' -> ℝ) (hV : Measurable V)
    (hVpos : ∀ᵐ w ∂nu, 0 < V w)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    (∫⁻ w, ENNReal.ofReal
        ((1 + (epsilon ^ 2)⁻¹ * V w)⁻¹) ∂nu) ≤
      ENNReal.ofReal (epsilon ^ 2) * ennInverseMoment nu V := by
  let t : ℝ := (epsilon ^ 2)⁻¹
  have hepsilon_sq : 0 < epsilon ^ 2 := by positivity
  have ht : 0 < t := by
    dsimp [t]
    positivity
  calc
    (∫⁻ w, ENNReal.ofReal
        ((1 + (epsilon ^ 2)⁻¹ * V w)⁻¹) ∂nu) ≤
        ∫⁻ w, ENNReal.ofReal (epsilon ^ 2 * (V w)⁻¹) ∂nu := by
      apply lintegral_mono_ae
      filter_upwards [hVpos] with w hw
      apply ENNReal.ofReal_le_ofReal
      have htV : 0 < t * V w := mul_pos ht hw
      have hden : 0 < 1 + t * V w := by linarith
      change (1 + t * V w)⁻¹ ≤ epsilon ^ 2 * (V w)⁻¹
      calc
        (1 + t * V w)⁻¹ ≤ (t * V w)⁻¹ :=
          (inv_le_inv₀ hden htV).2 (by linarith)
        _ = epsilon ^ 2 * (V w)⁻¹ := by
          simp [t, mul_comm]
    _ = ENNReal.ofReal (epsilon ^ 2) * ennInverseMoment nu V := by
      simp_rw [ENNReal.ofReal_mul (sq_nonneg epsilon)]
      rw [lintegral_const_mul]
      · rfl
      · exact hV.inv.ennreal_ofReal

/-- A reciprocal-kernel Laplace bound implies the corresponding `ENNReal`
small-ball estimate.  No finiteness assumption on the inverse moment is
needed.  The observable and the positive comparison variable may live on
different measure spaces. -/
theorem measure_norm_sub_le_exp_one_mul_sq_mul_ennInverseMoment_of_reciprocalLaplace_le
    (mu : Measure Omega) (nu : Measure Omega')
    (Y : Omega -> ℂ) (hY : Measurable Y)
    (V : Omega' -> ℝ) (hV : Measurable V)
    (hVpos : ∀ᵐ w ∂nu, 0 < V w)
    (z : ℂ) (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hLap : ∀ t : ℝ, 0 ≤ t ->
      ennLaplaceTransform mu (fun w => ‖Y w - z‖ ^ 2) t ≤
        ∫⁻ w, ENNReal.ofReal ((1 + t * V w)⁻¹) ∂nu) :
    mu {w | ‖Y w - z‖ ≤ epsilon} ≤
      ENNReal.ofReal (Real.exp 1 * epsilon ^ 2) *
        ennInverseMoment nu V := by
  let U : Omega -> ℝ := fun w => ‖Y w - z‖ ^ 2
  let t : ℝ := (epsilon ^ 2)⁻¹
  let F : Omega -> ENNReal := fun w =>
    ENNReal.ofReal (Real.exp 1) *
      ENNReal.ofReal (Real.exp (-t * U w))
  have hepsilon_sq : 0 < epsilon ^ 2 := by positivity
  have ht : 0 < t := by
    dsimp [t]
    positivity
  have hU : Measurable U := by
    dsimp [U]
    fun_prop
  have hF : AEMeasurable F mu := by
    apply Measurable.aemeasurable
    dsimp [F]
    exact measurable_const.mul
      ((hU.const_mul (-t)).exp.ennreal_ofReal)
  have hindicator :
      mu {w | ‖Y w - z‖ ≤ epsilon} ≤ ∫⁻ w, F w ∂mu := by
    apply meas_le_lintegral₀ hF
    intro w hw
    have hUle : U w ≤ epsilon ^ 2 := by
      dsimp [U]
      exact (sq_le_sq₀ (norm_nonneg _) hepsilon.le).2 hw
    have htu : t * U w ≤ 1 := by
      calc
        t * U w ≤ t * epsilon ^ 2 :=
          mul_le_mul_of_nonneg_left hUle ht.le
        _ = 1 := by simp [t, hepsilon_sq.ne']
    have hreal :
        (1 : ℝ) ≤ Real.exp 1 * Real.exp (-t * U w) := by
      rw [← Real.exp_add]
      have hexponent : 0 ≤ 1 + -t * U w := by linarith
      simpa using (Real.exp_le_exp.mpr hexponent)
    have henn :
        ENNReal.ofReal 1 ≤
          ENNReal.ofReal (Real.exp 1 * Real.exp (-t * U w)) :=
      ENNReal.ofReal_le_ofReal hreal
    simpa [F, ENNReal.ofReal_mul (Real.exp_pos 1).le] using henn
  have hF_integral :
      (∫⁻ w, F w ∂mu) =
        ENNReal.ofReal (Real.exp 1) * ennLaplaceTransform mu U t := by
    dsimp [F]
    rw [lintegral_const_mul]
    · rfl
    · exact (hU.const_mul (-t)).exp.ennreal_ofReal
  have hkernel :
      (∫⁻ w, ENNReal.ofReal ((1 + t * V w)⁻¹) ∂nu) ≤
        ENNReal.ofReal (epsilon ^ 2) * ennInverseMoment nu V := by
    calc
      (∫⁻ w, ENNReal.ofReal ((1 + t * V w)⁻¹) ∂nu) ≤
          ∫⁻ w, ENNReal.ofReal (epsilon ^ 2 * (V w)⁻¹) ∂nu := by
        apply lintegral_mono_ae
        filter_upwards [hVpos] with w hw
        apply ENNReal.ofReal_le_ofReal
        have htV : 0 < t * V w := mul_pos ht hw
        have hden : 0 < 1 + t * V w := by linarith
        calc
          (1 + t * V w)⁻¹ ≤ (t * V w)⁻¹ :=
            (inv_le_inv₀ hden htV).2 (by linarith)
          _ = epsilon ^ 2 * (V w)⁻¹ := by
            simp [t, mul_comm]
      _ = ENNReal.ofReal (epsilon ^ 2) * ennInverseMoment nu V := by
        simp_rw [ENNReal.ofReal_mul (sq_nonneg epsilon)]
        rw [lintegral_const_mul]
        · rfl
        · exact hV.inv.ennreal_ofReal
  calc
    mu {w | ‖Y w - z‖ ≤ epsilon} ≤
        ENNReal.ofReal (Real.exp 1) * ennLaplaceTransform mu U t := by
      rw [← hF_integral]
      exact hindicator
    _ ≤ ENNReal.ofReal (Real.exp 1) *
        (∫⁻ w, ENNReal.ofReal ((1 + t * V w)⁻¹) ∂nu) :=
      mul_le_mul le_rfl (by simpa [U] using hLap t ht.le) bot_le bot_le
    _ ≤ ENNReal.ofReal (Real.exp 1) *
        (ENNReal.ofReal (epsilon ^ 2) * ennInverseMoment nu V) :=
      mul_le_mul le_rfl hkernel bot_le bot_le
    _ = ENNReal.ofReal (Real.exp 1 * epsilon ^ 2) *
        ennInverseMoment nu V := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos 1).le]

/-- Finite real-valued corollary of
`measure_norm_sub_le_exp_one_mul_sq_mul_ennInverseMoment_of_reciprocalLaplace_le`.
The finiteness hypothesis is needed only to apply `ENNReal.toReal`. -/
theorem measureReal_norm_sub_le_exp_one_mul_sq_mul_ennInverseMoment_toReal_of_reciprocalLaplace_le
    (mu : Measure Omega) (nu : Measure Omega')
    (Y : Omega -> ℂ) (hY : Measurable Y)
    (V : Omega' -> ℝ) (hV : Measurable V)
    (hVpos : ∀ᵐ w ∂nu, 0 < V w)
    (hVfinite : ennInverseMoment nu V ≠ ⊤)
    (z : ℂ) (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hLap : ∀ t : ℝ, 0 ≤ t ->
      ennLaplaceTransform mu (fun w => ‖Y w - z‖ ^ 2) t ≤
        ∫⁻ w, ENNReal.ofReal ((1 + t * V w)⁻¹) ∂nu) :
    mu.real {w | ‖Y w - z‖ ≤ epsilon} ≤
      Real.exp 1 * epsilon ^ 2 * (ennInverseMoment nu V).toReal := by
  have henn :=
    measure_norm_sub_le_exp_one_mul_sq_mul_ennInverseMoment_of_reciprocalLaplace_le
      mu nu Y hY V hV hVpos z epsilon hepsilon hLap
  have hfactor_nonneg : 0 ≤ Real.exp 1 * epsilon ^ 2 :=
    mul_nonneg (Real.exp_pos 1).le (sq_nonneg epsilon)
  have hrhs_ne_top :
      ENNReal.ofReal (Real.exp 1 * epsilon ^ 2) *
          ennInverseMoment nu V ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVfinite
  have hreal := ENNReal.toReal_mono hrhs_ne_top henn
  rw [Measure.real_def]
  simpa [ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hfactor_nonneg, mul_assoc] using hreal

end

end LogdetLean.GramHafnian
