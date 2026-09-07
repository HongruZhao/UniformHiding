import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Extended Cauchy--Schwarz for a reciprocal moment

This isolated lemma records the exact nonnegative-integral form needed by the
radial lower-bound experiment.  In particular, it does not assume that the
reciprocal moment is finite: if that moment is infinite, the conclusion is
handled in `ENNReal` rather than silently asserting an ordinary expectation.
-/

open MeasureTheory
open scoped ENNReal

namespace LogdetLean.GramHafnian

noncomputable section

/-- Cauchy--Schwarz for a finite-valued nonnegative observable with nonzero
first moment.  The reciprocal integral is permitted to be infinite. -/
theorem measure_sq_le_lintegral_mul_lintegral_inv
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega)
    (X : Omega → ENNReal) (hX : AEMeasurable X mu)
    (hXtop : ∀ᵐ w ∂mu, X w ≠ ⊤)
    (hEX0 : (∫⁻ w, X w ∂mu) ≠ 0) :
    (mu Set.univ) ^ 2 ≤
      (∫⁻ w, X w ∂mu) * ∫⁻ w, (X w)⁻¹ ∂mu := by
  by_cases hinv : (∫⁻ w, (X w)⁻¹ ∂mu) = ⊤
  · rw [hinv, ENNReal.mul_top hEX0]
    exact le_top
  · have hInvLt : ∀ᵐ w ∂mu, (X w)⁻¹ < ⊤ :=
      ae_lt_top' hX.inv hinv
    have hX0 : ∀ᵐ w ∂mu, X w ≠ 0 := by
      filter_upwards [hInvLt] with w hw
      intro hzero
      simp [hzero] at hw
    let f : Omega → ENNReal := fun w ↦ (X w) ^ (1 / 2 : ℝ)
    let g : Omega → ENNReal := fun w ↦ ((X w)⁻¹) ^ (1 / 2 : ℝ)
    have hf : AEMeasurable f mu := hX.pow_const _
    have hg : AEMeasurable g mu := hX.inv.pow_const _
    have hholder : (2 : ℝ).HolderConjugate 2 := by
      rw [Real.holderConjugate_iff]
      norm_num
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq mu hholder hf hg
    have hfg : (∫⁻ w, (f * g) w ∂mu) = mu Set.univ := by
      calc
        (∫⁻ w, (f * g) w ∂mu) = ∫⁻ _w, (1 : ENNReal) ∂mu := by
          apply lintegral_congr_ae
          filter_upwards [hX0, hXtop] with w hw0 hwt
          change (X w) ^ (1 / 2 : ℝ) * ((X w)⁻¹) ^ (1 / 2 : ℝ) = 1
          rw [← ENNReal.mul_rpow_of_nonneg _ _
            (by norm_num : (0 : ℝ) ≤ 1 / 2)]
          rw [ENNReal.mul_inv_cancel hw0 hwt]
          simp
        _ = mu Set.univ := by simp
    have hf2 : (∫⁻ w, f w ^ (2 : ℝ) ∂mu) = ∫⁻ w, X w ∂mu := by
      apply lintegral_congr_ae
      filter_upwards [] with w
      change ((X w) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = X w
      rw [← ENNReal.rpow_mul]
      norm_num
    have hg2 : (∫⁻ w, g w ^ (2 : ℝ) ∂mu) =
        ∫⁻ w, (X w)⁻¹ ∂mu := by
      apply lintegral_congr_ae
      filter_upwards [] with w
      change (((X w)⁻¹) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = (X w)⁻¹
      rw [← ENNReal.rpow_mul]
      norm_num
    rw [hfg, hf2, hg2] at h
    have hsqrt :
        (∫⁻ w, X w ∂mu) ^ (1 / 2 : ℝ) *
            (∫⁻ w, (X w)⁻¹ ∂mu) ^ (1 / 2 : ℝ) =
          ((∫⁻ w, X w ∂mu) * ∫⁻ w, (X w)⁻¹ ∂mu) ^
            (1 / 2 : ℝ) := by
      exact (ENNReal.mul_rpow_of_nonneg _ _
        (by norm_num : (0 : ℝ) ≤ 1 / 2)).symm
    rw [hsqrt] at h
    have hsquare := pow_le_pow_left₀
      (show (0 : ENNReal) ≤ mu Set.univ by positivity) h 2
    have hrpow_sq (x : ENNReal) : (x ^ (1 / 2 : ℝ)) ^ (2 : ℕ) = x := by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      norm_num
    rw [hrpow_sq] at hsquare
    exact hsquare

end

end LogdetLean.GramHafnian
