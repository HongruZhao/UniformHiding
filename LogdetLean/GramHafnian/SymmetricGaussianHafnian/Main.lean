import LogdetLean.GramHafnian.SymmetricGaussianHafnian.LiteralCompression
import LogdetLean.GramHafnian.SymmetricGaussianHafnian.SingletonCharacteristic
import LogdetLean.GramHafnian.SymmetricGaussianHafnian.EuclideanCofactorLaw
import LogdetLean.GramHafnian.SymmetricGaussianHafnian.Constants
import LogdetLean.GramHafnian.SymmetricGaussianHafnian.SecondMoment
import LogdetLean.GramHafnian.SymmetricGaussianHafnian.ComplexSmallBallLower

/-!
# Unconditional complex Gaussian hafnian anticoncentration

The observable is the actual perfect-matching hafnian of a symmetric
matrix with independent CN(0,1) upper off-diagonal entries. There is no
assumed compression, moment bound, positivity, or Gaussian-mixture gate.
Real and ordered quaternionic endpoints are not asserted in this module.
-/

open MeasureTheory ProbabilityTheory Complex
open scoped BigOperators ENNReal Real

namespace LogdetLean.GramHafnian.SymmetricGaussianHafnian

noncomputable section

set_option maxHeartbeats 1200000

/-- Full characteristic-function bound at successive odd dimensions.
The index `r` corresponds to paper cofactor level `r+2`. -/
theorem edgeCofactorCharacteristic_re_le_previous_mixture
    (r : ℕ) (xi : CircularEuclideanSpace (2 * r + 3)) :
    (edgeCofactorCharacteristic (Fin (2 * r + 3)) (fun j ↦ xi j)).re ≤
      ∫ A : Edge (Fin (2 * r + 1)) → ℂ,
        Real.exp (-(edgeCofactorEnergy A * ‖xi‖ ^ 2) / 4)
        ∂edgeGaussian (Fin (2 * r + 1)) := by
  have hsize : 2 * (r + 2) - 1 = 2 * r + 3 := by omega
  have hc := edgeCofactorCharacteristic_norm_le_singleton (r + 2) (by omega)
  rw [hsize] at hc
  have hcomp := hc (Fin.last (2 * r + 2)) (fun j ↦ xi j)
  have henergy : coordinateEnergy (fun j ↦ xi j) = ‖xi‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [coordinateEnergy, Complex.normSq_eq_norm_sq]
  rw [edgeCofactorCharacteristic_singleton_last (2 * r + 1), henergy] at hcomp
  have hsqrt : Real.sqrt (‖xi‖ ^ 2) ^ 2 = ‖xi‖ ^ 2 :=
    Real.sq_sqrt (sq_nonneg _)
  calc
    _ ≤ ‖edgeCofactorCharacteristic (Fin (2 * r + 3)) (fun j ↦ xi j)‖ :=
      Complex.re_le_norm _
    _ ≤ ‖∫ A : Edge (Fin (2 * r + 1)) → ℂ,
        Complex.exp (-(((edgeCofactorEnergy A * Real.sqrt (‖xi‖ ^ 2) ^ 2 : ℝ) : ℂ) / 4))
        ∂edgeGaussian (Fin (2 * r + 1))‖ := hcomp
    _ ≤ ∫ A : Edge (Fin (2 * r + 1)) → ℂ,
        ‖Complex.exp (-(((edgeCofactorEnergy A * Real.sqrt (‖xi‖ ^ 2) ^ 2 : ℝ) : ℂ) / 4))‖
        ∂edgeGaussian (Fin (2 * r + 1)) := norm_integral_le_integral_norm _
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with A
      rw [Complex.norm_exp, hsqrt]
      congr 1
      norm_cast
      ring

/-- Internal zero-based indexing: the energy has `2r+1` cofactor coordinates. -/
def cofactorInverseMoment (r : ℕ) : ℝ≥0∞ :=
  ennInverseMoment (edgeGaussian (Fin (2 * r + 1))) edgeCofactorEnergy

@[simp] theorem cofactorInverseMoment_zero : cofactorInverseMoment 0 = 1 := by
  simp [cofactorInverseMoment, ennInverseMoment]

theorem cofactorInverseMoment_step (r : ℕ) :
    cofactorInverseMoment (r + 1) ≤ cofactorInverseMoment r *
      ENNReal.ofReal (((2 : ℝ) * r + 2)⁻¹) := by
  have hpos := ae_edgeCofactorEnergy_pos_odd (r + 1)
  have hsize : 2 * (r + 1) + 1 = 2 * r + 3 := by omega
  rw [hsize] at hpos
  have h := edgeInverseMoment_le_of_characteristic_bound
    (d := 2 * r + 3) (e := 2 * r + 1) (by omega)
    hpos (ae_edgeCofactorEnergy_pos_odd r)
    (edgeCofactorCharacteristic_re_le_previous_mixture r)
  unfold cofactorInverseMoment
  rw [hsize]
  have hfactor : ((2 * r + 3 : ℕ) : ℝ) - 1 = 2 * (r : ℝ) + 2 := by
    push_cast
    ring
  simpa only [hfactor] using h

theorem cofactorInverseMoment_le (r : ℕ) :
    cofactorInverseMoment r ≤ ENNReal.ofReal (inverseBound (r + 1)) := by
  induction r with
  | zero => simp
  | succ r ih =>
      calc
        cofactorInverseMoment (r + 1) ≤ cofactorInverseMoment r *
            ENNReal.ofReal (((2 : ℝ) * r + 2)⁻¹) := cofactorInverseMoment_step r
        _ ≤ ENNReal.ofReal (inverseBound (r + 1)) *
            ENNReal.ofReal (((2 : ℝ) * r + 2)⁻¹) :=
          mul_le_mul ih le_rfl bot_le bot_le
        _ = ENNReal.ofReal (inverseBound (r + 1) * ((2 : ℝ) * r + 2)⁻¹) := by
          rw [ENNReal.ofReal_mul (inverseBound_pos (r + 1) (by omega)).le]
        _ = ENNReal.ofReal (inverseBound (r + 1 + 1)) := by
          rw [inverseBound_succ (r + 1) (by omega)]
          congr 2
          push_cast
          ring

/-- Paper-indexed sharp inverse cofactor-energy bound, with no assumed
finiteness or positivity. -/
theorem symmetricCofactor_inverseMoment_le (n : ℕ) (hn : 1 ≤ n) :
    ennInverseMoment (edgeGaussian (Fin (2 * n - 1))) edgeCofactorEnergy ≤
      ENNReal.ofReal (inverseBound n) := by
  have h := cofactorInverseMoment_le (n - 1)
  have hsize : 2 * (n - 1) + 1 = 2 * n - 1 := by omega
  unfold cofactorInverseMoment at h
  rw [hsize] at h
  simpa only [Nat.sub_add_cancel hn] using h

theorem symmetricCofactor_inverseMoment_finite (n : ℕ) (hn : 1 ≤ n) :
    ennInverseMoment (edgeGaussian (Fin (2 * n - 1))) edgeCofactorEnergy < ⊤ :=
  lt_of_le_of_lt (symmetricCofactor_inverseMoment_le n hn) ENNReal.ofReal_lt_top

/-- The literal finite, uniform-in-shift complex Gaussian hafnian theorem.
Every hypothesis is a parameter-domain condition, not an analytic gate. -/
theorem symmetricHafnian_shifted_smallBall
    (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (ε : ℝ) (hε : 0 ≤ ε) :
    (edgeGaussian (Fin (2 * n)))
      {x | ‖edgeHafnian x - z‖ ≤ ε * sigma n} ≤
      min 1 (ENNReal.ofReal (coefficient n * ε ^ 2)) := by
  have hpos := ae_edgeCofactorEnergy_pos_odd (n - 1)
  have hsize : 2 * (n - 1) + 1 = 2 * n - 1 := by omega
  rw [hsize] at hpos
  have h := edgeHafnian_smallBall_of_cofactorEnergy_pos (2 * n - 1) hpos
    z (ε * sigma n) (mul_nonneg hε (sigma_nonneg n))
  rw [show 2 * n - 1 + 1 = 2 * n by omega] at h
  apply le_min
  · exact prob_le_one
  · calc
      _ ≤ ENNReal.ofReal ((ε * sigma n) ^ 2) *
          ennInverseMoment (edgeGaussian (Fin (2 * n - 1))) edgeCofactorEnergy := h
      _ ≤ ENNReal.ofReal ((ε * sigma n) ^ 2) * ENNReal.ofReal (inverseBound n) :=
        mul_le_mul le_rfl (symmetricCofactor_inverseMoment_le n hn) bot_le bot_le
      _ = ENNReal.ofReal (coefficient n * ε ^ 2) := by
        rw [← ENNReal.ofReal_mul (sq_nonneg _), mul_pow, sigma_sq]
        congr 1
        unfold coefficient
        ring

/-- Explicit elementary prefactor `2 sqrt(n)` for the same literal model. -/
theorem symmetricHafnian_shifted_smallBall_two_sqrt
    (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (ε : ℝ) (hε : 0 ≤ ε) :
    (edgeGaussian (Fin (2 * n)))
      {x | ‖edgeHafnian x - z‖ ≤ ε * sigma n} ≤
      min 1 (ENNReal.ofReal (2 * Real.sqrt (n : ℝ) * ε ^ 2)) := by
  exact (symmetricHafnian_shifted_smallBall n hn z ε hε).trans
    (min_le_min_left 1 (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (coefficient_le_two_sqrt n hn) (sq_nonneg ε))))

end

end LogdetLean.GramHafnian.SymmetricGaussianHafnian
