import LogdetLean.GramHafnian.RankOneGaussianBilinear
import LogdetLean.GramHafnian.AuxiliaryFieldExpansion
import LogdetLean.GramHafnian.GaussianEvenMoments
import LogdetLean.GramHafnian.GramMomentFubini

/-!
# Real Gaussian moments used by the hiding proof

This neutral module extracts the two elementary Gaussian moment lemmas needed
by `BetaPrimeMeanInternal`.  Their theorem names, statements, and proof bodies
are unchanged from their original proved location.
-/

open scoped BigOperators RealInnerProductSpace Nat
open MeasureTheory ProbabilityTheory

namespace LogdetLean.GramHafnian

noncomputable section

/-- A selected-coordinate monomial is integrable under an iid standard real
Gaussian coordinate field. -/
theorem integrable_realColorProduct_standardGaussian
    {m k : ℕ} (c : Fin m → Fin k) :
    Integrable (fun x : Fin k → ℝ ↦ ∏ i, x (c i))
      (standardRealGaussianVectorMeasure k) := by
  rw [show (fun x : Fin k → ℝ ↦ ∏ i, x (c i)) =
      realCoordinatePowerProduct (colorMultiplicity c) by
    funext x
    exact prod_comp_eq_coordinatePowerProduct c x]
  unfold realCoordinatePowerProduct standardRealGaussianVectorMeasure
  exact Integrable.fintype_prod fun a ↦
    integrable_pow_gaussianReal (colorMultiplicity c a)

/-- One standard real Gaussian column contracts two deterministic real
linear forms to their bilinear dot product. -/
theorem integral_realBilinearForms_standardGaussian
    {k : ℕ} (g h : Fin k → ℝ) :
    (∫ x : Fin k → ℝ, bilinearDot g x * bilinearDot h x
        ∂standardRealGaussianVectorMeasure k) = bilinearDot g h := by
  let E := EuclideanSpace ℝ (Fin k)
  let T : (Fin k → ℝ) → E := WithLp.toLp 2
  have hmap : Measure.map T (standardRealGaussianVectorMeasure k) =
      stdGaussian E := by
    simpa only [T, E, standardRealGaussianVectorMeasure] using
      (map_pi_eq_stdGaussian (ι := Fin k))
  calc
    (∫ x : Fin k → ℝ, bilinearDot g x * bilinearDot h x
        ∂standardRealGaussianVectorMeasure k) =
        ∫ x : Fin k → ℝ,
          inner ℝ (WithLp.toLp 2 g) (WithLp.toLp 2 x) *
            inner ℝ (WithLp.toLp 2 h) (WithLp.toLp 2 x)
          ∂standardRealGaussianVectorMeasure k := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦ by
        change bilinearDot g x * bilinearDot h x =
          inner ℝ (WithLp.toLp 2 g) (WithLp.toLp 2 x) *
            inner ℝ (WithLp.toLp 2 h) (WithLp.toLp 2 x)
        rw [inner_toLp_eq_bilinearDot, inner_toLp_eq_bilinearDot]
    _ = ∫ z : E,
          inner ℝ (WithLp.toLp 2 g) z * inner ℝ (WithLp.toLp 2 h) z
          ∂Measure.map T (standardRealGaussianVectorMeasure k) := by
      rw [integral_map (by fun_prop) (by fun_prop)]
    _ = ∫ z : E,
          inner ℝ (WithLp.toLp 2 g) z * inner ℝ (WithLp.toLp 2 h) z
          ∂stdGaussian E := by rw [hmap]
    _ = inner ℝ (WithLp.toLp 2 g) (WithLp.toLp 2 h) := by
      have hcov := covarianceBilin_apply
        (μ := stdGaussian E) IsGaussian.memLp_two_id
        (WithLp.toLp 2 g) (WithLp.toLp 2 h)
      rw [covarianceBilin_stdGaussian] at hcov
      have hmean : (∫ x : E, id x ∂stdGaussian E) = 0 := by
        simpa only [id_eq] using (integral_id_stdGaussian (E := E))
      rw [hmean] at hcov
      simp only [sub_zero] at hcov
      rw [← hcov, innerSL_apply_apply]
    _ = bilinearDot g h := inner_toLp_eq_bilinearDot g h

end

end LogdetLean.GramHafnian
