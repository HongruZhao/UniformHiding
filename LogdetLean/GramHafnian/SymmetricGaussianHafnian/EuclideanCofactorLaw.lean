import LogdetLean.GramHafnian.SymmetricGaussianHafnian.LiteralCharacteristic
import LogdetLean.GramHafnian.ShiftedAnticoncentration.FourierCompression.InverseRecurrence

/-!
# Euclidean realization of the literal independent-edge cofactor law

Conjugation is intentional: the real Hilbert pairing then equals the
raw transpose Fourier pairing `Re (sum w_j C_j)` used in the compression.
The inverse moment remains an extended nonnegative integral throughout.
-/

open MeasureTheory ProbabilityTheory Complex
open scoped BigOperators ENNReal Real

namespace LogdetLean.GramHafnian.SymmetricGaussianHafnian

noncomputable section

def conjugateEdgeCofactorEuclidean {d : ℕ}
    (x : Edge (Fin d) → ℂ) : CircularEuclideanSpace d :=
  WithLp.toLp 2 (fun j ↦ star (edgeCofactor x j))

@[fun_prop]
theorem measurable_conjugateEdgeCofactorEuclidean (d : ℕ) :
    Measurable (conjugateEdgeCofactorEuclidean (d := d)) := by
  unfold conjugateEdgeCofactorEuclidean
  apply (WithLp.measurable_toLp 2 (Fin d → ℂ)).comp
  rw [measurable_pi_iff]
  intro j
  exact Complex.continuous_conj.measurable.comp
    ((measurable_pi_apply j).comp measurable_edgeCofactor)

def conjugateEdgeCofactorLaw (d : ℕ) : Measure (CircularEuclideanSpace d) :=
  (edgeGaussian (Fin d)).map conjugateEdgeCofactorEuclidean

instance conjugateEdgeCofactorLaw_probability (d : ℕ) :
    IsProbabilityMeasure (conjugateEdgeCofactorLaw d) := by
  unfold conjugateEdgeCofactorLaw
  exact Measure.isProbabilityMeasure_map
    (measurable_conjugateEdgeCofactorEuclidean d).aemeasurable

theorem norm_sq_conjugateEdgeCofactorEuclidean {d : ℕ}
    (x : Edge (Fin d) → ℂ) :
    ‖conjugateEdgeCofactorEuclidean x‖ ^ 2 = edgeCofactorEnergy x := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [conjugateEdgeCofactorEuclidean, PiLp.toLp_apply, norm_star,
    edgeCofactorEnergy]

theorem edgeCofactorCharacteristic_eq_charFun {d : ℕ}
    (xi : CircularEuclideanSpace d) :
    edgeCofactorCharacteristic (Fin d) (fun j ↦ xi j) =
      charFun (conjugateEdgeCofactorLaw d) xi := by
  unfold edgeCofactorCharacteristic conjugateEdgeCofactorLaw charFun
  rw [integral_map (measurable_conjugateEdgeCofactorEuclidean d).aemeasurable
    (by fun_prop)]
  apply integral_congr_ae
  filter_upwards [] with x
  unfold edgeCofactorPhaseCharacter edgeCofactorPhase
  congr 2
  norm_cast
  rw [PiLp.inner_apply]
  unfold conjugateEdgeCofactorEuclidean
  simp only [Complex.inner, starRingEnd_apply, star_star]
  exact Complex.re_sum _ _

/-- Equality of extended inverse moments for the actual edge model and
its Euclidean pushforward; no finiteness assumption is used. -/
theorem ennInverseMoment_conjugateEdgeCofactorLaw (d : ℕ) :
    ennInverseMoment (conjugateEdgeCofactorLaw d) (fun x ↦ ‖x‖ ^ 2) =
      ennInverseMoment (edgeGaussian (Fin d)) edgeCofactorEnergy := by
  unfold ennInverseMoment conjugateEdgeCofactorLaw
  rw [lintegral_map (by fun_prop)
    (measurable_conjugateEdgeCofactorEuclidean d)]
  apply lintegral_congr
  intro x
  simp only [norm_sq_conjugateEdgeCofactorEuclidean]

theorem norm_sq_pos_ae_conjugateEdgeCofactorLaw {d : ℕ}
    (hpos : ∀ᵐ x ∂edgeGaussian (Fin d), 0 < edgeCofactorEnergy x) :
    ∀ᵐ x ∂conjugateEdgeCofactorLaw d, 0 < ‖x‖ ^ 2 := by
  rw [conjugateEdgeCofactorLaw]
  rw [ae_map_iff (measurable_conjugateEdgeCofactorEuclidean d).aemeasurable
    (measurableSet_lt measurable_const (by fun_prop))]
  simpa only [norm_sq_conjugateEdgeCofactorEuclidean] using hpos

/-- The analytic recurrence applied to the literal independent-edge
cofactor law. The model-specific characteristic bound and positivity are
explicit inputs here and are discharged in the public assembly module. -/
theorem edgeInverseMoment_le_of_characteristic_bound
    {d e : ℕ} (hd : 2 ≤ d)
    (hpos : ∀ᵐ x ∂edgeGaussian (Fin d), 0 < edgeCofactorEnergy x)
    (hprev : ∀ᵐ x ∂edgeGaussian (Fin e), 0 < edgeCofactorEnergy x)
    (hchar : ∀ xi : CircularEuclideanSpace d,
      (edgeCofactorCharacteristic (Fin d) (fun j ↦ xi j)).re ≤
        ∫ y, Real.exp (-(edgeCofactorEnergy y * ‖xi‖ ^ 2) / 4)
          ∂edgeGaussian (Fin e)) :
    ennInverseMoment (edgeGaussian (Fin d)) edgeCofactorEnergy ≤
      ennInverseMoment (edgeGaussian (Fin e)) edgeCofactorEnergy *
        ENNReal.ofReal ((d : ℝ) - 1)⁻¹ := by
  rw [← ennInverseMoment_conjugateEdgeCofactorLaw d]
  apply ennInverse_norm_sq_le_auxiliaryGamma_factor hd
    (conjugateEdgeCofactorLaw d) (edgeGaussian (Fin e)) edgeCofactorEnergy
    measurable_edgeCofactorEnergy edgeCofactorEnergy_nonneg hprev
  · intro xi
    rw [← edgeCofactorCharacteristic_eq_charFun]
    exact hchar xi
  · exact norm_sq_pos_ae_conjugateEdgeCofactorLaw hpos

end

end LogdetLean.GramHafnian.SymmetricGaussianHafnian
