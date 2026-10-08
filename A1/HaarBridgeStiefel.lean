import A1.HaarBridgeMeasure

open MeasureTheory Matrix
open LogdetLean.GramHafnian.LocalAnticoncentration
open scoped ENNReal

noncomputable section
namespace A1Research

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem haar_average_frame_independent {n m : ℕ} (hmn : m ≤ n)
    (Q : Matrix (Fin n) (Fin m) ℂ) (hQ : Q.conjTranspose * Q = 1)
    (f : Matrix (Fin n) (Fin m) ℂ → ℝ≥0∞) :
    (∫⁻ U : Matrix.unitaryGroup (Fin n) ℂ,
      f ((U : Matrix (Fin n) (Fin n) ℂ) * Q)
      ∂unitaryHaarProbabilityMeasure n) =
    ∫⁻ U : Matrix.unitaryGroup (Fin n) ℂ,
      f (firstColumns hmn U) ∂unitaryHaarProbabilityMeasure n := by
  obtain ⟨V, hV⟩ := exists_unitary_firstColumns hmn Q hQ
  have heq : (fun U : Matrix.unitaryGroup (Fin n) ℂ ↦
      f ((U : Matrix (Fin n) (Fin n) ℂ) * Q)) =
      (fun U ↦ f (firstColumns hmn (U * V))) := by
    funext U
    rw [firstColumns_mul, hV]
  rw [heq]
  exact lintegral_mul_right_eq_self (fun U ↦ f (firstColumns hmn U)) V

/-- A probability on actual orthonormal rectangular frames invariant under every left
unitary multiplication is exactly the leading-column Haar law. The proof is direct
Tonelli averaging; no quotient, disintegration, or measurable completion is assumed. -/
theorem stiefel_probability_eq_haar_firstColumns {n m : ℕ} (hmn : m ≤ n)
    (mu : Measure (Matrix (Fin n) (Fin m) ℂ)) [IsProbabilityMeasure mu]
    (hframe : ∀ᵐ Q ∂mu, Q.conjTranspose * Q = 1)
    (hinvariant : ∀ U : Matrix.unitaryGroup (Fin n) ℂ,
      mu.map (fun Q ↦ (U : Matrix (Fin n) (Fin n) ℂ) * Q) = mu) :
    mu = (unitaryHaarProbabilityMeasure n).map (firstColumns hmn) := by
  refine Measure.ext_of_lintegral _ fun f hf ↦ ?_
  have haction : ∀ U : Matrix.unitaryGroup (Fin n) ℂ,
      Measurable (fun Q : Matrix (Fin n) (Fin m) ℂ ↦
        (U : Matrix (Fin n) (Fin n) ℂ) * Q) := by
    intro U
    exact (measurable_unitary_matrix_left_action n m).comp
      (measurable_const.prodMk measurable_id)
  have hintegral (U : Matrix.unitaryGroup (Fin n) ℂ) :
      (∫⁻ Q, f ((U : Matrix (Fin n) (Fin n) ℂ) * Q) ∂mu) =
        ∫⁻ Q, f Q ∂mu := by
    rw [← lintegral_map hf (haction U), hinvariant U]
  calc
    ∫⁻ Q, f Q ∂mu =
        ∫⁻ U : Matrix.unitaryGroup (Fin n) ℂ,
          ∫⁻ Q, f ((U : Matrix (Fin n) (Fin n) ℂ) * Q) ∂mu
          ∂unitaryHaarProbabilityMeasure n := by
      simp only [hintegral, lintegral_const, measure_univ, mul_one]
    _ = ∫⁻ Q, ∫⁻ U : Matrix.unitaryGroup (Fin n) ℂ,
          f ((U : Matrix (Fin n) (Fin n) ℂ) * Q)
          ∂unitaryHaarProbabilityMeasure n ∂mu :=
      lintegral_lintegral_swap
        ((hf.comp (measurable_unitary_matrix_left_action n m)).aemeasurable)
    _ = ∫⁻ Q, ∫⁻ U : Matrix.unitaryGroup (Fin n) ℂ,
          f (firstColumns hmn U) ∂unitaryHaarProbabilityMeasure n ∂mu := by
      apply lintegral_congr_ae
      filter_upwards [hframe] with Q hQ
      exact haar_average_frame_independent hmn Q hQ f
    _ = ∫⁻ Q, f Q ∂(unitaryHaarProbabilityMeasure n).map (firstColumns hmn) := by
      rw [lintegral_const, measure_univ, mul_one,
        lintegral_map hf (measurable_firstColumns hmn)]

end A1Research
