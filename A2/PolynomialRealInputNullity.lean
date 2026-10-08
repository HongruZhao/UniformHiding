import A2.PolynomialNullity

open MeasureTheory

noncomputable section

namespace A2Research

/-- Real Lebesgue measure embedded in the complex coefficient field. -/
def complexRealAxisVolume : Measure ℂ :=
  Measure.map ((↑) : ℝ → ℂ) (volume : Measure ℝ)

theorem measurableEmbedding_complex_ofReal :
    MeasurableEmbedding ((↑) : ℝ → ℂ) :=
  Complex.isometry_ofReal.isClosedEmbedding.measurableEmbedding

instance : SigmaFinite complexRealAxisVolume :=
  measurableEmbedding_complex_ofReal.sigmaFinite_map

instance : NullSingletonClass complexRealAxisVolume where
  measure_singleton z := by
    rw [complexRealAxisVolume, Measure.map_apply (by fun_prop) (measurableSet_singleton z)]
    exact ((Set.finite_singleton z).preimage Complex.ofReal_injective.injOn).measure_zero _

/-- A nonzero polynomial with complex coefficients is nonzero almost
everywhere even when all of its variables are restricted to the real axis. -/
theorem ae_complexMvPolynomial_eval_realInput_ne_zero {ι : Type*} [Fintype ι]
    (p : MvPolynomial ι ℂ) (hp : p ≠ 0) :
    ∀ᵐ x ∂(volume : Measure (ι → ℝ)),
      MvPolynomial.eval (fun i ↦ (x i : ℂ)) p ≠ 0 := by
  letI : SigmaFinite (Measure.map ((↑) : ℝ → ℂ) (volume : Measure ℝ)) :=
    measurableEmbedding_complex_ofReal.sigmaFinite_map
  have h := ae_mvPolynomial_eval_ne_zero complexRealAxisVolume p hp
  let embed : (ι → ℝ) → (ι → ℂ) := fun x i ↦ (x i : ℂ)
  have hembed : Measurable embed := by fun_prop
  have hmap : Measure.map embed (volume : Measure (ι → ℝ)) =
      Measure.pi (fun _ : ι ↦ complexRealAxisVolume) := by
    exact Measure.pi_map_pi (fun _ ↦ (show Measurable ((↑) : ℝ → ℂ) by fun_prop).aemeasurable)
  have hs : MeasurableSet {x : ι → ℂ | MvPolynomial.eval x p ≠ 0} := by
    simpa only [Set.compl_setOf] using (p.continuous_eval.measurable.eq_const 0).setOf.compl
  rw [← hmap] at h
  exact (ae_map_iff hembed.aemeasurable hs).mp h

end A2Research
