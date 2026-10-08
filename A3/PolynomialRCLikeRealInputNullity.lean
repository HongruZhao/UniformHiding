import A3.Shared.PolynomialNullity

open MeasureTheory
noncomputable section
namespace A3Research

variable (K : Type*) [RCLike K] [MeasurableSpace K] [BorelSpace K]

def rclikeRealAxisVolume : Measure K :=
  Measure.map (RCLike.ofReal : ℝ → K) (volume : Measure ℝ)

theorem measurableEmbedding_rclike_ofReal :
    MeasurableEmbedding (RCLike.ofReal : ℝ → K) :=
  RCLike.ofRealLI.isometry.isClosedEmbedding.measurableEmbedding

instance : SigmaFinite (rclikeRealAxisVolume K) :=
  (measurableEmbedding_rclike_ofReal K).sigmaFinite_map

instance : NullSingletonClass (rclikeRealAxisVolume K) where
  measure_singleton z := by
    rw [rclikeRealAxisVolume, Measure.map_apply RCLike.continuous_ofReal.measurable
      (measurableSet_singleton z)]
    exact ((Set.finite_singleton z).preimage RCLike.ofReal_injective.injOn).measure_zero _

theorem ae_rclikeMvPolynomial_eval_realInput_ne_zero {ι : Type*} [Fintype ι]
    (p : MvPolynomial ι K) (hp : p ≠ 0) :
    ∀ᵐ x ∂(volume : Measure (ι → ℝ)),
      MvPolynomial.eval (fun i ↦ (x i : K)) p ≠ 0 := by
  letI : SigmaFinite (Measure.map (RCLike.ofReal : ℝ → K) (volume : Measure ℝ)) :=
    (measurableEmbedding_rclike_ofReal K).sigmaFinite_map
  have h := ae_mvPolynomial_eval_ne_zero (rclikeRealAxisVolume K) p hp
  let embed : (ι → ℝ) → (ι → K) := fun x i ↦ (x i : K)
  have hembed : Measurable embed := by fun_prop
  have hmap : Measure.map embed (volume : Measure (ι → ℝ)) =
      Measure.pi (fun _ : ι ↦ rclikeRealAxisVolume K) := by
    exact Measure.pi_map_pi (fun _ ↦ RCLike.continuous_ofReal.measurable.aemeasurable)
  have hs : MeasurableSet {x : ι → K | MvPolynomial.eval x p ≠ 0} := by
    simpa only [Set.compl_setOf] using (p.continuous_eval.measurable.eq_const 0).setOf.compl
  rw [← hmap] at h
  exact (ae_map_iff hembed.aemeasurable hs).mp h

end A3Research
