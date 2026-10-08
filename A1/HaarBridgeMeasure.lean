import A1.GaussianFrameAlgebra

open MeasureTheory Matrix
open LogdetLean.GramHafnian.LocalAnticoncentration
open scoped BigOperators ENNReal

noncomputable section
namespace A1Research

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

local instance unitaryCompact (n : ℕ) : CompactSpace (Matrix.unitaryGroup (Fin n) ℂ) :=
  isCompact_iff_compactSpace.mp (unitaryGroup_carrier_isCompact n)

instance unitaryHaar_isHaar (n : ℕ) :
    Measure.IsHaarMeasure (unitaryHaarProbabilityMeasure n) := by
  unfold unitaryHaarProbabilityMeasure
  infer_instance

/-- Right invariance of the exact normalized Haar measure in the original A1 target. -/
instance unitaryHaar_isMulRightInvariant (n : ℕ) :
    Measure.IsMulRightInvariant (unitaryHaarProbabilityMeasure n) := by
  constructor
  intro U
  letI : IsProbabilityMeasure
      ((unitaryHaarProbabilityMeasure n).map (fun V ↦ V * U)) :=
    Measure.isProbabilityMeasure_map (measurable_mul_const U).aemeasurable
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure
    ((unitaryHaarProbabilityMeasure n).map (fun V ↦ V * U))
    (unitaryHaarProbabilityMeasure n)

instance unitaryHaar_isInvInvariant (n : ℕ) :
    Measure.IsInvInvariant (unitaryHaarProbabilityMeasure n) := by
  let mu := unitaryHaarProbabilityMeasure n
  letI : IsProbabilityMeasure mu.inv := by
    change IsProbabilityMeasure (mu.map Inv.inv)
    exact Measure.isProbabilityMeasure_map measurable_inv.aemeasurable
  letI : Measure.IsHaarMeasure mu.inv :=
    Measure.isHaarMeasure_of_isCompact_nonempty_interior mu.inv Set.univ isCompact_univ
      (by simp) (by simp) (measure_ne_top _ _)
  exact ⟨Measure.isHaarMeasure_eq_of_isProbabilityMeasure mu.inv mu⟩

def unitaryConjugateHom (n : ℕ) :
    Matrix.unitaryGroup (Fin n) ℂ →* Matrix.unitaryGroup (Fin n) ℂ where
  toFun := UnitaryGroup.map_star
  map_one' := by
    apply Subtype.ext
    simp [UnitaryGroup.map_star]
  map_mul' U V := by
    apply Subtype.ext
    change ((U : Matrix (Fin n) (Fin n) ℂ) * V).map star =
      (U : Matrix (Fin n) (Fin n) ℂ).map star *
        (V : Matrix (Fin n) (Fin n) ℂ).map star
    exact Matrix.map_mul (f := starRingEnd ℂ)

theorem continuous_unitaryConjugateHom (n : ℕ) :
    Continuous (unitaryConjugateHom n) := by
  apply Continuous.subtype_mk
  change Continuous (fun U : Matrix.unitaryGroup (Fin n) ℂ ↦
    (U : Matrix (Fin n) (Fin n) ℂ).map star)
  fun_prop

theorem unitaryConjugateHom_surjective (n : ℕ) :
    Function.Surjective (unitaryConjugateHom n) := by
  intro U
  refine ⟨UnitaryGroup.map_star U, ?_⟩
  apply Subtype.ext
  ext i j
  simp [unitaryConjugateHom, UnitaryGroup.map_star]

theorem measurePreserving_unitaryConjugate (n : ℕ) :
    MeasurePreserving (UnitaryGroup.map_star :
      Matrix.unitaryGroup (Fin n) ℂ → Matrix.unitaryGroup (Fin n) ℂ)
      (unitaryHaarProbabilityMeasure n) (unitaryHaarProbabilityMeasure n) := by
  exact MonoidHom.measurePreserving (continuous_unitaryConjugateHom n)
    (unitaryConjugateHom_surjective n) rfl

/-- Ordinary transpose preserves the original normalized unitary Haar law. -/
theorem measurePreserving_unitaryTranspose (n : ℕ) :
    MeasurePreserving (UnitaryGroup.transpose :
      Matrix.unitaryGroup (Fin n) ℂ → Matrix.unitaryGroup (Fin n) ℂ)
      (unitaryHaarProbabilityMeasure n) (unitaryHaarProbabilityMeasure n) := by
  simpa only [Function.comp_def, UnitaryGroup.map_star_inv_eq_transpose] using
    (Measure.measurePreserving_inv (unitaryHaarProbabilityMeasure n)).comp
      (measurePreserving_unitaryConjugate n)

theorem measurable_firstColumns {n m : ℕ} (hmn : m ≤ n) :
    Measurable (firstColumns hmn) := by
  unfold firstColumns
  refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
  exact (measurable_pi_apply (Fin.castLE hmn j)).comp
    ((measurable_pi_apply i).comp measurable_subtype_coe)

theorem measurable_unitary_matrix_left_action (n m : ℕ) :
    Measurable (fun z : Matrix.unitaryGroup (Fin n) ℂ × Matrix (Fin n) (Fin m) ℂ ↦
      (z.1 : Matrix (Fin n) (Fin n) ℂ) * z.2) := by
  refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
  change Measurable (fun z : Matrix.unitaryGroup (Fin n) ℂ ×
      Matrix (Fin n) (Fin m) ℂ ↦
    ∑ k : Fin n, (z.1 : Matrix (Fin n) (Fin n) ℂ) i k * z.2 k j)
  refine Finset.measurable_sum _ fun k _ ↦ ?_
  have h1 : Measurable (fun z : Matrix.unitaryGroup (Fin n) ℂ ×
      Matrix (Fin n) (Fin m) ℂ ↦ (z.1 : Matrix (Fin n) (Fin n) ℂ) i k) :=
    (measurable_pi_apply k).comp ((measurable_pi_apply i).comp
      (measurable_subtype_coe.comp measurable_fst))
  have h2 : Measurable (fun z : Matrix.unitaryGroup (Fin n) ℂ ×
      Matrix (Fin n) (Fin m) ℂ ↦ z.2 k j) :=
    (measurable_pi_apply j).comp ((measurable_pi_apply k).comp measurable_snd)
  exact h1.mul h2

end A1Research
