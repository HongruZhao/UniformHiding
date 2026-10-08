import A4.LaplaceIntegrability
import A4.PositiveDefiniteNeighborhood
import A4.LocalTransformUniqueness

open MeasureTheory ProbabilityTheory Filter Set Topology Matrix
open scoped BigOperators

noncomputable section

namespace MatsumotoPaper

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

local instance (d : ℕ) : BorelSpace (RealMatrix d) := ⟨rfl⟩

/-- Every real linear functional on matrices has a symmetric trace representative
when restricted to symmetric matrices. -/
def symmetricTraceRepresentative {d : ℕ} (L : RealMatrix d →ₗ[ℝ] ℝ) : Sym d :=
  ⟨Matrix.of (fun i j ↦ (L (Matrix.single j i 1) + L (Matrix.single i j 1)) / 2), by
    apply Matrix.IsSymm.ext
    intro i j
    change (L (Matrix.single i j 1) + L (Matrix.single j i 1)) / 2 =
      (L (Matrix.single j i 1) + L (Matrix.single i j 1)) / 2
    ring⟩

theorem trace_symmetricTraceRepresentative {d : ℕ}
    (L : RealMatrix d →ₗ[ℝ] ℝ) (X : Sym d) :
    Matrix.trace ((symmetricTraceRepresentative L).1 * X.1) = L X.1 := by
  have hL : L X.1 = ∑ i, ∑ j, X.1 i j * L (Matrix.single i j 1) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single X.1]
    simp only [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    have heq : Matrix.single i j (X.1 i j) =
        X.1 i j • Matrix.single i j (1 : ℝ) := by simp
    rw [heq, map_smul, smul_eq_mul]
  have htranspose :
      (∑ i, ∑ j, X.1 j i * L (Matrix.single j i 1)) =
        ∑ i, ∑ j, X.1 i j * L (Matrix.single i j 1) := by
    exact Finset.sum_comm
  change (∑ i, ∑ j, ((L (Matrix.single j i 1) + L (Matrix.single i j 1)) / 2) *
    X.1 j i) = L X.1
  have hexpand :
      (∑ i, ∑ j, ((L (Matrix.single j i 1) + L (Matrix.single i j 1)) / 2) * X.1 j i) =
      (∑ i, ∑ j, X.1 j i * L (Matrix.single j i 1)) / 2 +
      (∑ i, ∑ j, X.1 j i * L (Matrix.single i j 1)) / 2 := by
    simp only [Finset.sum_div, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hexpand]
  rw [htranspose]
  have hsym : ∀ i j, X.1 j i = X.1 i j := fun i j ↦ X.2.apply i j
  simp_rw [hsym]
  rw [← hL]
  ring

/-- The law of a Wishart matrix viewed in the ambient finite-dimensional matrix
space. This does not construct the real-shape density. -/
def W_d.matrixLaw {d : ℕ} {beta : ℝ} {sigma : SymPosDef d}
    (W : W_d d beta sigma) : Measure (RealMatrix d) :=
  W.toMeasure.map Subtype.val

instance W_d.matrixLaw_isProbabilityMeasure {d : ℕ} {beta : ℝ}
    {sigma : SymPosDef d} (W : W_d d beta sigma) :
    IsProbabilityMeasure W.matrixLaw := by
  letI := W.probability
  exact Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable

def Sym.scale {d : ℕ} (theta : Sym d) (t : ℝ) : Sym d :=
  ⟨t • theta.1, by rw [Matrix.IsSymm, Matrix.transpose_smul, theta.2.eq]⟩

theorem etr_scale_traceRepresentative {d : ℕ}
    (L : RealMatrix d →ₗ[ℝ] ℝ) (t : ℝ) (w : SymPosDef d) :
    etr ((Sym.scale (symmetricTraceRepresentative L) t).1 * w.1) =
      Real.exp (t * L w.1) := by
  rw [etr, Sym.scale, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  rw [trace_symmetricTraceRepresentative L
    (⟨w.1, Matrix.isHermitian_iff_isSymm.mp w.2.isHermitian⟩ : Sym d)]

theorem W_d.integrable_exp_linearFunctional {d : ℕ} {beta : ℝ}
    {sigma : SymPosDef d} (W : W_d d beta sigma)
    (L : StrongDual ℝ (RealMatrix d)) (t : ℝ)
    (hgap : (sigma.1⁻¹ - t • (symmetricTraceRepresentative L.toLinearMap).1).PosDef) :
    Integrable (fun w : RealMatrix d ↦ Real.exp (t * L w)) W.matrixLaw := by
  have hcont : Continuous (fun w : RealMatrix d ↦ Real.exp (t * L w)) := by fun_prop
  apply (integrable_map_measure hcont.measurable.aestronglyMeasurable
    measurable_subtype_coe.aemeasurable).mpr
  exact (W.integrable_etr (Sym.scale (symmetricTraceRepresentative L.toLinearMap) t) hgap).congr
    (Eventually.of_forall fun w ↦ etr_scale_traceRepresentative L.toLinearMap t w)

theorem W_d.interior_integrableExpSet_linearFunctional {d : ℕ} {beta : ℝ}
    {sigma : SymPosDef d} (W : W_d d beta sigma)
    (L : StrongDual ℝ (RealMatrix d)) :
    0 ∈ interior (integrableExpSet L W.matrixLaw) := by
  rw [mem_interior_iff_mem_nhds]
  have hpos : ∀ᶠ t : ℝ in 𝓝 0,
      (sigma.1⁻¹ - t • (symmetricTraceRepresentative L.toLinearMap).1).PosDef :=
    A4Research.eventually_posDef_sub_smul sigma.2.inv
      (Matrix.isHermitian_iff_isSymm.mpr (symmetricTraceRepresentative L.toLinearMap).2)
  exact hpos.mono fun t ht ↦ W.integrable_exp_linearFunctional L t ht

theorem W_d.mgf_linearFunctional {d : ℕ} {beta : ℝ}
    {sigma : SymPosDef d} (W : W_d d beta sigma)
    (L : StrongDual ℝ (RealMatrix d)) (t : ℝ)
    (hgap : (sigma.1⁻¹ - t • (symmetricTraceRepresentative L.toLinearMap).1).PosDef) :
    mgf L W.matrixLaw t =
      Real.rpow (Matrix.det (1 - (t • (symmetricTraceRepresentative L.toLinearMap).1) *
        sigma.1)) (-beta) := by
  have hcont : Continuous (fun w : RealMatrix d ↦ Real.exp (t * L w)) := by fun_prop
  rw [W_d.matrixLaw, mgf_map measurable_subtype_coe.aemeasurable
    hcont.measurable.aestronglyMeasurable]
  change (∫ w : SymPosDef d, Real.exp (t * L w.1) ∂W.toMeasure) = _
  calc
    _ = ∫ w : SymPosDef d,
        etr ((Sym.scale (symmetricTraceRepresentative L.toLinearMap) t).1 * w.1)
          ∂W.toMeasure := integral_congr_ae
      (Eventually.of_forall fun w ↦ (etr_scale_traceRepresentative L.toLinearMap t w).symm)
    _ = _ := W.laplace_transform (Sym.scale (symmetricTraceRepresentative L.toLinearMap) t) hgap

set_option backward.isDefEq.respectTransparency false in
/-- The matrix Laplace characterization determines the ambient matrix law for
every real shape for which a `W_d` value exists. -/
theorem W_d.matrixLaw_eq {d : ℕ} {beta : ℝ} {sigma : SymPosDef d}
    (W V : W_d d beta sigma) : W.matrixLaw = V.matrixLaw := by
  haveI : BorelSpace (RealMatrix d) := ⟨rfl⟩
  apply @A4Research.measure_eq_of_directional_mgf_eventually_eq (RealMatrix d)
    Matrix.normedAddCommGroup Matrix.normedSpace
    (inferInstance : MeasurableSpace (RealMatrix d))
    (inferInstance : BorelSpace (RealMatrix d)) _ _ W.matrixLaw V.matrixLaw _ _
  · exact W.interior_integrableExpSet_linearFunctional
  · exact V.interior_integrableExpSet_linearFunctional
  intro L
  have hpos := A4Research.eventually_posDef_sub_smul sigma.2.inv
    (Matrix.isHermitian_iff_isSymm.mpr (symmetricTraceRepresentative L.toLinearMap).2)
  filter_upwards [hpos] with t ht
  exact (W.mgf_linearFunctional L t ht).trans (V.mgf_linearFunctional L t ht).symm

/-- Equality of characterized Wishart laws on the original positive-definite
subtype, with its exact original measurable structure. -/
theorem W_d.toMeasure_eq {d : ℕ} {beta : ℝ} {sigma : SymPosDef d}
    (W V : W_d d beta sigma) : W.toMeasure = V.toMeasure := by
  have hmap := W.matrixLaw_eq V
  ext s hs
  change ∃ t : Set (RealMatrix d), MeasurableSet t ∧ Subtype.val ⁻¹' t = s at hs
  obtain ⟨t, ht, rfl⟩ := hs
  rw [← Measure.map_apply measurable_subtype_coe ht,
    ← Measure.map_apply measurable_subtype_coe ht]
  exact congrArg (fun μ : Measure (RealMatrix d) ↦ μ t) hmap

/-- The probability measure and the transform are the only fields in `W_d`. -/
theorem W_d.ext {d : ℕ} {beta : ℝ} {sigma : SymPosDef d}
    (W V : W_d d beta sigma) : W = V := by
  cases W with | mk μ hμ hL =>
    cases V with | mk ν hν hM =>
      have heq : μ = ν := W_d.toMeasure_eq ⟨μ, hμ, hL⟩ ⟨ν, hν, hM⟩
      subst ν
      rfl

end MatsumotoPaper
