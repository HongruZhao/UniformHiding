import A4.GaussianWishartBridge

open MeasureTheory ProbabilityTheory Filter Set Topology Matrix
open scoped BigOperators

noncomputable section

namespace MatsumotoPaper

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

local instance (d : ℕ) : BorelSpace (RealMatrix d) := ⟨rfl⟩

def identityScale (d : ℕ) : SymPosDef d := ⟨1, Matrix.PosDef.one⟩

end MatsumotoPaper

namespace A4Research

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

local instance (d : ℕ) : BorelSpace (MatsumotoPaper.RealMatrix d) := ⟨rfl⟩

def standardGaussianGramLaw (k d : ℕ) : Measure (MatsumotoPaper.RealMatrix d) :=
  (standardGaussianRows k d).map standardGaussianGram

instance (k d : ℕ) : IsProbabilityMeasure (standardGaussianGramLaw k d) := by
  unfold standardGaussianGramLaw
  exact Measure.isProbabilityMeasure_map (measurable_standardGaussianGram k d).aemeasurable

theorem etr_scale_traceRepresentative_gram {k d : ℕ}
    (L : MatsumotoPaper.RealMatrix d →ₗ[ℝ] ℝ) (t : ℝ)
    (z : Fin k → Fin d → ℝ) :
    MatsumotoPaper.etr
      ((MatsumotoPaper.Sym.scale (MatsumotoPaper.symmetricTraceRepresentative L) t).1 *
        standardGaussianGram z) = Real.exp (t * L (standardGaussianGram z)) := by
  rw [MatsumotoPaper.etr, MatsumotoPaper.Sym.scale,
    Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  rw [MatsumotoPaper.trace_symmetricTraceRepresentative L
    (⟨standardGaussianGram z, standardGaussianGram_isSymm z⟩ : MatsumotoPaper.Sym d)]

theorem standardGaussianGramLaw_mgf {k d : ℕ}
    (L : StrongDual ℝ (MatsumotoPaper.RealMatrix d)) (t : ℝ)
    (hpos : (1 - t • (MatsumotoPaper.symmetricTraceRepresentative L.toLinearMap).1).PosDef) :
    mgf L (standardGaussianGramLaw k d) t =
      Matrix.det (1 - t • (MatsumotoPaper.symmetricTraceRepresentative L.toLinearMap).1) ^
        (-((k : ℝ) / 2)) := by
  rw [standardGaussianGramLaw, mgf_map
    (measurable_standardGaussianGram k d).aemeasurable (by fun_prop)]
  calc
    _ = ∫ z, MatsumotoPaper.etr
        ((MatsumotoPaper.Sym.scale
          (MatsumotoPaper.symmetricTraceRepresentative L.toLinearMap) t).1 *
          standardGaussianGram z) ∂standardGaussianRows k d := by
      exact integral_congr_ae (Eventually.of_forall fun z ↦
        (etr_scale_traceRepresentative_gram L.toLinearMap t z).symm)
    _ = _ := standardGaussianGram_integral_etr
      (MatsumotoPaper.Sym.scale
        (MatsumotoPaper.symmetricTraceRepresentative L.toLinearMap) t) hpos

theorem standardGaussianGramLaw_integrable_exp {k d : ℕ}
    (L : StrongDual ℝ (MatsumotoPaper.RealMatrix d)) (t : ℝ)
    (hpos : (1 - t • (MatsumotoPaper.symmetricTraceRepresentative L.toLinearMap).1).PosDef) :
    Integrable (fun X ↦ Real.exp (t * L X)) (standardGaussianGramLaw k d) := by
  apply Integrable.of_integral_ne_zero
  change mgf L (standardGaussianGramLaw k d) t ≠ 0
  rw [standardGaussianGramLaw_mgf L t hpos]
  exact (Real.rpow_pos_of_pos hpos.det_pos _).ne'

theorem standardGaussianGramLaw_interior_integrableExpSet {k d : ℕ}
    (L : StrongDual ℝ (MatsumotoPaper.RealMatrix d)) :
    0 ∈ interior (integrableExpSet L (standardGaussianGramLaw k d)) := by
  rw [mem_interior_iff_mem_nhds]
  have hpos := eventually_posDef_sub_smul
    (Matrix.PosDef.one : (1 : MatsumotoPaper.RealMatrix d).PosDef)
    (Matrix.isHermitian_iff_isSymm.mpr
      (MatsumotoPaper.symmetricTraceRepresentative L.toLinearMap).2)
  exact hpos.mono fun t ht ↦ standardGaussianGramLaw_integrable_exp L t ht

end A4Research

namespace MatsumotoPaper

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

local instance (d : ℕ) : BorelSpace (RealMatrix d) := ⟨rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-- The exact identity-scale Wishart law at shape `k/2` equals the actual
Gaussian Gram law. Equality is on the ambient matrix space, so the transform
comparison needs no separately assumed full-rank event. -/
theorem W_d.matrixLaw_eq_standardGaussianGramLaw {k d : ℕ}
    (W : W_d d ((k : ℝ) / 2) (identityScale d)) :
    W.matrixLaw = A4Research.standardGaussianGramLaw k d := by
  haveI : BorelSpace (RealMatrix d) := ⟨rfl⟩
  apply @A4Research.measure_eq_of_directional_mgf_eventually_eq (RealMatrix d)
    Matrix.normedAddCommGroup Matrix.normedSpace
    (inferInstance : MeasurableSpace (RealMatrix d))
    (inferInstance : BorelSpace (RealMatrix d)) _ _
    W.matrixLaw (A4Research.standardGaussianGramLaw k d) _ _
  · exact W.interior_integrableExpSet_linearFunctional
  · exact A4Research.standardGaussianGramLaw_interior_integrableExpSet
  intro L
  have hpos := A4Research.eventually_posDef_sub_smul
    (Matrix.PosDef.one : (1 : RealMatrix d).PosDef)
    (Matrix.isHermitian_iff_isSymm.mpr (symmetricTraceRepresentative L.toLinearMap).2)
  filter_upwards [hpos] with t ht
  have hgap : ((identityScale d).1⁻¹ -
      t • (symmetricTraceRepresentative L.toLinearMap).1).PosDef := by
    simpa only [identityScale, inv_one] using ht
  have hW := W.mgf_linearFunctional L t hgap
  have hG := A4Research.standardGaussianGramLaw_mgf (k := k) L t ht
  have hW' : mgf L W.matrixLaw t =
      Matrix.det (1 - t • (symmetricTraceRepresentative L.toLinearMap).1) ^
        (-((k : ℝ) / 2)) := by
    simpa only [identityScale, Matrix.mul_one, Real.rpow_eq_pow] using hW
  exact hW'.trans hG.symm

end MatsumotoPaper
