import A4.GaussianWishartLaw
import A4.WishartCongruence
import A4.TriangularFactorization

open MeasureTheory ProbabilityTheory Filter Set Topology Matrix
open scoped BigOperators

noncomputable section

namespace A4Research

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

local instance (d : ℕ) : BorelSpace (MatsumotoPaper.RealMatrix d) := ⟨rfl⟩

def scaledStandardGaussianGram {k d : ℕ} (A : MatsumotoPaper.RealMatrix d)
    (z : Fin k → Fin d → ℝ) : MatsumotoPaper.RealMatrix d :=
  A * standardGaussianGram z * Aᴴ

theorem scaledStandardGaussianGram_isSymm {k d : ℕ}
    (A : MatsumotoPaper.RealMatrix d) (z : Fin k → Fin d → ℝ) :
    (scaledStandardGaussianGram A z).IsSymm := by
  apply Matrix.isHermitian_iff_isSymm.mp
  exact Matrix.isHermitian_mul_mul_conjTranspose A
    (Matrix.isHermitian_iff_isSymm.mpr (standardGaussianGram_isSymm z))

theorem measurable_scaledStandardGaussianGram {k d : ℕ}
    (A : MatsumotoPaper.RealMatrix d) :
    Measurable (scaledStandardGaussianGram (k := k) A) := by
  have hA : Measurable (fun X : MatsumotoPaper.RealMatrix d ↦ A * X * Aᴴ) :=
    (by fun_prop : Continuous (fun X : MatsumotoPaper.RealMatrix d ↦ A * X * Aᴴ)).measurable
  exact hA.comp (measurable_standardGaussianGram k d)

theorem etr_scaledStandardGaussianGram {k d : ℕ}
    (A : MatsumotoPaper.RealMatrix d) (theta : MatsumotoPaper.Sym d)
    (z : Fin k → Fin d → ℝ) :
    MatsumotoPaper.etr (theta.1 * scaledStandardGaussianGram A z) =
      MatsumotoPaper.etr
        ((MatsumotoPaper.Sym.congruenceTilt A theta).1 * standardGaussianGram z) := by
  unfold MatsumotoPaper.etr scaledStandardGaussianGram MatsumotoPaper.Sym.congruenceTilt
  congr 1
  simpa only [Matrix.mul_assoc] using
    Matrix.trace_mul_cycle theta.1 (A * standardGaussianGram z) Aᴴ

theorem scaledStandardGaussianGram_integral_etr {k d : ℕ}
    (A : MatsumotoPaper.RealMatrix d) (hA : IsUnit A)
    (theta : MatsumotoPaper.Sym d)
    (hgap : ((MatsumotoPaper.SymPosDef.congruence A hA
      (MatsumotoPaper.identityScale d)).1⁻¹ - theta.1).PosDef) :
    (∫ z, MatsumotoPaper.etr (theta.1 * scaledStandardGaussianGram A z)
      ∂standardGaussianRows k d) =
      Matrix.det (1 - theta.1 * (MatsumotoPaper.SymPosDef.congruence A hA
        (MatsumotoPaper.identityScale d)).1) ^ (-((k : ℝ) / 2)) := by
  simp_rw [etr_scaledStandardGaussianGram]
  have hpos := MatsumotoPaper.congruence_laplace_domain A hA
    (MatsumotoPaper.identityScale d) theta hgap
  simp only [MatsumotoPaper.identityScale, inv_one] at hpos
  rw [standardGaussianGram_integral_etr (MatsumotoPaper.Sym.congruenceTilt A theta) hpos]
  have hdet := MatsumotoPaper.congruence_laplace_determinant A hA
    (MatsumotoPaper.identityScale d) theta
  simpa only [MatsumotoPaper.identityScale, Matrix.mul_one] using
    congrArg (fun x : ℝ ↦ x ^ (-((k : ℝ) / 2))) hdet

/-- The explicit Gaussian covariance factor for an arbitrary SPD scale. -/
def gaussianScaleFactor {d : ℕ} (sigma : MatsumotoPaper.SymPosDef d) :
    MatsumotoPaper.RealMatrix d := cholesky sigma.2

theorem gaussianScaleFactor_isUnit {d : ℕ} (sigma : MatsumotoPaper.SymPosDef d) :
    IsUnit (gaussianScaleFactor sigma) := cholesky_isUnit sigma.2

theorem gaussianScaleFactor_congruence {d : ℕ}
    (sigma : MatsumotoPaper.SymPosDef d) :
    MatsumotoPaper.SymPosDef.congruence (gaussianScaleFactor sigma)
      (gaussianScaleFactor_isUnit sigma) (MatsumotoPaper.identityScale d) = sigma := by
  apply Subtype.ext
  simpa only [MatsumotoPaper.SymPosDef.congruence, MatsumotoPaper.identityScale,
    Matrix.mul_one, Matrix.conjTranspose_eq_transpose_of_trivial, gaussianScaleFactor] using
      cholesky_mul_transpose sigma.2

def gaussianWishartGram {k d : ℕ} (sigma : MatsumotoPaper.SymPosDef d)
    (z : Fin k → Fin d → ℝ) : MatsumotoPaper.RealMatrix d :=
  scaledStandardGaussianGram (gaussianScaleFactor sigma) z

def gaussianWishartLaw (k : ℕ) {d : ℕ} (sigma : MatsumotoPaper.SymPosDef d) :
    Measure (MatsumotoPaper.RealMatrix d) :=
  (standardGaussianRows k d).map (gaussianWishartGram sigma)

theorem measurable_gaussianWishartGram {k d : ℕ}
    (sigma : MatsumotoPaper.SymPosDef d) :
    Measurable (gaussianWishartGram (k := k) sigma) :=
  measurable_scaledStandardGaussianGram (gaussianScaleFactor sigma)

instance (k : ℕ) {d : ℕ} (sigma : MatsumotoPaper.SymPosDef d) :
    IsProbabilityMeasure (gaussianWishartLaw k sigma) := by
  unfold gaussianWishartLaw
  exact Measure.isProbabilityMeasure_map (measurable_gaussianWishartGram sigma).aemeasurable

theorem gaussianWishartGram_integral_etr {k d : ℕ}
    (sigma : MatsumotoPaper.SymPosDef d) (theta : MatsumotoPaper.Sym d)
    (hgap : (sigma.1⁻¹ - theta.1).PosDef) :
    (∫ z, MatsumotoPaper.etr (theta.1 * gaussianWishartGram sigma z)
      ∂standardGaussianRows k d) =
      Matrix.det (1 - theta.1 * sigma.1) ^ (-((k : ℝ) / 2)) := by
  have h := scaledStandardGaussianGram_integral_etr (k := k)
    (gaussianScaleFactor sigma) (gaussianScaleFactor_isUnit sigma) theta
  rw [gaussianScaleFactor_congruence sigma] at h
  exact h hgap

theorem etr_scale_traceRepresentative_gaussianWishart {k d : ℕ}
    (sigma : MatsumotoPaper.SymPosDef d)
    (L : MatsumotoPaper.RealMatrix d →ₗ[ℝ] ℝ) (t : ℝ)
    (z : Fin k → Fin d → ℝ) :
    MatsumotoPaper.etr
      ((MatsumotoPaper.Sym.scale (MatsumotoPaper.symmetricTraceRepresentative L) t).1 *
        gaussianWishartGram sigma z) = Real.exp (t * L (gaussianWishartGram sigma z)) := by
  rw [MatsumotoPaper.etr, MatsumotoPaper.Sym.scale,
    Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  rw [MatsumotoPaper.trace_symmetricTraceRepresentative L
    (⟨gaussianWishartGram sigma z,
      scaledStandardGaussianGram_isSymm (gaussianScaleFactor sigma) z⟩ : MatsumotoPaper.Sym d)]

theorem gaussianWishartLaw_mgf {k d : ℕ}
    (sigma : MatsumotoPaper.SymPosDef d)
    (L : StrongDual ℝ (MatsumotoPaper.RealMatrix d)) (t : ℝ)
    (hgap : (sigma.1⁻¹ -
      t • (MatsumotoPaper.symmetricTraceRepresentative L.toLinearMap).1).PosDef) :
    mgf L (gaussianWishartLaw k sigma) t =
      Real.rpow (Matrix.det (1 -
        (t • (MatsumotoPaper.symmetricTraceRepresentative L.toLinearMap).1) * sigma.1))
        (-((k : ℝ) / 2)) := by
  rw [gaussianWishartLaw, mgf_map
    (measurable_gaussianWishartGram sigma).aemeasurable (by fun_prop)]
  calc
    _ = ∫ z, MatsumotoPaper.etr
        ((MatsumotoPaper.Sym.scale
          (MatsumotoPaper.symmetricTraceRepresentative L.toLinearMap) t).1 *
          gaussianWishartGram sigma z) ∂standardGaussianRows k d := by
      exact integral_congr_ae (Eventually.of_forall fun z ↦
        (etr_scale_traceRepresentative_gaussianWishart sigma L.toLinearMap t z).symm)
    _ = _ := gaussianWishartGram_integral_etr sigma
      (MatsumotoPaper.Sym.scale
        (MatsumotoPaper.symmetricTraceRepresentative L.toLinearMap) t) hgap

theorem gaussianWishartLaw_interior_integrableExpSet {k d : ℕ}
    (sigma : MatsumotoPaper.SymPosDef d)
    (L : StrongDual ℝ (MatsumotoPaper.RealMatrix d)) :
    0 ∈ interior (integrableExpSet L (gaussianWishartLaw k sigma)) := by
  rw [mem_interior_iff_mem_nhds]
  have hpos := eventually_posDef_sub_smul sigma.2.inv
    (Matrix.isHermitian_iff_isSymm.mpr
      (MatsumotoPaper.symmetricTraceRepresentative L.toLinearMap).2)
  apply hpos.mono
  intro t ht
  apply Integrable.of_integral_ne_zero
  change mgf L (gaussianWishartLaw k sigma) t ≠ 0
  rw [gaussianWishartLaw_mgf sigma L t ht]
  exact (Real.rpow_pos_of_pos
    (MatsumotoPaper.laplace_determinant_pos sigma
      (MatsumotoPaper.Sym.scale
        (MatsumotoPaper.symmetricTraceRepresentative L.toLinearMap) t) ht) _).ne'

end A4Research

namespace MatsumotoPaper

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

local instance (d : ℕ) : BorelSpace (RealMatrix d) := ⟨rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-- The actual Gaussian Gram law agrees with every `W_d` at its natural
half-integer shape and arbitrary positive-definite scale. -/
theorem W_d.matrixLaw_eq_gaussianWishartLaw {k d : ℕ} {sigma : SymPosDef d}
    (W : W_d d ((k : ℝ) / 2) sigma) :
    W.matrixLaw = A4Research.gaussianWishartLaw k sigma := by
  haveI : BorelSpace (RealMatrix d) := ⟨rfl⟩
  apply @A4Research.measure_eq_of_directional_mgf_eventually_eq (RealMatrix d)
    Matrix.normedAddCommGroup Matrix.normedSpace
    (inferInstance : MeasurableSpace (RealMatrix d))
    (inferInstance : BorelSpace (RealMatrix d)) _ _
    W.matrixLaw (A4Research.gaussianWishartLaw k sigma) _ _
  · exact W.interior_integrableExpSet_linearFunctional
  · exact A4Research.gaussianWishartLaw_interior_integrableExpSet sigma
  intro L
  have hpos := A4Research.eventually_posDef_sub_smul sigma.2.inv
    (Matrix.isHermitian_iff_isSymm.mpr (symmetricTraceRepresentative L.toLinearMap).2)
  filter_upwards [hpos] with t ht
  exact (W.mgf_linearFunctional L t ht).trans
    (A4Research.gaussianWishartLaw_mgf sigma L t ht).symm

end MatsumotoPaper
