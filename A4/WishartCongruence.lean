import A4.MatrixLaplaceUniqueness

open MeasureTheory Matrix

noncomputable section

namespace MatsumotoPaper

local instance (d : ℕ) : BorelSpace (RealMatrix d) := ⟨rfl⟩

def SymPosDef.congruence {d : ℕ} (A : RealMatrix d) (hA : IsUnit A)
    (w : SymPosDef d) : SymPosDef d :=
  ⟨A * w.1 * Aᴴ, (hA.posDef_star_right_conjugate_iff).mpr w.2⟩

theorem SymPosDef.measurable_congruence {d : ℕ}
    (A : RealMatrix d) (hA : IsUnit A) :
    Measurable (SymPosDef.congruence A hA) := by
  apply Measurable.subtype_mk
  have hbase : Measurable (fun w : RealMatrix d ↦ A * w * Aᴴ) :=
    (by fun_prop : Continuous (fun w : RealMatrix d ↦ A * w * Aᴴ)).measurable
  exact hbase.comp measurable_subtype_coe

def Sym.congruenceTilt {d : ℕ} (A : RealMatrix d) (theta : Sym d) : Sym d :=
  ⟨Aᴴ * theta.1 * A, Matrix.isHermitian_iff_isSymm.mp
    (Matrix.isHermitian_conjTranspose_mul_mul A
      (Matrix.isHermitian_iff_isSymm.mpr theta.2))⟩

theorem congruence_laplace_domain {d : ℕ} (A : RealMatrix d) (hA : IsUnit A)
    (sigma : SymPosDef d) (theta : Sym d)
    (hgap : ((SymPosDef.congruence A hA sigma).1⁻¹ - theta.1).PosDef) :
    (sigma.1⁻¹ - (Sym.congruenceTilt A theta).1).PosDef := by
  have hright : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A
    ((Matrix.isUnit_iff_isUnit_det A).mp hA)
  have hleft : Aᴴ * (Aᴴ)⁻¹ = 1 := Matrix.mul_nonsing_inv Aᴴ
    ((Matrix.isUnit_iff_isUnit_det Aᴴ).mp hA.star)
  have htrans := hgap.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hA)
  have heq : Aᴴ * ((SymPosDef.congruence A hA sigma).1⁻¹ - theta.1) * A =
      sigma.1⁻¹ - (Sym.congruenceTilt A theta).1 := by
    dsimp only [SymPosDef.congruence, Sym.congruenceTilt]
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
    calc
      _ = (Aᴴ * (Aᴴ)⁻¹) * sigma.1⁻¹ * (A⁻¹ * A) - Aᴴ * theta.1 * A := by
        noncomm_ring
      _ = _ := by rw [hright, hleft]; simp
  rwa [heq] at htrans

theorem congruence_laplace_determinant {d : ℕ} (A : RealMatrix d) (hA : IsUnit A)
    (sigma : SymPosDef d) (theta : Sym d) :
    Matrix.det (1 - (Sym.congruenceTilt A theta).1 * sigma.1) =
      Matrix.det (1 - theta.1 * (SymPosDef.congruence A hA sigma).1) := by
  simpa only [Sym.congruenceTilt, SymPosDef.congruence, Matrix.mul_assoc] using
    Matrix.det_one_sub_mul_comm Aᴴ (theta.1 * A * sigma.1)

theorem etr_congruence {d : ℕ} (A : RealMatrix d) (hA : IsUnit A)
    (theta : Sym d) (w : SymPosDef d) :
    etr (theta.1 * (SymPosDef.congruence A hA w).1) =
      etr ((Sym.congruenceTilt A theta).1 * w.1) := by
  unfold etr SymPosDef.congruence Sym.congruenceTilt
  congr 1
  simpa only [Matrix.mul_assoc] using
    Matrix.trace_mul_cycle theta.1 (A * w.1) Aᴴ

/-- An invertible congruence transforms every characterized real-shape Wishart
law with the corresponding congruence of its scale parameter. -/
def W_d.congruence {d : ℕ} {beta : ℝ} {sigma : SymPosDef d}
    (W : W_d d beta sigma) (A : RealMatrix d) (hA : IsUnit A) :
    W_d d beta (SymPosDef.congruence A hA sigma) where
  toMeasure := W.toMeasure.map (SymPosDef.congruence A hA)
  probability := by
    letI := W.probability
    exact Measure.isProbabilityMeasure_map (SymPosDef.measurable_congruence A hA).aemeasurable
  laplace_transform := by
    intro theta hgap
    have hbase : Measurable (fun w : RealMatrix d ↦ etr (theta.1 * w)) := by
      unfold etr
      exact (by fun_prop : Continuous (fun w : RealMatrix d ↦ Real.exp (Matrix.trace (theta.1 * w)))).measurable
    rw [integral_map (f := fun w : SymPosDef d ↦ etr (theta.1 * w.1))
      (SymPosDef.measurable_congruence A hA).aemeasurable
      (hbase.comp measurable_subtype_coe).aestronglyMeasurable]
    change (∫ w, etr (theta.1 * (SymPosDef.congruence A hA w).1) ∂W.toMeasure) = _
    have hfun : (fun w ↦ etr (theta.1 * (SymPosDef.congruence A hA w).1)) =
        (fun w ↦ etr ((Sym.congruenceTilt A theta).1 * w.1)) :=
      funext (etr_congruence A hA theta)
    rw [hfun, W.laplace_transform (Sym.congruenceTilt A theta)
      (congruence_laplace_domain A hA sigma theta hgap),
      congruence_laplace_determinant A hA sigma theta]

end MatsumotoPaper
