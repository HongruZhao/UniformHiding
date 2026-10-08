import A4.InverseSteinMatrixGaussian
import A4.InverseSteinProductDerivative
import A4.GaussianWishartLaw
import A4.WishartDensityInverseLp

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix ENNReal NNReal

noncomputable section
namespace A4Research.InverseStein

set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def scaledStandardRows {k d : ℕ} (z : Fin k → Fin d → ℝ) :
    Matrix (Fin k) (Fin d) ℝ :=
  Matrix.of fun a i ↦ (Real.sqrt 2)⁻¹ * z a i

theorem measurable_scaledStandardRows (k d : ℕ) :
    Measurable (scaledStandardRows : (Fin k → Fin d → ℝ) →
      Matrix (Fin k) (Fin d) ℝ) := by
  apply Continuous.measurable
  change Continuous (fun z : Fin k → Fin d → ℝ ↦
    fun a i ↦ (Real.sqrt 2)⁻¹ * z a i)
  fun_prop

theorem map_standardGaussianRows_scaled (k d : ℕ) :
    (A4Research.standardGaussianRows k d).map scaledStandardRows =
      halfGaussianMatrix k d := by
  let scale : (Fin k → Fin d → ℝ) → (Fin k → Fin d → ℝ) :=
    fun z a i ↦ (Real.sqrt 2)⁻¹ * z a i
  have hscale : Measurable scale := by fun_prop
  have hv : halfGaussianVariance = (1 / 2 : ℝ≥0) := by
    ext
    change (1 / 2 : ℝ) = (↑((1 : ℝ≥0) / 2) : ℝ)
    norm_num
  have hmap : (A4Research.standardGaussianRows k d).map scale =
      halfGaussianRowProduct k d := by
    unfold A4Research.standardGaussianRows
    rw [Measure.pi_map_pi (fun _ ↦
      (show Measurable (fun x : Fin d → ℝ ↦
        fun i ↦ (Real.sqrt 2)⁻¹ * x i) by fun_prop).aemeasurable)]
    congr 1
    funext a
    simpa only [halfGaussianRowProduct, hv] using
      A4Research.map_standardGaussianVector_half d
  rw [← map_curriedMatrix_halfGaussianRowProduct k d, ← hmap,
    Measure.map_map (curriedMatrixMeasurableEquiv k d).measurable hscale]
  rfl

theorem gram_scaledStandardRows {k d : ℕ} (z : Fin k → Fin d → ℝ) :
    realWishartGram (scaledStandardRows z) = A4Research.standardGaussianGram z := by
  have hc : ((Real.sqrt 2)⁻¹ : ℝ) ^ 2 = 1 / 2 := by
    rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  apply Matrix.ext
  intro i j
  simp only [realWishartGram, Matrix.mul_apply, Matrix.transpose_apply,
    scaledStandardRows, Matrix.of_apply, A4Research.standardGaussianGram,
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  calc
    _ = ((Real.sqrt 2)⁻¹ : ℝ) ^ 2 * (z a i * z a j) := by ring
    _ = _ := by rw [hc]; ring

theorem measurable_realWishartGram (k d : ℕ) :
    Measurable (realWishartGram : Matrix (Fin k) (Fin d) ℝ →
      MatsumotoPaper.RealMatrix d) := by
  apply Continuous.measurable
  unfold realWishartGram
  fun_prop

theorem map_halfGaussianMatrix_gram (k d : ℕ) :
    (halfGaussianMatrix k d).map realWishartGram =
      A4Research.standardGaussianGramLaw k d := by
  rw [← map_standardGaussianRows_scaled k d,
    Measure.map_map (measurable_realWishartGram k d) (measurable_scaledStandardRows k d)]
  unfold A4Research.standardGaussianGramLaw
  congr 1
  funext z
  exact gram_scaledStandardRows z

theorem wishart_matrixLaw_eq_halfGaussianGramLaw {k d : ℕ}
    (W : MatsumotoPaper.W_d d ((k : ℝ) / 2) (MatsumotoPaper.identityScale d)) :
    W.matrixLaw = (halfGaussianMatrix k d).map realWishartGram := by
  rw [map_halfGaussianMatrix_gram]
  exact W.matrixLaw_eq_standardGaussianGramLaw

theorem measurable_matrix_nonsing_inv (d : ℕ) :
    Measurable (fun X : MatsumotoPaper.RealMatrix d ↦ X⁻¹) := by
  simp_rw [Matrix.inv_def, Ring.inverse_eq_inv]
  exact continuous_id.matrix_det.measurable.inv.smul
    continuous_id.matrix_adjugate.measurable

def inverseMatrixEntryProduct {d q : ℕ} (indices : Fin q → Fin d × Fin d)
    (X : MatsumotoPaper.RealMatrix d) : ℝ :=
  ∏ r, X⁻¹ (indices r).1 (indices r).2

theorem measurable_inverseMatrixEntryProduct {d q : ℕ}
    (indices : Fin q → Fin d × Fin d) :
    Measurable (inverseMatrixEntryProduct indices) := by
  have hM := measurable_matrix_nonsing_inv d
  have he (r : Fin q) : Measurable (fun X : MatsumotoPaper.RealMatrix d ↦
      X⁻¹ (indices r).1 (indices r).2) := by
    have hE : Continuous (fun X : MatsumotoPaper.RealMatrix d ↦
        X (indices r).1 (indices r).2) := by fun_prop
    exact hE.measurable.comp hM
  unfold inverseMatrixEntryProduct
  exact Finset.measurable_fun_prod _ (fun r _ ↦ he r)

theorem memLp_inverseEntryProduct_halfGaussianMatrix {k d q : ℕ} {p : ℝ}
    (W : MatsumotoPaper.W_d d ((k : ℝ) / 2) (MatsumotoPaper.identityScale d))
    (hp : 0 < p) (hgap : (q : ℝ) * p - 1 < ((k : ℝ) - d - 1) / 2)
    (indices : Fin q → Fin d × Fin d) :
    MemLp (inverseEntryProduct indices : Matrix (Fin k) (Fin d) ℝ → ℝ)
      (ENNReal.ofReal p) (halfGaussianMatrix k d) := by
  have hcone := W.memLp_prod_inverse_entries hp
    (gamma := ((k : ℝ) - d - 1) / 2) (by ring) hgap
    (fun r ↦ (indices r).1) (fun r ↦ (indices r).2)
  have hambient : MemLp (inverseMatrixEntryProduct indices)
      (ENNReal.ofReal p) W.matrixLaw := by
    apply (memLp_map_measure_iff
      (measurable_inverseMatrixEntryProduct indices).aestronglyMeasurable
      measurable_subtype_coe.aemeasurable).mpr
    exact hcone
  rw [wishart_matrixLaw_eq_halfGaussianGramLaw W] at hambient
  exact hambient.comp_of_map (measurable_realWishartGram k d).aemeasurable

end A4Research.InverseStein
