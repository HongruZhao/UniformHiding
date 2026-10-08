import A4.Target

open MeasureTheory

namespace MatsumotoPaper

/-- The determinant appearing in the Wishart transform is positive throughout
its stated positive-definite domain. -/
theorem laplace_determinant_pos {d : ℕ} (sigma : SymPosDef d)
    (theta : Sym d) (hgap : (sigma.1⁻¹ - theta.1).PosDef) :
    0 < Matrix.det (1 - theta.1 * sigma.1) := by
  have hunit : IsUnit (Matrix.det sigma.1) :=
    isUnit_iff_ne_zero.mpr sigma.2.det_pos.ne'
  have hmatrix : (sigma.1⁻¹ - theta.1) * sigma.1 = 1 - theta.1 * sigma.1 := by
    rw [Matrix.sub_mul, Matrix.nonsing_inv_mul _ hunit]
  rw [← hmatrix, Matrix.det_mul]
  exact mul_pos hgap.det_pos sigma.2.det_pos

/-- The transform field cannot be satisfied using the totalized zero value of
a nonintegrable Bochner integral: its positive right side proves integrability. -/
theorem W_d.integrable_etr {d : ℕ} {beta : ℝ} {sigma : SymPosDef d}
    (W : W_d d beta sigma) (theta : Sym d)
    (hgap : (sigma.1⁻¹ - theta.1).PosDef) :
    Integrable (fun w : SymPosDef d ↦ etr (theta.1 * w.1)) W.toMeasure := by
  apply Integrable.of_integral_ne_zero
  rw [W.laplace_transform theta hgap]
  exact (Real.rpow_pos_of_pos (laplace_determinant_pos sigma theta hgap) (-beta)).ne'

end MatsumotoPaper
