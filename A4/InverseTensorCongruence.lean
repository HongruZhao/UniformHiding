import A4.InverseTensorCongruenceAlgebra
import A4.GaussianWishartCongruence

open MeasureTheory
open scoped BigOperators Matrix

noncomputable section
namespace A4Research

open MatsumotoPaper

set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

/-- The inverse covariance factor `A^{-T}` for the actual Cholesky factor. -/
def inverseScaleFactor {d : ℕ} (sigma : SymPosDef d) : RealMatrix d :=
  (gaussianScaleFactor sigma).transpose⁻¹

theorem inverseScaleFactor_covariance {d : ℕ} (sigma : SymPosDef d) :
    inverseScaleFactor sigma * (inverseScaleFactor sigma).transpose = sigma.1⁻¹ := by
  unfold inverseScaleFactor gaussianScaleFactor
  rw [Matrix.transpose_nonsing_inv, Matrix.transpose_transpose,
    ← Matrix.mul_inv_rev, cholesky_mul_transpose]

theorem inverse_scale_congruence {d : ℕ} (sigma : SymPosDef d) (w : SymPosDef d) :
    (SymPosDef.congruence (gaussianScaleFactor sigma)
      (gaussianScaleFactor_isUnit sigma) w).1⁻¹ =
        inverseScaleFactor sigma * w.1⁻¹ * (inverseScaleFactor sigma).transpose := by
  simp only [SymPosDef.congruence, inverseScaleFactor, Matrix.mul_inv_rev,
    Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_nonsing_inv,
    Matrix.transpose_transpose, Matrix.mul_assoc]

theorem wishart_measure_eq_identity_congruence {d : ℕ} {beta : ℝ}
    (sigma : SymPosDef d) (W0 : W_d d beta (identityScale d))
    (W : W_d d beta sigma) :
    W.toMeasure = W0.toMeasure.map
      (SymPosDef.congruence (gaussianScaleFactor sigma) (gaussianScaleFactor_isUnit sigma)) := by
  let V : W_d d beta sigma := gaussianScaleFactor_congruence sigma ▸
    W0.congruence (gaussianScaleFactor sigma) (gaussianScaleFactor_isUnit sigma)
  rw [W.toMeasure_eq V]
  exact wishart_toMeasure_cast_scale (gaussianScaleFactor_congruence sigma) _

theorem entryCongruenceCoefficient_complex {d n : ℕ}
    (B : RealMatrix d) (x y : EntryPairList d n) :
    Complex.ofReal (entryCongruenceCoefficient B x y) =
      entryCongruenceCoefficient (B.map Complex.ofReal) x y := by
  simp only [entryCongruenceCoefficient, Matrix.map_apply, Complex.ofReal_prod,
    Complex.ofReal_mul]

/-- Actual inverse moments transform by the complete finite tensor
congruence. The sharp inverse integrability bound justifies the sums. -/
theorem inverseEntryMomentTensor_scale_expansion {d n : ℕ} {beta gamma : ℝ}
    {sigma : SymPosDef d} (W0 : W_d d beta (identityScale d)) (W : W_d d beta sigma)
    (hgamma : gamma = beta - ((d : ℝ) + 1) / 2) (hgap : (n : ℝ) - 1 < gamma)
    (x : EntryPairList d n) :
    inverseEntryMomentTensor W n x =
      ∑ y : EntryPairList d n,
        entryCongruenceCoefficient ((inverseScaleFactor sigma).map Complex.ofReal) x y *
          inverseEntryMomentTensor W0 n y := by
  classical
  have hmap := wishart_measure_eq_identity_congruence sigma W0 W
  let f : SymPosDef d → ℝ := fun w ↦ ∏ r : Fin n, w.1⁻¹ (x r).1 (x r).2
  have hInt : Integrable f (W0.toMeasure.map
      (SymPosDef.congruence (gaussianScaleFactor sigma) (gaussianScaleFactor_isUnit sigma))) := by
    rw [← hmap]
    exact W.integrable_prod_inverse_entries hgamma hgap _ _
  have hreal : (∫ w : SymPosDef d, ∏ r : Fin n,
      w.1⁻¹ (x r).1 (x r).2 ∂W.toMeasure) =
        ∑ y : EntryPairList d n, entryCongruenceCoefficient (inverseScaleFactor sigma) x y *
          ∫ w : SymPosDef d, ∏ r : Fin n, w.1⁻¹ (y r).1 (y r).2 ∂W0.toMeasure := by
    change (∫ w, f w ∂W.toMeasure) = _
    rw [hmap, integral_map (SymPosDef.measurable_congruence _ _).aemeasurable
      hInt.aestronglyMeasurable]
    have hprod (w : SymPosDef d) :
        f (SymPosDef.congruence (gaussianScaleFactor sigma) (gaussianScaleFactor_isUnit sigma) w) =
          ∑ y : EntryPairList d n, entryCongruenceCoefficient (inverseScaleFactor sigma) x y *
            ∏ r : Fin n, w.1⁻¹ (y r).1 (y r).2 := by
      unfold f
      rw [inverse_scale_congruence]
      exact prod_entries_congruence _ _ x
    rw [integral_congr_ae (Filter.Eventually.of_forall hprod), integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro y _
      exact integral_const_mul _ _
    · intro y _
      exact (W0.integrable_prod_inverse_entries hgamma hgap _ _).const_mul _
  have h := congrArg Complex.ofReal hreal
  simpa only [Complex.ofReal_sum, Complex.ofReal_mul, entryCongruenceCoefficient_complex,
    inverseEntryMomentTensor] using h

theorem inverseScaleFactor_complex_covariance {d : ℕ} (sigma : SymPosDef d)
    (a b : Fin d) :
    (((inverseScaleFactor sigma).map Complex.ofReal) *
      ((inverseScaleFactor sigma).map Complex.ofReal).transpose) a b =
        (sigma.1⁻¹ a b : ℂ) := by
  have h := congrArg (fun X : RealMatrix d ↦ Complex.ofReal (X a b))
    (inverseScaleFactor_covariance sigma)
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Complex.ofReal_sum, Complex.ofReal_mul] using h

/-- The independently proved identity-scale tensor formula implies the
exact tensor formula at every SPD scale and every real Wishart shape. -/
theorem inverseEntryMomentTensor_eq_of_identityScale {d n : ℕ} {beta gamma : ℝ}
    {sigma : SymPosDef d} (W0 : W_d d beta (identityScale d)) (W : W_d d beta sigma)
    (hgamma : gamma = beta - ((d : ℝ) + 1) / 2) (hgap : (n : ℝ) - 1 < gamma)
    (hidentity : inverseEntryMomentTensor W0 n =
      inverseWeingartenEntryTensor gamma
        (fun a b ↦ ((identityScale d).1⁻¹ a b : ℂ)) n) :
    inverseEntryMomentTensor W n =
      inverseWeingartenEntryTensor gamma (fun a b ↦ (sigma.1⁻¹ a b : ℂ)) n := by
  classical
  have hweight : (fun a b : Fin d ↦ ((identityScale d).1⁻¹ a b : ℂ)) =
      (fun a b ↦ if a = b then (1 : ℂ) else 0) := by
    funext a b
    by_cases h : a = b <;> simp [identityScale, h]
  rw [hweight] at hidentity
  funext x
  rw [inverseEntryMomentTensor_scale_expansion W0 W hgamma hgap x]
  simp_rw [congrFun hidentity]
  rw [sum_entryCongruenceCoefficient_weingarten]
  have hcov : (fun a b : Fin d ↦
      (((inverseScaleFactor sigma).map Complex.ofReal) *
        ((inverseScaleFactor sigma).map Complex.ofReal).transpose) a b) =
        (fun a b ↦ (sigma.1⁻¹ a b : ℂ)) := by
    funext a b
    exact inverseScaleFactor_complex_covariance sigma a b
  rw [hcov]

end A4Research
