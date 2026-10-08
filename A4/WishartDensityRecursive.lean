import A4.TriangularRecursiveBorder
import A4.WishartCongruence

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix

noncomputable section
namespace A4Research

open MatsumotoPaper

local instance (d : ℕ) : BorelSpace (RealMatrix d) := ⟨rfl⟩

/-- Identity scale for the real Bartlett construction. -/
def bartlettIdentityScale (d : ℕ) : SymPosDef d := ⟨1, Matrix.PosDef.one⟩

/-- The independent first Bartlett column. -/
def bartlettFirstColumnMeasure (d : ℕ) (beta : ℝ) :
    Measure (ℝ × (Fin d → ℝ)) :=
  (gammaMeasure beta 1).prod (Measure.pi (fun _ : Fin d => gaussianReal 0 (1 / 2)))

theorem bartlettFirstColumn_probability {d : ℕ} {beta : ℝ} (hb : 0 < beta) :
    IsProbabilityMeasure (bartlettFirstColumnMeasure d beta) := by
  let := isProbabilityMeasure_gammaMeasure hb (by norm_num : (0 : ℝ) < 1)
  unfold bartlettFirstColumnMeasure
  infer_instance

theorem bartlettFirstColumn_ae_pos {d : ℕ} {beta : ℝ} (hb : 0 < beta) :
    ∀ᵐ q ∂bartlettFirstColumnMeasure d beta, 0 < q.1 := by
  let := isProbabilityMeasure_gammaMeasure hb (by norm_num : (0 : ℝ) < 1)
  exact (Measure.quasiMeasurePreserving_fst).ae (gammaMeasure_ae_pos beta 1)

/-- Adding one independent Gamma--Gaussian column to a characterized tail. -/
def bartlettStepMeasure {d : ℕ} {beta : ℝ}
    (W : W_d d (beta - 1 / 2) (bartlettIdentityScale d)) :
    Measure (SymPosDef (d + 1)) :=
  ((bartlettFirstColumnMeasure d beta).prod W.toMeasure).map bartlettBorder

theorem bartlettStep_probability {d : ℕ} {beta : ℝ}
    (W : W_d d (beta - 1 / 2) (bartlettIdentityScale d)) (hb : 0 < beta) :
    IsProbabilityMeasure (bartlettStepMeasure W) := by
  let := W.probability
  let := bartlettFirstColumn_probability (d := d) hb
  exact Measure.isProbabilityMeasure_map (measurable_bartlettBorder d).aemeasurable

/-- The complete dimension-increment transform, for arbitrary real shape. -/
theorem bartlettStep_laplace {d : ℕ} {beta : ℝ}
    (W : W_d d (beta - 1 / 2) (bartlettIdentityScale d)) (hb : 0 < beta)
    (theta : Sym (d + 1)) (hgap : (1 - theta.1).PosDef) :
    (∫ w : SymPosDef (d + 1), etr (theta.1 * w.1) ∂bartlettStepMeasure W) =
      Matrix.det (1 - theta.1) ^ (-beta) := by
  let := W.probability
  let := bartlettFirstColumn_probability (d := d) hb
  have htheta : theta.1.IsHermitian := Matrix.isHermitian_iff_isSymm.mpr theta.2
  let tailTilt : Sym d := ⟨matrixTail theta.1,
    Matrix.isHermitian_iff_isSymm.mp (matrixTail_isHermitian htheta)⟩
  have htail : ((bartlettIdentityScale d).1⁻¹ - tailTilt.1).PosDef := by
    simpa only [bartlettIdentityScale, tailTilt, inv_one] using matrixTail_gap_posDef hgap
  have hm : Measurable (fun w : SymPosDef (d + 1) => etr (theta.1 * w.1)) := by
    have hc : Continuous (fun w : RealMatrix (d + 1) => etr (theta.1 * w)) := by
      unfold etr
      fun_prop
    exact hc.measurable.comp measurable_subtype_coe
  rw [bartlettStepMeasure, integral_map (measurable_bartlettBorder d).aemeasurable
    hm.aestronglyMeasurable]
  have heq : (fun q : (ℝ × (Fin d → ℝ)) × SymPosDef d =>
      etr (theta.1 * (bartlettBorder q).1)) =ᵐ[
      (bartlettFirstColumnMeasure d beta).prod W.toMeasure]
      (fun q => bartlettColumnTilt (theta.1 0 0) (matrixTail theta.1)
        (fun i => theta.1 0 i.succ) q.1.1 q.1.2 * etr (matrixTail theta.1 * q.2.1)) := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst).ae
      (bartlettFirstColumn_ae_pos (d := d) hb)] with q hq
    exact bartlettBorder_etr htheta q hq
  rw [integral_congr_ae heq]
  let B : RealMatrix d := matrixTail theta.1
  let b : Fin d → ℝ := fun i => theta.1 0 i.succ
  let c : ℝ := theta.1 0 0
  change (∫ q : (ℝ × (Fin d → ℝ)) × SymPosDef d,
    bartlettColumnTilt c B b q.1.1 q.1.2 * etr (B * q.2.1)
    ∂(bartlettFirstColumnMeasure d beta).prod W.toMeasure) = _
  rw [integral_prod_mul (fun q : ℝ × (Fin d → ℝ) => bartlettColumnTilt c B b q.1 q.2)
    (fun w : SymPosDef d => etr (B * w.1))]
  change _ * (∫ w : SymPosDef d, etr (matrixTail theta.1 * w.1) ∂W.toMeasure) = _
  rw [show (∫ w : SymPosDef d, etr (matrixTail theta.1 * w.1) ∂W.toMeasure) =
      Matrix.det (1 - matrixTail theta.1) ^ (-(beta - 1 / 2)) from by
    have hW := W.laplace_transform tailTilt htail
    change (∫ w : SymPosDef d, etr (matrixTail theta.1 * w.1) ∂W.toMeasure) =
      Matrix.det (1 - matrixTail theta.1 * 1) ^ (-(beta - 1 / 2)) at hW
    rwa [Matrix.mul_one] at hW]
  rw [show (∫ q : ℝ × (Fin d → ℝ), bartlettColumnTilt c B b q.1 q.2
      ∂bartlettFirstColumnMeasure d beta) =
      Matrix.det (1 - B) ^ (-1 / 2 : ℝ) *
        (1 - (c + b ⬝ᵥ ((1 - B)⁻¹ *ᵥ b))) ^ (-beta) from
    bartlettColumn_integral hb (matrixTail_isHermitian htheta)
      (matrixTail_gap_posDef hgap) b (matrixGap_schur_lt_one htheta hgap)]
  let D : ℝ := Matrix.det (1 - matrixTail theta.1)
  let r : ℝ := 1 - (theta.1 0 0 + (fun i => theta.1 0 i.succ) ⬝ᵥ
    ((1 - matrixTail theta.1)⁻¹ *ᵥ (fun i => theta.1 0 i.succ)))
  have hD : 0 < D := (matrixTail_gap_posDef hgap).det_pos
  have hr : 0 < r := sub_pos.mpr (matrixGap_schur_lt_one htheta hgap)
  rw [matrixGap_det htheta hgap]
  change D ^ (-1 / 2 : ℝ) * r ^ (-beta) * D ^ (-(beta - 1 / 2)) =
    (D * r) ^ (-beta)
  rw [Real.mul_rpow hD.le hr.le]
  calc
    _ = (D ^ (-1 / 2 : ℝ) * D ^ (-(beta - 1 / 2))) * r ^ (-beta) := by ring
    _ = _ := by
      rw [← Real.rpow_add hD]
      congr 2
      ring

/-- The recursive dimension step constructs an actual characterized Wishart
law, rather than assuming a triangular Laplace identity. -/
def bartlettStepLaw {d : ℕ} {beta : ℝ}
    (W : W_d d (beta - 1 / 2) (bartlettIdentityScale d)) (hb : 0 < beta) :
    W_d (d + 1) beta (bartlettIdentityScale (d + 1)) where
  toMeasure := bartlettStepMeasure W
  probability := bartlettStep_probability W hb
  laplace_transform := by
    intro theta hgap
    have hg : (1 - theta.1).PosDef := by
      simpa only [bartlettIdentityScale, inv_one] using hgap
    change (∫ w : SymPosDef (d + 1), etr (theta.1 * w.1) ∂bartlettStepMeasure W) =
      Matrix.det (1 - theta.1 * 1) ^ (-beta)
    rw [Matrix.mul_one]
    exact bartlettStep_laplace W hb theta hg

/-- The zero-dimensional initialization is the unique empty SPD matrix. -/
def bartlettEmptyLaw (beta : ℝ) : W_d 0 beta (bartlettIdentityScale 0) where
  toMeasure := Measure.dirac (bartlettIdentityScale 0)
  probability := inferInstance
  laplace_transform := by
    intro theta hgap
    have htrace : ∀ w : SymPosDef 0, etr (theta.1 * w.1) = 1 := by
      intro w
      simp [etr, Matrix.trace, Matrix.diag]
    simp only [htrace, integral_const, probReal_univ, one_smul, Matrix.det_isEmpty]
    change (1 : ℝ) = (1 : ℝ) ^ (-beta)
    rw [Real.one_rpow]

/-- Bartlett existence in every dimension and every admissible real shape. -/
def recursiveBartlettLaw : (d : ℕ) → (beta : ℝ) →
    ((d : ℝ) - 1) / 2 < beta → W_d d beta (bartlettIdentityScale d)
  | 0, beta, _ => bartlettEmptyLaw beta
  | d + 1, beta, hb => bartlettStepLaw
      (recursiveBartlettLaw d (beta - 1 / 2) (by
        have hcast : ((d + 1 : ℕ) : ℝ) = (d : ℝ) + 1 := by norm_num
        rw [hcast] at hb
        linarith)) (by
          have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
          have hcast : ((d + 1 : ℕ) : ℝ) = (d : ℝ) + 1 := by norm_num
          rw [hcast] at hb
          linarith)

/-- In particular, the full positive real-shape range has a Wishart law. -/
theorem realShapeWishart_exists (d : ℕ) (beta : ℝ)
    (hb : ((d : ℝ) - 1) / 2 < beta) :
    Nonempty (W_d d beta (bartlettIdentityScale d)) :=
  ⟨recursiveBartlettLaw d beta hb⟩

/-- Congruence by the proved Cholesky factor supplies every SPD scale. -/
def recursiveBartlettScaledLaw (d : ℕ) (beta : ℝ) (sigma : SymPosDef d)
    (hb : ((d : ℝ) - 1) / 2 < beta) : W_d d beta sigma := by
  let C := cholesky sigma.2
  let hC : IsUnit C := cholesky_isUnit sigma.2
  have hs : SymPosDef.congruence C hC (bartlettIdentityScale d) = sigma := by
    apply Subtype.ext
    change C * 1 * Cᴴ = sigma.1
    rw [Matrix.mul_one]
    simpa only [C, Matrix.conjTranspose_eq_transpose_of_trivial] using
      cholesky_mul_transpose sigma.2
  exact hs ▸ (recursiveBartlettLaw d beta hb).congruence C hC

/-- Real-shape Wishart existence holds at every positive-definite scale. -/
theorem realShapeWishart_exists_anyScale (d : ℕ) (beta : ℝ) (sigma : SymPosDef d)
    (hb : ((d : ℝ) - 1) / 2 < beta) : Nonempty (W_d d beta sigma) :=
  ⟨recursiveBartlettScaledLaw d beta sigma hb⟩

end A4Research
