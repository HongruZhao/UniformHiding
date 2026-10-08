import A4.WishartDensityRecursive

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix

noncomputable section
namespace A4Research

open MatsumotoPaper

local instance (d : ℕ) : BorelSpace (RealMatrix d) := ⟨rfl⟩

/-- The determinant moment recurrence for the complete Gamma border. -/
theorem bartlettStep_integral_det_rpow {d : ℕ} {beta p : ℝ}
    (W : W_d d (beta - 1 / 2) (bartlettIdentityScale d))
    (hb : 0 < beta) (hbp : 0 < beta + p) :
    (∫ w : SymPosDef (d + 1), Matrix.det w.1 ^ p ∂bartlettStepMeasure W) =
      (Real.Gamma (beta + p) / Real.Gamma beta) *
        (∫ w : SymPosDef d, Matrix.det w.1 ^ p ∂W.toMeasure) := by
  let := W.probability
  let := isProbabilityMeasure_gammaMeasure hb (by norm_num : (0 : ℝ) < 1)
  let := bartlettFirstColumn_probability (d := d) hb
  have hm : Measurable (fun w : SymPosDef (d + 1) => Matrix.det w.1 ^ p) := by
    exact ((continuous_id.matrix_det : Continuous (Matrix.det : RealMatrix (d + 1) → ℝ)).measurable.comp
      measurable_subtype_coe).pow_const p
  rw [bartlettStepMeasure, integral_map (measurable_bartlettBorder d).aemeasurable
    hm.aestronglyMeasurable]
  have heq : (fun q : (ℝ × (Fin d → ℝ)) × SymPosDef d =>
      Matrix.det (bartlettBorder q).1 ^ p) =ᵐ[
      (bartlettFirstColumnMeasure d beta).prod W.toMeasure]
      (fun q => q.1.1 ^ p * Matrix.det q.2.1 ^ p) := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst).ae
      (bartlettFirstColumn_ae_pos (d := d) hb)] with q hq
    rw [bartlettBorder_det_of_pos q hq, Real.mul_rpow hq.le q.2.2.det_pos.le]
  rw [integral_congr_ae heq, integral_prod_mul
    (fun q : ℝ × (Fin d → ℝ) => q.1 ^ p) (fun w : SymPosDef d => Matrix.det w.1 ^ p)]
  congr 1
  unfold bartlettFirstColumnMeasure
  rw [integral_fun_fst (fun t : ℝ => t ^ p), probReal_univ, one_smul,
    gammaMeasure_integral_rpow hb (by norm_num) hbp]
  simp only [Real.one_rpow, one_mul]

/-- The full Gamma-product determinant moment for the actual characterized
real-shape law. This follows the proved matrix law, not a candidate density. -/
theorem recursiveBartlettLaw_integral_det_rpow (d : ℕ) (beta p : ℝ)
    (hb : ((d : ℝ) - 1) / 2 < beta)
    (hp : ∀ i : Fin d, 0 < bartlettShape beta i + p) :
    (∫ w : SymPosDef d, Matrix.det w.1 ^ p
      ∂(recursiveBartlettLaw d beta hb).toMeasure) =
      ∏ i : Fin d, Real.Gamma (bartlettShape beta i + p) /
        Real.Gamma (bartlettShape beta i) := by
  induction d generalizing beta with
  | zero =>
    simp only [recursiveBartlettLaw, bartlettEmptyLaw, Matrix.det_isEmpty,
      Real.one_rpow, integral_const, probReal_univ, one_smul, Fin.prod_univ_zero]
  | succ d ih =>
    have hbeta : 0 < beta := by
      have hd := Nat.cast_nonneg (α := ℝ) d
      have hcast : ((d + 1 : ℕ) : ℝ) = (d : ℝ) + 1 := by norm_num
      rw [hcast] at hb
      linarith
    have htail : ((d : ℝ) - 1) / 2 < beta - 1 / 2 := by
      have hcast : ((d + 1 : ℕ) : ℝ) = (d : ℝ) + 1 := by norm_num
      rw [hcast] at hb
      linarith
    have hshape (i : Fin d) : bartlettShape (beta - 1 / 2) i =
        bartlettShape beta i.succ := by
      unfold bartlettShape
      simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one]
      ring
    have hp0 : 0 < beta + p := by
      simpa only [bartlettShape, Fin.val_zero, Nat.cast_zero, zero_div, sub_zero] using hp 0
    have hptail : ∀ i : Fin d, 0 < bartlettShape (beta - 1 / 2) i + p := by
      intro i
      rw [hshape]
      exact hp i.succ
    change (∫ w : SymPosDef (d + 1), Matrix.det w.1 ^ p
      ∂bartlettStepMeasure (recursiveBartlettLaw d (beta - 1 / 2) htail)) = _
    rw [bartlettStep_integral_det_rpow _ hbeta hp0,
      ih (beta - 1 / 2) htail hptail, Fin.prod_univ_succ]
    simp only [bartlettShape, Fin.val_zero, Nat.cast_zero, zero_div, sub_zero]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    change Real.Gamma (bartlettShape (beta - 1 / 2) i + p) /
      Real.Gamma (bartlettShape (beta - 1 / 2) i) =
      Real.Gamma (bartlettShape beta i.succ + p) / Real.Gamma (bartlettShape beta i.succ)
    rw [hshape]

/-- The law characterization transfers the determinant formula to every
identity-scale Wishart law. -/
theorem identityWishart_integral_det_rpow {d : ℕ} {beta p : ℝ}
    (W : W_d d beta (bartlettIdentityScale d))
    (hb : ((d : ℝ) - 1) / 2 < beta)
    (hp : ∀ i : Fin d, 0 < bartlettShape beta i + p) :
    (∫ w : SymPosDef d, Matrix.det w.1 ^ p ∂W.toMeasure) =
      ∏ i : Fin d, Real.Gamma (bartlettShape beta i + p) /
        Real.Gamma (bartlettShape beta i) := by
  rw [W.toMeasure_eq (recursiveBartlettLaw d beta hb)]
  exact recursiveBartlettLaw_integral_det_rpow d beta p hb hp

/-- Transport in the scale parameter leaves the underlying measure unchanged. -/
theorem wishart_toMeasure_cast_scale {d : ℕ} {beta : ℝ}
    {sigma tau : SymPosDef d} (h : sigma = tau) (W : W_d d beta sigma) :
    (h ▸ W).toMeasure = W.toMeasure := by
  cases h
  rfl

/-- The scaled recursive law has the concrete Cholesky-congruence measure. -/
theorem recursiveBartlettScaledLaw_toMeasure {d : ℕ} {beta : ℝ}
    (sigma : SymPosDef d) (hb : ((d : ℝ) - 1) / 2 < beta) :
    (recursiveBartlettScaledLaw d beta sigma hb).toMeasure =
      (recursiveBartlettLaw d beta hb).toMeasure.map
        (SymPosDef.congruence (cholesky sigma.2) (cholesky_isUnit sigma.2)) := by
  unfold recursiveBartlettScaledLaw
  exact wishart_toMeasure_cast_scale _ _

/-- The exact real determinant-power moment at every SPD scale and real
admissible shape, for every law satisfying the original transform. -/
theorem wishart_integral_det_rpow {d : ℕ} {beta p : ℝ} {sigma : SymPosDef d}
    (W : W_d d beta sigma) (hb : ((d : ℝ) - 1) / 2 < beta)
    (hp : ∀ i : Fin d, 0 < bartlettShape beta i + p) :
    (∫ w : SymPosDef d, Matrix.det w.1 ^ p ∂W.toMeasure) =
      Matrix.det sigma.1 ^ p * ∏ i : Fin d,
        Real.Gamma (bartlettShape beta i + p) / Real.Gamma (bartlettShape beta i) := by
  rw [W.toMeasure_eq (recursiveBartlettScaledLaw d beta sigma hb),
    recursiveBartlettScaledLaw_toMeasure]
  have hm : Measurable (fun w : SymPosDef d => Matrix.det w.1 ^ p) := by
    exact ((continuous_id.matrix_det : Continuous (Matrix.det : RealMatrix d → ℝ)).measurable.comp
      measurable_subtype_coe).pow_const p
  rw [integral_map (SymPosDef.measurable_congruence _ _).aemeasurable hm.aestronglyMeasurable]
  have hC : Matrix.det sigma.1 = Matrix.det (cholesky sigma.2) ^ 2 := by
    have h := congrArg Matrix.det (cholesky_mul_transpose sigma.2)
    simpa only [Matrix.det_mul, Matrix.det_transpose, pow_two] using h.symm
  have heq : (fun w : SymPosDef d =>
      Matrix.det (SymPosDef.congruence (cholesky sigma.2) (cholesky_isUnit sigma.2) w).1 ^ p) =
      (fun w => Matrix.det sigma.1 ^ p * Matrix.det w.1 ^ p) := by
    funext w
    have hdet : Matrix.det (SymPosDef.congruence (cholesky sigma.2)
        (cholesky_isUnit sigma.2) w).1 = Matrix.det sigma.1 * Matrix.det w.1 := by
      change Matrix.det (cholesky sigma.2 * w.1 * (cholesky sigma.2)ᴴ) = _
      rw [hC]
      simp only [Matrix.det_mul, Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.det_transpose]
      ring
    rw [hdet, Real.mul_rpow sigma.2.det_pos.le w.2.det_pos.le]
  rw [heq, integral_const_mul, recursiveBartlettLaw_integral_det_rpow d beta p hb hp]

theorem wishart_integrable_det_rpow {d : ℕ} {beta p : ℝ} {sigma : SymPosDef d}
    (W : W_d d beta sigma) (hb : ((d : ℝ) - 1) / 2 < beta)
    (hp : ∀ i : Fin d, 0 < bartlettShape beta i + p) :
    Integrable (fun w : SymPosDef d => Matrix.det w.1 ^ p) W.toMeasure := by
  apply Integrable.of_integral_ne_zero
  rw [wishart_integral_det_rpow W hb hp]
  apply (mul_pos (Real.rpow_pos_of_pos sigma.2.det_pos p) _).ne'
  exact Finset.prod_pos fun i _ => div_pos (Real.Gamma_pos_of_pos (hp i))
    (Real.Gamma_pos_of_pos (bartlettShape_pos hb i))

/-- The exact A4 gap proves inverse determinant integrability at every degree
for every characterized real-shape Wishart law. -/
theorem wishart_integrable_det_inverse_degree {d n : ℕ} {beta gamma : ℝ}
    {sigma : SymPosDef d} (W : W_d d beta sigma)
    (hgamma : gamma = beta - ((d : ℝ) + 1) / 2) (hgap : (n : ℝ) - 1 < gamma) :
    Integrable (fun w : SymPosDef d => Matrix.det w.1 ^ (-(n : ℝ))) W.toMeasure := by
  have hb : ((d : ℝ) - 1) / 2 < beta := by
    have hn := Nat.cast_nonneg (α := ℝ) n
    linarith
  apply wishart_integrable_det_rpow W hb
  intro i
  simpa only [sub_eq_add_neg] using bartlettShape_sub_degree_pos hgamma hgap i

end A4Research
