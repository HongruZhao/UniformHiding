import A4.WishartDensityRecursiveMoments
import A4.WishartDensityGammaTilt

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix ENNReal NNReal

noncomputable section
namespace A4Research

open MatsumotoPaper

local instance (d : ℕ) : BorelSpace (RealMatrix d) := ⟨rfl⟩

/-- Weighting a pushforward pulls the scalar weight back to raw coordinates. -/
theorem withDensity_map_measurable {α δ : Type*} [MeasurableSpace α] [MeasurableSpace δ]
    (mu : Measure α) (f : α → δ) (hf : Measurable f) (g : δ → ℝ≥0∞) (hg : Measurable g) :
    (mu.map f).withDensity g = (mu.withDensity (g ∘ f)).map f := by
  refine Measure.ext_of_lintegral _ fun phi hphi => ?_
  rw [lintegral_withDensity_eq_lintegral_mul _ hg hphi,
    lintegral_map (hg.mul hphi) hf, lintegral_map hphi hf]
  change (∫⁻ a, ((g * phi) ∘ f) a ∂mu) =
    ∫⁻ a, (phi ∘ f) a ∂mu.withDensity (g ∘ f)
  rw [lintegral_withDensity_eq_lintegral_mul _ (hg.comp hf) (hphi.comp hf)]
  rfl

/-- The Gamma shape shift passes through the unused independent Gaussian
coordinates without changing their distribution. -/
theorem bartlettFirstColumn_withDensity_rpow {d : ℕ} {beta p : ℝ}
    (hb : 0 < beta) (hbp : 0 < beta + p) :
    (bartlettFirstColumnMeasure d beta).withDensity
      (fun q : ℝ × (Fin d → ℝ) => ENNReal.ofReal (q.1 ^ p)) =
      ENNReal.ofReal (Real.Gamma (beta + p) / Real.Gamma beta) •
        bartlettFirstColumnMeasure d (beta + p) := by
  have hm : Measurable (fun t : ℝ => ENNReal.ofReal (t ^ p)) :=
    (measurable_id.pow_const p).ennreal_ofReal
  unfold bartlettFirstColumnMeasure
  rw [← prod_withDensity_left hm, gammaMeasure_withDensity_rpow hb hbp,
    Measure.prod_smul_left]

/-- The determinant weight of the complete real-shape Bartlett law is exactly
the same law with shifted shape, including its normalization. -/
theorem recursiveBartlettLaw_withDensity_det_rpow (d : ℕ) (beta p : ℝ)
    (hb : ((d : ℝ) - 1) / 2 < beta)
    (hbp : ((d : ℝ) - 1) / 2 < beta + p) :
    (recursiveBartlettLaw d beta hb).toMeasure.withDensity
      (fun w : SymPosDef d => ENNReal.ofReal (Matrix.det w.1 ^ p)) =
      ENNReal.ofReal (∏ i : Fin d, Real.Gamma (bartlettShape beta i + p) /
        Real.Gamma (bartlettShape beta i)) •
        (recursiveBartlettLaw d (beta + p) hbp).toMeasure := by
  induction d generalizing beta with
  | zero =>
    simp only [recursiveBartlettLaw, bartlettEmptyLaw, Matrix.det_isEmpty,
      Real.one_rpow, ENNReal.ofReal_one, Fin.prod_univ_zero, withDensity_const, one_smul]
  | succ d ih =>
    have hcast : ((d + 1 : ℕ) : ℝ) = (d : ℝ) + 1 := by norm_num
    have hb0 : 0 < beta := by
      have hd := Nat.cast_nonneg (α := ℝ) d
      rw [hcast] at hb
      linarith
    have hbp0 : 0 < beta + p := by
      have hd := Nat.cast_nonneg (α := ℝ) d
      rw [hcast] at hbp
      linarith
    have hbTail : ((d : ℝ) - 1) / 2 < beta - 1 / 2 := by
      rw [hcast] at hb
      linarith
    have hbpTail : ((d : ℝ) - 1) / 2 < (beta - 1 / 2) + p := by
      rw [hcast] at hbp
      linarith
    let W := recursiveBartlettLaw d (beta - 1 / 2) hbTail
    let Wp := recursiveBartlettLaw d ((beta - 1 / 2) + p) hbpTail
    let := W.probability
    let := Wp.probability
    let := bartlettFirstColumn_probability (d := d) hb0
    let := bartlettFirstColumn_probability (d := d) hbp0
    have hm : Measurable (fun w : SymPosDef (d + 1) =>
        ENNReal.ofReal (Matrix.det w.1 ^ p)) := by
      exact (((continuous_id.matrix_det : Continuous (Matrix.det : RealMatrix (d + 1) → ℝ)).measurable.comp
        measurable_subtype_coe).pow_const p).ennreal_ofReal
    change (((bartlettFirstColumnMeasure d beta).prod W.toMeasure).map bartlettBorder).withDensity
      (fun w => ENNReal.ofReal (Matrix.det w.1 ^ p)) = _
    rw [withDensity_map_measurable _ _ (measurable_bartlettBorder d) _ hm]
    have heq : ((fun w : SymPosDef (d + 1) => ENNReal.ofReal (Matrix.det w.1 ^ p)) ∘
        bartlettBorder) =ᵐ[(bartlettFirstColumnMeasure d beta).prod W.toMeasure]
        (fun q : (ℝ × (Fin d → ℝ)) × SymPosDef d =>
          ENNReal.ofReal (q.1.1 ^ p) * ENNReal.ofReal (Matrix.det q.2.1 ^ p)) := by
      filter_upwards [(Measure.quasiMeasurePreserving_fst).ae
        (bartlettFirstColumn_ae_pos (d := d) hb0)] with q hq
      dsimp only [Function.comp_apply]
      rw [bartlettBorder_det_of_pos q hq, Real.mul_rpow hq.le q.2.2.det_pos.le,
        ENNReal.ofReal_mul (Real.rpow_pos_of_pos hq p).le]
    rw [withDensity_congr_ae heq]
    have hmcol : Measurable (fun q : ℝ × (Fin d → ℝ) => ENNReal.ofReal (q.1 ^ p)) := by fun_prop
    have hmtail : Measurable (fun w : SymPosDef d => ENNReal.ofReal (Matrix.det w.1 ^ p)) := by
      exact (((continuous_id.matrix_det : Continuous (Matrix.det : RealMatrix d → ℝ)).measurable.comp
        measurable_subtype_coe).pow_const p).ennreal_ofReal
    rw [← prod_withDensity hmcol hmtail, bartlettFirstColumn_withDensity_rpow hb0 hbp0]
    have hIh := ih (beta - 1 / 2) hbTail hbpTail
    change W.toMeasure.withDensity (fun w => ENNReal.ofReal (Matrix.det w.1 ^ p)) =
      ENNReal.ofReal (∏ i : Fin d, Real.Gamma (bartlettShape (beta - 1 / 2) i + p) /
        Real.Gamma (bartlettShape (beta - 1 / 2) i)) • Wp.toMeasure at hIh
    rw [hIh, Measure.prod_smul_left, Measure.prod_smul_right]
    simp only [Measure.map_smul, smul_smul]
    have hprod : (Real.Gamma (beta + p) / Real.Gamma beta) *
        (∏ i : Fin d, Real.Gamma (bartlettShape (beta - 1 / 2) i + p) /
          Real.Gamma (bartlettShape (beta - 1 / 2) i)) =
        ∏ i : Fin (d + 1), Real.Gamma (bartlettShape beta i + p) /
          Real.Gamma (bartlettShape beta i) := by
      rw [Fin.prod_univ_succ]
      simp only [bartlettShape, Fin.val_zero, Nat.cast_zero, zero_div, sub_zero]
      congr 1
      apply Finset.prod_congr rfl
      intro i _
      have hshape : beta - 1 / 2 - (i : ℝ) / 2 = beta - (i.succ : ℝ) / 2 := by
        simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one]
        ring
      rw [hshape]
    have hC : 0 ≤ Real.Gamma (beta + p) / Real.Gamma beta :=
      (div_pos (Real.Gamma_pos_of_pos hbp0) (Real.Gamma_pos_of_pos hb0)).le
    rw [← ENNReal.ofReal_mul hC, hprod]
    congr 1
    have hbetaeq : (beta - 1 / 2) + p = (beta + p) - 1 / 2 := by ring
    have hWpeq : Wp.toMeasure =
        (recursiveBartlettLaw d ((beta + p) - 1 / 2) (by
          rw [← hbetaeq]
          exact hbpTail)).toMeasure := by
      dsimp only [Wp]
      congr 2
      exact proof_irrel_heq _ _
    rw [hWpeq]
    rfl

/-- Determinant weighting shifts the actual characterized Wishart shape at
arbitrary SPD scale. The normalization is its complete determinant moment. -/
theorem wishart_withDensity_det_rpow {d : ℕ} {beta p : ℝ} {sigma : SymPosDef d}
    (W : W_d d beta sigma) (V : W_d d (beta + p) sigma)
    (hb : ((d : ℝ) - 1) / 2 < beta) (hbp : ((d : ℝ) - 1) / 2 < beta + p) :
    W.toMeasure.withDensity (fun w : SymPosDef d => ENNReal.ofReal (Matrix.det w.1 ^ p)) =
      ENNReal.ofReal (Matrix.det sigma.1 ^ p *
        ∏ i : Fin d, Real.Gamma (bartlettShape beta i + p) / Real.Gamma (bartlettShape beta i)) •
      V.toMeasure := by
  rw [W.toMeasure_eq (recursiveBartlettScaledLaw d beta sigma hb),
    V.toMeasure_eq (recursiveBartlettScaledLaw d (beta + p) sigma hbp),
    recursiveBartlettScaledLaw_toMeasure, recursiveBartlettScaledLaw_toMeasure]
  have hm : Measurable (fun w : SymPosDef d => ENNReal.ofReal (Matrix.det w.1 ^ p)) := by
    exact (((continuous_id.matrix_det : Continuous (Matrix.det : RealMatrix d → ℝ)).measurable.comp
      measurable_subtype_coe).pow_const p).ennreal_ofReal
  rw [withDensity_map_measurable _ _ (SymPosDef.measurable_congruence _ _) _ hm]
  have hC : Matrix.det sigma.1 = Matrix.det (cholesky sigma.2) ^ 2 := by
    have h := congrArg Matrix.det (cholesky_mul_transpose sigma.2)
    simpa only [Matrix.det_mul, Matrix.det_transpose, pow_two] using h.symm
  have heq : ((fun w : SymPosDef d => ENNReal.ofReal (Matrix.det w.1 ^ p)) ∘
      SymPosDef.congruence (cholesky sigma.2) (cholesky_isUnit sigma.2)) =
      ENNReal.ofReal (Matrix.det sigma.1 ^ p) •
        (fun w : SymPosDef d => ENNReal.ofReal (Matrix.det w.1 ^ p)) := by
    funext w
    have hdet : Matrix.det (SymPosDef.congruence (cholesky sigma.2)
        (cholesky_isUnit sigma.2) w).1 = Matrix.det sigma.1 * Matrix.det w.1 := by
      change Matrix.det (cholesky sigma.2 * w.1 * (cholesky sigma.2)ᴴ) = _
      rw [hC]
      simp only [Matrix.det_mul, Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.det_transpose]
      ring
    simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul]
    rw [hdet, Real.mul_rpow sigma.2.det_pos.le w.2.det_pos.le,
      ENNReal.ofReal_mul (Real.rpow_pos_of_pos sigma.2.det_pos p).le]
  rw [heq, withDensity_smul _ hm, recursiveBartlettLaw_withDensity_det_rpow d beta p hb hbp]
  simp only [Measure.map_smul, smul_smul]
  rw [← ENNReal.ofReal_mul (Real.rpow_pos_of_pos sigma.2.det_pos p).le]

/-- Expectations under the exact determinant shape shift. -/
theorem wishart_integral_det_rpow_mul {d : ℕ} {beta p : ℝ} {sigma : SymPosDef d}
    (W : W_d d beta sigma) (V : W_d d (beta + p) sigma)
    (hb : ((d : ℝ) - 1) / 2 < beta) (hbp : ((d : ℝ) - 1) / 2 < beta + p)
    (f : SymPosDef d → ℝ) :
    (∫ w : SymPosDef d, Matrix.det w.1 ^ p * f w ∂W.toMeasure) =
      (Matrix.det sigma.1 ^ p *
        ∏ i : Fin d, Real.Gamma (bartlettShape beta i + p) / Real.Gamma (bartlettShape beta i)) *
      (∫ w : SymPosDef d, f w ∂V.toMeasure) := by
  have hm : Measurable (fun w : SymPosDef d => ENNReal.ofReal (Matrix.det w.1 ^ p)) := by
    exact (((continuous_id.matrix_det : Continuous (Matrix.det : RealMatrix d → ℝ)).measurable.comp
      measurable_subtype_coe).pow_const p).ennreal_ofReal
  have hInt := congrArg (fun mu : Measure (SymPosDef d) => ∫ w, f w ∂mu)
    (wishart_withDensity_det_rpow W V hb hbp)
  rw [integral_withDensity_eq_integral_toReal_smul hm
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top), integral_smul_measure] at hInt
  have heq : (fun w : SymPosDef d => (ENNReal.ofReal (Matrix.det w.1 ^ p)).toReal • f w) =
      (fun w => Matrix.det w.1 ^ p * f w) := by
    funext w
    rw [ENNReal.toReal_ofReal (Real.rpow_pos_of_pos w.2.det_pos p).le, smul_eq_mul]
  rw [heq] at hInt
  have hC : 0 ≤ Matrix.det sigma.1 ^ p *
      ∏ i : Fin d, Real.Gamma (bartlettShape beta i + p) / Real.Gamma (bartlettShape beta i) := by
    apply mul_nonneg (Real.rpow_pos_of_pos sigma.2.det_pos p).le
    apply Finset.prod_nonneg
    intro i _
    exact (div_pos (Real.Gamma_pos_of_pos (by
      have h := bartlettShape_pos hbp i
      unfold bartlettShape at h ⊢
      linarith))
      (Real.Gamma_pos_of_pos (bartlettShape_pos hb i))).le
  simpa only [ENNReal.toReal_ofReal hC, smul_eq_mul] using hInt

end A4Research
