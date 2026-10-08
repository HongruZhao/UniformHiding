import A3.ComplexBartlettBorder
import A3.WishartBartlettSplitMeasure

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ComplexOrder

noncomputable section
namespace A3Research

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- The actual triangular complex Bartlett source has its determinant transform at every real shape. -/
theorem wishartComplexBartlettMeasure_laplace {n : ℕ} {alpha : ℝ}
    (ha : ∀ i : Fin n, 0 < wishartBartlettShape alpha ℂ i)
    {theta : Matrix (Fin n) (Fin n) ℂ} (htheta : theta.IsHermitian)
    (hpos : (1 - theta).PosDef) :
    (∫ x : HermitianCoordinates n ℂ,
      Real.exp ((theta * hermitianMatrixOfCoordinates (wishartGramCoordinates x)).trace).re
      ∂wishartComplexBartlettMeasure n alpha) = Real.rpow ((1 - theta).det.re) (-alpha) := by
  induction n generalizing alpha with
  | zero =>
      letI := wishartBartlettMeasure_probability
        LogdetLean.GramHafnian.circularGaussian ha
      change (∫ x : HermitianCoordinates 0 ℂ,
        Real.exp ((theta * hermitianMatrixOfCoordinates (wishartGramCoordinates x)).trace).re
          ∂wishartBartlettMeasure 0 alpha LogdetLean.GramHafnian.circularGaussian) = _
      simp [Matrix.trace, Matrix.diag, Matrix.det_isEmpty, integral_const,
        MeasureTheory.probReal_univ, Real.one_rpow]
  | succ d ih =>
      have hap : 0 < alpha := by simpa using ha 0
      have hat : ∀ i : Fin d, 0 < wishartBartlettShape (alpha - 1) ℂ i := by
        intro i
        have hi := ha i.succ
        simp only [wishartBartlettShape_complex, Fin.val_succ, Nat.cast_add, Nat.cast_one] at hi ⊢
        linarith
      letI := isProbabilityMeasure_gammaMeasure hap (by norm_num : (0 : ℝ) < 1)
      letI : IsProbabilityMeasure (wishartComplexBartlettMeasure (d + 1) alpha) :=
        wishartBartlettMeasure_probability LogdetLean.GramHafnian.circularGaussian ha
      letI : IsProbabilityMeasure (wishartComplexBartlettMeasure d (alpha - 1)) :=
        wishartBartlettMeasure_probability LogdetLean.GramHafnian.circularGaussian hat
      let e := (wishartCoordinatesSplitLinearEquiv d ℂ).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
      have hs : MeasurePreserving e (wishartComplexBartlettMeasure (d + 1) alpha)
          ((gammaMeasure alpha 1).prod
            ((LogdetLean.GramHafnian.circularGaussianVector d).prod
              (wishartComplexBartlettMeasure d (alpha - 1)))) := by
        convert! measurePreserving_wishartCoordinatesSplit
          LogdetLean.GramHafnian.circularGaussian ha using 1
        simp [Complex.finrank_real_complex,
          LogdetLean.GramHafnian.circularGaussianVector, wishartComplexBartlettMeasure]
      let B := complexMatrixTail theta
      let b : Fin d → ℂ := fun i ↦ theta 0 i.succ
      let c := (theta 0 0).re
      let column : ℝ × (Fin d → ℂ) → ℝ :=
        fun q ↦ complexBartlettColumnTilt c B.transpose b q.1 q.2
      let tail : HermitianCoordinates d ℂ → ℝ :=
        fun y ↦ Real.exp ((B * hermitianMatrixOfCoordinates (wishartGramCoordinates y)).trace).re
      have hBp : (1 - B).PosDef := complexMatrixTail_gap_posDef hpos
      have hBpt : (1 - B.transpose).PosDef := by
        simpa only [Matrix.transpose_sub, Matrix.transpose_one] using hBp.transpose
      have hBt := (complexMatrixTail_isHermitian htheta).transpose
      have hb := complexMatrixGap_schur_lt_one htheta hpos
      let f : ℝ × ((Fin d → ℂ) × HermitianCoordinates d ℂ) → ℝ :=
        fun q ↦ Real.exp ((theta * hermitianMatrixOfCoordinates
          (wishartGramCoordinates (wishartCoordinatesCons q.1 q.2.1 q.2.2))).trace).re
      have hsource : (∫ x : HermitianCoordinates (d + 1) ℂ,
          Real.exp ((theta * hermitianMatrixOfCoordinates (wishartGramCoordinates x)).trace).re
            ∂wishartComplexBartlettMeasure (d + 1) alpha) =
          ∫ q, f q ∂(gammaMeasure alpha 1).prod
            ((LogdetLean.GramHafnian.circularGaussianVector d).prod
              (wishartComplexBartlettMeasure d (alpha - 1))) := by
        calc
          _ = ∫ x, f (e x) ∂wishartComplexBartlettMeasure (d + 1) alpha := by
            apply integral_congr_ae
            apply Filter.Eventually.of_forall
            intro x
            change _ = Real.exp ((theta * hermitianMatrixOfCoordinates
              (wishartGramCoordinates (wishartCoordinatesCons (wishartCoordinatesSplit x).1
                (wishartCoordinatesSplit x).2.1 (wishartCoordinatesSplit x).2.2))).trace).re
            rw [wishartCoordinatesCons_split]
          _ = _ := hs.integral_comp' f
      rw [hsource]
      have heq : f =ᵐ[(gammaMeasure alpha 1).prod
          ((LogdetLean.GramHafnian.circularGaussianVector d).prod
            (wishartComplexBartlettMeasure d (alpha - 1)))]
          (fun q ↦ column (q.1, q.2.1) * tail q.2.2) := by
        filter_upwards [Measure.quasiMeasurePreserving_fst.ae
          (wishartGammaMeasure_ae_pos alpha 1)] with q hq
        exact complexBartlettBorderTilt_factor htheta q.1 q.2.1 q.2.2 hq.le
      rw [integral_congr_ae heq]
      have hassoc := measurePreserving_prodAssoc (gammaMeasure alpha 1)
        (LogdetLean.GramHafnian.circularGaussianVector d)
        (wishartComplexBartlettMeasure d (alpha - 1))
      have hprod : (∫ q : ℝ × ((Fin d → ℂ) × HermitianCoordinates d ℂ),
          column (q.1, q.2.1) * tail q.2.2
          ∂(gammaMeasure alpha 1).prod
            ((LogdetLean.GramHafnian.circularGaussianVector d).prod
              (wishartComplexBartlettMeasure d (alpha - 1)))) =
          (∫ q : ℝ × (Fin d → ℂ), column q
            ∂(gammaMeasure alpha 1).prod (LogdetLean.GramHafnian.circularGaussianVector d)) *
          (∫ y, tail y ∂wishartComplexBartlettMeasure d (alpha - 1)) := by
        rw [← hassoc.integral_comp' (fun q ↦ column (q.1, q.2.1) * tail q.2.2)]
        exact integral_prod_mul column tail
      rw [hprod]
      have ht : (∫ y, tail y ∂wishartComplexBartlettMeasure d (alpha - 1)) =
          Real.rpow ((1 - B).det.re) (-(alpha - 1)) :=
        ih hat (complexMatrixTail_isHermitian htheta) hBp
      have hc : (∫ q : ℝ × (Fin d → ℂ), column q
          ∂(gammaMeasure alpha 1).prod (LogdetLean.GramHafnian.circularGaussianVector d)) =
          ((1 - B.transpose).det.re)⁻¹ *
            Real.rpow (1 - (c + (star b ⬝ᵥ ((1 - B.transpose)⁻¹ *ᵥ b)).re)) (-alpha) :=
        complexBartlettColumn_integral hap hBt hBpt b hb
      rw [ht, hc]
      have hdet : (1 - B.transpose).det = (1 - B).det := by
        have htr : 1 - B.transpose = (1 - B).transpose := by
          ext i j
          simp [Matrix.transpose_apply, Matrix.one_apply, eq_comm]
        rw [htr, Matrix.det_transpose]
      rw [hdet, complexMatrixGap_det_re htheta hpos]
      let D := (1 - B).det.re
      let r := 1 - (c + (star b ⬝ᵥ ((1 - B.transpose)⁻¹ *ᵥ b)).re)
      have hD : 0 < D := complex_posDef_det_re_pos hBp
      have hr : 0 < r := sub_pos.mpr hb
      change D⁻¹ * r ^ (-alpha) * D ^ (-(alpha - 1)) = (D * r) ^ (-alpha)
      rw [Real.mul_rpow hD.le hr.le]
      calc
        _ = (D ^ (-1 : ℝ) * D ^ (-(alpha - 1))) * r ^ (-alpha) := by
          rw [Real.rpow_neg_one]
          ring
        _ = _ := by
          rw [← Real.rpow_add hD]
          congr 2
          ring

def complexBartlettGramCoordinateLaw (n : ℕ) (alpha : ℝ) :
    Measure (HermitianCoordinates n ℂ) :=
  (wishartComplexBartlettMeasure n alpha).map wishartGramCoordinates

theorem complexBartlettGramCoordinateLaw_probability {n : ℕ} {alpha : ℝ}
    (ha : ∀ i : Fin n, 0 < wishartBartlettShape alpha ℂ i) :
    IsProbabilityMeasure (complexBartlettGramCoordinateLaw n alpha) := by
  letI : IsProbabilityMeasure (wishartComplexBartlettMeasure n alpha) :=
    wishartBartlettMeasure_probability LogdetLean.GramHafnian.circularGaussian ha
  unfold complexBartlettGramCoordinateLaw
  exact Measure.isProbabilityMeasure_map continuous_wishartGramCoordinates.measurable.aemeasurable

theorem complexBartlettGramCoordinateLaw_laplace {n : ℕ} {alpha : ℝ}
    (ha : ∀ i : Fin n, 0 < wishartBartlettShape alpha ℂ i)
    {theta : Matrix (Fin n) (Fin n) ℂ} (htheta : theta.IsHermitian)
    (hpos : (1 - theta).PosDef) :
    (∫ x : HermitianCoordinates n ℂ,
      Real.exp ((theta * hermitianMatrixOfCoordinates x).trace).re
      ∂complexBartlettGramCoordinateLaw n alpha) = Real.rpow ((1 - theta).det.re) (-alpha) := by
  unfold complexBartlettGramCoordinateLaw
  have hc : Continuous (fun x : HermitianCoordinates n ℂ ↦
      Real.exp ((theta * hermitianMatrixOfCoordinates x).trace).re) :=
    Real.continuous_exp.comp (Complex.continuous_re.comp
      (continuous_const.matrix_mul continuous_hermitianMatrixOfCoordinates).matrix_trace)
  rw [integral_map continuous_wishartGramCoordinates.measurable.aemeasurable
    hc.measurable.aestronglyMeasurable]
  exact wishartComplexBartlettMeasure_laplace ha htheta hpos

theorem complexGaussianGramCoordinateLaw_eq_bartlett {rows n : ℕ} (hn : n ≤ rows) :
    complexGaussianGramCoordinateLaw rows n = complexBartlettGramCoordinateLaw n (rows : ℝ) := by
  letI := complexGaussianGramCoordinateLaw_probability rows n
  letI := complexBartlettGramCoordinateLaw_probability
    (wishartBartlettShape_complex_rows_pos hn)
  exact hermitian_coordinate_law_eq_of_laplace
    (fun _ ht hp ↦ complexGaussianGramCoordinateLaw_laplace ht hp)
    (fun _ ht hp ↦ complexBartlettGramCoordinateLaw_laplace
      (wishartBartlettShape_complex_rows_pos hn) ht hp)

end A3Research
