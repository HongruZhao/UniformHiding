import A3.RealBartlettBorder
import A3.WishartBartlettSplitMeasure

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators

noncomputable section
namespace A3Research

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- Determinant transform of the literal independent real Bartlett coordinates. -/
theorem wishartRealBartlettMeasure_laplace {n : ℕ} {alpha : ℝ}
    (ha : ∀ i : Fin n, 0 < wishartBartlettShape alpha ℝ i)
    {theta : Matrix (Fin n) (Fin n) ℝ} (htheta : theta.IsHermitian)
    (hpos : (1 - theta).PosDef) :
    (∫ x : HermitianCoordinates n ℝ,
      Real.exp (theta * hermitianMatrixOfCoordinates (wishartGramCoordinates x)).trace
      ∂wishartRealBartlettMeasure n alpha) = Real.rpow (1 - theta).det (-alpha) := by
  induction n generalizing alpha with
  | zero =>
      letI := wishartBartlettMeasure_probability (gaussianReal 0 (1 / 2)) ha
      change (∫ x : HermitianCoordinates 0 ℝ,
        Real.exp (theta * hermitianMatrixOfCoordinates (wishartGramCoordinates x)).trace
          ∂wishartBartlettMeasure 0 alpha (gaussianReal 0 (1 / 2))) = _
      simp [Matrix.trace, Matrix.diag, Matrix.det_isEmpty, integral_const,
        MeasureTheory.probReal_univ, Real.one_rpow]
      simpa only [one_div] using (MeasureTheory.probReal_univ
        (μ := wishartBartlettMeasure 0 alpha (gaussianReal 0 (1 / 2))))
  | succ d ih =>
      have hap : 0 < alpha := by simpa using ha 0
      have hat : ∀ i : Fin d, 0 < wishartBartlettShape (alpha - 1 / 2) ℝ i := by
        intro i
        have hi := ha i.succ
        simp only [wishartBartlettShape_real, Fin.val_succ, Nat.cast_add, Nat.cast_one] at hi ⊢
        linarith
      letI := isProbabilityMeasure_gammaMeasure hap (by norm_num : (0 : ℝ) < 1)
      letI : IsProbabilityMeasure (wishartRealBartlettMeasure (d + 1) alpha) :=
        wishartBartlettMeasure_probability (gaussianReal 0 (1 / 2)) ha
      letI : IsProbabilityMeasure (wishartRealBartlettMeasure d (alpha - 1 / 2)) :=
        wishartBartlettMeasure_probability (gaussianReal 0 (1 / 2)) hat
      let muZ : Measure (Fin d → ℝ) := Measure.pi (fun _ ↦ gaussianReal 0 (1 / 2))
      letI : IsProbabilityMeasure muZ := by dsimp [muZ]; infer_instance
      let e := (wishartCoordinatesSplitLinearEquiv d ℝ).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
      have hs : MeasurePreserving e (wishartRealBartlettMeasure (d + 1) alpha)
          ((gammaMeasure alpha 1).prod (muZ.prod (wishartRealBartlettMeasure d (alpha - 1 / 2)))) := by
        convert! measurePreserving_wishartCoordinatesSplit (gaussianReal 0 (1 / 2)) ha using 1
        simp [wishartRealBartlettMeasure, muZ]
      let B := A4Research.matrixTail theta
      let b : Fin d → ℝ := fun i ↦ theta 0 i.succ
      let c := theta 0 0
      let column : ℝ × (Fin d → ℝ) → ℝ :=
        fun q ↦ A4Research.bartlettColumnTilt c B b q.1 q.2
      let tail : HermitianCoordinates d ℝ → ℝ :=
        fun y ↦ Real.exp (B * hermitianMatrixOfCoordinates (wishartGramCoordinates y)).trace
      have hBp : (1 - B).PosDef := A4Research.matrixTail_gap_posDef hpos
      have hBt := A4Research.matrixTail_isHermitian htheta
      have hb := A4Research.matrixGap_schur_lt_one htheta hpos
      let f : ℝ × ((Fin d → ℝ) × HermitianCoordinates d ℝ) → ℝ :=
        fun q ↦ Real.exp (theta * hermitianMatrixOfCoordinates
          (wishartGramCoordinates (wishartCoordinatesCons q.1 q.2.1 q.2.2))).trace
      have hsource : (∫ x : HermitianCoordinates (d + 1) ℝ,
          Real.exp (theta * hermitianMatrixOfCoordinates (wishartGramCoordinates x)).trace
            ∂wishartRealBartlettMeasure (d + 1) alpha) =
          ∫ q, f q ∂(gammaMeasure alpha 1).prod
            (muZ.prod (wishartRealBartlettMeasure d (alpha - 1 / 2))) := by
        calc
          _ = ∫ x, f (e x) ∂wishartRealBartlettMeasure (d + 1) alpha := by
            apply integral_congr_ae
            apply Filter.Eventually.of_forall
            intro x
            change _ = Real.exp (theta * hermitianMatrixOfCoordinates
              (wishartGramCoordinates (wishartCoordinatesCons (wishartCoordinatesSplit x).1
                (wishartCoordinatesSplit x).2.1 (wishartCoordinatesSplit x).2.2))).trace
            rw [wishartCoordinatesCons_split]
          _ = _ := hs.integral_comp' f
      rw [hsource]
      have heq : f =ᵐ[(gammaMeasure alpha 1).prod
          (muZ.prod (wishartRealBartlettMeasure d (alpha - 1 / 2)))]
          (fun q ↦ column (q.1, q.2.1) * tail q.2.2) := by
        filter_upwards [Measure.quasiMeasurePreserving_fst.ae
          (wishartGammaMeasure_ae_pos alpha 1)] with q hq
        exact realBartlettBorderTilt_factor htheta q.1 q.2.1 q.2.2 hq.le
      rw [integral_congr_ae heq]
      have hassoc := measurePreserving_prodAssoc (gammaMeasure alpha 1) muZ
        (wishartRealBartlettMeasure d (alpha - 1 / 2))
      have hprod : (∫ q : ℝ × ((Fin d → ℝ) × HermitianCoordinates d ℝ),
          column (q.1, q.2.1) * tail q.2.2
          ∂(gammaMeasure alpha 1).prod (muZ.prod (wishartRealBartlettMeasure d (alpha - 1 / 2)))) =
          (∫ q : ℝ × (Fin d → ℝ), column q ∂(gammaMeasure alpha 1).prod muZ) *
          (∫ y, tail y ∂wishartRealBartlettMeasure d (alpha - 1 / 2)) := by
        rw [← hassoc.integral_comp' (fun q ↦ column (q.1, q.2.1) * tail q.2.2)]
        exact integral_prod_mul column tail
      rw [hprod]
      have ht : (∫ y, tail y ∂wishartRealBartlettMeasure d (alpha - 1 / 2)) =
          Real.rpow (1 - B).det (-(alpha - 1 / 2)) := ih hat hBt hBp
      have hc : (∫ q : ℝ × (Fin d → ℝ), column q ∂(gammaMeasure alpha 1).prod muZ) =
          (1 - B).det ^ (-1 / 2 : ℝ) *
            Real.rpow (1 - (c + b ⬝ᵥ ((1 - B)⁻¹ *ᵥ b))) (-alpha) :=
        A4Research.bartlettColumn_integral hap hBt hBp b hb
      rw [ht, hc, A4Research.matrixGap_det htheta hpos]
      let D := (1 - B).det
      let r := 1 - (c + b ⬝ᵥ ((1 - B)⁻¹ *ᵥ b))
      have hD : 0 < D := hBp.det_pos
      have hr : 0 < r := sub_pos.mpr hb
      change D ^ (-1 / 2 : ℝ) * r ^ (-alpha) * D ^ (-(alpha - 1 / 2)) = (D * r) ^ (-alpha)
      rw [Real.mul_rpow hD.le hr.le]
      calc
        _ = (D ^ (-1 / 2 : ℝ) * D ^ (-(alpha - 1 / 2))) * r ^ (-alpha) := by ring
        _ = _ := by
          rw [← Real.rpow_add hD]
          congr 2
          ring

def realBartlettGramCoordinateLaw (n : ℕ) (alpha : ℝ) :
    Measure (HermitianCoordinates n ℝ) :=
  (wishartRealBartlettMeasure n alpha).map wishartGramCoordinates

theorem realBartlettGramCoordinateLaw_probability {n : ℕ} {alpha : ℝ}
    (ha : ∀ i : Fin n, 0 < wishartBartlettShape alpha ℝ i) :
    IsProbabilityMeasure (realBartlettGramCoordinateLaw n alpha) := by
  letI : IsProbabilityMeasure (wishartRealBartlettMeasure n alpha) :=
    wishartBartlettMeasure_probability (gaussianReal 0 (1 / 2)) ha
  unfold realBartlettGramCoordinateLaw
  exact Measure.isProbabilityMeasure_map continuous_wishartGramCoordinates.measurable.aemeasurable

theorem realBartlettGramCoordinateLaw_laplace {n : ℕ} {alpha : ℝ}
    (ha : ∀ i : Fin n, 0 < wishartBartlettShape alpha ℝ i)
    {theta : Matrix (Fin n) (Fin n) ℝ} (htheta : theta.IsHermitian)
    (hpos : (1 - theta).PosDef) :
    (∫ x : HermitianCoordinates n ℝ,
      Real.exp (theta * hermitianMatrixOfCoordinates x).trace
      ∂realBartlettGramCoordinateLaw n alpha) = Real.rpow (1 - theta).det (-alpha) := by
  unfold realBartlettGramCoordinateLaw
  have hc : Continuous (fun x : HermitianCoordinates n ℝ ↦
      Real.exp (theta * hermitianMatrixOfCoordinates x).trace) :=
    Real.continuous_exp.comp
      (continuous_const.matrix_mul continuous_hermitianMatrixOfCoordinates).matrix_trace
  rw [integral_map continuous_wishartGramCoordinates.measurable.aemeasurable
    hc.measurable.aestronglyMeasurable]
  exact wishartRealBartlettMeasure_laplace ha htheta hpos

end A3Research
