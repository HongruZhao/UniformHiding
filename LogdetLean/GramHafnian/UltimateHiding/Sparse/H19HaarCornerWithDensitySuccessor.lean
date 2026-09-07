import LogdetLean.GramHafnian.UltimateHiding.Sparse.H19HaarCornerSuccessorRepresentation
import LogdetLean.GramHafnian.UltimateHiding.Sparse.H19HaarCornerFiberDensityMeasureBalance

set_option maxHeartbeats 800000

/-!
# Concrete Haar-corner density successor step

This downstream module combines the exact probabilistic successor
representation, the fixed-fiber Jacobian, and the Jiang density balance.  The
probabilistic representation remains an ordinary theorem argument in the
abstract adapter and is discharged by the internally proved Haar/Stiefel
representation at the concrete endpoint.
-/

open MeasureTheory Matrix Filter
open scoped ENNReal BigOperators ComplexOrder MatrixOrder

namespace LogdetLean.GramHafnian.UltimateHiding.Sparse

noncomputable section

open CurrentPRL

local instance h19HaarCornerSuccessorMatrixBorelSpace (K N : ℕ) :
    BorelSpace (Matrix (Fin K) (Fin N) ℂ) := by
  exact inferInstanceAs (BorelSpace (Fin K → Fin N → ℂ))

/-- The conditional density in ordinary appended-column coordinates. -/
def jiangHaarCornerSuccConditionalPDF (M K N : ℕ)
    (z : Matrix (Fin K) (Fin N) ℂ × (Fin K → ℂ)) : ℝ≥0∞ :=
  jiangUnscaledTallHaarCornerPDF M K (N + 1)
      (haarCornerAppendColumnMeasurableEquiv K N z) /
    jiangUnscaledTallHaarCornerPDF M K N z.1

theorem measurable_jiangHaarCornerSuccConditionalPDF (M K N : ℕ) :
    Measurable (jiangHaarCornerSuccConditionalPDF M K N) := by
  exact
    ((measurable_jiangUnscaledTallHaarCornerPDF M K (N + 1)).comp
      (haarCornerAppendColumnMeasurableEquiv K N).measurable).div
      ((measurable_jiangUnscaledTallHaarCornerPDF M K N).comp measurable_fst)

/-- Removing the last appended column adds its rank-one row Gram back to the
successor left defect. -/
theorem haarCornerLeftDefect_eq_appendColumn_leftDefect_add_outer
    {K N : ℕ} (A : Matrix (Fin K) (Fin N) ℂ) (x : Fin K → ℂ) :
    haarCornerLeftDefect A =
      haarCornerLeftDefect
          (haarCornerAppendColumnMeasurableEquiv K N (A, x)) +
        complexColumnMatrix x * (complexColumnMatrix x).conjTranspose := by
  unfold haarCornerLeftDefect
  ext i j
  simp [Matrix.mul_apply, Fin.sum_univ_castSucc, complexColumnMatrix]
  ring

/-- Cancellation in `ℝ≥0∞` with the finiteness hypotheses needed by division. -/
private theorem ennreal_inv_mul_eq_inv_mul_of_mul_eq
    {a b c t : ℝ≥0∞} (h : a * b = c * t)
    (ha0 : a ≠ 0) (hat : a ≠ ∞) (hc0 : c ≠ 0) (hct : c ≠ ∞) :
    c⁻¹ * b = a⁻¹ * t := by
  rw [mul_comm c⁻¹ b, mul_comm a⁻¹ t]
  change b / c = t / a
  exact (ENNReal.div_eq_div_iff ha0 hat hc0 hct).2 h

private theorem jiangUnscaledTallHaarCornerPDF_ne_top
    (M K N : ℕ) (A : Matrix (Fin K) (Fin N) ℂ) :
    jiangUnscaledTallHaarCornerPDF M K N A ≠ ∞ := by
  unfold jiangUnscaledTallHaarCornerPDF
  split_ifs <;> simp

/-- The pointwise fixed-fiber change-of-variables density, expressed as the
ordinary conditional Jiang density. -/
theorem haarCornerDefectSqrt_fiber_density_eq_conditional
    {M K N : ℕ} (hsize : K + (N + 1) ≤ M)
    (A : Matrix (Fin K) (Fin N) ℂ)
    (hA : (haarCornerLeftDefect A).PosDef) (x : Fin K → ℂ) :
    ENNReal.ofReal |((haarCornerLeftDefect A).det.re)⁻¹| *
        jiangHaarCornerSuccFiberPDF M K N
          ((haarCornerDefectSqrtMeasurableEquiv A hA).symm x) =
      jiangHaarCornerSuccConditionalPDF M K N (A, x) := by
  let e := haarCornerDefectSqrtMeasurableEquiv A hA
  let u : Fin K → ℂ := e.symm x
  let a := jiangUnscaledTallHaarCornerPDF M K N A
  let b := jiangHaarCornerSuccFiberPDF M K N u
  let c := ENNReal.ofReal (haarCornerLeftDefect A).det.re
  let t := jiangUnscaledTallHaarCornerPDF M K (N + 1)
    (haarCornerAppendSqrtColumn (A, u))
  have hd : 0 < (haarCornerLeftDefect A).det.re :=
    (RCLike.pos_iff.mp hA.det_pos).1
  have hab : a * b = c * t := by
    exact jiangUnscaledTallHaarCornerPDF_haarCornerAppendSqrtColumn_balance
      hsize A hA u
  have ha0 : a ≠ 0 :=
    jiangUnscaledTallHaarCornerPDF_ne_zero_of_leftDefect_posDef A hA
  have hat : a ≠ ∞ :=
    jiangUnscaledTallHaarCornerPDF_ne_top M K N A
  have hc0 : c ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hd)
  have hct : c ≠ ∞ := ENNReal.ofReal_ne_top
  have hcancel : c⁻¹ * b = a⁻¹ * t :=
    ennreal_inv_mul_eq_inv_mul_of_mul_eq hab ha0 hat hc0 hct
  have hjac :
      ENNReal.ofReal |((haarCornerLeftDefect A).det.re)⁻¹| = c⁻¹ := by
    rw [abs_of_pos (inv_pos.mpr hd), ENNReal.ofReal_inv_of_pos hd]
  have happend :
      haarCornerAppendColumnMeasurableEquiv K N (A, x) =
        haarCornerAppendSqrtColumn (A, u) := by
    rw [haarCornerAppendSqrtColumn_eq_appendColumnEquiv]
    change haarCornerAppendColumnMeasurableEquiv K N (A, x) =
      haarCornerAppendColumnMeasurableEquiv K N (A, e u)
    rw [MeasurableEquiv.apply_symm_apply]
  rw [hjac]
  calc
    c⁻¹ * jiangHaarCornerSuccFiberPDF M K N
          ((haarCornerDefectSqrtMeasurableEquiv A hA).symm x) =
        c⁻¹ * b := rfl
    _ = a⁻¹ * t := hcancel
    _ = t / a := by rw [ENNReal.div_eq_inv_mul]
    _ = jiangHaarCornerSuccConditionalPDF M K N (A, x) := by
      unfold jiangHaarCornerSuccConditionalPDF
      rw [happend]

/-- Fixed positive-definite fibers transport the successor ball density to
the conditional Jiang density in the appended column. -/
theorem map_haarCornerDefectSqrt_jiangFiberDensity
    {M K N : ℕ} (hsize : K + (N + 1) ≤ M)
    (A : Matrix (Fin K) (Fin N) ℂ)
    (hA : (haarCornerLeftDefect A).PosDef) :
    Measure.map (fun u : Fin K → ℂ ↦ haarCornerDefectSqrt A *ᵥ u)
        ((complexColumnLebesgueVolume K).withDensity
          (jiangHaarCornerSuccFiberPDF M K N)) =
      (complexColumnLebesgueVolume K).withDensity
        (fun x ↦ jiangHaarCornerSuccConditionalPDF M K N (A, x)) := by
  rw [show (fun u : Fin K → ℂ ↦ haarCornerDefectSqrt A *ᵥ u) =
      haarCornerDefectSqrtMeasurableEquiv A hA by rfl]
  rw [map_haarCornerDefectSqrtMeasurableEquiv_withDensity A hA
    (jiangHaarCornerSuccFiberPDF M K N)
    (measurable_jiangHaarCornerSuccFiberPDF M K N)]
  congr 1
  funext x
  exact haarCornerDefectSqrt_fiber_density_eq_conditional hsize A hA x

/-- Under strict successor size, the conditional-density quotient recombines
pointwise with the old Jiang density.  The only delicate case is a zero old
density; strict size makes the successor determinant exponent positive, and
a nonzero successor density would force a positive-definite successor defect,
hence a positive-definite old defect after adding back the last rank-one Gram.
-/
theorem jiangOldPDF_mul_succConditionalPDF_eq_succPDF_of_strict
    {M K N : ℕ} (hsize : K + (N + 1) < M)
    (z : Matrix (Fin K) (Fin N) ℂ × (Fin K → ℂ)) :
    jiangUnscaledTallHaarCornerPDF M K N z.1 *
        jiangHaarCornerSuccConditionalPDF M K N z =
      jiangUnscaledTallHaarCornerPDF M K (N + 1)
        (haarCornerAppendColumnMeasurableEquiv K N z) := by
  rcases z with ⟨A, x⟩
  let a := jiangUnscaledTallHaarCornerPDF M K N A
  let t := jiangUnscaledTallHaarCornerPDF M K (N + 1)
    (haarCornerAppendColumnMeasurableEquiv K N (A, x))
  by_cases ha : a = 0
  · have ht : t = 0 := by
      by_contra ht0
      have hnew :
          (haarCornerLeftDefect
            (haarCornerAppendColumnMeasurableEquiv K N (A, x))).PosDef :=
        haarCornerLeftDefect_posDef_of_jiangPDF_ne_zero
          (by omega : K + ((N + 1) + 1) ≤ M)
          (haarCornerAppendColumnMeasurableEquiv K N (A, x)) ht0
      have houter :
          (complexColumnMatrix x *
            (complexColumnMatrix x).conjTranspose).PosSemidef :=
        posSemidef_self_mul_conjTranspose (complexColumnMatrix x)
      have hold : (haarCornerLeftDefect A).PosDef := by
        rw [haarCornerLeftDefect_eq_appendColumn_leftDefect_add_outer A x]
        exact hnew.add_posSemidef houter
      exact
        (jiangUnscaledTallHaarCornerPDF_ne_zero_of_leftDefect_posDef A hold) ha
    change a * (t / a) = t
    simp [ha, ht]
  · change a * (t / a) = t
    exact ENNReal.mul_div_cancel ha
      (jiangUnscaledTallHaarCornerPDF_ne_top M K N A)

/-- Fubini assembles the fixed positive-definite fiber transports.  Singular
old defects are absent almost everywhere because the old Jiang exponent is
positive. -/
theorem map_haarCornerTriangular_jiangProductDensity
    {M K N : ℕ} (hsize : K + (N + 1) ≤ M) :
    Measure.map
        (fun z : Matrix (Fin K) (Fin N) ℂ × (Fin K → ℂ) ↦
          (z.1, haarCornerDefectSqrt z.1 *ᵥ z.2))
        (((complexRectangularLebesgueVolume K N).withDensity
            (jiangUnscaledTallHaarCornerPDF M K N)).prod
          ((complexColumnLebesgueVolume K).withDensity
            (jiangHaarCornerSuccFiberPDF M K N))) =
      (((complexRectangularLebesgueVolume K N).withDensity
            (jiangUnscaledTallHaarCornerPDF M K N)).prod
          (complexColumnLebesgueVolume K)).withDensity
        (jiangHaarCornerSuccConditionalPDF M K N) := by
  have hT : Measurable
      (fun z : Matrix (Fin K) (Fin N) ℂ × (Fin K → ℂ) ↦
        haarCornerDefectSqrt z.1 *ᵥ z.2) := by
    have happ := measurable_haarCornerAppendSqrtColumn K N
    refine measurable_pi_lambda _ fun i ↦ ?_
    have hi := (measurable_pi_apply (Fin.last N)).comp
      ((measurable_pi_apply i).comp happ)
    convert hi using 1
    funext z
    exact (haarCornerAppendSqrtColumn_last z.1 z.2 i).symm
  apply map_prod_fiberwise_withDensity
    ((complexRectangularLebesgueVolume K N).withDensity
      (jiangUnscaledTallHaarCornerPDF M K N))
    ((complexColumnLebesgueVolume K).withDensity
      (jiangHaarCornerSuccFiberPDF M K N))
    (complexColumnLebesgueVolume K)
    (fun A u ↦ haarCornerDefectSqrt A *ᵥ u)
    (jiangHaarCornerSuccConditionalPDF M K N)
    hT
    (measurable_jiangHaarCornerSuccConditionalPDF M K N)
  filter_upwards [ae_haarCornerLeftDefect_posDef_under_jiangDensity hsize]
    with A hA
  exact map_haarCornerDefectSqrt_jiangFiberDensity hsize A hA

/-- The plain append-coordinate equivalence turns the old-density base times
the conditional density into the successor Jiang density. -/
theorem map_haarCornerAppendColumn_conditionalDensity_of_strict
    {M K N : ℕ} (hsize : K + (N + 1) < M) :
    Measure.map (haarCornerAppendColumnMeasurableEquiv K N)
        ((((complexRectangularLebesgueVolume K N).withDensity
              (jiangUnscaledTallHaarCornerPDF M K N)).prod
            (complexColumnLebesgueVolume K)).withDensity
          (jiangHaarCornerSuccConditionalPDF M K N)) =
      (complexRectangularLebesgueVolume K (N + 1)).withDensity
        (jiangUnscaledTallHaarCornerPDF M K (N + 1)) := by
  let lambdaA := complexRectangularLebesgueVolume K N
  let lambdaX := complexColumnLebesgueVolume K
  let lambdaY := complexRectangularLebesgueVolume K (N + 1)
  let e := haarCornerAppendColumnMeasurableEquiv K N
  let f := jiangUnscaledTallHaarCornerPDF M K N
  let q := jiangHaarCornerSuccConditionalPDF M K N
  let target := jiangUnscaledTallHaarCornerPDF M K (N + 1)
  let fp : Matrix (Fin K) (Fin N) ℂ × (Fin K → ℂ) → ℝ≥0∞ :=
    fun z ↦ f z.1
  let fback : Matrix (Fin K) (Fin (N + 1)) ℂ → ℝ≥0∞ :=
    fp ∘ e.symm
  let qback : Matrix (Fin K) (Fin (N + 1)) ℂ → ℝ≥0∞ :=
    q ∘ e.symm
  have hf : Measurable f :=
    measurable_jiangUnscaledTallHaarCornerPDF M K N
  have hq : Measurable q :=
    measurable_jiangHaarCornerSuccConditionalPDF M K N
  have hfp : Measurable fp := hf.comp measurable_fst
  have hfback : Measurable fback := hfp.comp e.symm.measurable
  have hqback : Measurable qback := hq.comp e.symm.measurable
  have hprod :
      (lambdaA.withDensity f).prod lambdaX =
        (lambdaA.prod lambdaX).withDensity fp := by
    simpa only [fp] using
      (prod_withDensity_left (μ := lambdaA) (ν := lambdaX) hf)
  have hmapBase :
      Measure.map e ((lambdaA.withDensity f).prod lambdaX) =
        lambdaY.withDensity fback := by
    calc
      Measure.map e ((lambdaA.withDensity f).prod lambdaX) =
          Measure.map e ((lambdaA.prod lambdaX).withDensity fp) := by
            rw [hprod]
      _ = (Measure.map e (lambdaA.prod lambdaX)).withDensity fback := by
        exact LogdetLean.GramHafnian.map_measurableEquiv_withDensity_currentPRL
          e (lambdaA.prod lambdaX) fp hfp
      _ = lambdaY.withDensity fback := by
        rw [show Measure.map e (lambdaA.prod lambdaX) = lambdaY by
          exact map_haarCornerAppendColumnMeasurableEquiv_volume K N]
  change Measure.map e (((lambdaA.withDensity f).prod lambdaX).withDensity q) =
    lambdaY.withDensity target
  calc
    Measure.map e (((lambdaA.withDensity f).prod lambdaX).withDensity q) =
        (Measure.map e ((lambdaA.withDensity f).prod lambdaX)).withDensity
          qback := by
      exact LogdetLean.GramHafnian.map_measurableEquiv_withDensity_currentPRL
        e ((lambdaA.withDensity f).prod lambdaX) q hq
    _ = (lambdaY.withDensity fback).withDensity qback := by rw [hmapBase]
    _ = lambdaY.withDensity (fback * qback) :=
      (withDensity_mul lambdaY hfback hqback).symm
    _ = lambdaY.withDensity target := by
      congr 1
      funext Y
      have hcombine :=
        jiangOldPDF_mul_succConditionalPDF_eq_succPDF_of_strict
          hsize (e.symm Y)
      change f (e.symm Y).1 * q (e.symm Y) = target Y
      simpa only [f, q, target, e, MeasurableEquiv.apply_symm_apply]
        using hcombine

/-- Concrete strict-size `N → N+1` Jiang density rule.  Its only theorem
input is the preceding-column density equality; the exact Haar successor
representation, the ball-fiber density, the Jacobian, and the normalization
recursion are all discharged internally. -/
theorem jiangUnscaledTallHaarCorner_density_succ_proved
    {M K N : ℕ} (hK : 0 < K) (hsize : K + (N + 1) < M)
    (hprev :
      jiangUnscaledTallHaarCornerLaw M K N =
        (complexRectangularLebesgueVolume K N).withDensity
          (jiangUnscaledTallHaarCornerPDF M K N)) :
    jiangUnscaledTallHaarCornerLaw M K (N + 1) =
      (complexRectangularLebesgueVolume K (N + 1)).withDensity
        (jiangUnscaledTallHaarCornerPDF M K (N + 1)) := by
  let F := fun z : Matrix (Fin K) (Fin N) ℂ × (Fin K → ℂ) ↦
    (z.1, haarCornerDefectSqrt z.1 *ᵥ z.2)
  let e := haarCornerAppendColumnMeasurableEquiv K N
  let source :=
    ((complexRectangularLebesgueVolume K N).withDensity
        (jiangUnscaledTallHaarCornerPDF M K N)).prod
      ((complexColumnLebesgueVolume K).withDensity
        (jiangHaarCornerSuccFiberPDF M K N))
  have hexp : (M - N) - K = M - K - N := by omega
  have hrawClosed := withDensity_h19BaseColumnRawPDF_eq_jiangSuccFiber
    hK (Nat.le_of_lt hsize)
  have hT : Measurable
      (fun z : Matrix (Fin K) (Fin N) ℂ × (Fin K → ℂ) ↦
        haarCornerDefectSqrt z.1 *ᵥ z.2) := by
    have happ := measurable_haarCornerAppendSqrtColumn K N
    refine measurable_pi_lambda _ fun i ↦ ?_
    have hi := (measurable_pi_apply (Fin.last N)).comp
      ((measurable_pi_apply i).comp happ)
    convert hi using 1
    funext z
    exact (haarCornerAppendSqrtColumn_last z.1 z.2 i).symm
  have hF : Measurable F := measurable_fst.prodMk hT
  rw [jiangUnscaledTallHaarCornerLaw_succ_eq_map_appendSqrt_baseColumnRawPDF
    (by omega : 1 ≤ K) (Nat.le_of_lt hsize)]
  rw [hexp, hrawClosed, hprev]
  change Measure.map haarCornerAppendSqrtColumn source = _
  calc
    Measure.map haarCornerAppendSqrtColumn source =
        Measure.map e (Measure.map F source) := by
      rw [haarCornerAppendSqrtColumn_eq_appendColumnEquiv]
      exact (Measure.map_map e.measurable hF).symm
    _ = Measure.map e
        ((((complexRectangularLebesgueVolume K N).withDensity
              (jiangUnscaledTallHaarCornerPDF M K N)).prod
            (complexColumnLebesgueVolume K)).withDensity
          (jiangHaarCornerSuccConditionalPDF M K N)) := by
      rw [show Measure.map F source =
          (((complexRectangularLebesgueVolume K N).withDensity
                (jiangUnscaledTallHaarCornerPDF M K N)).prod
              (complexColumnLebesgueVolume K)).withDensity
            (jiangHaarCornerSuccConditionalPDF M K N) by
        exact map_haarCornerTriangular_jiangProductDensity
          (Nat.le_of_lt hsize)]
    _ = (complexRectangularLebesgueVolume K (N + 1)).withDensity
        (jiangUnscaledTallHaarCornerPDF M K (N + 1)) :=
      map_haarCornerAppendColumn_conditionalDensity_of_strict hsize

#print axioms haarCornerDefectSqrt_fiber_density_eq_conditional
#print axioms map_haarCornerDefectSqrt_jiangFiberDensity
#print axioms map_haarCornerTriangular_jiangProductDensity
#print axioms jiangOldPDF_mul_succConditionalPDF_eq_succPDF_of_strict
#print axioms map_haarCornerAppendColumn_conditionalDensity_of_strict
#print axioms jiangUnscaledTallHaarCorner_density_succ_proved

end

end LogdetLean.GramHafnian.UltimateHiding.Sparse
