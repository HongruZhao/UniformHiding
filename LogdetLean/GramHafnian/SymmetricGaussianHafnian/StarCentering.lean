import LogdetLean.GramHafnian.SymmetricGaussianHafnian.SecondMoment
import LogdetLean.GramHafnian.ShiftedAnticoncentration.IndependentShiftGaussianKernel

/-!
# Centering one complete Gaussian vertex star

The underlying independent edge law is unchanged.  Only deterministic
means on the selected star are set to zero, and an arbitrary output center
is removed.  Iteration may therefore use overlapping stars.
-/

open MeasureTheory ProbabilityTheory Complex
open scoped BigOperators Real

namespace LogdetLean.GramHafnian.SymmetricGaussianHafnian

noncomputable section

set_option maxHeartbeats 800000

/-- Set the means of every edge incident to one vertex to zero. -/
def zeroStar {ι : Type*} [DecidableEq ι] (v : ι)
    (a : Edge ι → ℂ) : Edge ι → ℂ :=
  fun e ↦ if v ∈ e.1 then 0 else a e

@[simp] theorem zeroStar_apply_mem {ι : Type*} [DecidableEq ι]
    (v : ι) (a : Edge ι → ℂ) (e : Edge ι) (h : v ∈ e.1) :
    zeroStar v a e = 0 := by simp [zeroStar, h]

@[simp] theorem zeroStar_apply_not_mem {ι : Type*} [DecidableEq ι]
    (v : ι) (a : Edge ι → ℂ) (e : Edge ι) (h : v ∉ e.1) :
    zeroStar v a e = a e := by simp [zeroStar, h]

@[simp] theorem restrictEdges_add {ι κ : Type*} (f : ι ↪ κ)
    (x a : Edge κ → ℂ) :
    restrictEdges f (x + a) = restrictEdges f x + restrictEdges f a := rfl

@[simp] theorem lastVertexSplit_add {n : ℕ}
    (x a : Edge (Fin (n + 1)) → ℂ) :
    lastVertexSplit n (x + a) = lastVertexSplit n x + lastVertexSplit n a := by
  apply Prod.ext
  · rfl
  · funext i
    simp [lastVertexSplit, matrixOfEdges, Fin.castSucc_ne_last]

@[simp] theorem lastVertexSplit_zeroStar_background {n : ℕ}
    (a : Edge (Fin (n + 1)) → ℂ) :
    (lastVertexSplit n (zeroStar (Fin.last n) a)).1 = (lastVertexSplit n a).1 := by
  funext e
  change (if Fin.last n ∈ (edgeEmbedding (initialVertexEmbedding n) e).1
    then 0 else a (edgeEmbedding (initialVertexEmbedding n) e)) = _
  have h : Fin.last n ∉ (edgeEmbedding (initialVertexEmbedding n) e).1 := by
    change Fin.last n ∉ e.1.map (initialVertexEmbedding n)
    simp only [Finset.mem_map]
    rintro ⟨i, hi, he⟩
    exact Fin.castSucc_ne_last i he
  simp only [h, ↓reduceIte]
  rfl

@[simp] theorem lastVertexSplit_zeroStar_star {n : ℕ}
    (a : Edge (Fin (n + 1)) → ℂ) :
    (lastVertexSplit n (zeroStar (Fin.last n) a)).2 = 0 := by
  funext i
  simp [lastVertexSplit, matrixOfEdges, Fin.castSucc_ne_last, zeroStar, edgeOfNe]

theorem edgeHafnian_add_lastVertexSplit {n : ℕ}
    (x a : Edge (Fin (n + 1)) → ℂ) :
    edgeHafnian (x + a) =
      iidCircularTransposeLinearForm
        (edgeCofactor ((lastVertexSplit n x).1 + (lastVertexSplit n a).1))
        ((lastVertexSplit n x).2 + (lastVertexSplit n a).2) := by
  rw [edgeHafnian_eq_lastVertexLinearForm, lastVertexSplit_add]
  rfl

theorem edgeHafnian_add_zeroStar_last {n : ℕ}
    (x a : Edge (Fin (n + 1)) → ℂ) :
    edgeHafnian (x + zeroStar (Fin.last n) a) =
      iidCircularTransposeLinearForm
        (edgeCofactor ((lastVertexSplit n x).1 + (lastVertexSplit n a).1))
        (lastVertexSplit n x).2 := by
  rw [edgeHafnian_add_lastVertexSplit, lastVertexSplit_zeroStar_background,
    lastVertexSplit_zeroStar_star, add_zero]

@[fun_prop] theorem continuous_edgeHafnian_shifted_laplace
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    (a : Edge ι → ℂ) (w : ℂ) (s : ℝ) :
    Continuous (fun x : Edge ι → ℂ ↦ Real.exp (-s * ‖edgeHafnian (x + a) - w‖ ^ 2)) := by
  fun_prop

theorem integrable_edgeHafnian_shifted_laplace
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    (a : Edge ι → ℂ) (w : ℂ) (s : ℝ) (hs : 0 ≤ s) :
    Integrable (fun x : Edge ι → ℂ ↦ Real.exp (-s * ‖edgeHafnian (x + a) - w‖ ^ 2))
      (edgeGaussian ι) := by
  apply Integrable.of_bound (continuous_edgeHafnian_shifted_laplace a w s).aestronglyMeasurable 1
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs) (sq_nonneg _))

private def shiftedStarLaplace {n : ℕ} (b : Edge (Fin n) → ℂ)
    (a : Fin n → ℂ) (w : ℂ) (s : ℝ)
    (p : (Edge (Fin n) → ℂ) × (Fin n → ℂ)) : ℝ :=
  Real.exp (-s * ‖iidCircularTransposeLinearForm (edgeCofactor (p.1 + b))
    (p.2 + a) - w‖ ^ 2)

private theorem integrable_shiftedStarLaplace {n : ℕ}
    (b : Edge (Fin n) → ℂ) (a : Fin n → ℂ) (w : ℂ) (s : ℝ) (hs : 0 ≤ s) :
    Integrable (shiftedStarLaplace b a w s)
      ((edgeGaussian (Fin n)).prod (standardGaussianProduct (Fin n))) := by
  apply Integrable.of_bound (by
    unfold shiftedStarLaplace iidCircularTransposeLinearForm
    fun_prop) 1
  filter_upwards [] with p
  unfold shiftedStarLaplace
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs) (sq_nonneg _))

private theorem integral_shiftedStarLaplace_le {n : ℕ}
    (b : Edge (Fin n) → ℂ) (a : Fin n → ℂ) (w : ℂ) (s : ℝ) (hs : 0 ≤ s) :
    (∫ p, shiftedStarLaplace b a w s p
      ∂((edgeGaussian (Fin n)).prod (standardGaussianProduct (Fin n)))) ≤
      ∫ p, shiftedStarLaplace b 0 0 s p
        ∂((edgeGaussian (Fin n)).prod (standardGaussianProduct (Fin n))) := by
  have hleft := integrable_shiftedStarLaplace b a w s hs
  have hright := integrable_shiftedStarLaplace b 0 0 s hs
  rw [integral_prod _ hleft, integral_prod _ hright]
  apply integral_mono hleft.integral_prod_left hright.integral_prod_left
  intro R
  let y := edgeCofactor (R + b)
  have hphase (g : Fin n → ℂ) :
      iidCircularTransposeLinearForm y (g + a) - w =
        iidCircularTransposeLinearForm y g + (iidCircularTransposeLinearForm y a - w) := by
    simp [iidCircularTransposeLinearForm, add_mul, Finset.sum_add_distrib, sub_eq_add_neg,
      add_assoc]
  calc
    _ = ∫ g : Fin n → ℂ,
        Real.exp (-s * ‖iidCircularTransposeLinearForm y g +
          (iidCircularTransposeLinearForm y a - w)‖ ^ 2)
        ∂standardGaussianProduct (Fin n) := by
      apply integral_congr_ae
      filter_upwards [] with g
      unfold shiftedStarLaplace
      rw [hphase]
    _ ≤ (1 + s * circularCoefficientEnergy y)⁻¹ :=
      integral_exp_neg_norm_sq_iidCircularTransposeLinearForm_add_le
        y (iidCircularTransposeLinearForm y a - w) s hs
    _ = _ := by
      simpa only [shiftedStarLaplace, add_zero, sub_zero, y, standardGaussianProduct] using
        (integral_exp_neg_norm_sq_iidCircularTransposeLinearForm y s hs).symm

/-- Exact one-star centering at the final vertex. No parity or nonzero
variance hypothesis is needed. -/
theorem edgeHafnian_laplace_le_zeroStar_last
    (n : ℕ) (a : Edge (Fin (n + 1)) → ℂ) (w : ℂ) (s : ℝ) (hs : 0 ≤ s) :
    (∫ x : Edge (Fin (n + 1)) → ℂ,
      Real.exp (-s * ‖edgeHafnian (x + a) - w‖ ^ 2) ∂edgeGaussian (Fin (n + 1))) ≤
      ∫ x : Edge (Fin (n + 1)) → ℂ,
        Real.exp (-s * ‖edgeHafnian (x + zeroStar (Fin.last n) a)‖ ^ 2)
        ∂edgeGaussian (Fin (n + 1)) := by
  let b := (lastVertexSplit n a).1
  let c := (lastVertexSplit n a).2
  have he := measurePreserving_lastVertexSplit n
  have hpull (c' : Fin n → ℂ) (w' : ℂ) :
      (∫ x : Edge (Fin (n + 1)) → ℂ,
        shiftedStarLaplace b c' w' s (lastVertexSplit n x)
        ∂edgeGaussian (Fin (n + 1))) =
      ∫ p, shiftedStarLaplace b c' w' s p
        ∂((edgeGaussian (Fin n)).prod (standardGaussianProduct (Fin n))) := by
    rw [← he.map_eq]
    symm
    exact integral_map he.measurable.aemeasurable (by
      rw [he.map_eq]
      exact (integrable_shiftedStarLaplace b c' w' s hs).aestronglyMeasurable)
  calc
    _ = ∫ x : Edge (Fin (n + 1)) → ℂ,
        shiftedStarLaplace b c w s (lastVertexSplit n x)
        ∂edgeGaussian (Fin (n + 1)) := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [edgeHafnian_add_lastVertexSplit]
      rfl
    _ = _ := hpull c w
    _ ≤ _ := integral_shiftedStarLaplace_le b c w s hs
    _ = ∫ x : Edge (Fin (n + 1)) → ℂ,
        shiftedStarLaplace b 0 0 s (lastVertexSplit n x)
        ∂edgeGaussian (Fin (n + 1)) := (hpull 0 0).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [edgeHafnian_add_zeroStar_last]
      simp only [shiftedStarLaplace, add_zero, sub_zero, b]

theorem restrictEdges_zeroStar_equiv
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) (v : ι) (a : Edge κ → ℂ) :
    restrictEdges e.toEmbedding (zeroStar (e v) a) =
      zeroStar v (restrictEdges e.toEmbedding a) := by
  funext d
  have h : e v ∈ (edgeEmbedding e.toEmbedding d).1 ↔ v ∈ d.1 := by
    change e v ∈ d.1.map e.toEmbedding ↔ v ∈ d.1
    simp
  simp only [restrictEdges, zeroStar, h]

theorem edgeHafnian_shifted_laplace_reindex
    {ι κ : Type*} [Fintype ι] [LinearOrder ι] [Fintype κ] [LinearOrder κ]
    (e : ι ≃ κ) (a : Edge κ → ℂ) (w : ℂ) (s : ℝ) :
    (∫ x : Edge ι → ℂ,
      Real.exp (-s * ‖edgeHafnian (x + restrictEdges e.toEmbedding a) - w‖ ^ 2)
      ∂edgeGaussian ι) =
      ∫ x : Edge κ → ℂ,
        Real.exp (-s * ‖edgeHafnian (x + a) - w‖ ^ 2) ∂edgeGaussian κ := by
  rw [← (measurePreserving_restrictEdges e.toEmbedding).map_eq,
    integral_map (measurable_restrictEdges e.toEmbedding).aemeasurable (by fun_prop)]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [← restrictEdges_add, edgeHafnian_restrict_equiv]

/-- Center any complete vertex star of the literal symmetric Gaussian
matrix. Overlap with other stars does not affect this pointwise mean update. -/
theorem edgeHafnian_laplace_le_zeroStar {m : ℕ}
    (v : Fin m) (a : Edge (Fin m) → ℂ) (w : ℂ) (s : ℝ) (hs : 0 ≤ s) :
    (∫ x : Edge (Fin m) → ℂ,
      Real.exp (-s * ‖edgeHafnian (x + a) - w‖ ^ 2) ∂edgeGaussian (Fin m)) ≤
      ∫ x : Edge (Fin m) → ℂ,
        Real.exp (-s * ‖edgeHafnian (x + zeroStar v a)‖ ^ 2) ∂edgeGaussian (Fin m) := by
  classical
  cases m with
  | zero => exact Fin.elim0 v
  | succ n =>
      let e := Equiv.swap v (Fin.last n)
      have hzero : restrictEdges e.toEmbedding (zeroStar v a) =
          zeroStar (Fin.last n) (restrictEdges e.toEmbedding a) := by
        simpa only [e, Equiv.swap_apply_right] using
          restrictEdges_zeroStar_equiv e (Fin.last n) a
      calc
        _ = ∫ x : Edge (Fin (n + 1)) → ℂ,
            Real.exp (-s * ‖edgeHafnian (x + restrictEdges e.toEmbedding a) - w‖ ^ 2)
            ∂edgeGaussian (Fin (n + 1)) :=
          (edgeHafnian_shifted_laplace_reindex e a w s).symm
        _ ≤ ∫ x : Edge (Fin (n + 1)) → ℂ,
            Real.exp (-s * ‖edgeHafnian
              (x + zeroStar (Fin.last n) (restrictEdges e.toEmbedding a))‖ ^ 2)
            ∂edgeGaussian (Fin (n + 1)) :=
          edgeHafnian_laplace_le_zeroStar_last n (restrictEdges e.toEmbedding a) w s hs
        _ = _ := by
          rw [← hzero]
          simpa only [sub_zero] using edgeHafnian_shifted_laplace_reindex e (zeroStar v a) 0 s

end

end LogdetLean.GramHafnian.SymmetricGaussianHafnian
