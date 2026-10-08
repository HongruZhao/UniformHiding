import A4.GaussianWishartFlattening
import A4.DirectMomentsGaussianGram

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators

noncomputable section

namespace MatsumotoPaper

local instance (d : ℕ) : BorelSpace (RealMatrix d) := ⟨rfl⟩

def gaussianEntryCoefficients {d n : ℕ} (sigma : SymPosDef d)
    (j : Fin (2 * n) → Fin d) : Matrix (Fin d) (Fin (2 * n)) ℂ :=
  Matrix.of fun a i ↦ (A4Research.gaussianScaleFactor sigma (j i) a : ℂ)

theorem gaussianRowLinear_entryCoefficients {k d n : ℕ} (sigma : SymPosDef d)
    (j : Fin (2 * n) → Fin d) (z : Fin (k * d) → ℝ)
    (c : Fin k) (i : Fin (2 * n)) :
    gaussianRowLinear (gaussianEntryCoefficients sigma j) z c i =
      ((A4Research.gaussianScaleFactor sigma *ᵥ
        A4Research.flatToGaussianRows k d z c) (j i) : ℂ) := by
  simp only [gaussianRowLinear, gaussianEntryCoefficients, Matrix.of_apply,
    Matrix.mulVec, dotProduct, A4Research.flatToGaussianRows_apply,
    Complex.ofReal_sum, Complex.ofReal_mul]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem gaussianGramSlot_entryCoefficients {k d n : ℕ} (sigma : SymPosDef d)
    (j : Fin (2 * n) → Fin d) (z : Fin (k * d) → ℝ)
    (i q : Fin (2 * n)) :
    gaussianGramSlot (gaussianEntryCoefficients sigma j) z i q =
      2 * (A4Research.flatGaussianWishartGram sigma z (j i) (j q) : ℂ) := by
  unfold gaussianGramSlot
  simp_rw [gaussianRowLinear_entryCoefficients, ← Complex.ofReal_mul]
  rw [← Complex.ofReal_sum]
  change _ = 2 *
    (A4Research.scaledStandardGaussianGram (A4Research.gaussianScaleFactor sigma)
      (A4Research.flatToGaussianRows k d z) (j i) (j q) : ℂ)
  rw [A4Research.scaledStandardGaussianGram_entry]
  push_cast
  ring

theorem gaussianEntryCoefficients_covariance {d n : ℕ} (sigma : SymPosDef d)
    (j : Fin (2 * n) → Fin d) (i q : Fin (2 * n)) :
    (∑ a : Fin d, gaussianEntryCoefficients sigma j a i *
      gaussianEntryCoefficients sigma j a q) = (sigma.1 (j i) (j q) : ℂ) := by
  have h := congrArg (fun X : RealMatrix d ↦ X (j i) (j q))
    (A4Research.cholesky_mul_transpose sigma.2)
  change (∑ a : Fin d, A4Research.gaussianScaleFactor sigma (j i) a *
    A4Research.gaussianScaleFactor sigma (j q) a) = sigma.1 (j i) (j q) at h
  simp only [gaussianEntryCoefficients, Matrix.of_apply, ← Complex.ofReal_mul,
    ← Complex.ofReal_sum, h]

/-- Equality of all continuous observables under the characterized Wishart
law and its genuine iid Gaussian Gram realization at shape `k/2`. -/
theorem W_d.integral_continuous_eq_flatGaussian {k d : ℕ} {sigma : SymPosDef d}
    (W : W_d d ((k : ℝ) / 2) sigma)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [SecondCountableTopology E]
    (F : RealMatrix d → E) (hF : Continuous F) :
    (∫ w, F w.1 ∂W.toMeasure) =
      ∫ z, F (A4Research.flatGaussianWishartGram sigma z)
        ∂A4Research.standardGaussianVector (k * d) := by
  have hmap := W.matrixLaw_eq_gaussianWishartLaw
  rw [A4Research.gaussianWishartLaw_eq_flat_map k sigma] at hmap
  calc
    _ = ∫ X, F X ∂W.matrixLaw := by
      rw [W_d.matrixLaw, integral_map measurable_subtype_coe.aemeasurable
        hF.aestronglyMeasurable]
    _ = ∫ X, F X ∂(A4Research.standardGaussianVector (k * d)).map
        (A4Research.flatGaussianWishartGram sigma) := by rw [hmap]
    _ = _ := integral_map (A4Research.measurable_flatGaussianWishartGram sigma).aemeasurable
      hF.aestronglyMeasurable

/-- A4's full Gaussian sample identity for selected matrix entries, in the
literal involution matching notation. It works in every tensor degree and
every positive-definite scale; the row count is the only discrete parameter. -/
theorem W_d.integral_pairEntryProduct_half_integer {k d n : ℕ} {sigma : SymPosDef d}
    (W : W_d d ((k : ℝ) / 2) sigma)
    (j : Fin (2 * n) → Fin d) (M : A4Standalone.GramHafnian.PerfectMatching n) :
    (∫ w, (∏ i : M.pairReps, (w.1 (j i.1) (j (M i.1)) : ℂ)) ∂W.toMeasure) =
      (2 : ℂ) ^ (- (n : ℤ)) *
        ∑ N : A4Standalone.GramHafnian.PerfectMatching n,
          (k : ℂ) ^ matchingKappa M N *
            ∏ i : N.pairReps, (sigma.1 (j i.1) (j (N i.1)) : ℂ) := by
  let F : RealMatrix d → ℂ := fun X ↦ ∏ i : M.pairReps,
    (X (j i.1) (j (M i.1)) : ℂ)
  have hF : Continuous F := by
    dsimp only [F]
    fun_prop
  rw [W.integral_continuous_eq_flatGaussian F hF]
  have hprod (z : Fin (k * d) → ℝ) :
      (∏ i : M.pairReps,
        gaussianGramSlot (gaussianEntryCoefficients sigma j) z i.1 (M i.1)) =
      (2 : ℂ) ^ n * F (A4Research.flatGaussianWishartGram sigma z) := by
    simp_rw [gaussianGramSlot_entryCoefficients]
    rw [Finset.prod_mul_distrib]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_coe,
      A4Standalone.GramHafnian.PerfectMatching.card_pairReps]
    rfl
  have hpoint (z : Fin (k * d) → ℝ) :
      F (A4Research.flatGaussianWishartGram sigma z) =
      (2 : ℂ) ^ (-(n : ℤ)) *
        (∏ i : M.pairReps,
          gaussianGramSlot (gaussianEntryCoefficients sigma j) z i.1 (M i.1)) := by
    rw [hprod, ← mul_assoc, _root_.zpow_neg, zpow_natCast, inv_mul_cancel₀]
    · simp
    · exact pow_ne_zero n (by norm_num)
  change (∫ z, F (A4Research.flatGaussianWishartGram sigma z)
    ∂A4Research.standardGaussianVector (k * d)) = _
  simp_rw [hpoint]
  rw [integral_const_mul]
  unfold A4Research.standardGaussianVector
  rw [integral_product_gaussianGramSlot_eq_loop_moments]
  simp_rw [gaussianEntryCoefficients_covariance]

theorem W_d.integral_pairEntryProduct_half_integer_real {k d n : ℕ}
    {sigma : SymPosDef d} (W : W_d d ((k : ℝ) / 2) sigma)
    (j : Fin (2 * n) → Fin d) (M : A4Standalone.GramHafnian.PerfectMatching n) :
    (∫ w, (∏ i : M.pairReps, w.1 (j i.1) (j (M i.1))) ∂W.toMeasure) =
      (2 : ℝ) ^ (-(n : ℤ)) *
        ∑ N : A4Standalone.GramHafnian.PerfectMatching n,
          (k : ℝ) ^ matchingKappa M N *
            ∏ i : N.pairReps, sigma.1 (j i.1) (j (N i.1)) := by
  apply Complex.ofReal_injective
  have h := W.integral_pairEntryProduct_half_integer j M
  simpa only [← Complex.ofReal_prod, integral_complex_ofReal,
    ← Complex.ofReal_natCast, ← Complex.ofReal_ofNat, ← Complex.ofReal_pow,
    ← Complex.ofReal_zpow, ← Complex.ofReal_mul, ← Complex.ofReal_sum] using h

end MatsumotoPaper
