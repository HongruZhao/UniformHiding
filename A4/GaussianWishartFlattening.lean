import A4.GaussianWishartCongruence
import Mathlib.Probability.ProductMeasure

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators

noncomputable section

namespace A4Research

def flatToGaussianRows (k d : ℕ) :
    (Fin (k * d) → ℝ) ≃ᵐ (Fin k → Fin d → ℝ) :=
  ((MeasurableEquiv.piCongrLeft (fun _ : Fin (k * d) ↦ ℝ)
    (finProdFinEquiv : Fin k × Fin d ≃ Fin (k * d))).symm).trans
      (MeasurableEquiv.curry (Fin k) (Fin d) ℝ)

@[simp] theorem flatToGaussianRows_apply (k d : ℕ) (z : Fin (k * d) → ℝ)
    (c : Fin k) (a : Fin d) :
    flatToGaussianRows k d z c a = z (finProdFinEquiv (c, a)) := rfl

/-- Flattening transports the entire iid Gaussian law, not only its moments. -/
theorem map_flatToGaussianRows (k d : ℕ) :
    (standardGaussianVector (k * d)).map (flatToGaussianRows k d) =
      standardGaussianRows k d := by
  let reindex : (Fin (k * d) → ℝ) ≃ᵐ (Fin k × Fin d → ℝ) :=
    (MeasurableEquiv.piCongrLeft (fun _ : Fin (k * d) ↦ ℝ)
      (finProdFinEquiv : Fin k × Fin d ≃ Fin (k * d))).symm
  let curry : (Fin k × Fin d → ℝ) ≃ᵐ (Fin k → Fin d → ℝ) :=
    MeasurableEquiv.curry (Fin k) (Fin d) ℝ
  have hindex : MeasurePreserving reindex (standardGaussianVector (k * d))
      (Measure.pi fun _ : Fin k × Fin d ↦ gaussianReal 0 1) := by
    simpa only [standardGaussianVector] using
      (measurePreserving_piCongrLeft
        (fun _ : Fin (k * d) ↦ gaussianReal 0 1)
        (finProdFinEquiv : Fin k × Fin d ≃ Fin (k * d))).symm
  have hcurry : MeasurePreserving curry
      (Measure.pi fun _ : Fin k × Fin d ↦ gaussianReal 0 1)
      (standardGaussianRows k d) := by
    refine ⟨curry.measurable, ?_⟩
    unfold standardGaussianRows standardGaussianVector
    rw [← Measure.infinitePi_eq_pi, ← Measure.infinitePi_eq_pi]
    simp_rw [← Measure.infinitePi_eq_pi]
    exact Measure.infinitePi_map_curry
      (fun _ : Fin k ↦ fun _ : Fin d ↦ gaussianReal 0 1)
  exact (hcurry.comp hindex).map_eq

def flatGaussianWishartGram {k d : ℕ} (sigma : MatsumotoPaper.SymPosDef d)
    (z : Fin (k * d) → ℝ) : MatsumotoPaper.RealMatrix d :=
  gaussianWishartGram sigma (flatToGaussianRows k d z)

theorem measurable_flatGaussianWishartGram {k d : ℕ}
    (sigma : MatsumotoPaper.SymPosDef d) :
    Measurable (flatGaussianWishartGram (k := k) sigma) :=
  (measurable_gaussianWishartGram sigma).comp (flatToGaussianRows k d).measurable

theorem gaussianWishartLaw_eq_flat_map (k : ℕ) {d : ℕ}
    (sigma : MatsumotoPaper.SymPosDef d) :
    gaussianWishartLaw k sigma =
      (standardGaussianVector (k * d)).map (flatGaussianWishartGram sigma) := by
  rw [gaussianWishartLaw, ← map_flatToGaussianRows k d,
    Measure.map_map (measurable_gaussianWishartGram sigma)
      (flatToGaussianRows k d).measurable]
  rfl

/-- Entrywise Gram evaluation after a deterministic covariance factor. -/
theorem scaledStandardGaussianGram_entry {k d : ℕ}
    (A : MatsumotoPaper.RealMatrix d) (z : Fin k → Fin d → ℝ) (i j : Fin d) :
    scaledStandardGaussianGram A z i j =
      (∑ c : Fin k, (A *ᵥ z c) i * (A *ᵥ z c) j) / 2 := by
  change (∑ b : Fin d, (∑ a : Fin d,
    A i a * standardGaussianGram z a b) * Aᴴ b j) = _
  simp only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_apply,
    standardGaussianGram, Matrix.of_apply, Matrix.mulVec, dotProduct, Finset.sum_mul,
    Finset.mul_sum, Finset.sum_div, mul_div_assoc, div_mul_eq_mul_div]
  calc
    _ = ∑ b : Fin d, ∑ c : Fin k, ∑ a : Fin d,
        A i a * (z c a * (z c b / 2)) * A j b := by
      apply Finset.sum_congr rfl
      intro b _
      exact Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
        (f := fun (a : Fin d) (c : Fin k) ↦ A i a * (z c a * (z c b / 2)) * A j b)
    _ = ∑ c : Fin k, ∑ b : Fin d, ∑ a : Fin d,
        A i a * (z c a * (z c b / 2)) * A j b := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro a _
      ring

end A4Research
