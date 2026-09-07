import LogdetLean.GramHafnian.UltimateHiding.Basic

/-!
# Normalized product matrix statement

The code base stores the laws of `M U Uᵀ` and `G Gᵀ`.  The proof note
prints both matrices after the common deterministic factor `1 / sqrt K`.
This file verifies that literal paper normalization by total variation data
processing.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding

noncomputable section

open LocalAnticoncentration

/-- Common deterministic normalization used in the matrix theorem. -/
def normalizeTransposeGram (N K : ℕ) :
    Matrix (Fin N) (Fin N) ℂ -> Matrix (Fin N) (Fin N) ℂ :=
  fun A => (((Real.sqrt (K : ℝ))⁻¹ : ℝ) : ℂ) • A

theorem measurable_normalizeTransposeGram (N K : ℕ) :
    Measurable (normalizeTransposeGram N K) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  change Measurable fun A : Matrix (Fin N) (Fin N) ℂ =>
    (((Real.sqrt (K : ℝ))⁻¹ : ℝ) : ℂ) * A i j
  have hi : Measurable
      (fun A : Matrix (Fin N) (Fin N) ℂ => A i) := measurable_pi_apply i
  have hj : Measurable (fun row : Fin N -> ℂ => row j) :=
    measurable_pi_apply j
  exact (hj.comp hi).const_mul _

/-- Inverse deterministic scaling, valid as an inverse when `K` is
positive. -/
def denormalizeTransposeGram (N K : ℕ) :
    Matrix (Fin N) (Fin N) ℂ -> Matrix (Fin N) (Fin N) ℂ :=
  fun A => ((Real.sqrt (K : ℝ) : ℝ) : ℂ) • A

theorem measurable_denormalizeTransposeGram (N K : ℕ) :
    Measurable (denormalizeTransposeGram N K) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  change Measurable fun A : Matrix (Fin N) (Fin N) ℂ =>
    ((Real.sqrt (K : ℝ) : ℝ) : ℂ) * A i j
  have hi : Measurable
      (fun A : Matrix (Fin N) (Fin N) ℂ => A i) := measurable_pi_apply i
  have hj : Measurable (fun row : Fin N -> ℂ => row j) :=
    measurable_pi_apply j
  exact (hj.comp hi).const_mul _

theorem denormalize_normalizeTransposeGram
    (N : ℕ) {K : ℕ} (hK : 1 <= K)
    (A : Matrix (Fin N) (Fin N) ℂ) :
    denormalizeTransposeGram N K (normalizeTransposeGram N K A) = A := by
  have hsqrt : Real.sqrt (K : ℝ) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast hK))
  ext i j
  simp [denormalizeTransposeGram, normalizeTransposeGram, hsqrt]

/-- Law of `(M/sqrt K) U Uᵀ`. -/
def normalizedHaarTransposeGramLaw
    (H : UnitaryHaarProbabilityFamily) (M N K : ℕ) :
    Measure (Matrix (Fin N) (Fin N) ℂ) :=
  Measure.map (normalizeTransposeGram N K)
    (scaledHaarTransposeGramLaw H M N K)

/-- Law of `(1/sqrt K) G Gᵀ`. -/
def normalizedGaussianTransposeGramLaw (N K : ℕ) :
    Measure (Matrix (Fin N) (Fin N) ℂ) :=
  Measure.map (normalizeTransposeGram N K)
    (gaussianTransposeGramLaw N K)

/-- The unnormalized hiding estimate implies the exact normalized statement
printed in the proof note, with the identical error. -/
theorem normalizedProductMatrixHiding_of_unnormalized
    {C : ℝ} (hhide : UniformProductMatrixHidingAt C)
    (H : UnitaryHaarProbabilityFamily) {M N K : ℕ}
    (hN : 1 <= N) (hNK : N <= K) (hKM : K <= M) :
    probabilityTotalVariationLE
      (normalizedHaarTransposeGramLaw H M N K)
      (normalizedGaussianTransposeGramLaw N K)
      (min 1 (C * ultimateHidingRate M N)) := by
  unfold normalizedHaarTransposeGramLaw normalizedGaussianTransposeGramLaw
  exact (hhide.apply H hN hNK hKM).map
    (measurable_normalizeTransposeGram N K)

/-- Because `K >= 1`, the common normalization is invertible.  Thus a bound
for the printed normalized laws also gives the stored unnormalized law bound. -/
theorem unnormalizedProductMatrixHiding_of_normalized
    (H : UnitaryHaarProbabilityFamily) {M N K : ℕ}
    (hK : 1 <= K) {delta : ℝ}
    (h : probabilityTotalVariationLE
      (normalizedHaarTransposeGramLaw H M N K)
      (normalizedGaussianTransposeGramLaw N K) delta) :
    probabilityTotalVariationLE
      (scaledHaarTransposeGramLaw H M N K)
      (gaussianTransposeGramLaw N K) delta := by
  have hmap := h.map (measurable_denormalizeTransposeGram N K)
  unfold normalizedHaarTransposeGramLaw normalizedGaussianTransposeGramLaw at hmap
  rw [Measure.map_map (measurable_denormalizeTransposeGram N K)
      (measurable_normalizeTransposeGram N K),
    Measure.map_map (measurable_denormalizeTransposeGram N K)
      (measurable_normalizeTransposeGram N K)] at hmap
  have hcomp : denormalizeTransposeGram N K ∘ normalizeTransposeGram N K = id := by
    funext A
    exact denormalize_normalizeTransposeGram N hK A
  simpa [hcomp] using hmap

end

end LogdetLean.GramHafnian.UltimateHiding
