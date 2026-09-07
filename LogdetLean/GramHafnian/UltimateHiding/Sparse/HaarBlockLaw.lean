import LogdetLean.GramHafnian.UltimateHiding.HaarGaussianMatrixLaws
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Mathlib.Topology.Bases

/-!
# Rectangular Haar block laws and the transpose Gram statistic

This file supplies the measure theoretic bridge needed by the finite sparse
comparison.  It defines the law of the literal block `sqrt M U_{N,K}` and
proves that applying `X |-> X X^T` gives exactly the already formalized law of
`M U_{N,K} U_{N,K}^T`.  Thus any block level total variation or KL estimate
passes to the product matrix with no normalization or orientation gap.
-/

open MeasureTheory TopologicalSpace

namespace LogdetLean.GramHafnian.UltimateHiding.Sparse

noncomputable section

open CurrentPRL

local instance matrixBorelSpace (N K : ℕ) :
    BorelSpace (Matrix (Fin N) (Fin K) ℂ) := by
  exact inferInstanceAs (BorelSpace (Fin N → Fin K → ℂ))

local instance matrixSecondCountableTopology (N K : ℕ) :
    SecondCountableTopology (Matrix (Fin N) (Fin K) ℂ) := by
  exact inferInstanceAs (SecondCountableTopology (Fin N → Fin K → ℂ))

local instance unitaryGroupCompactSpace (M : ℕ) :
    CompactSpace (Matrix.unitaryGroup (Fin M) ℂ) :=
  isCompact_iff_compactSpace.mp (unitaryGroup_carrier_isCompact M)

local instance unitaryGroupSecondCountableTopology (M : ℕ) :
    SecondCountableTopology (Matrix.unitaryGroup (Fin M) ℂ) := by
  exact TopologicalSpace.secondCountableTopology_induced
    (Matrix.unitaryGroup (Fin M) ℂ)
    (Matrix (Fin M) (Fin M) ℂ) Subtype.val

/-- A normalized Haar family has the canonical normalized Haar law.  This
removes the family parameter from the genuinely analytic block density task. -/
theorem normalizedUnitaryHaarLaw_eq_canonical
    (H : UnitaryHaarProbabilityFamily) (M : ℕ) :
    H.law M = unitaryHaarProbabilityMeasure M := by
  letI : IsProbabilityMeasure (H.law M) := H.isProbability M
  letI : Measure.IsHaarMeasure (H.law M) := H.isHaar M
  have h := Measure.haarMeasure_unique (H.law M)
    (⊤ : PositiveCompacts (Matrix.unitaryGroup (Fin M) ℂ))
  simpa [unitaryHaarProbabilityMeasure] using h

/-- The literal scaled upper left block `sqrt M U_{N,K}`. -/
def sqrtScaledHaarBlockMatrix {M N K : ℕ}
    (hNM : N ≤ M) (hKM : K ≤ M)
    (U : Matrix.unitaryGroup (Fin M) ℂ) : Matrix (Fin N) (Fin K) ℂ :=
  fun i j => ((Real.sqrt (M : ℝ) : ℝ) : ℂ) *
    topLeftUnitaryBlock hNM hKM U i j

@[fun_prop]
theorem measurable_sqrtScaledHaarBlockMatrix {M N K : ℕ}
    (hNM : N ≤ M) (hKM : K ≤ M) :
    Measurable (sqrtScaledHaarBlockMatrix hNM hKM) := by
  unfold sqrtScaledHaarBlockMatrix
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  exact measurable_const.mul
    ((measurable_pi_apply j).comp
      ((measurable_pi_apply i).comp
        (measurable_topLeftUnitaryBlock hNM hKM)))

/-- Law of the scaled rectangular corner `sqrt M U_{N,K}`.  As in the
existing product law, invalid dimensions are completed by the zero measure so
that this is a total definition. -/
def sqrtScaledHaarBlockLaw
    (H : UnitaryHaarProbabilityFamily) (M N K : ℕ) :
    Measure (Matrix (Fin N) (Fin K) ℂ) :=
  if h : N ≤ M ∧ K ≤ M then
    Measure.map (sqrtScaledHaarBlockMatrix h.1 h.2) (H.law M)
  else 0

/-- The scaled block law is independent of the chosen presentation of
normalized Haar probability.  Hence the remaining density calculation may be
stated only for the canonical Haar probability measure. -/
theorem sqrtScaledHaarBlockLaw_eq_canonical
    (H : UnitaryHaarProbabilityFamily) (M N K : ℕ) :
    sqrtScaledHaarBlockLaw H M N K =
      sqrtScaledHaarBlockLaw canonicalUnitaryHaarProbabilityFamily M N K := by
  unfold sqrtScaledHaarBlockLaw
  split_ifs with h
  · rw [normalizedUnitaryHaarLaw_eq_canonical H M]
    rfl
  · rfl

theorem sqrtScaledHaarBlockLaw_isProbability
    (H : UnitaryHaarProbabilityFamily) {M N K : ℕ}
    (hNM : N ≤ M) (hKM : K ≤ M) :
    IsProbabilityMeasure (sqrtScaledHaarBlockLaw H M N K) := by
  rw [sqrtScaledHaarBlockLaw, dif_pos ⟨hNM, hKM⟩]
  letI : IsProbabilityMeasure (H.law M) := H.isProbability M
  exact Measure.isProbabilityMeasure_map
    (measurable_sqrtScaledHaarBlockMatrix hNM hKM).aemeasurable

/-- The Gaussian block law, named at the same semantic level as the Haar
block law. -/
abbrev standardGaussianBlockLaw (N K : ℕ) :
    Measure (Matrix (Fin N) (Fin K) ℂ) :=
  standardComplexGaussianRectangularMeasure N K

/-- Entrywise algebra: the transpose Gram statistic of `sqrt M U_{N,K}` is
exactly `M U_{N,K} U_{N,K}^T`. -/
theorem rectangularTransposeGram_sqrtScaledHaarBlockMatrix
    {M N K : ℕ} (hNM : N ≤ M) (hKM : K ≤ M)
    (U : Matrix.unitaryGroup (Fin M) ℂ) :
    rectangularTransposeGram (sqrtScaledHaarBlockMatrix hNM hKM U) =
      scaledHaarTransposeGramMatrix hNM hKM U := by
  ext i j
  have hsqrtR :
      Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) = (M : ℝ) :=
    Real.mul_self_sqrt (Nat.cast_nonneg M)
  have hsqrtC :
      ((Real.sqrt (M : ℝ) : ℝ) : ℂ) *
          ((Real.sqrt (M : ℝ) : ℝ) : ℂ) = (M : ℂ) := by
    exact_mod_cast hsqrtR
  simp only [rectangularTransposeGram, Matrix.mul_apply,
    Matrix.transpose_apply, sqrtScaledHaarBlockMatrix,
    scaledHaarTransposeGramMatrix]
  calc
    ∑ a, ((Real.sqrt (M : ℝ) : ℝ) : ℂ) *
          topLeftUnitaryBlock hNM hKM U i a *
          (((Real.sqrt (M : ℝ) : ℝ) : ℂ) *
            topLeftUnitaryBlock hNM hKM U j a) =
        ∑ a, (M : ℂ) *
          (topLeftUnitaryBlock hNM hKM U i a *
            topLeftUnitaryBlock hNM hKM U j a) := by
              apply Finset.sum_congr rfl
              intro a _
              rw [← hsqrtC]
              ring
    _ = (M : ℂ) * ∑ a,
          topLeftUnitaryBlock hNM hKM U i a *
            topLeftUnitaryBlock hNM hKM U j a := by
              rw [Finset.mul_sum]

/-- Applying the transpose Gram statistic to the scaled Haar block law gives
the existing scaled Haar transpose Gram law exactly. -/
theorem map_rectangularTransposeGram_sqrtScaledHaarBlockLaw
    (H : UnitaryHaarProbabilityFamily) {M N K : ℕ}
    (hNM : N ≤ M) (hKM : K ≤ M) :
    Measure.map rectangularTransposeGram
        (sqrtScaledHaarBlockLaw H M N K) =
      scaledHaarTransposeGramLaw H M N K := by
  rw [sqrtScaledHaarBlockLaw, dif_pos ⟨hNM, hKM⟩,
    scaledHaarTransposeGramLaw, dif_pos ⟨hNM, hKM⟩,
    Measure.map_map]
  · apply Measure.map_congr
    filter_upwards with U
    exact rectangularTransposeGram_sqrtScaledHaarBlockMatrix hNM hKM U
  · exact measurable_rectangularTransposeGram N K
  · exact measurable_sqrtScaledHaarBlockMatrix hNM hKM

/-- The already defined scaled transpose-Gram law is likewise independent of
the chosen normalized Haar family. -/
theorem scaledHaarTransposeGramLaw_eq_canonical
    (H : UnitaryHaarProbabilityFamily) (M N K : ℕ) :
    scaledHaarTransposeGramLaw H M N K =
      scaledHaarTransposeGramLaw canonicalUnitaryHaarProbabilityFamily M N K := by
  unfold scaledHaarTransposeGramLaw
  split_ifs with h
  · rw [normalizedUnitaryHaarLaw_eq_canonical H M]
    rfl
  · rfl

/-- The same statistic maps the standard Gaussian block law to the existing
Gaussian transpose Gram law. -/
theorem map_rectangularTransposeGram_standardGaussianBlockLaw
    (N K : ℕ) :
    Measure.map rectangularTransposeGram (standardGaussianBlockLaw N K) =
      gaussianTransposeGramLaw N K := by
  rfl

/-- KL data processing from the rectangular block to its complex symmetric
transpose Gram product. -/
theorem klDiv_transposeGram_le_block
    (H : UnitaryHaarProbabilityFamily) {M N K : ℕ}
    (hNM : N ≤ M) (hKM : K ≤ M) :
    InformationTheory.klDiv
        (scaledHaarTransposeGramLaw H M N K)
        (gaussianTransposeGramLaw N K) ≤
      InformationTheory.klDiv
        (sqrtScaledHaarBlockLaw H M N K)
        (standardGaussianBlockLaw N K) := by
  letI : IsProbabilityMeasure (sqrtScaledHaarBlockLaw H M N K) :=
    sqrtScaledHaarBlockLaw_isProbability H hNM hKM
  letI : IsProbabilityMeasure (standardGaussianBlockLaw N K) :=
    standardComplexGaussianRectangularMeasure_isProbability N K
  rw [← map_rectangularTransposeGram_sqrtScaledHaarBlockLaw H hNM hKM,
    ← map_rectangularTransposeGram_standardGaussianBlockLaw N K]
  exact InformationTheory.klDiv_map_le _ _
    (measurable_rectangularTransposeGram N K)

end

end LogdetLean.GramHafnian.UltimateHiding.Sparse
