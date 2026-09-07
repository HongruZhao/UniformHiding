import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ClassicalCOEExternal
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H5_FriedmanMelloA1Adapter
import Mathlib.Analysis.Matrix.Order

/-!
# COE-corner support from the literal Friedman--Mello density

This file removes the former separate almost-sure support assumption.  It
proves measurability of the complex-matrix positive-definite locus by writing
it as the intersection of the closed nonnegative cone and the open unit
locus.  The determinant-density weight is then measurable and vanishes off
the matrix ball by definition.  Standard `withDensity`, `Measure.map`, and
scalar-normalization lemmas transport that pointwise fact to the scaled COE
corner law.

The only scientific input in the final support theorem is the already-stated
exact Friedman--Mello determinant-density equality.
-/

open scoped ENNReal BigOperators ComplexConjugate ComplexOrder
open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

open scoped MatrixOrder Matrix.Norms.L2Operator in
theorem measurableSet_concreteMatrix_posDef (N : ℕ) :
    MeasurableSet {A : ConcreteMatrixState N | A.PosDef} := by
  classical
  letI : OpensMeasurableSpace (ConcreteMatrixState N) :=
    Pi.opensMeasurableSpace
  have hset :
      {A : ConcreteMatrixState N | A.PosDef} =
        {A : ConcreteMatrixState N | 0 ≤ A} ∩
          {A : ConcreteMatrixState N | IsUnit A} := by
    ext A
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
    rw [← Matrix.isStrictlyPositive_iff_posDef]
    exact IsStrictlyPositive.iff_of_unital
  rw [hset]
  have hclosed : IsClosed {A : ConcreteMatrixState N | 0 ≤ A} :=
    CStarAlgebra.isClosed_nonneg
  have hopen : IsOpen {A : ConcreteMatrixState N | IsUnit A} :=
    Units.isOpen
  exact hclosed.measurableSet.inter hopen.measurableSet

theorem measurable_coeCornerDenominator (N : ℕ) :
    Measurable (fun C : ConcreteMatrixState N ↦
      1 - C.conjTranspose * C) := by
  have hstar : Measurable (fun C : ConcreteMatrixState N ↦
      C.conjTranspose) := by
    refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
    simp only [Matrix.conjTranspose_apply]
    fun_prop
  have hprod : Measurable (fun C : ConcreteMatrixState N ↦
      C.conjTranspose * C) :=
    measurable_complexMatrix_mul hstar measurable_id
  refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
  exact measurable_const.sub
    ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hprod))

theorem measurableSet_coeCornerSupport (N : ℕ) :
    MeasurableSet {C : ConcreteMatrixState N | coeCornerSupport C} :=
  (measurableSet_concreteMatrix_posDef N).preimage
    (measurable_coeCornerDenominator N)

private theorem measurable_complexMatrix_det_for_support (N : ℕ) :
    Measurable (fun A : ConcreteMatrixState N ↦ A.det) := by
  simp only [Matrix.det_apply']
  fun_prop

theorem measurable_coeCornerDeterminantWeight (N K : ℕ) :
    Measurable (coeCornerDeterminantWeight N K) := by
  classical
  unfold coeCornerDeterminantWeight
  dsimp only
  apply Measurable.ite
  · exact (measurableSet_coeCornerSupport N).preimage
      (measurable_complexSymmetricMatrixOfCoordinates N)
  · have hden : Measurable (fun x : ComplexSymmetricCoordinates N ↦
        1 - (complexSymmetricMatrixOfCoordinates x).conjTranspose *
          complexSymmetricMatrixOfCoordinates x) :=
      (measurable_coeCornerDenominator N).comp
        (measurable_complexSymmetricMatrixOfCoordinates N)
    have hdetComplex : Measurable (fun x : ComplexSymmetricCoordinates N ↦
        Matrix.det
          (1 - (complexSymmetricMatrixOfCoordinates x).conjTranspose *
            complexSymmetricMatrixOfCoordinates x)) :=
      (measurable_complexMatrix_det_for_support N).comp hden
    have hdet : Measurable (fun x : ComplexSymmetricCoordinates N ↦
        (Matrix.det
          (1 - (complexSymmetricMatrixOfCoordinates x).conjTranspose *
            complexSymmetricMatrixOfCoordinates x)).re) := by
      fun_prop
    have hrpow : Measurable (fun z : ℝ ↦
        Real.rpow z (coeCornerDensityExponent N K)) := by
      refine measurable_of_continuousOn_compl_singleton 0 ?_
      exact continuousOn_id.rpow_const fun z hz ↦ Or.inl hz
    exact ENNReal.measurable_ofReal.comp (hrpow.comp hdet)
  · exact measurable_const

theorem measurableSet_concreteMatrix_isSymm (N : ℕ) :
    MeasurableSet {A : ConcreteMatrixState N | A.IsSymm} := by
  rw [show {A : ConcreteMatrixState N | A.IsSymm} =
      {A : ConcreteMatrixState N | ∀ i j, A j i = A i j} by
    ext A
    simp only [Set.mem_ofPred_eq, Matrix.IsSymm]
    constructor
    · intro h i j
      simpa only [Matrix.transpose_apply] using congrFun (congrFun h i) j
    · intro h
      ext i j
      simpa only [Matrix.transpose_apply] using h i j]
  rw [← Set.iInter_ofPred]
  apply MeasurableSet.iInter
  intro i
  rw [← Set.iInter_ofPred]
  apply MeasurableSet.iInter
  intro j
  ·
    have hji : Measurable (fun A : ConcreteMatrixState N ↦ A j i) :=
      (measurable_pi_apply i).comp (measurable_pi_apply j)
    have hij : Measurable (fun A : ConcreteMatrixState N ↦ A i j) :=
      (measurable_pi_apply j).comp (measurable_pi_apply i)
    exact measurableSet_eq_fun hji hij

theorem coeCornerDensityCoordinates_ae_support (N K : ℕ) :
    ∀ᵐ x ∂((complexSymmetricCoordinateVolume N).withDensity
        (coeCornerDeterminantWeight N K)),
      coeCornerSupport (complexSymmetricMatrixOfCoordinates x) := by
  refine (ae_withDensity_iff
    (measurable_coeCornerDeterminantWeight N K)).2 ?_
  filter_upwards [] with x
  intro hne
  by_contra hs
  simp [coeCornerDeterminantWeight, hs] at hne

theorem coeCornerRawDeterminantDensityMeasure_ae_support (N K : ℕ) :
    ∀ᵐ A ∂(coeCornerRawDeterminantDensityMeasure N K),
      A.IsSymm ∧ coeCornerSupport A := by
  let ν := (complexSymmetricCoordinateVolume N).withDensity
    (coeCornerDeterminantWeight N K)
  have hpredicate : MeasurableSet
      {A : ConcreteMatrixState N | A.IsSymm ∧ coeCornerSupport A} :=
    (measurableSet_concreteMatrix_isSymm N).inter
      (measurableSet_coeCornerSupport N)
  rw [coeCornerRawDeterminantDensityMeasure,
    ae_map_iff (measurable_complexSymmetricMatrixOfCoordinates N).aemeasurable
      hpredicate]
  filter_upwards [coeCornerDensityCoordinates_ae_support N K] with x hx
  exact ⟨complexSymmetricMatrixOfCoordinates_isSymm x, hx⟩

theorem coeCornerDeterminantDensityProbabilityMeasure_ae_support (N K : ℕ) :
    ∀ᵐ A ∂(coeCornerDeterminantDensityProbabilityMeasure N K),
      A.IsSymm ∧ coeCornerSupport A := by
  unfold coeCornerDeterminantDensityProbabilityMeasure
  exact (coeCornerRawDeterminantDensityMeasure_ae_support N K).filter_mono
    (Measure.ae_mono' Measure.smul_absolutelyContinuous)

/-- The almost-sure matrix-ball support is a formal consequence of the
literal Friedman--Mello determinant density, rather than a separate source
assumption. -/
theorem friedmanMello1985_scaledCOECorner_ae_support_from_density
    {N K : ℕ} (hN : 1 ≤ N) (h2NK : 2 * N ≤ K) :
    ∀ᵐ A ∂(concreteScaledCOECornerLaw
        LogdetLean.GramHafnian.CurrentPRL.canonicalUnitaryHaarProbabilityFamily N K),
      (unscaleCOECorner K A).IsSymm ∧
        coeCornerSupport (unscaleCOECorner K A) := by
  have hunscaled :
      ∀ᵐ C ∂(concreteUnscaledCOECornerLaw
          LogdetLean.GramHafnian.CurrentPRL.canonicalUnitaryHaarProbabilityFamily N K),
        C.IsSymm ∧ coeCornerSupport C := by
    have heq :=
      friedmanMello1985_unscaledCOECornerLaw_eq_determinantDensity_of_A1
        hN h2NK
    exact heq.symm ▸
      coeCornerDeterminantDensityProbabilityMeasure_ae_support N K
  exact ae_of_ae_map (measurable_unscaleCOECorner N K).aemeasurable hunscaled

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
