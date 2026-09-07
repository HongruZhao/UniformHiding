import LogdetLean.GramHafnian.UltimateHiding.DenseScore.FriedmanMelloSupportFromDensity
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H6_RadialContractsConditional
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H6_RadialMeasureAdapters
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Raw Takagi--Weyl contract and proved COE adapters for H6

The primitive scientific boundary in this file is a flat-measure pushforward:
the squared Takagi coordinates of a complex symmetric matrix have density
`|Delta(lambda)|` on the positive orthant, up to one positive finite orbit
constant.  It contains no determinant weight, no H5 statement, no Wishart
law, and no H6 endpoint.

Everything surrounding that boundary is proved here: the literal coordinate
volume is rewritten as a matrix-space density, the determinant and matrix-ball
support are computed in Takagi coordinates, the Friedman--Mello weight is
pushed to the exact Jacobi radial density, and the unknown orbit constant is
cancelled by canonical normalization.  The resulting theorem constructs the
older normalized `COETakagiWeylRadialContract`.
-/

open scoped BigOperators ENNReal ComplexConjugate ComplexOrder MatrixOrder
open Set MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open H6CoordinateAlgebra H6DensityTransform H6VectorChangeOfVariables
open H6RadialMeasureAdapters

/-- Flat measure on the embedded space of complex symmetric matrices, using
exactly the independent upper-triangular coordinate convention of H5. -/
def complexSymmetricMatrixVolume (N : ℕ) : Measure (ConcreteMatrixState N) :=
  Measure.map (complexSymmetricMatrixOfCoordinates (N := N))
    (complexSymmetricCoordinateVolume N)

/-- The literal Friedman--Mello weight regarded as a function on matrices. -/
def coeCornerMatrixDeterminantWeight (N K : ℕ)
    (C : ConcreteMatrixState N) : ℝ≥0∞ := by
  classical
  exact if coeCornerSupport C then
      ENNReal.ofReal <|
        Real.rpow (Matrix.det (1 - C.conjTranspose * C)).re
          (coeCornerDensityExponent N K)
    else 0

/-- Flat squared-Takagi density.  Its only coordinate factor is the absolute
Vandermonde of power one; there is no `lambda_i` power. -/
def takagiFlatEigenvalueDensity (N : ℕ) (lambda : Fin N → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (vandermondeAbs N lambda)

/-- Unnormalized flat squared-Takagi radial measure on the full unordered
positive orthant. -/
def takagiFlatEigenvalueRadialMeasure (N : ℕ) : Measure (Fin N → ℝ) :=
  (volume.restrict (openPositiveOrthant N)).withDensity
    (takagiFlatEigenvalueDensity N)

/-- The non-indicated boundary product. -/
def coeTakagiBoundaryFactorDensity (N K : ℕ)
    (lambda : Fin N → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (unitBoundaryRpowProduct N
    (coeEigenvalueExponent N K) lambda)

/-- The determinant boundary factor, extended by zero outside the open unit
cube. -/
def coeTakagiBoundaryDensity (N K : ℕ)
    (lambda : Fin N → ℝ) : ℝ≥0∞ := by
  classical
  exact if lambda ∈ openUnitCube N then
      ENNReal.ofReal (unitBoundaryRpowProduct N
        (coeEigenvalueExponent N K) lambda)
    else 0

theorem measurableSet_openPositiveOrthant_h6 (N : ℕ) :
    MeasurableSet (openPositiveOrthant N) := by
  simpa [← betaPrimeCoordVector_target] using
    (betaPrimeCoordVector N).open_target.measurableSet

theorem measurableSet_openUnitCube_h6 (N : ℕ) :
    MeasurableSet (openUnitCube N) := by
  simpa [← betaPrimeCoordVector_source] using
    (betaPrimeCoordVector N).open_source.measurableSet

theorem measurable_takagiFlatEigenvalueDensity (N : ℕ) :
    Measurable (takagiFlatEigenvalueDensity N) :=
  ENNReal.continuous_ofReal.measurable.comp
    (continuous_vandermondeAbs N).measurable

theorem measurable_unitBoundaryRpowProduct_h6
    (N : ℕ) (alpha : ℝ) :
    Measurable (unitBoundaryRpowProduct N alpha) := by
  classical
  unfold unitBoundaryRpowProduct
  apply Finset.measurable_prod
  intro i _hi
  have hrpow : Measurable (fun z : ℝ ↦ Real.rpow z alpha) := by
    refine measurable_of_continuousOn_compl_singleton 0 ?_
    exact continuousOn_id.rpow_const fun z hz ↦ Or.inl hz
  exact hrpow.comp (measurable_const.sub (measurable_pi_apply i))

theorem measurable_coeTakagiBoundaryDensity (N K : ℕ) :
    Measurable (coeTakagiBoundaryDensity N K) := by
  classical
  unfold coeTakagiBoundaryDensity
  exact Measurable.ite (measurableSet_openUnitCube_h6 N)
    (ENNReal.measurable_ofReal.comp
      (measurable_unitBoundaryRpowProduct_h6 N
        (coeEigenvalueExponent N K))) measurable_const

theorem measurable_coeTakagiBoundaryFactorDensity (N K : ℕ) :
    Measurable (coeTakagiBoundaryFactorDensity N K) :=
  ENNReal.measurable_ofReal.comp
    (measurable_unitBoundaryRpowProduct_h6 N
      (coeEigenvalueExponent N K))

theorem coeTakagiBoundaryDensity_eq_indicator (N K : ℕ) :
    coeTakagiBoundaryDensity N K =
      (openUnitCube N).indicator
        (coeTakagiBoundaryFactorDensity N K) := by
  funext lambda
  by_cases h : lambda ∈ openUnitCube N <;>
    simp [coeTakagiBoundaryDensity, coeTakagiBoundaryFactorDensity, h]

theorem measurable_coeCornerMatrixDeterminantWeight (N K : ℕ) :
    Measurable (coeCornerMatrixDeterminantWeight N K) := by
  classical
  unfold coeCornerMatrixDeterminantWeight
  apply Measurable.ite (measurableSet_coeCornerSupport N)
  · have hdetMatrix : Measurable
        (fun A : ConcreteMatrixState N ↦ A.det) := by
      simp only [Matrix.det_apply']
      fun_prop
    have hdet : Measurable (fun C : ConcreteMatrixState N ↦
        (Matrix.det (1 - C.conjTranspose * C)).re) :=
      Complex.measurable_re.comp
        (hdetMatrix.comp (measurable_coeCornerDenominator N))
    have hrpow : Measurable (fun z : ℝ ↦
        Real.rpow z (coeCornerDensityExponent N K)) := by
      refine measurable_of_continuousOn_compl_singleton 0 ?_
      exact continuousOn_id.rpow_const fun z hz ↦ Or.inl hz
    exact ENNReal.measurable_ofReal.comp (hrpow.comp hdet)
  · exact measurable_const

/-- Determinant of the Takagi complement. -/
theorem det_one_sub_h6TakagiForward_conjTranspose_mul_self
    {N : ℕ} (U : Matrix.unitaryGroup (Fin N) ℂ)
    (lambda : Fin N → ℝ) (hlambda : ∀ i, 0 ≤ lambda i) :
    Matrix.det (1 - (h6TakagiForward U lambda).conjTranspose *
        h6TakagiForward U lambda) =
      ∏ i : Fin N, (((1 - lambda i) : ℝ) : ℂ) := by
  rw [one_sub_h6TakagiForward_conjTranspose_mul_self U lambda hlambda,
    Matrix.det_mul, Matrix.det_mul, h6TakagiComplementDiagonal,
    Matrix.det_diagonal]
  have hunit : Matrix.det U.1.transpose.conjTranspose *
      Matrix.det U.1.transpose = 1 := by
    rw [← Matrix.det_mul, unitary_transpose_conjTranspose_mul,
      Matrix.det_one]
  calc
    Matrix.det U.1.transpose.conjTranspose *
          (∏ i : Fin N, (((1 - lambda i) : ℝ) : ℂ)) *
        Matrix.det U.1.transpose =
      (∏ i : Fin N, (((1 - lambda i) : ℝ) : ℂ)) *
        (Matrix.det U.1.transpose.conjTranspose *
          Matrix.det U.1.transpose) := by ring
    _ = ∏ i : Fin N, (((1 - lambda i) : ℝ) : ℂ) := by
      rw [hunit, mul_one]

/-- Matrix-ball support is exactly the upper bound `lambda_i < 1` once the
squared Takagi coordinates are nonnegative. -/
theorem coeCornerSupport_h6TakagiForward_iff
    {N : ℕ} (U : Matrix.unitaryGroup (Fin N) ℂ)
    (lambda : Fin N → ℝ) (hlambda : ∀ i, 0 ≤ lambda i) :
    coeCornerSupport (h6TakagiForward U lambda) ↔
      ∀ i, lambda i < 1 := by
  unfold coeCornerSupport
  rw [one_sub_h6TakagiForward_conjTranspose_mul_self U lambda hlambda]
  have hUt : IsUnit U.1.transpose := by
    apply (Matrix.isUnit_iff_isUnit_det U.1.transpose).mpr
    simpa only [Matrix.det_transpose] using
      Matrix.UnitaryGroup.det_isUnit U
  change (star U.1.transpose * h6TakagiComplementDiagonal lambda *
      U.1.transpose).PosDef ↔ _
  rw [Matrix.IsUnit.posDef_star_left_conjugate_iff hUt]
  simp only [h6TakagiComplementDiagonal, Matrix.posDef_diagonal_iff]
  constructor
  · intro h i
    exact sub_pos.mp (Complex.zero_lt_real.mp (h i))
  · intro h i
    exact Complex.zero_lt_real.mpr (sub_pos.mpr (h i))

/-- The literal determinant density becomes exactly the boundary product in
squared Takagi coordinates. -/
theorem coeCornerMatrixDeterminantWeight_h6TakagiForward
    {N K : ℕ} (U : Matrix.unitaryGroup (Fin N) ℂ)
    (lambda : Fin N → ℝ) (hlambda : lambda ∈ openPositiveOrthant N) :
    coeCornerMatrixDeterminantWeight N K (h6TakagiForward U lambda) =
      coeTakagiBoundaryDensity N K lambda := by
  have hnonneg : ∀ i, 0 ≤ lambda i := fun i ↦ (hlambda i).le
  have hsupp := coeCornerSupport_h6TakagiForward_iff U lambda hnonneg
  by_cases hcube : lambda ∈ openUnitCube N
  · have hs : coeCornerSupport (h6TakagiForward U lambda) :=
      hsupp.mpr (fun i ↦ (hcube i).2)
    simp only [coeCornerMatrixDeterminantWeight, coeTakagiBoundaryDensity,
      if_pos hs, if_pos hcube]
    have hdetRe :
        (Matrix.det (1 - (h6TakagiForward U lambda).conjTranspose *
          h6TakagiForward U lambda)).re =
          ∏ i : Fin N, (1 - lambda i) := by
      rw [det_one_sub_h6TakagiForward_conjTranspose_mul_self
        U lambda hnonneg]
      have hprod :
          (((∏ i : Fin N, (1 - lambda i)) : ℝ) : ℂ) =
            ∏ i : Fin N, (((1 - lambda i) : ℝ) : ℂ) := by
        norm_cast
      rw [← hprod]
      exact Complex.ofReal_re _
    rw [hdetRe]
    change ENNReal.ofReal
        (Real.rpow (∏ i : Fin N, (1 - lambda i))
          (coeEigenvalueExponent N K)) =
      ENNReal.ofReal
        (∏ i : Fin N, Real.rpow (1 - lambda i)
          (coeEigenvalueExponent N K))
    congr 1
    symm
    exact Real.finsetProd_rpow Finset.univ (fun i ↦ 1 - lambda i)
      (fun i _hi ↦ (sub_pos.mpr (hcube i).2).le)
      (coeEigenvalueExponent N K)
  · have hs : ¬coeCornerSupport (h6TakagiForward U lambda) := by
      intro hs'
      apply hcube
      intro i
      exact ⟨hlambda i, hsupp.mp hs' i⟩
    simp [coeCornerMatrixDeterminantWeight, coeTakagiBoundaryDensity,
      hs, hcube]

/-- The original coordinate-space determinant weight is literally the matrix
weight composed with the coordinate embedding. -/
theorem coeCornerDeterminantWeight_eq_matrix_comp (N K : ℕ) :
    coeCornerDeterminantWeight N K =
      coeCornerMatrixDeterminantWeight N K ∘
        complexSymmetricMatrixOfCoordinates := by
  funext x
  rfl

/-- The literal raw H5 measure is the flat symmetric-matrix volume with the
matrix determinant density. -/
theorem coeCornerRawDeterminantDensityMeasure_eq_withDensity
    (N K : ℕ) :
    coeCornerRawDeterminantDensityMeasure N K =
      (complexSymmetricMatrixVolume N).withDensity
        (coeCornerMatrixDeterminantWeight N K) := by
  unfold coeCornerRawDeterminantDensityMeasure complexSymmetricMatrixVolume
  rw [coeCornerDeterminantWeight_eq_matrix_comp]
  exact map_withDensity_comp
    (complexSymmetricCoordinateVolume N)
    (complexSymmetricMatrixOfCoordinates (N := N))
    (coeCornerMatrixDeterminantWeight N K)
    (measurable_complexSymmetricMatrixOfCoordinates N)
    (measurable_coeCornerMatrixDeterminantWeight N K).aemeasurable

theorem openUnitCube_subset_openPositiveOrthant (N : ℕ) :
    openUnitCube N ⊆ openPositiveOrthant N := by
  intro lambda hlambda i
  exact (hlambda i).1

theorem vandermondeAbs_nonneg_h6 (N : ℕ) (lambda : Fin N → ℝ) :
    0 ≤ vandermondeAbs N lambda := by
  classical
  unfold vandermondeAbs
  positivity

theorem takagiFlatDensity_mul_boundaryFactor (N K : ℕ) :
    takagiFlatEigenvalueDensity N *
        coeTakagiBoundaryFactorDensity N K =
      coeEigenvalueDensity N K := by
  funext lambda
  unfold takagiFlatEigenvalueDensity coeTakagiBoundaryFactorDensity
    coeEigenvalueDensity coeEigenvalueWeight
  rw [ENNReal.ofReal_mul (vandermondeAbs_nonneg_h6 N lambda)]
  rfl

/-- Weighting the flat Takagi radial measure by the determinant boundary
factor gives exactly the existing unnormalized COE radial measure. -/
theorem takagiFlatRadial_withDensity_boundary_eq_coeRadial
    (N K : ℕ) :
    (takagiFlatEigenvalueRadialMeasure N).withDensity
        (coeTakagiBoundaryDensity N K) =
      coeEigenvalueRadialMeasure N K := by
  unfold takagiFlatEigenvalueRadialMeasure coeEigenvalueRadialMeasure
  rw [coeTakagiBoundaryDensity_eq_indicator]
  rw [withDensity_indicator (measurableSet_openUnitCube_h6 N)]
  rw [restrict_withDensity (measurableSet_openUnitCube_h6 N)]
  rw [Measure.restrict_restrict_of_subset
    (openUnitCube_subset_openPositiveOrthant N)]
  rw [← withDensity_mul
    (volume.restrict (openUnitCube N))
    (measurable_takagiFlatEigenvalueDensity N)
    (measurable_coeTakagiBoundaryFactorDensity N K)]
  rw [takagiFlatDensity_mul_boundaryFactor]

/-! ## Primitive flat Takagi--Weyl contract -/

/-- **CONDITIONAL primitive Takagi--Weyl contract.**  This is the isolated
coarea/Jacobian theorem still missing from the project.  The right side is
flat Lebesgue measure on squared Takagi coordinates with Vandermonde power
one and no coordinate power, up to a positive finite orbit constant.

The contract is independent of `K`, the determinant density, H5, Wishart
matrices, trace vectors, and H6. -/
structure TakagiWeylFlatContract (N : ℕ) where
  spectrum : ConcreteMatrixState N → (Fin N → ℝ)
  measurable_spectrum : Measurable spectrum
  unitary : ConcreteMatrixState N → Matrix.unitaryGroup (Fin N) ℂ
  representation : ∀ᵐ C ∂complexSymmetricMatrixVolume N,
    C = h6TakagiForward (unitary C) (spectrum C)
  orbitConstant : NNReal
  orbitConstant_ne_zero : orbitConstant ≠ 0
  flat_radial_law :
    Measure.map spectrum (complexSymmetricMatrixVolume N) =
      (orbitConstant : ℝ≥0∞) • takagiFlatEigenvalueRadialMeasure N

theorem takagiFlatEigenvalueRadialMeasure_ae_positive (N : ℕ) :
    ∀ᵐ lambda ∂takagiFlatEigenvalueRadialMeasure N,
      lambda ∈ openPositiveOrthant N := by
  unfold takagiFlatEigenvalueRadialMeasure
  exact withDensity_restrict_ae_mem volume (openPositiveOrthant N)
    (takagiFlatEigenvalueDensity N)
    (measurableSet_openPositiveOrthant_h6 N)

theorem TakagiWeylFlatContract.spectrum_ae_positive
    {N : ℕ} (h : TakagiWeylFlatContract N) :
    ∀ᵐ C ∂complexSymmetricMatrixVolume N,
      h.spectrum C ∈ openPositiveOrthant N := by
  have htarget' :
      ∀ᵐ lambda ∂(h.orbitConstant : ℝ≥0∞) •
          takagiFlatEigenvalueRadialMeasure N,
        lambda ∈ openPositiveOrthant N :=
    Measure.smul_absolutelyContinuous.ae_le
      (takagiFlatEigenvalueRadialMeasure_ae_positive N)
  have htarget :
      ∀ᵐ lambda ∂Measure.map h.spectrum
          (complexSymmetricMatrixVolume N),
        lambda ∈ openPositiveOrthant N :=
    h.flat_radial_law.symm ▸ htarget'
  exact (ae_map_iff h.measurable_spectrum.aemeasurable
    (measurableSet_openPositiveOrthant_h6 N)).mp htarget

theorem TakagiWeylFlatContract.matrixWeight_ae_eq_boundary_comp
    {N : ℕ} (h : TakagiWeylFlatContract N) (K : ℕ) :
    coeCornerMatrixDeterminantWeight N K =ᵐ[
      complexSymmetricMatrixVolume N]
      coeTakagiBoundaryDensity N K ∘ h.spectrum := by
  filter_upwards [h.representation, h.spectrum_ae_positive] with C hrep hpos
  calc
    coeCornerMatrixDeterminantWeight N K C =
        coeCornerMatrixDeterminantWeight N K
          (h6TakagiForward (h.unitary C) (h.spectrum C)) :=
      congrArg (coeCornerMatrixDeterminantWeight N K) hrep
    _ = (coeTakagiBoundaryDensity N K ∘ h.spectrum) C :=
      coeCornerMatrixDeterminantWeight_h6TakagiForward
        (h.unitary C) (h.spectrum C) hpos

/-- The flat Takagi Jacobian plus proved density algebra yields the exact raw
Friedman--Mello radial pushforward, retaining only the same harmless orbit
constant. -/
theorem TakagiWeylFlatContract.raw_coe_radial_law
    {N : ℕ} (h : TakagiWeylFlatContract N) (K : ℕ) :
    Measure.map h.spectrum
        (coeCornerRawDeterminantDensityMeasure N K) =
      (h.orbitConstant : ℝ≥0∞) • coeEigenvalueRadialMeasure N K := by
  calc
    Measure.map h.spectrum
        (coeCornerRawDeterminantDensityMeasure N K) =
      Measure.map h.spectrum
        ((complexSymmetricMatrixVolume N).withDensity
          (coeCornerMatrixDeterminantWeight N K)) := by
      rw [coeCornerRawDeterminantDensityMeasure_eq_withDensity]
    _ = Measure.map h.spectrum
        ((complexSymmetricMatrixVolume N).withDensity
          (coeTakagiBoundaryDensity N K ∘ h.spectrum)) := by
      congr 1
      exact withDensity_congr_ae
        (h.matrixWeight_ae_eq_boundary_comp K)
    _ = (Measure.map h.spectrum (complexSymmetricMatrixVolume N)).withDensity
        (coeTakagiBoundaryDensity N K) :=
      map_withDensity_comp (complexSymmetricMatrixVolume N) h.spectrum
        (coeTakagiBoundaryDensity N K) h.measurable_spectrum
        (measurable_coeTakagiBoundaryDensity N K).aemeasurable
    _ = ((h.orbitConstant : ℝ≥0∞) •
          takagiFlatEigenvalueRadialMeasure N).withDensity
        (coeTakagiBoundaryDensity N K) := by rw [h.flat_radial_law]
    _ = (h.orbitConstant : ℝ≥0∞) •
        ((takagiFlatEigenvalueRadialMeasure N).withDensity
          (coeTakagiBoundaryDensity N K)) := by
      rw [withDensity_smul_measure]
    _ = (h.orbitConstant : ℝ≥0∞) •
        coeEigenvalueRadialMeasure N K := by
      rw [takagiFlatRadial_withDensity_boundary_eq_coeRadial]

theorem TakagiWeylFlatContract.representation_raw
    {N : ℕ} (h : TakagiWeylFlatContract N) (K : ℕ) :
    ∀ᵐ C ∂coeCornerRawDeterminantDensityMeasure N K,
      C = h6TakagiForward (h.unitary C) (h.spectrum C) := by
  rw [coeCornerRawDeterminantDensityMeasure_eq_withDensity]
  exact (withDensity_absolutelyContinuous
    (complexSymmetricMatrixVolume N)
    (coeCornerMatrixDeterminantWeight N K)).ae_le h.representation

theorem TakagiWeylFlatContract.representation_probability
    {N : ℕ} (h : TakagiWeylFlatContract N) (K : ℕ) :
    ∀ᵐ C ∂coeCornerDeterminantDensityProbabilityMeasure N K,
      C = h6TakagiForward (h.unitary C) (h.spectrum C) := by
  unfold coeCornerDeterminantDensityProbabilityMeasure
  exact Measure.smul_absolutelyContinuous.ae_le (h.representation_raw K)

/-- The positive finite orbit constant cancels exactly. -/
theorem TakagiWeylFlatContract.normalized_coe_radial_law
    {N : ℕ} (h : TakagiWeylFlatContract N) (K : ℕ) :
    Measure.map h.spectrum
        (coeCornerDeterminantDensityProbabilityMeasure N K) =
      normalizedCOEEigenvalueRadialMeasure N K := by
  have hnorm := map_normalizeMeasure_of_map_eq_nnreal_smul
    (coeCornerRawDeterminantDensityMeasure N K)
    (coeEigenvalueRadialMeasure N K) h.spectrum h.orbitConstant
    h.measurable_spectrum h.orbitConstant_ne_zero (h.raw_coe_radial_law K)
  simpa [normalizeMeasure, coeCornerDeterminantDensityProbabilityMeasure,
    normalizedCOEEigenvalueRadialMeasure] using hnorm

theorem normalizedCOEEigenvalueRadialMeasure_ae_openUnitCube
    (N K : ℕ) :
    ∀ᵐ lambda ∂normalizedCOEEigenvalueRadialMeasure N K,
      lambda ∈ openUnitCube N := by
  have hraw : ∀ᵐ lambda ∂coeEigenvalueRadialMeasure N K,
      lambda ∈ openUnitCube N := by
    unfold coeEigenvalueRadialMeasure
    exact withDensity_restrict_ae_mem volume (openUnitCube N)
      (coeEigenvalueDensity N K) (measurableSet_openUnitCube_h6 N)
  simpa [normalizeMeasure, normalizedCOEEigenvalueRadialMeasure] using
    (normalizeMeasure_ae_of_ae hraw)

/-- Fully proved adapter from the primitive flat Takagi--Weyl theorem to the
previous normalized COE radial contract consumed by the H6 reduction. -/
def TakagiWeylFlatContract.toCOETakagiWeylRadialContract
    {N : ℕ} (h : TakagiWeylFlatContract N) (K : ℕ) :
    COETakagiWeylRadialContract N K where
  spectrum := h.spectrum
  measurable_spectrum := h.measurable_spectrum
  unitary := h.unitary
  support := by
    have htarget :
        ∀ᵐ lambda ∂Measure.map h.spectrum
            (coeCornerDeterminantDensityProbabilityMeasure N K),
          lambda ∈ openUnitCube N :=
      (h.normalized_coe_radial_law K).symm ▸
        normalizedCOEEigenvalueRadialMeasure_ae_openUnitCube N K
    exact (ae_map_iff h.measurable_spectrum.aemeasurable
      (measurableSet_openUnitCube_h6 N)).mp htarget
  representation := h.representation_probability K
  radial_law := h.normalized_coe_radial_law K

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
