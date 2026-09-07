import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H6_TakagiWeylAdapters

/-!
# Selector-free canonical-gap reduction of the Takagi--Weyl input

This module implements the selector-free geometric reduction used by the
A2-prime production route.  It proves that the H6 COE-side reduction does not need an
Autonne--Takagi factorization or a measurable unitary selector.

The fixed statistic is the reflected ordered spectrum of the Hermitian gap
`I - Cᴴ C`.  Once its flat pushforward law is known, all determinant
weighting, normalization, support, and trace-power algebra are derived in
Lean.  Thus the remaining general-dimensional geometric obligation is only
the measurable eigenvalue pushforward/coarea formula.
-/

open scoped BigOperators ENNReal ComplexConjugate ComplexOrder MatrixOrder
open Set MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open H6CoordinateAlgebra H6DensityTransform H6VectorChangeOfVariables
open H6RadialMeasureAdapters

/-- The Hermitian right gap attached to an arbitrary complex matrix. -/
def coeHermitianGap {N : ℕ} (C : ConcreteMatrixState N) :
    ConcreteMatrixState N :=
  1 - C.conjTranspose * C

theorem coeHermitianGap_isHermitian {N : ℕ}
    (C : ConcreteMatrixState N) : (coeHermitianGap C).IsHermitian := by
  exact Matrix.isHermitian_one.sub
    (Matrix.isHermitian_conjTranspose_mul_self C)

/-- Canonical squared-singular-value statistic, without any Takagi vectors:
`lambda_i = 1 - eigenvalue_i(I - Cᴴ C)`. -/
def canonicalGapSquaredSpectrum (N : ℕ)
    (C : ConcreteMatrixState N) : Fin N → ℝ :=
  fun i ↦ 1 - (coeHermitianGap_isHermitian C).eigenvalues i

/-- The COE support is exactly the upper spectral bound.  This is pure
Hermitian spectral algebra and uses no Takagi representation. -/
theorem coeCornerSupport_iff_canonicalGapSquaredSpectrum_lt_one
    {N : ℕ} (C : ConcreteMatrixState N) :
    coeCornerSupport C ↔
      ∀ i, canonicalGapSquaredSpectrum N C i < 1 := by
  change (coeHermitianGap C).PosDef ↔ _
  rw [(coeHermitianGap_isHermitian C).posDef_iff_eigenvalues_pos]
  constructor <;> intro h i
  · simpa [canonicalGapSquaredSpectrum] using h i
  · simpa [canonicalGapSquaredSpectrum] using h i

/-- Determinant of the gap in the canonical reflected spectrum. -/
theorem det_coeHermitianGap_eq_prod_one_sub_canonicalSpectrum
    {N : ℕ} (C : ConcreteMatrixState N) :
    Matrix.det (coeHermitianGap C) =
      ∏ i : Fin N,
        (((1 - canonicalGapSquaredSpectrum N C i) : ℝ) : ℂ) := by
  rw [(coeHermitianGap_isHermitian C).det_eq_prod_eigenvalues]
  apply Finset.prod_congr rfl
  intro i _hi
  simp [canonicalGapSquaredSpectrum]

/-- On the positive spectral orthant, the literal Friedman--Mello matrix
weight is exactly the Jacobi boundary density.  No unitary selector or
Takagi factorization occurs. -/
theorem coeCornerMatrixDeterminantWeight_eq_boundary_canonicalSpectrum
    {N K : ℕ} (C : ConcreteMatrixState N)
    (hpos : canonicalGapSquaredSpectrum N C ∈ openPositiveOrthant N) :
    coeCornerMatrixDeterminantWeight N K C =
      coeTakagiBoundaryDensity N K (canonicalGapSquaredSpectrum N C) := by
  let lambda := canonicalGapSquaredSpectrum N C
  have hsupp :=
    coeCornerSupport_iff_canonicalGapSquaredSpectrum_lt_one C
  by_cases hcube : lambda ∈ openUnitCube N
  · have hcube' : canonicalGapSquaredSpectrum N C ∈ openUnitCube N := by
      simpa [lambda] using hcube
    have hs : coeCornerSupport C := hsupp.mpr (fun i ↦ (hcube i).2)
    simp only [coeCornerMatrixDeterminantWeight, coeTakagiBoundaryDensity,
      if_pos hs, if_pos hcube']
    have hdetRe :
        (Matrix.det (coeHermitianGap C)).re =
          ∏ i : Fin N, (1 - lambda i) := by
      rw [det_coeHermitianGap_eq_prod_one_sub_canonicalSpectrum C]
      have hprod :
          (((∏ i : Fin N, (1 - lambda i)) : ℝ) : ℂ) =
            ∏ i : Fin N, (((1 - lambda i) : ℝ) : ℂ) := by
        norm_cast
      rw [← hprod]
      exact Complex.ofReal_re _
    change ENNReal.ofReal
        (Real.rpow (Matrix.det (coeHermitianGap C)).re
          (coeCornerDensityExponent N K)) = _
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
  · have hs : ¬coeCornerSupport C := by
      intro hs'
      apply hcube
      intro i
      exact ⟨hpos i, hsupp.mp hs' i⟩
    have hleft : coeCornerMatrixDeterminantWeight N K C = 0 := by
      simp [coeCornerMatrixDeterminantWeight, hs]
    have hright : coeTakagiBoundaryDensity N K
        (canonicalGapSquaredSpectrum N C) = 0 := by
      simpa [lambda] using
        (show coeTakagiBoundaryDensity N K lambda = 0 by
          simp [coeTakagiBoundaryDensity, hcube])
    rw [hleft, hright]

/-! ## Nondegeneracy of the flat radial target -/

/-- One explicit point in the positive orthant with pairwise distinct
coordinates. -/
def canonicalDistinctPositivePoint (N : ℕ) : Fin N → ℝ :=
  fun i ↦ (i.1 : ℝ) + 1

theorem canonicalDistinctPositivePoint_mem_openPositiveOrthant (N : ℕ) :
    canonicalDistinctPositivePoint N ∈ openPositiveOrthant N := by
  intro i
  exact add_pos_of_nonneg_of_pos (Nat.cast_nonneg i.1) zero_lt_one

theorem vandermondeAbs_canonicalDistinctPositivePoint_pos (N : ℕ) :
    0 < vandermondeAbs N (canonicalDistinctPositivePoint N) := by
  classical
  unfold vandermondeAbs
  apply Finset.prod_pos
  intro p hp
  have hp' : p.1 < p.2 := (mem_strictPairs).mp hp
  rw [abs_pos]
  have hcast : (p.1.1 : ℝ) < (p.2.1 : ℝ) := by exact_mod_cast hp'
  simp only [canonicalDistinctPositivePoint]
  linarith

theorem isOpen_openPositiveOrthant_h6 (N : ℕ) :
    IsOpen (openPositiveOrthant N) := by
  have hrepr : openPositiveOrthant N =
      ⋂ i : Fin N, {x : Fin N → ℝ | 0 < x i} := by
    ext x
    simp [openPositiveOrthant]
  rw [hrepr]
  exact isOpen_iInter_of_finite fun i ↦
    isOpen_lt continuous_const (continuous_apply i)

/-- The target of the flat Takagi--Weyl pushforward is not the zero measure.
Consequently a nonzero flat pushforward law itself already forces
almost-everywhere measurability of the canonical spectrum. -/
theorem takagiFlatEigenvalueRadialMeasure_ne_zero (N : ℕ) :
    takagiFlatEigenvalueRadialMeasure N ≠ 0 := by
  rw [← Measure.measure_univ_ne_zero]
  unfold takagiFlatEigenvalueRadialMeasure
  rw [withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  change (∫⁻ lambda in openPositiveOrthant N,
      takagiFlatEigenvalueDensity N lambda ∂volume) ≠ 0
  rw [← pos_iff_ne_zero]
  rw [setLIntegral_pos_iff (measurable_takagiFlatEigenvalueDensity N)]
  let U := Function.support (takagiFlatEigenvalueDensity N) ∩
    openPositiveOrthant N
  have hopenDensity : IsOpen
      (Function.support (takagiFlatEigenvalueDensity N)) :=
    (ENNReal.continuous_ofReal.comp
      (continuous_vandermondeAbs N)).isOpen_support
  have hopenU : IsOpen U :=
    hopenDensity.inter (isOpen_openPositiveOrthant_h6 N)
  have hmemDensity : canonicalDistinctPositivePoint N ∈
      Function.support (takagiFlatEigenvalueDensity N) := by
    exact ENNReal.ofReal_ne_zero_iff.mpr
      (vandermondeAbs_canonicalDistinctPositivePoint_pos N)
  have hneU : U.Nonempty :=
    ⟨canonicalDistinctPositivePoint N, hmemDensity,
      canonicalDistinctPositivePoint_mem_openPositiveOrthant N⟩
  simpa only [U] using hopenU.measure_pos volume hneU

/-! ## Minimal selector-free flat Weyl contract -/

/-- The single geometric law before imposing any separate measurability
field.  Since the target measure is nonzero, this law itself forces the
canonical spectrum to be almost-everywhere measurable. -/
structure CanonicalGapWeylLawContract (N : ℕ) where
  orbitConstant : NNReal
  orbitConstant_ne_zero : orbitConstant ≠ 0
  flat_radial_law :
    Measure.map (canonicalGapSquaredSpectrum N)
        (complexSymmetricMatrixVolume N) =
      (orbitConstant : ℝ≥0∞) • takagiFlatEigenvalueRadialMeasure N

theorem CanonicalGapWeylLawContract.flat_target_ne_zero
    {N : ℕ} (h : CanonicalGapWeylLawContract N) :
    (h.orbitConstant : ℝ≥0∞) •
        takagiFlatEigenvalueRadialMeasure N ≠ 0 := by
  intro hz
  have hz' : (h.orbitConstant : ℝ≥0∞) = 0 ∨
      takagiFlatEigenvalueRadialMeasure N = 0 :=
    Measure.ennreal_smul_eq_zero.mp hz
  exact hz'.elim
    (ENNReal.coe_ne_zero.mpr h.orbitConstant_ne_zero)
    (takagiFlatEigenvalueRadialMeasure_ne_zero N)

theorem CanonicalGapWeylLawContract.map_ne_zero
    {N : ℕ} (h : CanonicalGapWeylLawContract N) :
    Measure.map (canonicalGapSquaredSpectrum N)
        (complexSymmetricMatrixVolume N) ≠ 0 := by
  rw [h.flat_radial_law]
  exact h.flat_target_ne_zero

/-- No independent measurability premise is needed at the measure-theoretic
level: a nonzero `Measure.map` equality already supplies it. -/
theorem CanonicalGapWeylLawContract.aemeasurable_spectrum
    {N : ℕ} (h : CanonicalGapWeylLawContract N) :
    AEMeasurable (canonicalGapSquaredSpectrum N)
      (complexSymmetricMatrixVolume N) :=
  AEMeasurable.of_map_ne_zero h.map_ne_zero

/-- A globally measurable representative of the canonical spectrum. -/
noncomputable def CanonicalGapWeylLawContract.measurableSpectrum
    {N : ℕ} (h : CanonicalGapWeylLawContract N) :
    ConcreteMatrixState N → (Fin N → ℝ) :=
  h.aemeasurable_spectrum.mk (canonicalGapSquaredSpectrum N)

theorem CanonicalGapWeylLawContract.measurable_measurableSpectrum
    {N : ℕ} (h : CanonicalGapWeylLawContract N) :
    Measurable h.measurableSpectrum :=
  h.aemeasurable_spectrum.measurable_mk

theorem CanonicalGapWeylLawContract.canonical_ae_eq_measurableSpectrum
    {N : ℕ} (h : CanonicalGapWeylLawContract N) :
    canonicalGapSquaredSpectrum N =ᵐ[
      complexSymmetricMatrixVolume N] h.measurableSpectrum :=
  h.aemeasurable_spectrum.ae_eq_mk

theorem CanonicalGapWeylLawContract.measurable_flat_radial_law
    {N : ℕ} (h : CanonicalGapWeylLawContract N) :
    Measure.map h.measurableSpectrum
        (complexSymmetricMatrixVolume N) =
      (h.orbitConstant : ℝ≥0∞) •
        takagiFlatEigenvalueRadialMeasure N := by
  calc
    Measure.map h.measurableSpectrum
        (complexSymmetricMatrixVolume N) =
      Measure.map (canonicalGapSquaredSpectrum N)
        (complexSymmetricMatrixVolume N) :=
      (Measure.map_congr
        h.canonical_ae_eq_measurableSpectrum).symm
    _ = (h.orbitConstant : ℝ≥0∞) •
        takagiFlatEigenvalueRadialMeasure N := h.flat_radial_law

theorem CanonicalGapWeylLawContract.measurableSpectrum_ae_positive
    {N : ℕ} (h : CanonicalGapWeylLawContract N) :
    ∀ᵐ C ∂complexSymmetricMatrixVolume N,
      h.measurableSpectrum C ∈ openPositiveOrthant N := by
  have htarget' :
      ∀ᵐ lambda ∂(h.orbitConstant : ℝ≥0∞) •
          takagiFlatEigenvalueRadialMeasure N,
        lambda ∈ openPositiveOrthant N :=
    Measure.smul_absolutelyContinuous.ae_le
      (takagiFlatEigenvalueRadialMeasure_ae_positive N)
  have htarget :
      ∀ᵐ lambda ∂Measure.map h.measurableSpectrum
          (complexSymmetricMatrixVolume N),
        lambda ∈ openPositiveOrthant N :=
    h.measurable_flat_radial_law.symm ▸ htarget'
  exact (ae_map_iff h.measurable_measurableSpectrum.aemeasurable
    (measurableSet_openPositiveOrthant_h6 N)).mp htarget

theorem CanonicalGapWeylLawContract.matrixWeight_ae_eq_boundary_comp
    {N : ℕ} (h : CanonicalGapWeylLawContract N) (K : ℕ) :
    coeCornerMatrixDeterminantWeight N K =ᵐ[
      complexSymmetricMatrixVolume N]
      coeTakagiBoundaryDensity N K ∘ h.measurableSpectrum := by
  filter_upwards [h.canonical_ae_eq_measurableSpectrum,
    h.measurableSpectrum_ae_positive] with C heq hpos
  have hcanonPos :
      canonicalGapSquaredSpectrum N C ∈ openPositiveOrthant N := by
    simpa only [heq] using hpos
  calc
    coeCornerMatrixDeterminantWeight N K C =
        coeTakagiBoundaryDensity N K
          (canonicalGapSquaredSpectrum N C) :=
      coeCornerMatrixDeterminantWeight_eq_boundary_canonicalSpectrum C hcanonPos
    _ = coeTakagiBoundaryDensity N K (h.measurableSpectrum C) := by
      rw [heq]

theorem CanonicalGapWeylLawContract.raw_coe_radial_law
    {N : ℕ} (h : CanonicalGapWeylLawContract N) (K : ℕ) :
    Measure.map h.measurableSpectrum
        (coeCornerRawDeterminantDensityMeasure N K) =
      (h.orbitConstant : ℝ≥0∞) •
        coeEigenvalueRadialMeasure N K := by
  calc
    Measure.map h.measurableSpectrum
        (coeCornerRawDeterminantDensityMeasure N K) =
      Measure.map h.measurableSpectrum
        ((complexSymmetricMatrixVolume N).withDensity
          (coeCornerMatrixDeterminantWeight N K)) := by
      rw [coeCornerRawDeterminantDensityMeasure_eq_withDensity]
    _ = Measure.map h.measurableSpectrum
        ((complexSymmetricMatrixVolume N).withDensity
          (coeTakagiBoundaryDensity N K ∘ h.measurableSpectrum)) := by
      congr 1
      exact withDensity_congr_ae
        (h.matrixWeight_ae_eq_boundary_comp K)
    _ = (Measure.map h.measurableSpectrum
          (complexSymmetricMatrixVolume N)).withDensity
        (coeTakagiBoundaryDensity N K) :=
      map_withDensity_comp (complexSymmetricMatrixVolume N)
        h.measurableSpectrum (coeTakagiBoundaryDensity N K)
        h.measurable_measurableSpectrum
        (measurable_coeTakagiBoundaryDensity N K).aemeasurable
    _ = ((h.orbitConstant : ℝ≥0∞) •
          takagiFlatEigenvalueRadialMeasure N).withDensity
        (coeTakagiBoundaryDensity N K) := by
      rw [h.measurable_flat_radial_law]
    _ = (h.orbitConstant : ℝ≥0∞) •
        ((takagiFlatEigenvalueRadialMeasure N).withDensity
          (coeTakagiBoundaryDensity N K)) := by
      rw [withDensity_smul_measure]
    _ = (h.orbitConstant : ℝ≥0∞) •
        coeEigenvalueRadialMeasure N K := by
      rw [takagiFlatRadial_withDensity_boundary_eq_coeRadial]

theorem CanonicalGapWeylLawContract.normalized_coe_radial_law
    {N : ℕ} (h : CanonicalGapWeylLawContract N) (K : ℕ) :
    Measure.map h.measurableSpectrum
        (coeCornerDeterminantDensityProbabilityMeasure N K) =
      normalizedCOEEigenvalueRadialMeasure N K := by
  have hnorm := map_normalizeMeasure_of_map_eq_nnreal_smul
    (coeCornerRawDeterminantDensityMeasure N K)
    (coeEigenvalueRadialMeasure N K)
    h.measurableSpectrum h.orbitConstant
    h.measurable_measurableSpectrum h.orbitConstant_ne_zero
    (h.raw_coe_radial_law K)
  simpa [normalizeMeasure, coeCornerDeterminantDensityProbabilityMeasure,
    normalizedCOEEigenvalueRadialMeasure] using hnorm

/-- The canonical spectrum and its measurable representative still agree
almost everywhere after inserting the determinant density. -/
theorem CanonicalGapWeylLawContract.canonical_ae_eq_measurableSpectrum_raw
    {N : ℕ} (h : CanonicalGapWeylLawContract N) (K : ℕ) :
    canonicalGapSquaredSpectrum N =ᵐ[
      coeCornerRawDeterminantDensityMeasure N K] h.measurableSpectrum := by
  rw [coeCornerRawDeterminantDensityMeasure_eq_withDensity]
  exact (withDensity_absolutelyContinuous
    (complexSymmetricMatrixVolume N)
    (coeCornerMatrixDeterminantWeight N K)).ae_le
      h.canonical_ae_eq_measurableSpectrum

/-- The same null-set replacement is valid under the normalized A1 density. -/
theorem CanonicalGapWeylLawContract.canonical_ae_eq_measurableSpectrum_probability
    {N : ℕ} (h : CanonicalGapWeylLawContract N) (K : ℕ) :
    canonicalGapSquaredSpectrum N =ᵐ[
      coeCornerDeterminantDensityProbabilityMeasure N K]
        h.measurableSpectrum := by
  unfold coeCornerDeterminantDensityProbabilityMeasure
  exact Measure.smul_absolutelyContinuous.ae_le
    (h.canonical_ae_eq_measurableSpectrum_raw K)

/-- The exact smaller general-dimensional input sufficient for H6.  Unlike
`TakagiWeylFlatContract`, it has no factorization witness and no unitary
selector.  Its only substantive field is the canonical eigenvalue
pushforward formula. -/
structure CanonicalGapWeylFlatContract (N : ℕ) where
  measurable_spectrum : Measurable (canonicalGapSquaredSpectrum N)
  orbitConstant : NNReal
  orbitConstant_ne_zero : orbitConstant ≠ 0
  flat_radial_law :
    Measure.map (canonicalGapSquaredSpectrum N)
        (complexSymmetricMatrixVolume N) =
      (orbitConstant : ℝ≥0∞) • takagiFlatEigenvalueRadialMeasure N

theorem CanonicalGapWeylFlatContract.spectrum_ae_positive
    {N : ℕ} (h : CanonicalGapWeylFlatContract N) :
    ∀ᵐ C ∂complexSymmetricMatrixVolume N,
      canonicalGapSquaredSpectrum N C ∈ openPositiveOrthant N := by
  have htarget' :
      ∀ᵐ lambda ∂(h.orbitConstant : ℝ≥0∞) •
          takagiFlatEigenvalueRadialMeasure N,
        lambda ∈ openPositiveOrthant N :=
    Measure.smul_absolutelyContinuous.ae_le
      (takagiFlatEigenvalueRadialMeasure_ae_positive N)
  have htarget :
      ∀ᵐ lambda ∂Measure.map (canonicalGapSquaredSpectrum N)
          (complexSymmetricMatrixVolume N),
        lambda ∈ openPositiveOrthant N :=
    h.flat_radial_law.symm ▸ htarget'
  exact (ae_map_iff h.measurable_spectrum.aemeasurable
    (measurableSet_openPositiveOrthant_h6 N)).mp htarget

theorem CanonicalGapWeylFlatContract.matrixWeight_ae_eq_boundary_comp
    {N : ℕ} (h : CanonicalGapWeylFlatContract N) (K : ℕ) :
    coeCornerMatrixDeterminantWeight N K =ᵐ[
      complexSymmetricMatrixVolume N]
      coeTakagiBoundaryDensity N K ∘ canonicalGapSquaredSpectrum N := by
  filter_upwards [h.spectrum_ae_positive] with C hpos
  exact coeCornerMatrixDeterminantWeight_eq_boundary_canonicalSpectrum C hpos

theorem CanonicalGapWeylFlatContract.raw_coe_radial_law
    {N : ℕ} (h : CanonicalGapWeylFlatContract N) (K : ℕ) :
    Measure.map (canonicalGapSquaredSpectrum N)
        (coeCornerRawDeterminantDensityMeasure N K) =
      (h.orbitConstant : ℝ≥0∞) • coeEigenvalueRadialMeasure N K := by
  calc
    Measure.map (canonicalGapSquaredSpectrum N)
        (coeCornerRawDeterminantDensityMeasure N K) =
      Measure.map (canonicalGapSquaredSpectrum N)
        ((complexSymmetricMatrixVolume N).withDensity
          (coeCornerMatrixDeterminantWeight N K)) := by
      rw [coeCornerRawDeterminantDensityMeasure_eq_withDensity]
    _ = Measure.map (canonicalGapSquaredSpectrum N)
        ((complexSymmetricMatrixVolume N).withDensity
          (coeTakagiBoundaryDensity N K ∘
            canonicalGapSquaredSpectrum N)) := by
      congr 1
      exact withDensity_congr_ae
        (h.matrixWeight_ae_eq_boundary_comp K)
    _ = (Measure.map (canonicalGapSquaredSpectrum N)
          (complexSymmetricMatrixVolume N)).withDensity
        (coeTakagiBoundaryDensity N K) :=
      map_withDensity_comp (complexSymmetricMatrixVolume N)
        (canonicalGapSquaredSpectrum N) (coeTakagiBoundaryDensity N K)
        h.measurable_spectrum
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

theorem CanonicalGapWeylFlatContract.normalized_coe_radial_law
    {N : ℕ} (h : CanonicalGapWeylFlatContract N) (K : ℕ) :
    Measure.map (canonicalGapSquaredSpectrum N)
        (coeCornerDeterminantDensityProbabilityMeasure N K) =
      normalizedCOEEigenvalueRadialMeasure N K := by
  have hnorm := map_normalizeMeasure_of_map_eq_nnreal_smul
    (coeCornerRawDeterminantDensityMeasure N K)
    (coeEigenvalueRadialMeasure N K)
    (canonicalGapSquaredSpectrum N) h.orbitConstant
    h.measurable_spectrum h.orbitConstant_ne_zero (h.raw_coe_radial_law K)
  simpa [normalizeMeasure, coeCornerDeterminantDensityProbabilityMeasure,
    normalizedCOEEigenvalueRadialMeasure] using hnorm

/-! ## Direct trace algebra, without a Takagi representation -/

private theorem canonical_inverse_conjugate_pow_complex
    {n : ℕ} (S X : Matrix (Fin n) (Fin n) ℂ)
    (m : ℕ) (hS : IsUnit S.det) :
    (S⁻¹ * X * S) ^ m = S⁻¹ * X ^ m * S := by
  have hconj : SemiconjBy S (S⁻¹ * X * S) X := by
    unfold SemiconjBy
    calc
      S * (S⁻¹ * X * S) = (S * S⁻¹) * X * S := by
        simp only [Matrix.mul_assoc]
      _ = X * S := by rw [Matrix.mul_nonsing_inv S hS, one_mul]
  have hpow := hconj.pow_right m
  calc
    (S⁻¹ * X * S) ^ m =
        S⁻¹ * (S * (S⁻¹ * X * S) ^ m) := by
      rw [Matrix.nonsing_inv_mul_cancel_left S _ hS]
    _ = S⁻¹ * (X ^ m * S) := by rw [hpow.eq]
    _ = S⁻¹ * X ^ m * S := by rw [Matrix.mul_assoc]

private theorem canonical_trace_inverse_conjugate_pow_complex
    {n : ℕ} (S X : Matrix (Fin n) (Fin n) ℂ)
    (m : ℕ) (hS : IsUnit S.det) :
    Matrix.trace ((S⁻¹ * X * S) ^ m) = Matrix.trace (X ^ m) := by
  rw [canonical_inverse_conjugate_pow_complex S X m hS]
  calc
    Matrix.trace (S⁻¹ * X ^ m * S) =
        Matrix.trace (S * (S⁻¹ * X ^ m)) := by
      rw [Matrix.trace_mul_cycle]
      congr 1
      noncomm_ring
    _ = Matrix.trace ((S * S⁻¹) * X ^ m) := by
      congr 1
      noncomm_ring
    _ = Matrix.trace (X ^ m) := by
      rw [Matrix.mul_nonsing_inv S hS, one_mul]

private theorem canonical_jacobiOdds_inverse_conjugate
    {n : ℕ} (S D : Matrix (Fin n) (Fin n) ℂ)
    (hS : IsUnit S.det) :
    (1 - S⁻¹ * D * S)⁻¹ * (S⁻¹ * D * S) =
      S⁻¹ * ((1 - D)⁻¹ * D) * S := by
  have hsub :
      1 - S⁻¹ * D * S = S⁻¹ * (1 - D) * S := by
    calc
      1 - S⁻¹ * D * S =
          S⁻¹ * S - S⁻¹ * D * S := by
        rw [Matrix.nonsing_inv_mul S hS]
      _ = S⁻¹ * (1 - D) * S := by noncomm_ring
  rw [hsub]
  letI := Matrix.invertibleOfIsUnitDet S hS
  simp only [Matrix.mul_inv_rev, Matrix.inv_inv_of_invertible,
    Matrix.mul_assoc]
  have hcancel : S * (S⁻¹ * (D * S)) = D * S := by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv S hS, one_mul]
  rw [hcancel]

private theorem canonical_trace_diagonal_jacobiOdds_pow
    {n : ℕ} (lambda : Fin n → ℝ)
    (hne : ∀ i, (1 - (lambda i : ℂ)) ≠ 0) (m : ℕ) :
    Matrix.trace
        ((((1 : Matrix (Fin n) (Fin n) ℂ) -
          Matrix.diagonal (RCLike.ofReal ∘ lambda))⁻¹ *
            Matrix.diagonal (RCLike.ofReal ∘ lambda)) ^ m) =
      ∑ i : Fin n, ((betaPrimeForward (lambda i) : ℂ) ^ m) := by
  classical
  have hsub :
      (1 : Matrix (Fin n) (Fin n) ℂ) -
          Matrix.diagonal (RCLike.ofReal ∘ lambda) =
        Matrix.diagonal (fun i ↦ (1 - lambda i : ℝ) : Fin n → ℂ) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [Matrix.one_apply, Matrix.diagonal, hij]
  have hinv :
      (Matrix.diagonal (fun i ↦ (1 - lambda i : ℝ) : Fin n → ℂ))⁻¹ =
        Matrix.diagonal (fun i ↦ (1 - (lambda i : ℂ))⁻¹) := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simp [hne]
    · simp [Matrix.one_apply, Matrix.diagonal, hij]
  rw [hsub, hinv]
  simp [Matrix.diagonal_pow, betaPrimeForward, div_eq_mul_inv]
  apply Finset.sum_congr rfl
  intro i _hi
  change (((1 - (lambda i : ℂ))⁻¹ * (lambda i : ℂ)) ^ m) =
    (((lambda i : ℂ) * (1 - (lambda i : ℂ))⁻¹) ^ m)
  rw [mul_comm]

/-- A2-free Hermitian functional calculus for reflected eigenvalue odds. -/
theorem canonical_trace_inverse_mul_one_sub_pow_eq_reflected_eigenvalue_odds
    {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ)
    (hH : H.IsHermitian)
    (hne : ∀ i, (hH.eigenvalues i : ℂ) ≠ 0)
    (q : ℕ) :
    Matrix.trace ((H⁻¹ * (1 - H)) ^ q) =
      ∑ i : Fin m,
        ((betaPrimeForward (1 - hH.eigenvalues i) : ℂ) ^ q) := by
  let U := hH.eigenvectorUnitary
  let D : Matrix (Fin m) (Fin m) ℂ :=
    Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues)
  have hSinv : (star (U : Matrix (Fin m) (Fin m) ℂ))⁻¹ =
      (U : Matrix (Fin m) (Fin m) ℂ) := by
    exact Matrix.inv_eq_left_inv (Unitary.coe_mul_star_self U)
  have hSunit : IsUnit (star (U : Matrix (Fin m) (Fin m) ℂ)) := by
    simpa only [Unitary.coe_star] using
      (Unitary.isUnit_coe (U := star U))
  have hSdet : IsUnit
      (star (U : Matrix (Fin m) (Fin m) ℂ)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hSunit
  have hspec : H =
      (star (U : Matrix (Fin m) (Fin m) ℂ))⁻¹ * D *
        star (U : Matrix (Fin m) (Fin m) ℂ) := by
    simpa only [D, U, hSinv, Unitary.conjStarAlgAut_apply] using
      hH.spectral_theorem
  have hsub : 1 - H =
      (star (U : Matrix (Fin m) (Fin m) ℂ))⁻¹ * (1 - D) *
        star (U : Matrix (Fin m) (Fin m) ℂ) := by
    rw [hspec]
    calc
      1 - (star (U : Matrix (Fin m) (Fin m) ℂ))⁻¹ * D * star U =
          (star (U : Matrix (Fin m) (Fin m) ℂ))⁻¹ * star U -
            (star (U : Matrix (Fin m) (Fin m) ℂ))⁻¹ * D * star U := by
        rw [hSinv, Unitary.coe_mul_star_self]
      _ = (star (U : Matrix (Fin m) (Fin m) ℂ))⁻¹ * (1 - D) *
          star U := by noncomm_ring
  have hratio : H⁻¹ * (1 - H) =
      (star (U : Matrix (Fin m) (Fin m) ℂ))⁻¹ *
        (D⁻¹ * (1 - D)) *
          star (U : Matrix (Fin m) (Fin m) ℂ) := by
    calc
      H⁻¹ * (1 - H) =
          (1 - (1 - H))⁻¹ * (1 - H) := by
        rw [show 1 - (1 - H) = H by noncomm_ring]
      _ = (1 -
            (star (U : Matrix (Fin m) (Fin m) ℂ))⁻¹ * (1 - D) *
              star (U : Matrix (Fin m) (Fin m) ℂ))⁻¹ *
          ((star (U : Matrix (Fin m) (Fin m) ℂ))⁻¹ * (1 - D) *
            star (U : Matrix (Fin m) (Fin m) ℂ)) := by
        rw [hsub]
      _ = (star (U : Matrix (Fin m) (Fin m) ℂ))⁻¹ *
          ((1 - (1 - D))⁻¹ * (1 - D)) *
            star (U : Matrix (Fin m) (Fin m) ℂ) := by
        simpa only [Unitary.coe_star] using
          (canonical_jacobiOdds_inverse_conjugate
            (star (U : Matrix (Fin m) (Fin m) ℂ)) (1 - D) hSdet)
      _ = (star (U : Matrix (Fin m) (Fin m) ℂ))⁻¹ *
          (D⁻¹ * (1 - D)) *
            star (U : Matrix (Fin m) (Fin m) ℂ) := by
        rw [show 1 - (1 - D) = D by noncomm_ring]
  let reflected : Fin m → ℝ := fun i ↦ 1 - hH.eigenvalues i
  let reflectedDiagonal : Matrix (Fin m) (Fin m) ℂ :=
    Matrix.diagonal (RCLike.ofReal ∘ reflected)
  have hreflected : 1 - D = reflectedDiagonal := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [D, reflectedDiagonal, reflected]
    · simp [D, reflectedDiagonal, reflected, Matrix.one_apply, hij]
  have hdenominator : 1 - reflectedDiagonal = D := by
    rw [← hreflected]
    noncomm_ring
  have hoddsMatrix : D⁻¹ * (1 - D) =
      (1 - reflectedDiagonal)⁻¹ * reflectedDiagonal := by
    rw [hreflected, hdenominator]
  rw [hratio, canonical_trace_inverse_conjugate_pow_complex _ _ q hSdet,
    hoddsMatrix]
  exact canonical_trace_diagonal_jacobiOdds_pow reflected
    (fun i ↦ by simpa [reflected] using hne i) q

private theorem matrix_mul_mul_pow_succ
    {N : ℕ} (A B : ConcreteMatrixState N) (q : ℕ) :
    (A * B) ^ (q + 1) = A * (B * A) ^ q * B := by
  rw [pow_succ, ← mul_assoc, mul_pow_mul]

private theorem trace_mul_mul_pow_succ_swap
    {N : ℕ} (A B : ConcreteMatrixState N) (q : ℕ) :
    Matrix.trace ((A * B) ^ (q + 1)) =
      Matrix.trace ((B * A) ^ (q + 1)) := by
  rw [matrix_mul_mul_pow_succ]
  rw [Matrix.trace_mul_cycle]
  rw [pow_succ']

/-- On the matrix-ball support, every trace-power vector factors through the
canonical gap spectrum.  This is the replacement for the old use of an
almost-everywhere Takagi representation. -/
theorem unscaledCOETracePowerVector_eq_canonicalGapSpectrum
    {r N : ℕ} (C : ConcreteMatrixState N)
    (hsupport : coeCornerSupport C) :
    unscaledCOETracePowerVector r N C =
      (spectralPowerSumVector r N ∘ betaPrimeForwardVector N ∘
        canonicalGapSquaredSpectrum N) C := by
  let H := coeHermitianGap C
  let hH : H.IsHermitian := coeHermitianGap_isHermitian C
  have heigpos : ∀ i, 0 < hH.eigenvalues i := by
    exact hH.posDef_iff_eigenvalues_pos.mp hsupport
  have heigne : ∀ i, (hH.eigenvalues i : ℂ) ≠ 0 := by
    intro i
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (heigpos i))
  funext j
  let q := j.1 + 1
  have hswap :
      Matrix.trace
          ((C * (H⁻¹ * C.conjTranspose)) ^ q) =
        Matrix.trace
          (((H⁻¹ * C.conjTranspose) * C) ^ q) := by
    simpa [q] using trace_mul_mul_pow_succ_swap C
      (H⁻¹ * C.conjTranspose) j.1
  have hBA : (H⁻¹ * C.conjTranspose) * C = H⁻¹ * (1 - H) := by
    dsimp [H, coeHermitianGap]
    noncomm_ring
  have hspectral :=
    canonical_trace_inverse_mul_one_sub_pow_eq_reflected_eigenvalue_odds
      H hH heigne q
  unfold unscaledCOETracePowerVector concreteCOETracePowerVector
    concreteCOEZ spectralPowerSumVector betaPrimeForwardVector
    canonicalGapSquaredSpectrum
  simp only [unscaleCOECorner_one, Function.comp_apply]
  rw [show C * (1 - C.conjTranspose * C)⁻¹ * C.conjTranspose =
      C * (H⁻¹ * C.conjTranspose) by
    dsimp [H, coeHermitianGap]
    noncomm_ring]
  rw [hswap, hBA, hspectral]
  rw [show
      (∑ i : Fin N,
        ((betaPrimeForward (1 - hH.eigenvalues i) : ℂ) ^ q)).re =
        ∑ i : Fin N,
          (((betaPrimeForward (1 - hH.eigenvalues i) : ℂ) ^ q)).re by
    simpa using (Complex.re_sum (s := Finset.univ)
      (fun i : Fin N ↦
        ((betaPrimeForward (1 - hH.eigenvalues i) : ℂ) ^ q)))]
  apply Finset.sum_congr rfl
  intro i _hi
  norm_cast

/-- The one-law contract supplies trace factorization through its measurable
representative; the replacement changes the canonical statistic only on a
null set. -/
theorem CanonicalGapWeylLawContract.trace_factorization
    {N : ℕ} (h : CanonicalGapWeylLawContract N) (K r : ℕ) :
    unscaledCOETracePowerVector r N =ᵐ[
      coeCornerDeterminantDensityProbabilityMeasure N K]
      spectralPowerSumVector r N ∘ betaPrimeForwardVector N ∘
        h.measurableSpectrum := by
  filter_upwards
    [coeCornerDeterminantDensityProbabilityMeasure_ae_support N K,
      h.canonical_ae_eq_measurableSpectrum_probability K]
      with C hsupport heq
  calc
    unscaledCOETracePowerVector r N C =
        (spectralPowerSumVector r N ∘ betaPrimeForwardVector N ∘
          canonicalGapSquaredSpectrum N) C :=
      unscaledCOETracePowerVector_eq_canonicalGapSpectrum C hsupport.2
    _ = (spectralPowerSumVector r N ∘ betaPrimeForwardVector N ∘
          h.measurableSpectrum) C := by
      simp only [Function.comp_apply, heq]

/-- The single flat pushforward law is sufficient to build the complete COE
spectral contract consumed by H6. -/
def CanonicalGapWeylLawContract.toCOETakagiDensityContract
    {N : ℕ} (h : CanonicalGapWeylLawContract N) (K : ℕ)
    (hN : 1 ≤ N) :
    COETakagiDensityContract N K
      (normalizedBetaPrimeEigenvalueRadialMeasure N K) where
  spectrum := betaPrimeForwardVector N ∘ h.measurableSpectrum
  measurable_spectrum :=
    (measurable_betaPrimeForwardVector N).comp
      h.measurable_measurableSpectrum
  trace_factorization := fun r ↦ by
    simpa only [Function.comp_assoc] using h.trace_factorization K r
  spectral_law := by
    calc
      Measure.map (betaPrimeForwardVector N ∘ h.measurableSpectrum)
          (coeCornerDeterminantDensityProbabilityMeasure N K) =
        Measure.map (betaPrimeForwardVector N)
          (Measure.map h.measurableSpectrum
            (coeCornerDeterminantDensityProbabilityMeasure N K)) := by
        rw [Measure.map_map (measurable_betaPrimeForwardVector N)
          h.measurable_measurableSpectrum]
      _ = Measure.map (betaPrimeForwardVector N)
          (normalizedCOEEigenvalueRadialMeasure N K) := by
        rw [h.normalized_coe_radial_law K]
      _ = normalizedBetaPrimeEigenvalueRadialMeasure N K :=
        map_normalizedCOEEigenvalueRadialMeasure_eq_normalizedBetaPrime
          (N := N) (K := K) hN

theorem CanonicalGapWeylFlatContract.trace_factorization
    {N : ℕ} (h : CanonicalGapWeylFlatContract N) (K r : ℕ) :
    unscaledCOETracePowerVector r N =ᵐ[
      coeCornerDeterminantDensityProbabilityMeasure N K]
      spectralPowerSumVector r N ∘ betaPrimeForwardVector N ∘
        canonicalGapSquaredSpectrum N := by
  filter_upwards [coeCornerDeterminantDensityProbabilityMeasure_ae_support N K]
    with C hsupport
  exact unscaledCOETracePowerVector_eq_canonicalGapSpectrum C hsupport.2

/-- The selector-free flat law supplies the original abstract COE spectral
contract with the beta-prime transformed canonical gap spectrum.  This
formally confirms that neither a Takagi factorization nor a measurable
unitary selector is consumed by H6. -/
def CanonicalGapWeylFlatContract.toCOETakagiDensityContract
    {N : ℕ} (h : CanonicalGapWeylFlatContract N) (K : ℕ)
    (hN : 1 ≤ N) :
    COETakagiDensityContract N K
      (normalizedBetaPrimeEigenvalueRadialMeasure N K) where
  spectrum := betaPrimeForwardVector N ∘ canonicalGapSquaredSpectrum N
  measurable_spectrum :=
    (measurable_betaPrimeForwardVector N).comp h.measurable_spectrum
  trace_factorization := fun r ↦ by
    simpa only [Function.comp_assoc] using h.trace_factorization K r
  spectral_law := by
    calc
      Measure.map
          (betaPrimeForwardVector N ∘ canonicalGapSquaredSpectrum N)
          (coeCornerDeterminantDensityProbabilityMeasure N K) =
        Measure.map (betaPrimeForwardVector N)
          (Measure.map (canonicalGapSquaredSpectrum N)
            (coeCornerDeterminantDensityProbabilityMeasure N K)) := by
        rw [Measure.map_map (measurable_betaPrimeForwardVector N)
          h.measurable_spectrum]
      _ = Measure.map (betaPrimeForwardVector N)
          (normalizedCOEEigenvalueRadialMeasure N K) := by
        rw [h.normalized_coe_radial_law K]
      _ = normalizedBetaPrimeEigenvalueRadialMeasure N K :=
        map_normalizedCOEEigenvalueRadialMeasure_eq_normalizedBetaPrime
          (N := N) (K := K) hN

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
