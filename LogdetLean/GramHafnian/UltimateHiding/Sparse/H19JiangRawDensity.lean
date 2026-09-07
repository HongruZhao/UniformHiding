import LogdetLean.GramHafnian.UltimateHiding.Sparse.H19MatrixBetaDefinitions
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Jiang density definitions and elementary coordinate transports

This release module records the definitions used by the internally proved
strict-size H19 density before any transpose, `sqrt M` scaling, Gaussian
comparison, Radon--Nikodym conversion, logarithm, expectation, or KL
calculation.

For `N <= K`, Jiang's Proposition 2.1 is applied in its native tall-block
orientation: the upper-left `K x N` corner of Haar `U(M)`.  Its density with
respect to coordinatewise complex Lebesgue measure is the matrix-ball density

`C * det(I - X^* X)^(M-K-N)`

on `I - X^* X >= 0`, where the displayed factorial product is the exact
normalizer in Proposition 2.1.

The historical non-strict Jiang literature declaration is deliberately not
part of this source-pruned release: the active endpoint uses the internally
proved strict-size induction in `H19JiangDensityProved`.
-/

open MeasureTheory Matrix
open scoped BigOperators ENNReal ComplexOrder

namespace LogdetLean.GramHafnian.UltimateHiding.Sparse

noncomputable section

open CurrentPRL

/-! ## General density transport used by the Jiang scaling adapter -/

/-- Transport a density through a measurable equivalence.  This elementary
measure-theory lemma is copied into the hiding package so the sparse Jiang
branch does not import the anticoncentration paper's `MixtureDensity` module. -/
theorem map_measurableEquiv_withDensity_H19
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (μ : Measure α) (f : α → ENNReal)
    (hf : Measurable f) :
    Measure.map e (μ.withDensity f) =
      (Measure.map e μ).withDensity (f ∘ e.symm) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs,
    withDensity_apply _ (hs.preimage e.measurable),
    withDensity_apply _ hs]
  rw [← lintegral_indicator hs]
  rw [lintegral_map]
  · rw [← lintegral_indicator (hs.preimage e.measurable)]
    congr 1
    funext x
    by_cases hx : e x ∈ s
    · simp [Set.indicator, hx]
    · simp [Set.indicator, hx]
  · exact (hf.comp e.symm.measurable).indicator hs
  · exact e.measurable

local instance matrixNormedAddCommGroupH19Jiang (K N : ℕ) :
    NormedAddCommGroup (Matrix (Fin K) (Fin N) ℂ) :=
  Matrix.normedAddCommGroup

local instance matrixNormedSpaceH19Jiang (K N : ℕ) :
    NormedSpace ℝ (Matrix (Fin K) (Fin N) ℂ) :=
  Matrix.normedSpace

local instance matrixBorelSpaceH19Jiang (K N : ℕ) :
    BorelSpace (Matrix (Fin K) (Fin N) ℂ) := by
  exact inferInstanceAs (BorelSpace (Fin K → Fin N → ℂ))

local instance unitaryGroupCompactSpaceH19Jiang (M : ℕ) :
    CompactSpace (Matrix.unitaryGroup (Fin M) ℂ) :=
  isCompact_iff_compactSpace.mp (unitaryGroup_carrier_isCompact M)

/-- Coordinatewise complex Lebesgue measure on a rectangular matrix. -/
def complexRectangularLebesgueVolume (K N : ℕ) :
    Measure (Matrix (Fin K) (Fin N) ℂ) :=
  Measure.pi fun _ : Fin K ↦ Measure.pi fun _ : Fin N ↦ (volume : Measure ℂ)

instance complexRectangularLebesgueVolume_sigmaFinite (K N : ℕ) :
    SigmaFinite (complexRectangularLebesgueVolume K N) := by
  unfold complexRectangularLebesgueVolume
  letI : ∀ _ : Fin K,
      SigmaFinite (Measure.pi fun _ : Fin N ↦ (volume : Measure ℂ)) :=
    fun _ ↦ Measure.pi.sigmaFinite _
  exact Measure.pi.sigmaFinite _

instance complexRectangularLebesgueVolume_isAddHaarMeasure (K N : ℕ) :
    Measure.IsAddHaarMeasure (complexRectangularLebesgueVolume K N) := by
  unfold complexRectangularLebesgueVolume
  letI : ∀ _ : Fin K,
      SigmaFinite (Measure.pi fun _ : Fin N ↦ (volume : Measure ℂ)) :=
    fun _ ↦ Measure.pi.sigmaFinite _
  letI : ∀ _ : Fin K,
      Measure.IsAddHaarMeasure
        (Measure.pi fun _ : Fin N ↦ (volume : Measure ℂ)) :=
    fun _ ↦ Measure.pi.isAddHaarMeasure _
  exact Measure.pi.isAddHaarMeasure _

/-- The literal unscaled `K x N` upper-left corner in Jiang's `K >= N`
orientation. -/
def jiangUnscaledTallHaarCornerMatrix {M K N : ℕ}
    (hKM : K ≤ M) (hNM : N ≤ M)
    (U : Matrix.unitaryGroup (Fin M) ℂ) : Matrix (Fin K) (Fin N) ℂ :=
  topLeftUnitaryBlock hKM hNM U

theorem measurable_jiangUnscaledTallHaarCornerMatrix {M K N : ℕ}
    (hKM : K ≤ M) (hNM : N ≤ M) :
    Measurable (jiangUnscaledTallHaarCornerMatrix hKM hNM) :=
  measurable_topLeftUnitaryBlock hKM hNM

/-- Totalized law of Jiang's unscaled tall Haar corner. -/
def jiangUnscaledTallHaarCornerLaw (M K N : ℕ) :
    Measure (Matrix (Fin K) (Fin N) ℂ) :=
  if h : K ≤ M ∧ N ≤ M then
    Measure.map (jiangUnscaledTallHaarCornerMatrix h.1 h.2)
      (unitaryHaarProbabilityMeasure M)
  else 0

/-- Jiang's factorial normalizer
`pi^(-K*N) * product_{j=1}^N (M-j)!/(M-j-K)!`. -/
def jiangUnscaledTallHaarCornerNormalizer (M K N : ℕ) : ℝ :=
  (Real.pi ^ (K * N))⁻¹ *
    ∏ j : Fin N,
      ((Nat.factorial (M - (j.1 + 1)) : ℕ) : ℝ) /
        ((Nat.factorial (M - (j.1 + 1) - K) : ℕ) : ℝ)

/-- The matrix-ball support in the exact orientation of Proposition 2.1. -/
def jiangUnscaledTallHaarCornerSupport {K N : ℕ}
    (X : Matrix (Fin K) (Fin N) ℂ) : Prop :=
  ∀ v : Fin N → ℂ,
    0 ≤ (star v ⬝ᵥ ((1 - X.conjTranspose * X) *ᵥ v)).re

theorem isClosed_jiangUnscaledTallHaarCornerSupport (K N : ℕ) :
    IsClosed {X : Matrix (Fin K) (Fin N) ℂ |
      jiangUnscaledTallHaarCornerSupport X} := by
  rw [show {X : Matrix (Fin K) (Fin N) ℂ |
        jiangUnscaledTallHaarCornerSupport X} =
      ⋂ v : Fin N → ℂ,
        {X | 0 ≤
          (star v ⬝ᵥ ((1 - X.conjTranspose * X) *ᵥ v)).re} by
    ext X
    simp [jiangUnscaledTallHaarCornerSupport]]
  apply isClosed_iInter
  intro v
  exact isClosed_le (by fun_prop) (by fun_prop)

/-- The literal unscaled density printed in Jiang Proposition 2.1. -/
def jiangUnscaledTallHaarCornerPDF (M K N : ℕ)
    (X : Matrix (Fin K) (Fin N) ℂ) : ℝ≥0∞ :=
  @ite ℝ≥0∞ (jiangUnscaledTallHaarCornerSupport X)
    (Classical.propDecidable _) 
    (ENNReal.ofReal
      (jiangUnscaledTallHaarCornerNormalizer M K N *
        (Matrix.det (1 - X.conjTranspose * X)).re ^ (M - K - N)))
    0

theorem measurable_jiangUnscaledTallHaarCornerPDF (M K N : ℕ) :
    Measurable (jiangUnscaledTallHaarCornerPDF M K N) := by
  unfold jiangUnscaledTallHaarCornerPDF
  apply Measurable.ite
  · exact (isClosed_jiangUnscaledTallHaarCornerSupport K N).measurableSet
  · have hmat : Continuous
        (fun X : Matrix (Fin K) (Fin N) ℂ ↦
          1 - X.conjTranspose * X) := by
      fun_prop
    have hdet : Measurable
        (fun X : Matrix (Fin K) (Fin N) ℂ ↦
          Matrix.det (1 - X.conjTranspose * X)) :=
      hmat.matrix_det.measurable
    have hre : Measurable
        (fun X : Matrix (Fin K) (Fin N) ℂ ↦
          (Matrix.det (1 - X.conjTranspose * X)).re) :=
      Complex.measurable_re.comp hdet
    exact (measurable_const.mul (hre.pow_const _)).ennreal_ofReal
  · exact measurable_const

/-! ## Elementary square-root scaling -/

/-- Multiplication by `sqrt M` as a measurable equivalence of the native
rectangular coordinate space. -/
def rectangularSqrtScaleMeasurableEquiv (M K N : ℕ) (hM : 0 < M) :
    Matrix (Fin K) (Fin N) ℂ ≃ᵐ Matrix (Fin K) (Fin N) ℂ :=
  ((Homeomorph.smulOfNeZero (Real.sqrt (M : ℝ))
    (ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast hM))) :
      Matrix (Fin K) (Fin N) ℂ ≃ₜ Matrix (Fin K) (Fin N) ℂ).toMeasurableEquiv)

@[simp]
theorem rectangularSqrtScaleMeasurableEquiv_apply
    {M K N : ℕ} (hM : 0 < M) (X : Matrix (Fin K) (Fin N) ℂ) :
    rectangularSqrtScaleMeasurableEquiv M K N hM X =
      Real.sqrt (M : ℝ) • X :=
  rfl

@[simp]
theorem rectangularSqrtScaleMeasurableEquiv_symm_apply
    {M K N : ℕ} (hM : 0 < M) (Z : Matrix (Fin K) (Fin N) ℂ) :
    (rectangularSqrtScaleMeasurableEquiv M K N hM).symm Z =
      (Real.sqrt (M : ℝ))⁻¹ • Z :=
  rfl

theorem finrank_real_rectangularComplexMatrix (K N : ℕ) :
    Module.finrank ℝ (Matrix (Fin K) (Fin N) ℂ) = 2 * K * N := by
  rw [Module.finrank_matrix]
  simp
  ring

/-- The elementary real Jacobian of entrywise multiplication by `sqrt M`.
The exponent is `2KN` over `ℝ`, hence the volume multiplier is `M^(-KN)`. -/
theorem map_rectangularSqrtScale_complexRectangularLebesgueVolume
    {M K N : ℕ} (hM : 0 < M) :
    Measure.map (rectangularSqrtScaleMeasurableEquiv M K N hM)
        (complexRectangularLebesgueVolume K N) =
      ENNReal.ofReal (((M : ℝ)⁻¹) ^ (K * N)) •
        complexRectangularLebesgueVolume K N := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hsqrt : Real.sqrt (M : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hMr)
  change Measure.map (fun X : Matrix (Fin K) (Fin N) ℂ ↦
      Real.sqrt (M : ℝ) • X)
      (complexRectangularLebesgueVolume K N) = _
  have hscale := @Measure.map_addHaar_smul
    (Matrix (Fin K) (Fin N) ℂ)
    (matrixNormedAddCommGroupH19Jiang K N)
    (matrixNormedSpaceH19Jiang K N)
    (CurrentPRL.hidingReleaseComplexMatrixMeasurableSpace
      (Fin K) (Fin N))
    (matrixBorelSpaceH19Jiang K N)
    (by infer_instance)
    (complexRectangularLebesgueVolume K N)
    (complexRectangularLebesgueVolume_isAddHaarMeasure K N)
    (Real.sqrt (M : ℝ)) hsqrt
  rw [hscale]
  congr 1
  apply congrArg ENNReal.ofReal
  rw [finrank_real_rectangularComplexMatrix]
  rw [show 2 * K * N = 2 * (K * N) by ring, pow_mul,
    Real.sq_sqrt hMr.le]
  rw [abs_of_pos (inv_pos.mpr (pow_pos hMr _)), inv_pow]

/-- Jiang's native tall corner after entrywise multiplication by `sqrt M`. -/
def jiangSqrtScaledTallHaarCornerLaw (M K N : ℕ) :
    Measure (Matrix (Fin K) (Fin N) ℂ) :=
  Measure.map (fun X ↦ Real.sqrt (M : ℝ) • X)
    (jiangUnscaledTallHaarCornerLaw M K N)

/-- Density obtained from the literal Jiang density by the elementary
`2KN`-dimensional real Jacobian of the `sqrt M` dilation. -/
def jiangSqrtScaledTallHaarCornerPDF (M K N : ℕ)
    (Z : Matrix (Fin K) (Fin N) ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (((M : ℝ)⁻¹) ^ (K * N)) *
    jiangUnscaledTallHaarCornerPDF M K N
      ((Real.sqrt (M : ℝ))⁻¹ • Z)

theorem measurable_jiangSqrtScaledTallHaarCornerPDF (M K N : ℕ) :
    Measurable (jiangSqrtScaledTallHaarCornerPDF M K N) := by
  unfold jiangSqrtScaledTallHaarCornerPDF
  exact measurable_const.mul
    ((measurable_jiangUnscaledTallHaarCornerPDF M K N).comp
      (measurable_const_smul (Real.sqrt (M : ℝ))⁻¹))

/-! ## Elementary orientation transport -/

/-- Conjugate transpose as a measurable equivalence between rectangular
matrix coordinate spaces. -/
def rectangularConjTransposeMeasurableEquiv (K N : ℕ) :
    Matrix (Fin K) (Fin N) ℂ ≃ᵐ Matrix (Fin N) (Fin K) ℂ :=
  { toEquiv := (Matrix.conjTransposeAddEquiv (Fin K) (Fin N) ℂ).toEquiv
    measurable_toFun := continuous_id.matrix_conjTranspose.measurable
    measurable_invFun := continuous_id.matrix_conjTranspose.measurable }

@[simp]
theorem rectangularConjTransposeMeasurableEquiv_apply
    {K N : ℕ} (X : Matrix (Fin K) (Fin N) ℂ) :
    rectangularConjTransposeMeasurableEquiv K N X = X.conjTranspose :=
  rfl

@[simp]
theorem rectangularConjTransposeMeasurableEquiv_symm_apply
    {K N : ℕ} (Z : Matrix (Fin N) (Fin K) ℂ) :
    (rectangularConjTransposeMeasurableEquiv K N).symm Z = Z.conjTranspose :=
  rfl

/-- Normalized Haar probability on the compact unitary group is also right
invariant.  This is proved from left Haar uniqueness and total mass one. -/
theorem map_unitaryHaarProbabilityMeasure_mul_right_H19
    (M : ℕ) (V : Matrix.unitaryGroup (Fin M) ℂ) :
    Measure.map (fun U : Matrix.unitaryGroup (Fin M) ℂ ↦ U * V)
        (unitaryHaarProbabilityMeasure M) =
      unitaryHaarProbabilityMeasure M := by
  let G := Matrix.unitaryGroup (Fin M) ℂ
  let μ : Measure G := unitaryHaarProbabilityMeasure M
  let ν : Measure G := Measure.map (fun U : G ↦ U * V) μ
  letI : IsProbabilityMeasure μ :=
    unitaryHaarProbabilityMeasure_isProbability M
  letI : Measure.IsHaarMeasure μ :=
    canonicalUnitaryHaarProbabilityFamily.isHaar M
  haveI : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map
      (measurable_mul_const V).aemeasurable
  haveI : Measure.IsMulLeftInvariant ν := by
    dsimp only [ν]
    infer_instance
  have hν : ν = Measure.haarScalarFactor ν μ • μ :=
    Measure.isMulInvariant_eq_smul_of_compactSpace ν μ
  have hc : Measure.haarScalarFactor ν μ = 1 := by
    have hu := congrArg (fun m : Measure G ↦ m Set.univ) hν
    apply ENNReal.coe_injective
    simpa [measure_univ] using hu.symm
  have hν' : ν = μ := by simpa [hc] using hν
  simpa only [ν, μ] using hν'

/-- Inversion preserves normalized Haar probability on the compact unitary
group.  No random-matrix density calculation enters this fact. -/
theorem map_unitaryHaarProbabilityMeasure_inv_H19 (M : ℕ) :
    Measure.map Inv.inv (unitaryHaarProbabilityMeasure M) =
      unitaryHaarProbabilityMeasure M := by
  let G := Matrix.unitaryGroup (Fin M) ℂ
  let μ : Measure G := unitaryHaarProbabilityMeasure M
  let ν : Measure G := Measure.map Inv.inv μ
  letI : IsProbabilityMeasure μ :=
    unitaryHaarProbabilityMeasure_isProbability M
  letI : Measure.IsHaarMeasure μ :=
    canonicalUnitaryHaarProbabilityFamily.isHaar M
  letI : Measure.IsMulRightInvariant μ :=
    ⟨fun V ↦ by simpa only [μ] using
      map_unitaryHaarProbabilityMeasure_mul_right_H19 M V⟩
  haveI : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map measurable_inv.aemeasurable
  haveI : Measure.IsMulLeftInvariant ν := by
    dsimp only [ν]
    change Measure.IsMulLeftInvariant μ.inv
    infer_instance
  have hν : ν = Measure.haarScalarFactor ν μ • μ :=
    Measure.isMulInvariant_eq_smul_of_compactSpace ν μ
  have hc : Measure.haarScalarFactor ν μ = 1 := by
    have hu := congrArg (fun m : Measure G ↦ m Set.univ) hν
    apply ENNReal.coe_injective
    simpa [measure_univ] using hu.symm
  have hν' : ν = μ := by simpa [hc] using hν
  simpa only [ν, μ] using hν'

/-- The actual unscaled `N x K` corner law used by the project. -/
def jiangUnscaledWideHaarCornerLaw (M N K : ℕ) :
    Measure (Matrix (Fin N) (Fin K) ℂ) :=
  if h : N ≤ M ∧ K ≤ M then
    Measure.map (topLeftUnitaryBlock h.1 h.2)
      (unitaryHaarProbabilityMeasure M)
  else 0

/-- Conjugate transposing Jiang's native `K x N` corner gives the project's
`N x K` corner law.  The only probabilistic ingredient is inversion
invariance of normalized Haar probability proved immediately above. -/
theorem map_rectangularConjTranspose_jiangUnscaledTallHaarCornerLaw
    {M N K : ℕ} (hNK : N ≤ K) (hs : K + N ≤ M) :
    Measure.map (rectangularConjTransposeMeasurableEquiv K N)
        (jiangUnscaledTallHaarCornerLaw M K N) =
      jiangUnscaledWideHaarCornerLaw M N K := by
  have hKM : K ≤ M := by omega
  have hNM : N ≤ M := hNK.trans hKM
  rw [jiangUnscaledTallHaarCornerLaw, dif_pos ⟨hKM, hNM⟩,
    jiangUnscaledWideHaarCornerLaw, dif_pos ⟨hNM, hKM⟩]
  let f := (rectangularConjTransposeMeasurableEquiv K N) ∘
    jiangUnscaledTallHaarCornerMatrix hKM hNM
  have hf : Measurable f :=
    (rectangularConjTransposeMeasurableEquiv K N).measurable.comp
      (measurable_jiangUnscaledTallHaarCornerMatrix hKM hNM)
  rw [Measure.map_map
    (rectangularConjTransposeMeasurableEquiv K N).measurable
    (measurable_jiangUnscaledTallHaarCornerMatrix hKM hNM)]
  change Measure.map f (unitaryHaarProbabilityMeasure M) = _
  calc
    Measure.map f (unitaryHaarProbabilityMeasure M) =
        Measure.map f
          (Measure.map Inv.inv (unitaryHaarProbabilityMeasure M)) := by
      rw [map_unitaryHaarProbabilityMeasure_inv_H19 M]
    _ = Measure.map (f ∘ Inv.inv) (unitaryHaarProbabilityMeasure M) := by
      rw [Measure.map_map hf measurable_inv]
    _ = Measure.map (topLeftUnitaryBlock hNM hKM)
          (unitaryHaarProbabilityMeasure M) := by
      apply Measure.map_congr
      filter_upwards with U
      ext i j
      simp [f, Function.comp_def, jiangUnscaledTallHaarCornerMatrix,
        topLeftUnitaryBlock, Matrix.star_eq_conjTranspose]

/-- Conjugate transposition of the scaled native Jiang corner is exactly the
project's canonical `N x K` scaled Haar-block law. -/
theorem map_rectangularConjTranspose_jiangSqrtScaledTallHaarCornerLaw
    {M N K : ℕ} (hNK : N ≤ K) (hs : K + N ≤ M) :
    Measure.map (rectangularConjTransposeMeasurableEquiv K N)
        (jiangSqrtScaledTallHaarCornerLaw M K N) =
      sqrtScaledHaarBlockLaw canonicalUnitaryHaarProbabilityFamily M N K := by
  have hKM : K ≤ M := by omega
  have hNM : N ≤ M := hNK.trans hKM
  let sTall : Matrix (Fin K) (Fin N) ℂ →
      Matrix (Fin K) (Fin N) ℂ :=
    fun X ↦ Real.sqrt (M : ℝ) • X
  let sWide : Matrix (Fin N) (Fin K) ℂ →
      Matrix (Fin N) (Fin K) ℂ :=
    fun X ↦ Real.sqrt (M : ℝ) • X
  have hsTall : Measurable sTall := measurable_const_smul _
  have hsWide : Measurable sWide := measurable_const_smul _
  have hcomm :
      (rectangularConjTransposeMeasurableEquiv K N) ∘ sTall =
        sWide ∘ (rectangularConjTransposeMeasurableEquiv K N) := by
    funext X
    ext i j
    simp [sTall, sWide, Function.comp_def, RCLike.star_def]
  rw [jiangSqrtScaledTallHaarCornerLaw,
    Measure.map_map
      (rectangularConjTransposeMeasurableEquiv K N).measurable hsTall,
    hcomm, ← Measure.map_map hsWide
      (rectangularConjTransposeMeasurableEquiv K N).measurable,
    map_rectangularConjTranspose_jiangUnscaledTallHaarCornerLaw hNK hs,
    jiangUnscaledWideHaarCornerLaw, dif_pos ⟨hNM, hKM⟩,
    sqrtScaledHaarBlockLaw, dif_pos ⟨hNM, hKM⟩,
    Measure.map_map hsWide
      (measurable_topLeftUnitaryBlock hNM hKM)]
  apply Measure.map_congr
  filter_upwards with U
  ext i j
  simp [sWide, Function.comp_def, sqrtScaledHaarBlockMatrix]

end

end LogdetLean.GramHafnian.UltimateHiding.Sparse
