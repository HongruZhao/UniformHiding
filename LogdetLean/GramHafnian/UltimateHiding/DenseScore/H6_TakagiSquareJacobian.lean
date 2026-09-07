import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H6_TakagiWeylAdapters
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Squared-radius Jacobian adapter for the H6 Takagi reduction

The conventional Takagi coarea formula is written in positive singular
radii `rho_i` with density

`prod_i rho_i * |Delta(rho^2)|`.

This file proves the complete finite-dimensional change of variables
`lambda_i = rho_i^2`.  Its Jacobian `prod_i (2*rho_i)` cancels every radius
factor, leaving exactly `2^(-N) * |Delta(lambda)|`.  In particular, the
squared-Takagi density has no extra coordinate power.
-/

open scoped BigOperators ENNReal
open Set MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open H6CoordinateAlgebra H6DensityTransform H6VectorChangeOfVariables

/-- Coordinatewise squaring of positive Takagi radii. -/
def takagiRadiusSquareVector (N : ℕ) (rho : Fin N → ℝ) : Fin N → ℝ :=
  fun i ↦ (rho i) ^ 2

/-- Product chart `(0,∞)^N -> (0,∞)^N`, `rho_i ↦ rho_i^2`. -/
def takagiRadiusSquareCoordVector (N : ℕ) :
    OpenPartialHomeomorph (Fin N → ℝ) (Fin N → ℝ) :=
  OpenPartialHomeomorph.pi fun _ : Fin N ↦ Real.sqPartialHomeomorph

@[simp]
theorem takagiRadiusSquareCoordVector_apply
    (N : ℕ) (rho : Fin N → ℝ) :
    takagiRadiusSquareCoordVector N rho =
      takagiRadiusSquareVector N rho := by
  rfl

@[simp]
theorem takagiRadiusSquareCoordVector_source (N : ℕ) :
    (takagiRadiusSquareCoordVector N).source = openPositiveOrthant N := by
  ext rho
  simp [takagiRadiusSquareCoordVector, Real.sqPartialHomeomorph,
    openPositiveOrthant]

@[simp]
theorem takagiRadiusSquareCoordVector_target (N : ℕ) :
    (takagiRadiusSquareCoordVector N).target = openPositiveOrthant N := by
  ext lambda
  simp [takagiRadiusSquareCoordVector, Real.sqPartialHomeomorph,
    openPositiveOrthant]

theorem measurable_takagiRadiusSquareVector (N : ℕ) :
    Measurable (takagiRadiusSquareVector N) := by
  unfold takagiRadiusSquareVector
  fun_prop

open ContinuousLinearMap in
/-- Derivative of the coordinatewise square map. -/
noncomputable def fderivTakagiRadiusSquareVector
    {N : ℕ} (rho : Fin N → ℝ) :
    (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) :=
  pi fun i ↦
    (toSpanSingleton ℝ (2 * rho i)).comp (proj i)

theorem hasDerivAt_takagiRadiusSquare (rho : ℝ) :
    HasDerivAt (fun x : ℝ ↦ x ^ 2) (2 * rho) rho := by
  simpa using hasDerivAt_pow 2 rho

/-- The coordinatewise square derivative is diagonal with entries
`2*rho_i`. -/
theorem hasFDerivAt_takagiRadiusSquareVector
    {N : ℕ} (rho : Fin N → ℝ) :
    HasFDerivAt (takagiRadiusSquareVector N)
      (fderivTakagiRadiusSquareVector rho) rho := by
  change HasFDerivAt (fun y i ↦ (y i) ^ 2)
    (fderivTakagiRadiusSquareVector rho) rho
  rw [fderivTakagiRadiusSquareVector, hasFDerivAt_pi]
  intro i
  simpa only [Function.comp_def] using
    (HasFDerivAt.comp
      (𝕜 := ℝ) (E := Fin N → ℝ) (F := ℝ) (G := ℝ)
      (f := fun y : Fin N → ℝ ↦ y i)
      (f' := ContinuousLinearMap.proj i)
      (g := fun x : ℝ ↦ x ^ 2)
      (g' := ContinuousLinearMap.toSpanSingleton ℝ (2 * rho i))
      (x := rho)
      (hasDerivAt_takagiRadiusSquare (rho i)).hasFDerivAt
      (hasFDerivAt_apply i rho))

/-- Real determinant of the square-map derivative. -/
def takagiRadiusSquareJacobian (N : ℕ) (rho : Fin N → ℝ) : ℝ :=
  ∏ i : Fin N, 2 * rho i

theorem det_fderivTakagiRadiusSquareVector
    {N : ℕ} (rho : Fin N → ℝ) :
    (fderivTakagiRadiusSquareVector rho).det =
      takagiRadiusSquareJacobian N rho := by
  simp_rw [fderivTakagiRadiusSquareVector, ContinuousLinearMap.det_pi,
    ContinuousLinearMap.det_toSpanSingleton]
  rfl

theorem takagiRadiusSquareJacobian_pos
    {N : ℕ} {rho : Fin N → ℝ}
    (hrho : rho ∈ openPositiveOrthant N) :
    0 < takagiRadiusSquareJacobian N rho := by
  classical
  unfold takagiRadiusSquareJacobian
  exact Finset.prod_pos fun i _hi ↦ mul_pos zero_lt_two (hrho i)

/-- Exact vector change of variables from positive radii to squared radii. -/
theorem lintegral_takagiRadiusSquareVector
    (N : ℕ) (f : (Fin N → ℝ) → ℝ≥0∞) :
    (∫⁻ lambda in openPositiveOrthant N, f lambda) =
      ∫⁻ rho in openPositiveOrthant N,
        ENNReal.ofReal (takagiRadiusSquareJacobian N rho) *
          f (takagiRadiusSquareVector N rho) := by
  conv_lhs =>
    rw [← takagiRadiusSquareCoordVector_target]
  conv_rhs =>
    rw [← takagiRadiusSquareCoordVector_source]
  calc
    (∫⁻ lambda in (takagiRadiusSquareCoordVector N).target, f lambda) =
        ∫⁻ lambda in
          takagiRadiusSquareCoordVector N ''
            (takagiRadiusSquareCoordVector N).source,
          f lambda := by
      rw [(takagiRadiusSquareCoordVector N).image_source_eq_target]
    _ = ∫⁻ rho in (takagiRadiusSquareCoordVector N).source,
        ENNReal.ofReal |(fderivTakagiRadiusSquareVector rho).det| *
          f (takagiRadiusSquareCoordVector N rho) := by
      change (∫⁻ lambda in takagiRadiusSquareVector N ''
          (takagiRadiusSquareCoordVector N).source, f lambda) =
        ∫⁻ rho in (takagiRadiusSquareCoordVector N).source,
          ENNReal.ofReal |(fderivTakagiRadiusSquareVector rho).det| *
            f (takagiRadiusSquareVector N rho)
      rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
        (takagiRadiusSquareCoordVector N).open_source.measurableSet
        (fun rho _hrho ↦
          (hasFDerivAt_takagiRadiusSquareVector rho).hasFDerivWithinAt)
        (takagiRadiusSquareCoordVector N).injOn]
    _ = ∫⁻ rho in (takagiRadiusSquareCoordVector N).source,
        ENNReal.ofReal (takagiRadiusSquareJacobian N rho) *
          f (takagiRadiusSquareVector N rho) := by
      refine setLIntegral_congr_fun
        (takagiRadiusSquareCoordVector N).open_source.measurableSet
        (fun rho hrho ↦ ?_)
      rw [det_fderivTakagiRadiusSquareVector,
        abs_of_pos (takagiRadiusSquareJacobian_pos (by simpa using hrho)),
        takagiRadiusSquareCoordVector_apply]

/-! ## The conventional radius density and cancellation -/

def takagiRadiusProduct (N : ℕ) (rho : Fin N → ℝ) : ℝ :=
  ∏ i : Fin N, rho i

/-- The conventional unsquared Takagi radial weight. -/
def takagiRadiusJacobianWeight (N : ℕ) (rho : Fin N → ℝ) : ℝ :=
  takagiRadiusProduct N rho *
    vandermondeAbs N (takagiRadiusSquareVector N rho)

def takagiRadiusJacobianDensity (N : ℕ)
    (rho : Fin N → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (takagiRadiusJacobianWeight N rho)

def takagiRadiusJacobianMeasure (N : ℕ) : Measure (Fin N → ℝ) :=
  (volume.restrict (openPositiveOrthant N)).withDensity
    (takagiRadiusJacobianDensity N)

/-- The factor introduced by `lambda_i = rho_i^2`. -/
def takagiSquareScale (N : ℕ) : NNReal :=
  ((2 : NNReal) ^ N)⁻¹

theorem takagiSquareScale_ne_zero (N : ℕ) :
    takagiSquareScale N ≠ 0 := by
  simp [takagiSquareScale]

theorem takagiRadiusSquareJacobian_eq_two_pow_mul
    (N : ℕ) (rho : Fin N → ℝ) :
    takagiRadiusSquareJacobian N rho =
      (2 : ℝ) ^ N * takagiRadiusProduct N rho := by
  classical
  unfold takagiRadiusSquareJacobian takagiRadiusProduct
  rw [Finset.prod_mul_distrib]
  simp

theorem takagiRadiusProduct_nonneg
    {N : ℕ} {rho : Fin N → ℝ}
    (hrho : rho ∈ openPositiveOrthant N) :
    0 ≤ takagiRadiusProduct N rho := by
  classical
  unfold takagiRadiusProduct
  exact Finset.prod_nonneg fun i _hi ↦ (hrho i).le

theorem measurable_takagiRadiusProduct (N : ℕ) :
    Measurable (takagiRadiusProduct N) := by
  classical
  unfold takagiRadiusProduct
  exact Finset.measurable_prod _ fun i _hi ↦ measurable_pi_apply i

theorem measurable_takagiRadiusSquareJacobian (N : ℕ) :
    Measurable (takagiRadiusSquareJacobian N) := by
  classical
  unfold takagiRadiusSquareJacobian
  exact Finset.measurable_prod _ fun i _hi ↦
    measurable_const.mul (measurable_pi_apply i)

theorem measurable_takagiRadiusJacobianWeight (N : ℕ) :
    Measurable (takagiRadiusJacobianWeight N) :=
  (measurable_takagiRadiusProduct N).mul
    ((continuous_vandermondeAbs N).measurable.comp
      (measurable_takagiRadiusSquareVector N))

theorem measurable_takagiRadiusJacobianDensity (N : ℕ) :
    Measurable (takagiRadiusJacobianDensity N) :=
  ENNReal.measurable_ofReal.comp
    (measurable_takagiRadiusJacobianWeight N)

/-- Pointwise density identity showing that the radius product is exactly
cancelled by the square-map Jacobian. -/
theorem takagiRadiusDensity_eq_scale_mul_jacobian_flat
    {N : ℕ} {rho : Fin N → ℝ}
    (hrho : rho ∈ openPositiveOrthant N) :
    takagiRadiusJacobianDensity N rho =
      (takagiSquareScale N : ℝ≥0∞) *
        (ENNReal.ofReal (takagiRadiusSquareJacobian N rho) *
          takagiFlatEigenvalueDensity N
            (takagiRadiusSquareVector N rho)) := by
  have hprod := takagiRadiusProduct_nonneg hrho
  have hvand : 0 ≤ vandermondeAbs N
      (takagiRadiusSquareVector N rho) :=
    vandermondeAbs_nonneg_h6 N _
  unfold takagiRadiusJacobianDensity takagiRadiusJacobianWeight
    takagiFlatEigenvalueDensity
  rw [takagiRadiusSquareJacobian_eq_two_pow_mul]
  rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (2 : ℝ) ^ N)]
  rw [ENNReal.ofReal_mul hprod]
  simp only [ENNReal.ofReal_pow (by positivity : 0 ≤ (2 : ℝ)),
    ENNReal.ofReal_ofNat]
  change ENNReal.ofReal (takagiRadiusProduct N rho) *
      ENNReal.ofReal (vandermondeAbs N
        (takagiRadiusSquareVector N rho)) =
    ((((2 : NNReal) ^ N)⁻¹ : NNReal) : ℝ≥0∞) *
      (((2 : ℝ≥0∞) ^ N *
        ENNReal.ofReal (takagiRadiusProduct N rho)) *
          ENNReal.ofReal (vandermondeAbs N
            (takagiRadiusSquareVector N rho)))
  rw [ENNReal.coe_inv
    (pow_ne_zero N (by norm_num : (2 : NNReal) ≠ 0))]
  have hcoe : ((((2 : NNReal) ^ N) : NNReal) : ℝ≥0∞) =
      (2 : ℝ≥0∞) ^ N := by norm_cast
  rw [hcoe]
  symm
  calc
    ((2 : ℝ≥0∞) ^ N)⁻¹ *
          (((2 : ℝ≥0∞) ^ N *
            ENNReal.ofReal (takagiRadiusProduct N rho)) *
              ENNReal.ofReal (vandermondeAbs N
                (takagiRadiusSquareVector N rho))) =
        (((2 : ℝ≥0∞) ^ N)⁻¹ * (2 : ℝ≥0∞) ^ N) *
          (ENNReal.ofReal (takagiRadiusProduct N rho) *
            ENNReal.ofReal (vandermondeAbs N
              (takagiRadiusSquareVector N rho))) := by ac_rfl
    _ = ENNReal.ofReal (takagiRadiusProduct N rho) *
          ENNReal.ofReal (vandermondeAbs N
            (takagiRadiusSquareVector N rho)) := by
      rw [ENNReal.inv_mul_cancel
        (pow_ne_zero N (by norm_num : (2 : ℝ≥0∞) ≠ 0))
        (by simp), one_mul]

/-- The full measure-level square-coordinate Jacobian.  The conventional
radius law pushes to the flat squared-Takagi law with only the harmless
constant `2^(-N)`. -/
theorem map_takagiRadiusJacobianMeasure_eq_flat
    (N : ℕ) :
    Measure.map (takagiRadiusSquareVector N)
        (takagiRadiusJacobianMeasure N) =
      (takagiSquareScale N : ℝ≥0∞) •
        takagiFlatEigenvalueRadialMeasure N := by
  apply Measure.ext_of_lintegral _
  intro g hg
  rw [lintegral_map hg (measurable_takagiRadiusSquareVector N)]
  unfold takagiRadiusJacobianMeasure
  change (∫⁻ a, (g ∘ takagiRadiusSquareVector N) a ∂
      (volume.restrict (openPositiveOrthant N)).withDensity
        (takagiRadiusJacobianDensity N)) = _
  rw [lintegral_withDensity_eq_lintegral_mul₀
    (measurable_takagiRadiusJacobianDensity N).aemeasurable
    ((hg.comp (measurable_takagiRadiusSquareVector N)).aemeasurable)]
  rw [lintegral_smul_measure]
  unfold takagiFlatEigenvalueRadialMeasure
  rw [lintegral_withDensity_eq_lintegral_mul₀
    (measurable_takagiFlatEigenvalueDensity N).aemeasurable
    hg.aemeasurable]
  change (∫⁻ rho in openPositiveOrthant N,
      takagiRadiusJacobianDensity N rho *
        g (takagiRadiusSquareVector N rho)) =
    (takagiSquareScale N : ℝ≥0∞) *
      ∫⁻ lambda in openPositiveOrthant N,
        takagiFlatEigenvalueDensity N lambda * g lambda
  rw [lintegral_takagiRadiusSquareVector N
    (fun lambda ↦ takagiFlatEigenvalueDensity N lambda * g lambda)]
  have hmeas : Measurable (fun rho : Fin N → ℝ ↦
      ENNReal.ofReal (takagiRadiusSquareJacobian N rho) *
        (takagiFlatEigenvalueDensity N
          (takagiRadiusSquareVector N rho) *
            g (takagiRadiusSquareVector N rho))) :=
    (ENNReal.measurable_ofReal.comp
      (measurable_takagiRadiusSquareJacobian N)).mul
      (((measurable_takagiFlatEigenvalueDensity N).comp
        (measurable_takagiRadiusSquareVector N)).mul
          (hg.comp (measurable_takagiRadiusSquareVector N)))
  rw [← lintegral_const_mul
    (μ := volume.restrict (openPositiveOrthant N))
    (takagiSquareScale N : ℝ≥0∞) hmeas]
  refine setLIntegral_congr_fun
    (measurableSet_openPositiveOrthant_h6 N) (fun rho hrho ↦ ?_)
  rw [takagiRadiusDensity_eq_scale_mul_jacobian_flat hrho]
  ac_rfl

/-! ## Conventional unsquared Takagi--Weyl contract -/

/-- **CONDITIONAL primitive radius-coordinate Takagi--Weyl contract.**
This is the standard source form of the missing coarea theorem.  Its radial
density is `prod_i rho_i * |Delta(rho^2)|`.  It is independent of `K`, H5,
Wishart matrices, trace vectors, and H6. -/
structure TakagiWeylRadiusContract (N : ℕ) where
  radius : ConcreteMatrixState N → (Fin N → ℝ)
  measurable_radius : Measurable radius
  unitary : ConcreteMatrixState N → Matrix.unitaryGroup (Fin N) ℂ
  representation : ∀ᵐ C ∂complexSymmetricMatrixVolume N,
    C = h6TakagiForward (unitary C)
      (takagiRadiusSquareVector N (radius C))
  orbitConstant : NNReal
  orbitConstant_ne_zero : orbitConstant ≠ 0
  radius_radial_law :
    Measure.map radius (complexSymmetricMatrixVolume N) =
      (orbitConstant : ℝ≥0∞) • takagiRadiusJacobianMeasure N

/-- The proved square-coordinate Jacobian converts the conventional radius
coarea theorem to the flat squared-Takagi theorem, absorbing `2^(-N)` into
the harmless orbit constant. -/
def TakagiWeylRadiusContract.toTakagiWeylFlatContract
    {N : ℕ} (h : TakagiWeylRadiusContract N) :
    TakagiWeylFlatContract N where
  spectrum := fun C ↦ takagiRadiusSquareVector N (h.radius C)
  measurable_spectrum :=
    (measurable_takagiRadiusSquareVector N).comp h.measurable_radius
  unitary := h.unitary
  representation := h.representation
  orbitConstant := h.orbitConstant * takagiSquareScale N
  orbitConstant_ne_zero :=
    mul_ne_zero h.orbitConstant_ne_zero (takagiSquareScale_ne_zero N)
  flat_radial_law := by
    calc
      Measure.map (fun C ↦ takagiRadiusSquareVector N (h.radius C))
          (complexSymmetricMatrixVolume N) =
        Measure.map (takagiRadiusSquareVector N)
          (Measure.map h.radius (complexSymmetricMatrixVolume N)) := by
        simpa only [Function.comp_def] using
          (Measure.map_map (measurable_takagiRadiusSquareVector N)
            h.measurable_radius).symm
      _ = Measure.map (takagiRadiusSquareVector N)
          ((h.orbitConstant : ℝ≥0∞) •
            takagiRadiusJacobianMeasure N) := by
        rw [h.radius_radial_law]
      _ = (h.orbitConstant : ℝ≥0∞) •
          Measure.map (takagiRadiusSquareVector N)
            (takagiRadiusJacobianMeasure N) := by
        rw [Measure.map_smul]
      _ = (h.orbitConstant : ℝ≥0∞) •
          ((takagiSquareScale N : ℝ≥0∞) •
            takagiFlatEigenvalueRadialMeasure N) := by
        rw [map_takagiRadiusJacobianMeasure_eq_flat]
      _ = ((h.orbitConstant * takagiSquareScale N : NNReal) : ℝ≥0∞) •
          takagiFlatEigenvalueRadialMeasure N := by
        rw [smul_smul]
        rfl

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
