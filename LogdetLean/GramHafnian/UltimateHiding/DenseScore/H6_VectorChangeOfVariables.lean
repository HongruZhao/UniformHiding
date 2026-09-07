import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H6_DensityTransform
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-!
# H6 vector change of variables

This file upgrades the elementary coordinate algebra to the exact
finite-dimensional Jacobian formula used in H6.  It is independent of the
Takagi--Weyl and Muirhead random-matrix inputs.
-/

open scoped BigOperators ENNReal
open Set MeasureTheory

namespace H6VectorChangeOfVariables

noncomputable section

open H6CoordinateAlgebra H6DensityTransform

/-- The scalar open partial homeomorphism
`lambda ↦ lambda / (1-lambda)` from `(0,1)` onto `(0,∞)`. -/
def betaPrimeCoord : OpenPartialHomeomorph ℝ ℝ where
  toFun := betaPrimeForward
  invFun := betaPrimeInverse
  source := Ioo (0 : ℝ) 1
  target := Ioi (0 : ℝ)
  map_target' := fun _x hx ↦ betaPrimeInverse_mem_Ioo hx
  map_source' := fun _lambda hlambda ↦
    betaPrimeForward_pos_iff.mpr hlambda
  right_inv' := by
    intro x hx
    change 0 < x at hx
    exact betaPrimeForward_inverse (by linarith)
  left_inv' := by
    intro lambda hlambda
    exact betaPrimeInverse_forward (by linarith [hlambda.2])
  open_source := isOpen_Ioo
  open_target := isOpen_Ioi
  continuousOn_invFun := by
    unfold betaPrimeInverse
    refine continuousOn_id.div (continuousOn_const.add continuousOn_id) ?_
    intro x hx
    change 0 < x at hx
    exact (by linarith : 1 + x ≠ 0)
  continuousOn_toFun := by
    unfold betaPrimeForward
    refine continuousOn_id.div (continuousOn_const.sub continuousOn_id) ?_
    intro lambda hlambda
    exact (sub_pos.mpr hlambda.2).ne'

@[simp]
theorem betaPrimeCoord_apply (lambda : ℝ) :
    betaPrimeCoord lambda = betaPrimeForward lambda := rfl

@[simp]
theorem betaPrimeCoord_symm_apply (x : ℝ) :
    betaPrimeCoord.symm x = betaPrimeInverse x := rfl

/-- Coordinatewise product of the scalar beta-to-beta-prime chart. -/
def betaPrimeCoordVector (N : ℕ) :
    OpenPartialHomeomorph (Fin N → ℝ) (Fin N → ℝ) :=
  OpenPartialHomeomorph.pi fun _ : Fin N ↦ betaPrimeCoord

@[simp]
theorem betaPrimeCoordVector_apply (N : ℕ) (lambda : Fin N → ℝ) :
    betaPrimeCoordVector N lambda = betaPrimeForwardVector N lambda := by
  rfl

@[simp]
theorem betaPrimeCoordVector_symm_apply (N : ℕ) (x : Fin N → ℝ) :
    (betaPrimeCoordVector N).symm x = betaPrimeInverseVector N x := by
  rfl

@[simp]
theorem betaPrimeCoordVector_source (N : ℕ) :
    (betaPrimeCoordVector N).source = openUnitCube N := by
  ext lambda
  simp [betaPrimeCoordVector, betaPrimeCoord, openUnitCube]

@[simp]
theorem betaPrimeCoordVector_target (N : ℕ) :
    (betaPrimeCoordVector N).target = openPositiveOrthant N := by
  ext x
  simp [betaPrimeCoordVector, betaPrimeCoord, openPositiveOrthant]

open ContinuousLinearMap in
/-- Derivative of the coordinatewise inverse map at `x`. -/
noncomputable def fderivBetaPrimeCoordVectorSymm
    {N : ℕ} (x : Fin N → ℝ) :
    (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) :=
  pi fun i ↦
    (toSpanSingleton ℝ (betaPrimeInverseJacobian (x i))).comp (proj i)

/-- Coordinatewise inverse derivative on the positive orthant. -/
theorem hasFDerivAt_betaPrimeCoordVector_symm
    {N : ℕ} {x : Fin N → ℝ} (hx : x ∈ openPositiveOrthant N) :
    HasFDerivAt (betaPrimeCoordVector N).symm
      (fderivBetaPrimeCoordVectorSymm x) x := by
  change HasFDerivAt (fun y i ↦ betaPrimeInverse (y i))
    (fderivBetaPrimeCoordVectorSymm x) x
  rw [fderivBetaPrimeCoordVectorSymm, hasFDerivAt_pi]
  intro i
  exact HasFDerivAt.comp x
    (hasDerivAt_betaPrimeInverse (by linarith [hx i])).hasFDerivAt
    (hasFDerivAt_apply i x)

/-- Determinant of the inverse derivative. -/
theorem det_fderivBetaPrimeCoordVectorSymm
    {N : ℕ} (x : Fin N → ℝ) :
    (fderivBetaPrimeCoordVectorSymm x).det =
      inverseJacobianProduct N x := by
  simp_rw [fderivBetaPrimeCoordVectorSymm, ContinuousLinearMap.det_pi,
    ContinuousLinearMap.det_toSpanSingleton]
  rfl

theorem inverseJacobianProduct_pos
    {N : ℕ} {x : Fin N → ℝ} (hx : x ∈ openPositiveOrthant N) :
    0 < inverseJacobianProduct N x := by
  classical
  unfold inverseJacobianProduct
  exact Finset.prod_pos fun i _hi ↦ betaPrimeInverseJacobian_pos (hx i)

/-- Nonnegative change of variables for the full finite vector. -/
theorem lintegral_comp_betaPrimeCoordVector_symm
    (N : ℕ) (f : (Fin N → ℝ) → ℝ≥0∞) :
    (∫⁻ x in openPositiveOrthant N,
        ENNReal.ofReal (inverseJacobianProduct N x) *
          f (betaPrimeInverseVector N x)) =
      ∫⁻ lambda in openUnitCube N, f lambda := by
  rw [← betaPrimeCoordVector_target, ← betaPrimeCoordVector_source]
  symm
  calc
    (∫⁻ lambda in (betaPrimeCoordVector N).source, f lambda) =
        ∫⁻ lambda in
          (betaPrimeCoordVector N).symm '' (betaPrimeCoordVector N).target,
          f lambda := by
      rw [(betaPrimeCoordVector N).symm_image_target_eq_source]
    _ = ∫⁻ x in (betaPrimeCoordVector N).target,
        ENNReal.ofReal |(fderivBetaPrimeCoordVectorSymm x).det| *
          f ((betaPrimeCoordVector N).symm x) := by
      rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
        (betaPrimeCoordVector N).open_target.measurableSet
        (fun x hx ↦ (hasFDerivAt_betaPrimeCoordVector_symm
          (by simpa using hx)).hasFDerivWithinAt)
        (betaPrimeCoordVector N).symm.injOn]
    _ = ∫⁻ x in (betaPrimeCoordVector N).target,
        ENNReal.ofReal (inverseJacobianProduct N x) *
          f (betaPrimeInverseVector N x) := by
      refine setLIntegral_congr_fun
        (betaPrimeCoordVector N).open_target.measurableSet (fun x hx ↦ ?_)
      rw [det_fderivBetaPrimeCoordVectorSymm,
        abs_of_pos (inverseJacobianProduct_pos (by simpa using hx)),
        betaPrimeCoordVector_symm_apply]

/-- The exact density transformation, already promoted from pointwise algebra
to an equality of all nonnegative test-function integrals. -/
theorem lintegral_coeWeight_comp_forward_eq_betaPrimeWeight
    {N K : ℕ} (hN : 1 ≤ N) (g : (Fin N → ℝ) → ℝ≥0∞) :
    (∫⁻ lambda in openUnitCube N,
        ENNReal.ofReal
            (coeEigenvalueWeight N (coeEigenvalueExponent N K) lambda) *
          g (betaPrimeForwardVector N lambda)) =
      ∫⁻ x in openPositiveOrthant N,
        ENNReal.ofReal
            (betaPrimeEigenvalueWeight N (((K : ℝ) + 1) / 2) x) *
          g x := by
  calc
    (∫⁻ lambda in openUnitCube N,
        ENNReal.ofReal
            (coeEigenvalueWeight N (coeEigenvalueExponent N K) lambda) *
          g (betaPrimeForwardVector N lambda)) =
      ∫⁻ x in openPositiveOrthant N,
        ENNReal.ofReal (inverseJacobianProduct N x) *
          (ENNReal.ofReal
              (coeEigenvalueWeight N (coeEigenvalueExponent N K)
                (betaPrimeInverseVector N x)) *
            g (betaPrimeForwardVector N (betaPrimeInverseVector N x))) := by
      exact (lintegral_comp_betaPrimeCoordVector_symm N
        (fun lambda ↦
          ENNReal.ofReal
              (coeEigenvalueWeight N (coeEigenvalueExponent N K) lambda) *
            g (betaPrimeForwardVector N lambda))).symm
    _ = ∫⁻ x in openPositiveOrthant N,
        ENNReal.ofReal
            (betaPrimeEigenvalueWeight N (((K : ℝ) + 1) / 2) x) *
          g x := by
      refine setLIntegral_congr_fun
        (by simpa [openPositiveOrthant] using
          (betaPrimeCoordVector N).open_target.measurableSet)
        (fun x hx ↦ ?_)
      rw [betaPrimeForwardVector_inverseVector hx]
      have hJ : 0 ≤ inverseJacobianProduct N x :=
        (inverseJacobianProduct_pos hx).le
      calc
        ENNReal.ofReal (inverseJacobianProduct N x) *
              (ENNReal.ofReal
                  (coeEigenvalueWeight N (coeEigenvalueExponent N K)
                    (betaPrimeInverseVector N x)) * g x) =
            ENNReal.ofReal
                (inverseJacobianProduct N x *
                  coeEigenvalueWeight N (coeEigenvalueExponent N K)
                    (betaPrimeInverseVector N x)) * g x := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hJ]
        _ = ENNReal.ofReal
                (coeEigenvalueWeight N (coeEigenvalueExponent N K)
                    (betaPrimeInverseVector N x) *
                  inverseJacobianProduct N x) * g x := by
          rw [mul_comm (inverseJacobianProduct N x)]
        _ = ENNReal.ofReal
                (betaPrimeEigenvalueWeight N (((K : ℝ) + 1) / 2) x) *
              g x := by
          rw [coeWeight_mul_inverseJacobian_eq_betaPrimeWeight hN hx]

/-! ## Measure-level density transport -/

def coeEigenvalueDensity (N K : ℕ) (lambda : Fin N → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal
    (coeEigenvalueWeight N (coeEigenvalueExponent N K) lambda)

def betaPrimeEigenvalueDensity (N K : ℕ) (x : Fin N → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal
    (betaPrimeEigenvalueWeight N (((K : ℝ) + 1) / 2) x)

theorem continuous_vandermondeAbs (N : ℕ) :
    Continuous (vandermondeAbs N) := by
  unfold vandermondeAbs
  fun_prop

theorem continuousOn_unitBoundaryRpowProduct
    (N : ℕ) (alpha : ℝ) :
    ContinuousOn (unitBoundaryRpowProduct N alpha) (openUnitCube N) := by
  unfold unitBoundaryRpowProduct
  simpa using continuousOn_finsetProd (Finset.univ : Finset (Fin N))
    (fun i _hi ↦
      (continuous_const.sub (continuous_apply i)).continuousOn.rpow_const
        (fun lambda hlambda ↦
          Or.inl (sub_pos.mpr (hlambda i).2).ne'))

theorem continuousOn_positiveCoordinateRpowProduct
    (N : ℕ) (q : ℝ) :
    ContinuousOn (positiveCoordinateRpowProduct N q)
      (openPositiveOrthant N) := by
  unfold positiveCoordinateRpowProduct
  simpa using continuousOn_finsetProd (Finset.univ : Finset (Fin N))
    (fun i _hi ↦
      ((continuous_const :
          Continuous (fun _ : (Fin N → ℝ) ↦ (1 : ℝ))).add
        (continuous_apply i)).continuousOn.rpow_const
        (fun x hx ↦ Or.inl (by linarith [hx i] : 1 + x i ≠ 0)))

theorem continuousOn_coeEigenvalueWeight (N K : ℕ) :
    ContinuousOn
      (coeEigenvalueWeight N (coeEigenvalueExponent N K))
      (openUnitCube N) :=
  (continuous_vandermondeAbs N).continuousOn.mul
    (continuousOn_unitBoundaryRpowProduct N (coeEigenvalueExponent N K))

theorem continuousOn_betaPrimeEigenvalueWeight (N K : ℕ) :
    ContinuousOn
      (betaPrimeEigenvalueWeight N (((K : ℝ) + 1) / 2))
      (openPositiveOrthant N) :=
  (continuous_vandermondeAbs N).continuousOn.mul
    (continuousOn_positiveCoordinateRpowProduct N
      (-(((K : ℝ) + 1) / 2)))

theorem aemeasurable_coeEigenvalueDensity (N K : ℕ) :
    AEMeasurable (coeEigenvalueDensity N K)
      (volume.restrict (openUnitCube N)) := by
  apply ContinuousOn.aemeasurable
    (ENNReal.continuous_ofReal.comp_continuousOn
      (continuousOn_coeEigenvalueWeight N K))
  simpa [← betaPrimeCoordVector_source] using
    (betaPrimeCoordVector N).open_source.measurableSet

theorem aemeasurable_betaPrimeEigenvalueDensity (N K : ℕ) :
    AEMeasurable (betaPrimeEigenvalueDensity N K)
      (volume.restrict (openPositiveOrthant N)) := by
  apply ContinuousOn.aemeasurable
    (ENNReal.continuous_ofReal.comp_continuousOn
      (continuousOn_betaPrimeEigenvalueWeight N K))
  simpa [← betaPrimeCoordVector_target] using
    (betaPrimeCoordVector N).open_target.measurableSet

/-- The unnormalized Jacobi/Takagi radial measure supplied by the H5 density
after a Takagi--Weyl disintegration. -/
def coeEigenvalueRadialMeasure (N K : ℕ) : Measure (Fin N → ℝ) :=
  (volume.restrict (openUnitCube N)).withDensity
    (coeEigenvalueDensity N K)

/-- The matching unnormalized real matrix beta-II eigenvalue measure. -/
def betaPrimeEigenvalueRadialMeasure (N K : ℕ) : Measure (Fin N → ℝ) :=
  (volume.restrict (openPositiveOrthant N)).withDensity
    (betaPrimeEigenvalueDensity N K)

/-- Exact pushforward equality of the two unnormalized radial measures.  In
particular, no Selberg normalization constant is needed: both masses agree by
the same coordinate change. -/
theorem map_coeEigenvalueRadialMeasure_eq_betaPrime
    {N K : ℕ} (hN : 1 ≤ N) :
    Measure.map (betaPrimeForwardVector N)
        (coeEigenvalueRadialMeasure N K) =
      betaPrimeEigenvalueRadialMeasure N K := by
  apply Measure.ext_of_lintegral _
  intro g hg
  unfold coeEigenvalueRadialMeasure betaPrimeEigenvalueRadialMeasure
  rw [lintegral_map hg (measurable_betaPrimeForwardVector N)]
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable₀ _
    (aemeasurable_coeEigenvalueDensity N K)
    (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable₀ _
    (aemeasurable_betaPrimeEigenvalueDensity N K)
    (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  simpa only [coeEigenvalueDensity, betaPrimeEigenvalueDensity,
    Function.comp_apply, Pi.mul_apply] using
    lintegral_coeWeight_comp_forward_eq_betaPrimeWeight hN g

/-- Canonical normalization of the unnormalized COE radial measure.  This
definition is totalized: if the raw mass were zero or infinite, the resulting
measure would be zero.  A source-density theorem equating a probability law to
this measure therefore carries the required finiteness/nondegeneracy content. -/
def normalizedCOEEigenvalueRadialMeasure (N K : ℕ) : Measure (Fin N → ℝ) :=
  ((coeEigenvalueRadialMeasure N K) Set.univ)⁻¹ •
    coeEigenvalueRadialMeasure N K

/-- Canonical normalization of the unnormalized real beta-II radial measure. -/
def normalizedBetaPrimeEigenvalueRadialMeasure (N K : ℕ) :
    Measure (Fin N → ℝ) :=
  ((betaPrimeEigenvalueRadialMeasure N K) Set.univ)⁻¹ •
    betaPrimeEigenvalueRadialMeasure N K

/-- The proved coordinate change also transports the canonical normalized
radial measures.  Hence the conditional source theorems need not assume a
shared, separately computed Selberg normalizer. -/
theorem map_normalizedCOEEigenvalueRadialMeasure_eq_normalizedBetaPrime
    {N K : ℕ} (hN : 1 ≤ N) :
    Measure.map (betaPrimeForwardVector N)
        (normalizedCOEEigenvalueRadialMeasure N K) =
      normalizedBetaPrimeEigenvalueRadialMeasure N K := by
  have hraw := map_coeEigenvalueRadialMeasure_eq_betaPrime
    (N := N) (K := K) hN
  have hmass :
      coeEigenvalueRadialMeasure N K Set.univ =
        betaPrimeEigenvalueRadialMeasure N K Set.univ := by
    rw [← hraw]
    rw [Measure.map_apply (measurable_betaPrimeForwardVector N)
      MeasurableSet.univ]
    simp
  unfold normalizedCOEEigenvalueRadialMeasure
    normalizedBetaPrimeEigenvalueRadialMeasure
  rw [Measure.map_smul, hraw, hmass]

end

end H6VectorChangeOfVariables
