import LogdetLean.GramHafnian.UltimateHiding.Dense.H1_UnitarySphereAction
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-!
# The last column of a Haar unitary is uniform on the complex sphere

This file proves the elementary homogeneous-space fact needed by H1.  The
last column is the orbit of the last coordinate vector under the left action
of `U(M)`.  Normalized Haar invariance and transitivity of this action imply
that its law is the normalized surface measure on the complex unit sphere.
-/

open scoped ENNReal MeasureTheory Matrix BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Metric

namespace LogdetLean.GramHafnian.UltimateHiding.Dense

noncomputable section

open LogdetLean.GramHafnian.LocalAnticoncentration

local instance h1HaarLastMatrixBorelSpace (N K : ℕ) :
    BorelSpace (Matrix (Fin N) (Fin K) ℂ) := by
  exact inferInstanceAs (BorelSpace (Fin N → Fin K → ℂ))

/-- The final coordinate of a nonempty `Fin M`. -/
def haarLastColumnIndex {M : ℕ} (hM : 1 ≤ M) : Fin M :=
  ⟨M - 1, by omega⟩

/-- The final standard coordinate vector, as a point of the complex unit
sphere. -/
def haarLastColumnBaseSphere {M : ℕ} (hM : 1 ≤ M) :
    ComplexUnitSphere M :=
  ⟨EuclideanSpace.single (haarLastColumnIndex hM) (1 : ℂ), by
    rw [mem_sphere_zero_iff_norm]
    simp⟩

/-- The last column of a unitary matrix, regarded as a unit vector. -/
def haarLastColumnSphere {M : ℕ} (hM : 1 ≤ M) :
    Matrix.unitaryGroup (Fin M) ℂ → ComplexUnitSphere M :=
  fun U ↦ h1UnitarySphereAction U (haarLastColumnBaseSphere hM)

@[simp]
theorem haarLastColumnSphere_apply {M : ℕ} (hM : 1 ≤ M)
    (U : Matrix.unitaryGroup (Fin M) ℂ) (i : Fin M) :
    (haarLastColumnSphere hM U).1 i =
      (U : Matrix (Fin M) (Fin M) ℂ) i (haarLastColumnIndex hM) := by
  simp [haarLastColumnSphere, h1UnitarySphereAction_val,
    haarLastColumnBaseSphere]

theorem continuous_haarLastColumnSphere {M : ℕ} (hM : 1 ≤ M) :
    Continuous (haarLastColumnSphere hM) := by
  apply Continuous.subtype_mk
  change Continuous (fun U : Matrix.unitaryGroup (Fin M) ℂ ↦
    WithLp.toLp 2 (Matrix.mulVec
      (U : Matrix (Fin M) (Fin M) ℂ)
      (WithLp.ofLp (haarLastColumnBaseSphere hM).1)))
  fun_prop

theorem measurable_haarLastColumnSphere {M : ℕ} (hM : 1 ≤ M) :
    Measurable (haarLastColumnSphere hM) :=
  (continuous_haarLastColumnSphere hM).measurable

theorem unitarySphereAction_comp {M : ℕ}
    (U V : Matrix.unitaryGroup (Fin M) ℂ)
    (v : ComplexUnitSphere M) :
    h1UnitarySphereAction U (h1UnitarySphereAction V v) =
      h1UnitarySphereAction (U * V) v := by
  apply Subtype.ext
  change WithLp.toLp 2
      ((U : Matrix (Fin M) (Fin M) ℂ) *ᵥ
        ((V : Matrix (Fin M) (Fin M) ℂ) *ᵥ WithLp.ofLp v.1)) =
    WithLp.toLp 2
      (((U * V : Matrix.unitaryGroup (Fin M) ℂ) :
        Matrix (Fin M) (Fin M) ℂ) *ᵥ WithLp.ofLp v.1)
  rw [Matrix.mulVec_mulVec]
  rw [show ((U * V : Matrix.unitaryGroup (Fin M) ℂ) :
      Matrix (Fin M) (Fin M) ℂ) =
        (U : Matrix (Fin M) (Fin M) ℂ) *
          (V : Matrix (Fin M) (Fin M) ℂ) from rfl]

/-- The unitary action is jointly continuous in the unitary and sphere
variables. -/
theorem continuous_uncurry_unitarySphereAction (M : ℕ) :
    Continuous (fun p : Matrix.unitaryGroup (Fin M) ℂ ×
        ComplexUnitSphere M ↦ h1UnitarySphereAction p.1 p.2) := by
  apply Continuous.subtype_mk
  change Continuous (fun p : Matrix.unitaryGroup (Fin M) ℂ ×
      ComplexUnitSphere M ↦
    WithLp.toLp 2 (Matrix.mulVec
      (p.1 : Matrix (Fin M) (Fin M) ℂ) (WithLp.ofLp p.2.1)))
  fun_prop

/-- Joint continuity with the product variables ordered as
`sphere × unitary`. -/
theorem continuous_swap_uncurry_unitarySphereAction (M : ℕ) :
    Continuous (fun p : ComplexUnitSphere M ×
        Matrix.unitaryGroup (Fin M) ℂ ↦ h1UnitarySphereAction p.2 p.1) := by
  apply Continuous.subtype_mk
  change Continuous (fun p : ComplexUnitSphere M ×
      Matrix.unitaryGroup (Fin M) ℂ ↦
    WithLp.toLp 2 (Matrix.mulVec
      (p.2 : Matrix (Fin M) (Fin M) ℂ) (WithLp.ofLp p.1.1)))
  fun_prop

/-- The jointly continuous action as a continuous map, for Fubini below. -/
def unitarySphereActionSwapContinuousMap (M : ℕ) :
    ContinuousMap
      (ComplexUnitSphere M × Matrix.unitaryGroup (Fin M) ℂ)
      (ComplexUnitSphere M) :=
  ⟨fun p ↦ h1UnitarySphereAction p.2 p.1,
    continuous_swap_uncurry_unitarySphereAction M⟩

/-! ## Transitivity -/

/-- Every unit vector can be installed as the last column of a unitary
matrix. -/
theorem exists_unitary_lastColumn_eq {M : ℕ} (hM : 1 ≤ M)
    (v : ComplexUnitSphere M) :
    ∃ U : Matrix.unitaryGroup (Fin M) ℂ,
      haarLastColumnSphere hM U = v := by
  classical
  let j₀ : Fin M := haarLastColumnIndex hM
  let seed : Fin M → EuclideanSpace ℂ (Fin M) := fun _ ↦ v.1
  have horth : Orthonormal ℂ
      (({j₀} : Set (Fin M)).domRestrict seed) := by
    rw [orthonormal_subsingleton_iff]
    intro j
    change ‖v.1‖ = 1
    exact mem_sphere_zero_iff_norm.mp v.2
  have hcard : Module.finrank ℂ (EuclideanSpace ℂ (Fin M)) =
      Fintype.card (Fin M) := by simp
  obtain ⟨b, hb⟩ :=
    horth.exists_orthonormalBasis_extension_of_card_eq hcard
  let U : Matrix.unitaryGroup (Fin M) ℂ :=
    ⟨(EuclideanSpace.basisFun (Fin M) ℂ).toBasis.toMatrix b.toBasis,
      (EuclideanSpace.basisFun (Fin M) ℂ).toMatrix_orthonormalBasis_mem_unitary b⟩
  refine ⟨U, ?_⟩
  apply Subtype.ext
  ext i
  rw [haarLastColumnSphere_apply]
  change b j₀ i = v.1 i
  rw [hb j₀ (by simp)]

/-- The unitary action on the complex unit sphere is transitive. -/
theorem exists_unitarySphereAction_eq {M : ℕ} (hM : 1 ≤ M)
    (v w : ComplexUnitSphere M) :
    ∃ U : Matrix.unitaryGroup (Fin M) ℂ,
      h1UnitarySphereAction U v = w := by
  obtain ⟨V, hV⟩ := exists_unitary_lastColumn_eq hM v
  obtain ⟨W, hW⟩ := exists_unitary_lastColumn_eq hM w
  refine ⟨W * V⁻¹, ?_⟩
  rw [← hV]
  change h1UnitarySphereAction (W * V⁻¹)
      (h1UnitarySphereAction V (haarLastColumnBaseSphere hM)) = w
  rw [unitarySphereAction_comp]
  simpa [haarLastColumnSphere] using hW

/-! ## Uniqueness of the invariant sphere probability -/

/-- Haar-average of a bounded continuous test function along the inverse
unitary orbit.  Using the inverse lets the proof use left Haar invariance
directly. -/
def complexSphereOrbitAverage {M : ℕ}
    (f : ComplexUnitSphere M →ᵇ ℝ)
    (v : ComplexUnitSphere M) : ℝ :=
  ∫ U : Matrix.unitaryGroup (Fin M) ℂ,
    f (h1UnitarySphereAction U⁻¹ v)
      ∂(unitaryHaarProbabilityMeasure M)

theorem complexSphereOrbitAverage_eq {M : ℕ} (hM : 1 ≤ M)
    (f : ComplexUnitSphere M →ᵇ ℝ)
    (v w : ComplexUnitSphere M) :
    complexSphereOrbitAverage f v = complexSphereOrbitAverage f w := by
  obtain ⟨W, hW⟩ := exists_unitarySphereAction_eq hM v w
  let μG := unitaryHaarProbabilityMeasure M
  letI : Measure.IsHaarMeasure μG :=
    canonicalUnitaryHaarProbabilityFamily.isHaar M
  rw [← hW]
  unfold complexSphereOrbitAverage
  simpa [unitarySphereAction_comp, μG] using
    (integral_mul_left_eq_self
      (μ := μG)
      (fun U : Matrix.unitaryGroup (Fin M) ℂ ↦
        f (h1UnitarySphereAction U⁻¹ v)) W⁻¹).symm

theorem continuous_swap_uncurry_unitarySphereAction_inv (M : ℕ) :
    Continuous (fun p : ComplexUnitSphere M ×
        Matrix.unitaryGroup (Fin M) ℂ ↦
      h1UnitarySphereAction p.2⁻¹ p.1) := by
  apply Continuous.subtype_mk
  change Continuous (fun p : ComplexUnitSphere M ×
      Matrix.unitaryGroup (Fin M) ℂ ↦
    WithLp.toLp 2 (Matrix.mulVec
      ((p.2⁻¹ : Matrix.unitaryGroup (Fin M) ℂ) :
        Matrix (Fin M) (Fin M) ℂ) (WithLp.ofLp p.1.1)))
  fun_prop

/-- Integrating a test function after a fixed unitary action does not change
its integral under an invariant measure. -/
theorem integral_comp_unitarySphereAction_eq_of_map_eq
    {M : ℕ} {μ : Measure (ComplexUnitSphere M)}
    (f : ComplexUnitSphere M →ᵇ ℝ)
    (U : Matrix.unitaryGroup (Fin M) ℂ)
    (hinv : Measure.map (h1UnitarySphereAction U) μ = μ) :
    (∫ v, f (h1UnitarySphereAction U v) ∂μ) = ∫ v, f v ∂μ := by
  calc
    (∫ v, f (h1UnitarySphereAction U v) ∂μ) =
        ∫ v, f v ∂Measure.map (h1UnitarySphereAction U) μ := by
      rw [integral_map
        (measurable_h1UnitarySphereAction U).aemeasurable
        f.continuous.measurable.aestronglyMeasurable]
    _ = ∫ v, f v ∂μ := by rw [hinv]

/-- Every invariant probability on the complex unit sphere integrates a
bounded continuous function as the common Haar orbit-average. -/
theorem integral_eq_complexSphereOrbitAverage_of_invariant
    {M : ℕ} (hM : 1 ≤ M)
    (μ : Measure (ComplexUnitSphere M)) [IsProbabilityMeasure μ]
    (hinv : ∀ U : Matrix.unitaryGroup (Fin M) ℂ,
      Measure.map (h1UnitarySphereAction U) μ = μ)
    (v₀ : ComplexUnitSphere M)
    (f : ComplexUnitSphere M →ᵇ ℝ) :
    (∫ v, f v ∂μ) = complexSphereOrbitAverage f v₀ := by
  let μG : Measure (Matrix.unitaryGroup (Fin M) ℂ) :=
    unitaryHaarProbabilityMeasure M
  letI : IsProbabilityMeasure μG :=
    unitaryHaarProbabilityMeasure_isProbability M
  let F : ComplexUnitSphere M ×
      Matrix.unitaryGroup (Fin M) ℂ →ᵇ ℝ :=
    f.compContinuous
      ⟨fun p ↦ h1UnitarySphereAction p.2⁻¹ p.1,
        continuous_swap_uncurry_unitarySphereAction_inv M⟩
  have hFint : Integrable
      (Function.uncurry fun v : ComplexUnitSphere M ↦
        fun U : Matrix.unitaryGroup (Fin M) ℂ ↦
          f (h1UnitarySphereAction U⁻¹ v))
      (μ.prod μG) := by
    convert BoundedContinuousFunction.integrable (μ.prod μG) F using 1
    rfl
  have hswap :
      (∫ v, complexSphereOrbitAverage f v ∂μ) =
        ∫ U : Matrix.unitaryGroup (Fin M) ℂ,
          (∫ v, f (h1UnitarySphereAction U⁻¹ v) ∂μ) ∂μG := by
    simpa only [complexSphereOrbitAverage, μG] using
      (integral_integral_swap hFint)
  have havgInt :
      (∫ v, complexSphereOrbitAverage f v ∂μ) = ∫ v, f v ∂μ := by
    rw [hswap]
    simp_rw [integral_comp_unitarySphereAction_eq_of_map_eq f _ (hinv _)]
    simp
  have hae : ∀ᵐ v ∂μ,
      complexSphereOrbitAverage f v = complexSphereOrbitAverage f v₀ :=
    Filter.Eventually.of_forall fun v ↦
      complexSphereOrbitAverage_eq hM f v v₀
  calc
    (∫ v, f v ∂μ) =
        ∫ v, complexSphereOrbitAverage f v ∂μ := havgInt.symm
    _ = ∫ _v, complexSphereOrbitAverage f v₀ ∂μ :=
      integral_congr_ae hae
    _ = complexSphereOrbitAverage f v₀ := by simp

/-- There is at most one unitary-invariant probability measure on the
complex unit sphere. -/
theorem complexUnitSphere_invariantProbability_unique
    {M : ℕ} (hM : 1 ≤ M)
    (μ ν : Measure (ComplexUnitSphere M))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμinv : ∀ U : Matrix.unitaryGroup (Fin M) ℂ,
      Measure.map (h1UnitarySphereAction U) μ = μ)
    (hνinv : ∀ U : Matrix.unitaryGroup (Fin M) ℂ,
      Measure.map (h1UnitarySphereAction U) ν = ν) :
    μ = ν := by
  let v₀ := haarLastColumnBaseSphere hM
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_eq_complexSphereOrbitAverage_of_invariant
      hM μ hμinv v₀ f,
    integral_eq_complexSphereOrbitAverage_of_invariant
      hM ν hνinv v₀ f]

/-! ## Haar last-column law -/

/-- The pushforward of normalized Haar probability on `U(M)` by the last
column map is normalized surface probability on the complex unit sphere. -/
theorem map_haarLastColumnSphere_unitaryHaarProbabilityMeasure
    {M : ℕ} (hM : 1 ≤ M) :
    Measure.map (haarLastColumnSphere hM)
        (unitaryHaarProbabilityMeasure M) =
      complexUnitSphereProbabilityMeasure M := by
  let μG : Measure (Matrix.unitaryGroup (Fin M) ℂ) :=
    unitaryHaarProbabilityMeasure M
  let ν : Measure (ComplexUnitSphere M) :=
    Measure.map (haarLastColumnSphere hM) μG
  let σ : Measure (ComplexUnitSphere M) :=
    complexUnitSphereProbabilityMeasure M
  letI : IsProbabilityMeasure μG :=
    unitaryHaarProbabilityMeasure_isProbability M
  letI : Measure.IsHaarMeasure μG :=
    canonicalUnitaryHaarProbabilityFamily.isHaar M
  letI : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map
      (measurable_haarLastColumnSphere hM).aemeasurable
  letI : IsProbabilityMeasure σ :=
    complexUnitSphereProbabilityMeasure_isProbability hM
  have hνinv (V : Matrix.unitaryGroup (Fin M) ℂ) :
      Measure.map (h1UnitarySphereAction V) ν = ν := by
    calc
      Measure.map (h1UnitarySphereAction V) ν =
          Measure.map ((h1UnitarySphereAction V) ∘ haarLastColumnSphere hM)
            μG := by
        simp only [ν]
        rw [Measure.map_map (measurable_h1UnitarySphereAction V)
          (measurable_haarLastColumnSphere hM)]
      _ = Measure.map
          (haarLastColumnSphere hM ∘
            fun U : Matrix.unitaryGroup (Fin M) ℂ ↦ V * U) μG := by
        apply Measure.map_congr
        filter_upwards [] with U
        exact unitarySphereAction_comp V U (haarLastColumnBaseSphere hM)
      _ = Measure.map (haarLastColumnSphere hM)
          (Measure.map (fun U : Matrix.unitaryGroup (Fin M) ℂ ↦ V * U) μG) := by
        rw [Measure.map_map (measurable_haarLastColumnSphere hM)
          (measurable_const_mul V)]
      _ = Measure.map (haarLastColumnSphere hM) μG := by
        rw [map_mul_left_eq_self μG V]
      _ = ν := rfl
  have hσinv (V : Matrix.unitaryGroup (Fin M) ℂ) :
      Measure.map (h1UnitarySphereAction V) σ = σ := by
    simpa only [σ] using
      map_h1ComplexUnitSphereProbabilityMeasure_unitarySphereAction hM V
  have hEq : ν = σ :=
    complexUnitSphere_invariantProbability_unique hM ν σ hνinv hσinv
  simpa only [ν, σ, μG] using hEq

end

end LogdetLean.GramHafnian.UltimateHiding.Dense
