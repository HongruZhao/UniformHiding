import LogdetLean.GramHafnian.UltimateHiding.Dense.OneColumnConcrete
import LogdetLean.GaussianSphereDirection
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# H1-local unitary action on the complex sphere

This dependency-light module contains the elementary unitary sphere action
and invariance of normalized surface probability used by the H1 last-column
argument. It deliberately stays below the dense Haar-recursion layer.
-/

open MeasureTheory ProbabilityTheory Metric
open scoped MeasureTheory InnerProductSpace

namespace LogdetLean.GramHafnian.UltimateHiding.Dense

noncomputable section

/-! ## The unitary action on the complex sphere -/

/-- The complex-linear action of a unitary matrix on Euclidean coordinate
space. -/
def h1UnitaryEuclideanLinearEquiv {N : ℕ}
    (U : Matrix.unitaryGroup (Fin N) ℂ) :
    EuclideanSpace ℂ (Fin N) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin N) :=
  (WithLp.linearEquiv 2 ℂ (Fin N → ℂ)).trans
    (Matrix.UnitaryGroup.toLinearEquiv U) |>.trans
      (WithLp.linearEquiv 2 ℂ (Fin N → ℂ)).symm

theorem h1UnitaryEuclideanLinearEquiv_apply {N : ℕ}
    (U : Matrix.unitaryGroup (Fin N) ℂ)
    (x : EuclideanSpace ℂ (Fin N)) :
    h1UnitaryEuclideanLinearEquiv U x =
      WithLp.toLp 2 (Matrix.mulVec
        (U : Matrix (Fin N) (Fin N) ℂ) (WithLp.ofLp x)) := by
  rfl

/-- The preceding linear equivalence preserves the Hermitian inner product. -/
theorem h1UnitaryEuclideanLinearEquiv_inner_map_map {N : ℕ}
    (U : Matrix.unitaryGroup (Fin N) ℂ)
    (x y : EuclideanSpace ℂ (Fin N)) :
    ⟪h1UnitaryEuclideanLinearEquiv U x, h1UnitaryEuclideanLinearEquiv U y⟫_ℂ =
      ⟪x, y⟫_ℂ := by
  rw [h1UnitaryEuclideanLinearEquiv_apply,
    h1UnitaryEuclideanLinearEquiv_apply]
  simp only [EuclideanSpace.inner_eq_star_dotProduct]
  rw [Matrix.star_mulVec, dotProduct_comm,
    Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    ← Matrix.star_eq_conjTranspose]
  rw [Matrix.UnitaryGroup.star_mul_self]
  simp [dotProduct_comm]

/-- A unitary matrix as a complex-linear isometric equivalence of Euclidean
coordinate space. -/
def h1UnitaryEuclideanIsometryEquiv {N : ℕ}
    (U : Matrix.unitaryGroup (Fin N) ℂ) :
    EuclideanSpace ℂ (Fin N) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin N) :=
  (h1UnitaryEuclideanLinearEquiv U).isometryOfInner
    (h1UnitaryEuclideanLinearEquiv_inner_map_map U)

/-- The same unitary action, regarded as a real-linear isometry. -/
def h1UnitaryEuclideanRealIsometryEquiv {N : ℕ}
    (U : Matrix.unitaryGroup (Fin N) ℂ) :
    EuclideanSpace ℂ (Fin N) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin N) :=
  LinearIsometryEquiv.mk
    ((h1UnitaryEuclideanLinearEquiv U).restrictScalars ℝ)
    (h1UnitaryEuclideanIsometryEquiv U).norm_map

/-- The induced action on the complex unit sphere. -/
def h1UnitarySphereAction {N : ℕ}
    (U : Matrix.unitaryGroup (Fin N) ℂ) :
    ComplexUnitSphere N → ComplexUnitSphere N :=
  fun v ↦ ⟨h1UnitaryEuclideanIsometryEquiv U v.1, by
    simpa only [mem_sphere_zero_iff_norm,
      LinearIsometryEquiv.norm_map] using v.2⟩

theorem h1UnitarySphereAction_val {N : ℕ}
    (U : Matrix.unitaryGroup (Fin N) ℂ)
    (v : ComplexUnitSphere N) :
    (h1UnitarySphereAction U v).1 =
      WithLp.toLp 2 (Matrix.mulVec
        (U : Matrix (Fin N) (Fin N) ℂ) (WithLp.ofLp v.1)) := by
  rfl

theorem measurable_h1UnitarySphereAction {N : ℕ}
    (U : Matrix.unitaryGroup (Fin N) ℂ) :
    Measurable (h1UnitarySphereAction U) := by
  exact (((h1UnitaryEuclideanIsometryEquiv U).continuous.measurable).comp
    measurable_subtype_coe).subtype_mk

theorem h1UnitDirection_h1UnitaryEuclideanRealIsometryEquiv {N : ℕ}
    (U : Matrix.unitaryGroup (Fin N) ℂ)
    (x : EuclideanSpace ℂ (Fin N)) :
    LogdetLean.unitDirection (h1UnitaryEuclideanRealIsometryEquiv U x) =
      h1UnitaryEuclideanRealIsometryEquiv U (LogdetLean.unitDirection x) := by
  classical
  by_cases hx : x = 0
  · simp [hx, LogdetLean.unitDirection]
  · have hUx : h1UnitaryEuclideanRealIsometryEquiv U x ≠ 0 :=
      by simpa using (h1UnitaryEuclideanRealIsometryEquiv U).injective.ne hx
    simp [LogdetLean.unitDirection, hx, hUx]

/-- Normalized surface probability
on the complex unit sphere is invariant under every unitary linear isometry.

This is proved from the already formalized Gaussian polar decomposition:
standard Gaussian measure is invariant under real-linear isometries, its
normalized direction is normalized Haar surface measure, and unit direction
commutes with the unitary action.
-/
theorem map_h1ComplexUnitSphereProbabilityMeasure_unitarySphereAction
    {N : ℕ} (hN : 1 ≤ N)
    (U : Matrix.unitaryGroup (Fin N) ℂ) :
    Measure.map (h1UnitarySphereAction U)
        (complexUnitSphereProbabilityMeasure N) =
      complexUnitSphereProbabilityMeasure N := by
  let _ : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp (by omega)
  let E := EuclideanSpace ℂ (Fin N)
  let f : E ≃ₗᵢ[ℝ] E := h1UnitaryEuclideanRealIsometryEquiv U
  let sigma : Measure (sphere (0 : E) 1) :=
    LogdetLean.uniformSphereSurfaceMeasure (E := E)
  have hsigma : sigma = complexUnitSphereProbabilityMeasure N := by
    rfl
  rw [← hsigma]
  apply (MeasurableEmbedding.subtype_coe isClosed_sphere.measurableSet).map_injective
  rw [Measure.map_map measurable_subtype_coe
    (measurable_h1UnitarySphereAction U)]
  have hval :
      ((Subtype.val : sphere (0 : E) 1 → E) ∘ h1UnitarySphereAction U) =
        f ∘ (Subtype.val : sphere (0 : E) 1 → E) := by
    funext v
    rfl
  rw [hval]
  rw [← Measure.map_map f.continuous.measurable measurable_subtype_coe]
  rw [← LogdetLean.map_unitDirection_stdGaussian_eq_uniformSphereSurfaceMeasure]
  rw [Measure.map_map f.continuous.measurable
    LogdetLean.measurable_unitDirection]
  have hcomp :
      f ∘ LogdetLean.unitDirection = LogdetLean.unitDirection ∘ f := by
    funext x
    exact (h1UnitDirection_h1UnitaryEuclideanRealIsometryEquiv U x).symm
  rw [hcomp]
  rw [← Measure.map_map LogdetLean.measurable_unitDirection
    f.continuous.measurable]
  rw [ProbabilityTheory.stdGaussian_map f]

end

end LogdetLean.GramHafnian.UltimateHiding.Dense
