import LogdetLean.GramHafnian.UltimateHiding.Dense.RadialConcrete
import LogdetLean.GaussianSphereDirection
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Unitary covariance of the concrete H2 factor laws

This module isolates the elementary rotational input used to turn the generic
`GL_N(C) / U(N)` sandwich theorem into a statement about the paper's concrete
rank-one factors.  It contains no radial/orbital commutation endpoint.

The only external input is invariance of normalized surface measure on the
complex unit sphere under a unitary linear isometry.  All projection, factor,
pushforward, and preservation identities are proved below.
-/

open MeasureTheory ProbabilityTheory Metric
open scoped MeasureTheory InnerProductSpace

namespace LogdetLean.GramHafnian.UltimateHiding.Dense

noncomputable section

/-! ## The unitary action on the complex sphere -/

/-- The complex-linear action of a unitary matrix on Euclidean coordinate
space. -/
def unitaryEuclideanLinearEquiv {N : ℕ}
    (U : Matrix.unitaryGroup (Fin N) ℂ) :
    EuclideanSpace ℂ (Fin N) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin N) :=
  (WithLp.linearEquiv 2 ℂ (Fin N → ℂ)).trans
    (Matrix.UnitaryGroup.toLinearEquiv U) |>.trans
      (WithLp.linearEquiv 2 ℂ (Fin N → ℂ)).symm

theorem unitaryEuclideanLinearEquiv_apply {N : ℕ}
    (U : Matrix.unitaryGroup (Fin N) ℂ)
    (x : EuclideanSpace ℂ (Fin N)) :
    unitaryEuclideanLinearEquiv U x =
      WithLp.toLp 2 (Matrix.mulVec
        (U : Matrix (Fin N) (Fin N) ℂ) (WithLp.ofLp x)) := by
  rfl

/-- The preceding linear equivalence preserves the Hermitian inner product. -/
theorem unitaryEuclideanLinearEquiv_inner_map_map {N : ℕ}
    (U : Matrix.unitaryGroup (Fin N) ℂ)
    (x y : EuclideanSpace ℂ (Fin N)) :
    ⟪unitaryEuclideanLinearEquiv U x, unitaryEuclideanLinearEquiv U y⟫_ℂ =
      ⟪x, y⟫_ℂ := by
  rw [unitaryEuclideanLinearEquiv_apply,
    unitaryEuclideanLinearEquiv_apply]
  simp only [EuclideanSpace.inner_eq_star_dotProduct]
  rw [Matrix.star_mulVec, dotProduct_comm,
    Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    ← Matrix.star_eq_conjTranspose]
  rw [Matrix.UnitaryGroup.star_mul_self]
  simp [dotProduct_comm]

/-- A unitary matrix as a complex-linear isometric equivalence of Euclidean
coordinate space. -/
def unitaryEuclideanIsometryEquiv {N : ℕ}
    (U : Matrix.unitaryGroup (Fin N) ℂ) :
    EuclideanSpace ℂ (Fin N) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin N) :=
  (unitaryEuclideanLinearEquiv U).isometryOfInner
    (unitaryEuclideanLinearEquiv_inner_map_map U)

/-- The same unitary action, regarded as a real-linear isometry. -/
def unitaryEuclideanRealIsometryEquiv {N : ℕ}
    (U : Matrix.unitaryGroup (Fin N) ℂ) :
    EuclideanSpace ℂ (Fin N) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin N) :=
  LinearIsometryEquiv.mk
    ((unitaryEuclideanLinearEquiv U).restrictScalars ℝ)
    (unitaryEuclideanIsometryEquiv U).norm_map

/-- The induced action on the complex unit sphere. -/
def unitarySphereAction {N : ℕ}
    (U : Matrix.unitaryGroup (Fin N) ℂ) :
    ComplexUnitSphere N → ComplexUnitSphere N :=
  fun v ↦ ⟨unitaryEuclideanIsometryEquiv U v.1, by
    simpa only [mem_sphere_zero_iff_norm,
      LinearIsometryEquiv.norm_map] using v.2⟩

theorem unitarySphereAction_val {N : ℕ}
    (U : Matrix.unitaryGroup (Fin N) ℂ)
    (v : ComplexUnitSphere N) :
    (unitarySphereAction U v).1 =
      WithLp.toLp 2 (Matrix.mulVec
        (U : Matrix (Fin N) (Fin N) ℂ) (WithLp.ofLp v.1)) := by
  rfl

theorem measurable_unitarySphereAction {N : ℕ}
    (U : Matrix.unitaryGroup (Fin N) ℂ) :
    Measurable (unitarySphereAction U) := by
  exact (((unitaryEuclideanIsometryEquiv U).continuous.measurable).comp
    measurable_subtype_coe).subtype_mk

theorem unitDirection_unitaryEuclideanRealIsometryEquiv {N : ℕ}
    (U : Matrix.unitaryGroup (Fin N) ℂ)
    (x : EuclideanSpace ℂ (Fin N)) :
    LogdetLean.unitDirection (unitaryEuclideanRealIsometryEquiv U x) =
      unitaryEuclideanRealIsometryEquiv U (LogdetLean.unitDirection x) := by
  classical
  by_cases hx : x = 0
  · simp [hx, LogdetLean.unitDirection]
  · have hUx : unitaryEuclideanRealIsometryEquiv U x ≠ 0 :=
      by simpa using (unitaryEuclideanRealIsometryEquiv U).injective.ne hx
    simp [LogdetLean.unitDirection, hx, hUx]

/-- Normalized surface probability
on the complex unit sphere is invariant under every unitary linear isometry.

This is proved from the already formalized Gaussian polar decomposition:
standard Gaussian measure is invariant under real-linear isometries, its
normalized direction is normalized Haar surface measure, and unit direction
commutes with the unitary action.
-/
theorem map_complexUnitSphereProbabilityMeasure_unitarySphereAction
    {N : ℕ} (hN : 1 ≤ N)
    (U : Matrix.unitaryGroup (Fin N) ℂ) :
    Measure.map (unitarySphereAction U)
        (complexUnitSphereProbabilityMeasure N) =
      complexUnitSphereProbabilityMeasure N := by
  let _ : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp (by omega)
  let E := EuclideanSpace ℂ (Fin N)
  let f : E ≃ₗᵢ[ℝ] E := unitaryEuclideanRealIsometryEquiv U
  let sigma : Measure (sphere (0 : E) 1) :=
    LogdetLean.uniformSphereSurfaceMeasure (E := E)
  have hsigma : sigma = complexUnitSphereProbabilityMeasure N := by
    rfl
  rw [← hsigma]
  apply (MeasurableEmbedding.subtype_coe isClosed_sphere.measurableSet).map_injective
  rw [Measure.map_map measurable_subtype_coe
    (measurable_unitarySphereAction U)]
  have hval :
      ((Subtype.val : sphere (0 : E) 1 → E) ∘ unitarySphereAction U) =
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
    exact (unitDirection_unitaryEuclideanRealIsometryEquiv U x).symm
  rw [hcomp]
  rw [← Measure.map_map LogdetLean.measurable_unitDirection
    f.continuous.measurable]
  rw [ProbabilityTheory.stdGaussian_map f]

/-! ## Pointwise covariance of the concrete factors -/

/-- Conjugation of a matrix by a unitary matrix. -/
def unitaryMatrixConjugation {N : ℕ}
    (U : Matrix.unitaryGroup (Fin N) ℂ)
    (A : ConcreteMatrixState N) : ConcreteMatrixState N :=
  (U : Matrix (Fin N) (Fin N) ℂ) * A *
    Matrix.conjTranspose (U : Matrix (Fin N) (Fin N) ℂ)

theorem measurable_unitaryMatrixConjugation {N : ℕ}
    (U : Matrix.unitaryGroup (Fin N) ℂ) :
    Measurable (unitaryMatrixConjugation U) := by
  have hA : Measurable (id : ConcreteMatrixState N →
      ConcreteMatrixState N) := measurable_id
  exact measurable_complexMatrix_mul
    (measurable_complexMatrix_mul measurable_const hA) measurable_const

theorem complexRankOneProjection_unitarySphereAction {N : ℕ}
    (U : Matrix.unitaryGroup (Fin N) ℂ)
    (v : ComplexUnitSphere N) :
    complexRankOneProjection (unitarySphereAction U v) =
      unitaryMatrixConjugation U (complexRankOneProjection v) := by
  ext i j
  let x : Fin N → ℂ := WithLp.ofLp v.1
  change
    (∑ k, (U : Matrix (Fin N) (Fin N) ℂ) i k * x k) *
        star (∑ l, (U : Matrix (Fin N) (Fin N) ℂ) j l * x l) =
      ∑ k, (∑ l, (U : Matrix (Fin N) (Fin N) ℂ) i l *
        (x l * star (x k))) *
          star ((U : Matrix (Fin N) (Fin N) ℂ) j k)
  rw [star_sum]
  simp only [star_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro l hl
  ring

theorem concreteOrbitalFactor_unitarySphereAction
    {N : ℕ} (U : Matrix.unitaryGroup (Fin N) ℂ)
    (s : ℝ) (v : ComplexUnitSphere N) :
    concreteOrbitalFactor N s (unitarySphereAction U v) =
      unitaryMatrixConjugation U (concreteOrbitalFactor N s v) := by
  rw [concreteOrbitalFactor, concreteOrbitalFactor,
    complexRankOneProjection_unitarySphereAction]
  unfold unitaryMatrixConjugation
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_assoc]
  have hUU : (U : Matrix (Fin N) (Fin N) ℂ) *
      Matrix.conjTranspose (U : Matrix (Fin N) (Fin N) ℂ) = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using U.2.2
  rw [Matrix.one_mul, hUU]

theorem concreteOneColumnFactor_unitarySphereAction
    (m : ℕ) {N : ℕ}
    (U : Matrix.unitaryGroup (Fin N) ℂ)
    (q : ℝ) (v : ComplexUnitSphere N) :
    concreteOneColumnFactor m N q (unitarySphereAction U v) =
      unitaryMatrixConjugation U (concreteOneColumnFactor m N q v) := by
  rw [concreteOneColumnFactor, concreteOneColumnFactor,
    complexRankOneProjection_unitarySphereAction]
  unfold unitaryMatrixConjugation
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_assoc]
  have hUU : (U : Matrix (Fin N) (Fin N) ℂ) *
      Matrix.conjTranspose (U : Matrix (Fin N) (Fin N) ℂ) = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using U.2.2
  rw [Matrix.one_mul, hUU]

/-! ## Conjugation-invariant matrix factor laws -/

/-- Law of the positive centered-orbital factor. -/
def concreteOrbitalFactorLaw (N : ℕ) (s : ℝ) :
    Measure (ConcreteMatrixState N) :=
  Measure.map (concreteOrbitalFactor N s)
    (complexUnitSphereProbabilityMeasure N)

theorem concreteOrbitalFactorLaw_isProbability
    {N : ℕ} (hN : 1 ≤ N) (s : ℝ) :
    IsProbabilityMeasure (concreteOrbitalFactorLaw N s) := by
  unfold concreteOrbitalFactorLaw
  let _ : IsProbabilityMeasure (complexUnitSphereProbabilityMeasure N) :=
    complexUnitSphereProbabilityMeasure_isProbability hN
  exact Measure.isProbabilityMeasure_map
    (measurable_concreteOrbitalFactor N s).aemeasurable

/-- Law of the positive one-column factor. -/
def concreteOneColumnFactorLaw (m N : ℕ) :
    Measure (ConcreteMatrixState N) :=
  Measure.map
    (fun p : ℝ × ComplexUnitSphere N ↦
      concreteOneColumnFactor m N p.1 p.2)
    (concreteOneColumnParameterLaw m N)

theorem concreteOneColumnFactorLaw_isProbability
    {m N : ℕ} (hN : 1 ≤ N) (hNm : N ≤ m) :
    IsProbabilityMeasure (concreteOneColumnFactorLaw m N) := by
  unfold concreteOneColumnFactorLaw
  let _ : IsProbabilityMeasure (concreteOneColumnParameterLaw m N) :=
    concreteOneColumnParameterLaw_isProbability hN hNm
  exact Measure.isProbabilityMeasure_map
    (measurable_concreteOneColumnFactor m N).aemeasurable

theorem map_concreteOneColumnParameterLaw_unitarySphereAction
    {m N : ℕ} (hN : 1 ≤ N) (hNm : N ≤ m)
    (U : Matrix.unitaryGroup (Fin N) ℂ) :
    Measure.map (Prod.map id (unitarySphereAction U))
        (concreteOneColumnParameterLaw m N) =
      concreteOneColumnParameterLaw m N := by
  let _ : IsProbabilityMeasure (oneColumnBetaLaw m N) :=
    oneColumnBetaLaw_isProbability hN hNm
  let _ : IsProbabilityMeasure (complexUnitSphereProbabilityMeasure N) :=
    complexUnitSphereProbabilityMeasure_isProbability hN
  unfold concreteOneColumnParameterLaw oneColumnParameterLaw
  rw [← Measure.map_prod_map]
  · rw [Measure.map_id,
      map_complexUnitSphereProbabilityMeasure_unitarySphereAction hN U]
  · exact measurable_id
  · exact measurable_unitarySphereAction U

theorem concreteOrbitalFactorLaw_unitary_conjugation_invariant
    {N : ℕ} (hN : 1 ≤ N) (s : ℝ)
    (U : Matrix.unitaryGroup (Fin N) ℂ) :
    Measure.map (unitaryMatrixConjugation U)
        (concreteOrbitalFactorLaw N s) =
      concreteOrbitalFactorLaw N s := by
  unfold concreteOrbitalFactorLaw
  rw [Measure.map_map (measurable_unitaryMatrixConjugation U)
    (measurable_concreteOrbitalFactor N s)]
  calc
    Measure.map
        (unitaryMatrixConjugation U ∘ concreteOrbitalFactor N s)
        (complexUnitSphereProbabilityMeasure N) =
      Measure.map
        (concreteOrbitalFactor N s ∘ unitarySphereAction U)
        (complexUnitSphereProbabilityMeasure N) := by
          apply Measure.map_congr
          filter_upwards [] with v
          exact (concreteOrbitalFactor_unitarySphereAction U s v).symm
    _ = Measure.map (concreteOrbitalFactor N s)
          (Measure.map (unitarySphereAction U)
            (complexUnitSphereProbabilityMeasure N)) := by
      rw [Measure.map_map (measurable_concreteOrbitalFactor N s)
        (measurable_unitarySphereAction U)]
    _ = Measure.map (concreteOrbitalFactor N s)
          (complexUnitSphereProbabilityMeasure N) := by
      rw [map_complexUnitSphereProbabilityMeasure_unitarySphereAction hN U]

theorem concreteOneColumnFactorLaw_unitary_conjugation_invariant
    {m N : ℕ} (hN : 1 ≤ N) (hNm : N ≤ m)
    (U : Matrix.unitaryGroup (Fin N) ℂ) :
    Measure.map (unitaryMatrixConjugation U)
        (concreteOneColumnFactorLaw m N) =
      concreteOneColumnFactorLaw m N := by
  unfold concreteOneColumnFactorLaw
  rw [Measure.map_map (measurable_unitaryMatrixConjugation U)
    (measurable_concreteOneColumnFactor m N)]
  let rotate : ℝ × ComplexUnitSphere N →
      ℝ × ComplexUnitSphere N :=
    Prod.map id (unitarySphereAction U)
  have hrotate : Measurable rotate :=
    measurable_id.prodMap (measurable_unitarySphereAction U)
  calc
    Measure.map
        (unitaryMatrixConjugation U ∘
          fun p : ℝ × ComplexUnitSphere N ↦
            concreteOneColumnFactor m N p.1 p.2)
        (concreteOneColumnParameterLaw m N) =
      Measure.map
        ((fun p : ℝ × ComplexUnitSphere N ↦
            concreteOneColumnFactor m N p.1 p.2) ∘ rotate)
        (concreteOneColumnParameterLaw m N) := by
          apply Measure.map_congr
          filter_upwards [] with p
          exact (concreteOneColumnFactor_unitarySphereAction
            m U p.1 p.2).symm
    _ = Measure.map
          (fun p : ℝ × ComplexUnitSphere N ↦
            concreteOneColumnFactor m N p.1 p.2)
          (Measure.map rotate
            (concreteOneColumnParameterLaw m N)) := by
      rw [Measure.map_map (measurable_concreteOneColumnFactor m N) hrotate]
    _ = Measure.map
          (fun p : ℝ × ComplexUnitSphere N ↦
            concreteOneColumnFactor m N p.1 p.2)
          (concreteOneColumnParameterLaw m N) := by
      rw [map_concreteOneColumnParameterLaw_unitarySphereAction hN hNm U]

end

end LogdetLean.GramHafnian.UltimateHiding.Dense
