import A3.HermitianFlagChartSpectrum

open Set
open scoped Matrix Matrix.Norms.Elementwise ContDiff Topology

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace A3Research

variable {n : ℕ} {K : Type*} [RCLike K]

theorem hermitianAngularDensity_zero_pos :
    0 < hermitianAngularDensity (0 : HermitianCoordinateIndex n → K) := by
  rw [hermitianAngularDensity, hermitianAngularTangentOperator_zero_det]
  positivity

theorem hermitianReferenceOrbitChartDerivative_det_ne_zero (n : ℕ) (K : Type*) [RCLike K] :
    LinearMap.det (hermitianCayleyOrbitChartDerivative
      (1 : Matrix.unitaryGroup (Fin n) K) (hermitianReferenceSpectrum n, 0)).toLinearMap ≠ 0 :=
  hermitianCayleyOrbitChartDerivative_det_ne_zero _ _
    hermitianAngularDensity_zero_pos (hermitianReferenceSpectrum_injective n)

def hermitianReferenceOrbitChartLinearEquiv (n : ℕ) (K : Type*) [RCLike K] :
    HermitianCoordinates n K ≃L[ℝ] HermitianCoordinates n K :=
  (LinearMap.equivOfIsUnitDet
    (isUnit_iff_ne_zero.mpr (hermitianReferenceOrbitChartDerivative_det_ne_zero n K))).toContinuousLinearEquiv

theorem hermitianReferenceOrbitChartLinearEquiv_coe (n : ℕ) (K : Type*) [RCLike K] :
    (hermitianReferenceOrbitChartLinearEquiv n K :
      HermitianCoordinates n K →L[ℝ] HermitianCoordinates n K) =
      hermitianCayleyOrbitChartDerivative
        (1 : Matrix.unitaryGroup (Fin n) K) (hermitianReferenceSpectrum n, 0) := by
  apply ContinuousLinearMap.ext
  intro v
  exact LinearMap.equivOfIsUnitDet_apply
    (isUnit_iff_ne_zero.mpr (hermitianReferenceOrbitChartDerivative_det_ne_zero n K)) v

theorem hasFDerivAt_hermitianReferenceOrbitChart (n : ℕ) (K : Type*) [RCLike K] :
    HasFDerivAt (hermitianCayleyOrbitChart (1 : Matrix.unitaryGroup (Fin n) K))
      (hermitianReferenceOrbitChartLinearEquiv n K :
        HermitianCoordinates n K →L[ℝ] HermitianCoordinates n K)
      (hermitianReferenceSpectrum n, 0) := by
  rw [hermitianReferenceOrbitChartLinearEquiv_coe]
  exact hasFDerivAt_hermitianCayleyOrbitChart _ _

/-- The actual inverse function theorem chart at a fixed distinct reference spectrum. -/
def hermitianReferenceLocalHomeomorph (n : ℕ) (K : Type*) [RCLike K] :
    OpenPartialHomeomorph (HermitianCoordinates n K) (HermitianCoordinates n K) :=
  (contDiff_hermitianCayleyOrbitChart (1 : Matrix.unitaryGroup (Fin n) K) 1).contDiffAt.toOpenPartialHomeomorph
    (hermitianCayleyOrbitChart (1 : Matrix.unitaryGroup (Fin n) K))
    (hasFDerivAt_hermitianReferenceOrbitChart n K) (by norm_num)

@[simp] theorem hermitianReferenceLocalHomeomorph_apply (x : HermitianCoordinates n K) :
    hermitianReferenceLocalHomeomorph n K x =
      hermitianCayleyOrbitChart (1 : Matrix.unitaryGroup (Fin n) K) x := rfl

theorem hermitianReference_mem_source (n : ℕ) (K : Type*) [RCLike K] :
    (hermitianReferenceSpectrum n, 0) ∈ (hermitianReferenceLocalHomeomorph n K).source :=
  ContDiffAt.mem_toOpenPartialHomeomorph_source _
    (hasFDerivAt_hermitianReferenceOrbitChart n K) (by norm_num)

def hermitianReferenceAngularSource (n : ℕ) (K : Type*) [RCLike K] :
    Set (HermitianCoordinateIndex n → K) :=
  {a | (hermitianReferenceSpectrum n, a) ∈ (hermitianReferenceLocalHomeomorph n K).source}

theorem isOpen_hermitianReferenceAngularSource (n : ℕ) (K : Type*) [RCLike K] :
    IsOpen (hermitianReferenceAngularSource n K) :=
  (hermitianReferenceLocalHomeomorph n K).open_source.preimage (by fun_prop)

theorem zero_mem_hermitianReferenceAngularSource (n : ℕ) (K : Type*) [RCLike K] :
    0 ∈ hermitianReferenceAngularSource n K := hermitianReference_mem_source n K

theorem exists_hermitianFlagChart_radius (n : ℕ) (K : Type*) [RCLike K] :
    ∃ r : ℝ, 0 < r ∧
      Metric.ball (0 : HermitianCoordinateIndex n → K) r ⊆ hermitianReferenceAngularSource n K ∧
      ∀ a : HermitianCoordinateIndex n → K, a ∈ Metric.closedBall 0 r →
        0 < hermitianAngularDensity a := by
  obtain ⟨r₁, hr₁, hball⟩ := Metric.isOpen_iff.mp
    (isOpen_hermitianReferenceAngularSource n K) 0 (zero_mem_hermitianReferenceAngularSource n K)
  obtain ⟨r₂, hr₂, hdensity⟩ := exists_hermitianAngularDensity_positive_closedBall (n := n) (K := K)
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, ?_, ?_⟩
  · exact (Metric.ball_subset_ball (min_le_left _ _)).trans hball
  · intro a ha
    exact hdensity a ((Metric.closedBall_subset_closedBall (min_le_right _ _)) ha)

theorem hermitianAngularFlagChart_injOn (r : ℝ)
    (hball : Metric.ball (0 : HermitianCoordinateIndex n → K) r ⊆
      hermitianReferenceAngularSource n K) :
    Set.InjOn (hermitianAngularFlagChart : (HermitianCoordinateIndex n → K) → _)
      (Metric.ball 0 r) := by
  intro a ha b hb hab
  have he : hermitianCayleyOrbitChart (1 : Matrix.unitaryGroup (Fin n) K)
      (hermitianReferenceSpectrum n, a) =
      hermitianCayleyOrbitChart (1 : Matrix.unitaryGroup (Fin n) K)
        (hermitianReferenceSpectrum n, b) := by
    rw [hermitianCayleyOrbitChart_one_reference, hermitianCayleyOrbitChart_one_reference, hab]
  have hx := (hermitianReferenceLocalHomeomorph n K).injOn (hball ha) (hball hb) he
  exact congrArg Prod.snd hx

end A3Research
