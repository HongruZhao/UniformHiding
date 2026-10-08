import A3.HermitianFlagChartInverse

open Set
open scoped Matrix Matrix.Norms.Elementwise ContDiff Topology

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace A3Research

variable {n : ℕ} {K : Type*} [RCLike K]

def hermitianReferenceBallChamber (n : ℕ) (K : Type*) [RCLike K] (r : ℝ) :
    Set (HermitianCoordinates n K) :=
  {x | x.1 ∈ hermitianReferenceChamber n ∧ x.2 ∈ Metric.ball 0 r}

theorem isOpen_hermitianReferenceBallChamber (n : ℕ) (K : Type*) [RCLike K] (r : ℝ) :
    IsOpen (hermitianReferenceBallChamber n K r) :=
  ((isOpen_hermitianReferenceChamber n).preimage continuous_fst).inter
    (Metric.isOpen_ball.preimage continuous_snd)

def hermitianReferenceBallHomeomorph (n : ℕ) (K : Type*) [RCLike K] (r : ℝ) :
    OpenPartialHomeomorph (HermitianCoordinates n K) (HermitianCoordinates n K) :=
  (hermitianReferenceLocalHomeomorph n K).restrOpen (hermitianReferenceBallChamber n K r)
    (isOpen_hermitianReferenceBallChamber n K r)

@[simp] theorem hermitianReferenceBallHomeomorph_apply (r : ℝ) (x : HermitianCoordinates n K) :
    hermitianReferenceBallHomeomorph n K r x =
      hermitianCayleyOrbitChart (1 : Matrix.unitaryGroup (Fin n) K) x := rfl

theorem hermitianReferenceBallHomeomorph_source (n : ℕ) (K : Type*) [RCLike K] (r : ℝ) :
    (hermitianReferenceBallHomeomorph n K r).source =
      (hermitianReferenceLocalHomeomorph n K).source ∩ hermitianReferenceBallChamber n K r := rfl

/-- The angular image is a genuine open part of the ordered projector flag space.
The inverse function theorem and the proved spectral-label uniqueness discharge
the phase freedom rather than assuming a gauge chart. -/
theorem hermitianAngularFlagChart_image_eq_preimage_target (r : ℝ)
    (hball : Metric.ball (0 : HermitianCoordinateIndex n → K) r ⊆
      hermitianReferenceAngularSource n K) :
    hermitianAngularFlagChart '' Metric.ball (0 : HermitianCoordinateIndex n → K) r =
      (flagCoordinateEvaluation (K := K) (hermitianReferenceSpectrum n)) ⁻¹'
        (hermitianReferenceBallHomeomorph n K r).target := by
  apply Set.ext
  intro P
  constructor
  · rintro ⟨a, ha, rfl⟩
    have hx : (hermitianReferenceSpectrum n, a) ∈
        (hermitianReferenceBallHomeomorph n K r).source := by
      rw [hermitianReferenceBallHomeomorph_source]
      exact ⟨hball ha, hermitianReferenceSpectrum_mem_chamber n, ha⟩
    have ht := (hermitianReferenceBallHomeomorph n K r).map_source hx
    simpa only [Set.mem_preimage, hermitianReferenceBallHomeomorph_apply,
      hermitianCayleyOrbitChart_one_reference] using ht
  · intro hP
    let e := hermitianReferenceBallHomeomorph n K r
    let x := e.symm (flagCoordinateEvaluation (hermitianReferenceSpectrum n) P)
    have hx : x ∈ e.source := e.symm.map_source hP
    have he : hermitianCayleyOrbitChart (1 : Matrix.unitaryGroup (Fin n) K) x =
        flagCoordinateEvaluation (hermitianReferenceSpectrum n) P := by
      exact e.right_inv hP
    have hsource : x ∈ (hermitianReferenceLocalHomeomorph n K).source ∩
        hermitianReferenceBallChamber n K r := by
      exact hx
    obtain ⟨sigma, hperm⟩ := hermitianCayleyOrbitChart_one_eq_flag_permutation
      (hermitianReferenceSpectrum n) x P he
    have hlambda : x.1 = hermitianReferenceSpectrum n :=
      hermitianReferenceChamber_permutation_unique x.1 hsource.2.1 sigma hperm
    refine ⟨x.2, hsource.2.2, ?_⟩
    apply flagCoordinateEvaluation_injective (hermitianReferenceSpectrum n)
      (hermitianReferenceSpectrum_injective n)
    rw [← hermitianCayleyOrbitChart_one_reference]
    have hpair : x = (hermitianReferenceSpectrum n, x.2) := Prod.ext hlambda rfl
    rw [← hpair]
    exact he

theorem isOpen_hermitianAngularFlagChart_image (r : ℝ)
    (hball : Metric.ball (0 : HermitianCoordinateIndex n → K) r ⊆
      hermitianReferenceAngularSource n K) :
    IsOpen (hermitianAngularFlagChart '' Metric.ball (0 : HermitianCoordinateIndex n → K) r) := by
  rw [hermitianAngularFlagChart_image_eq_preimage_target r hball]
  exact (hermitianReferenceBallHomeomorph n K r).open_target.preimage
    (continuous_flagCoordinateEvaluation (hermitianReferenceSpectrum n))

/-- A proved bounded injective open flag chart, with a continuous strictly
positive angular Jacobian on its closed coordinate ball. -/
theorem exists_hermitian_open_flag_chart (n : ℕ) (K : Type*) [RCLike K] :
    ∃ r : ℝ, 0 < r ∧
      Set.InjOn (hermitianAngularFlagChart : (HermitianCoordinateIndex n → K) → _) (Metric.ball 0 r) ∧
      IsOpen (hermitianAngularFlagChart '' Metric.ball (0 : HermitianCoordinateIndex n → K) r) ∧
      flagOrbit (1 : Matrix.unitaryGroup (Fin n) K) ∈
        hermitianAngularFlagChart '' Metric.ball (0 : HermitianCoordinateIndex n → K) r ∧
      ∀ a : HermitianCoordinateIndex n → K, a ∈ Metric.closedBall 0 r →
        0 < hermitianAngularDensity a := by
  obtain ⟨r, hr, hball, hdensity⟩ := exists_hermitianFlagChart_radius n K
  refine ⟨r, hr, hermitianAngularFlagChart_injOn r hball,
    isOpen_hermitianAngularFlagChart_image r hball, ?_, hdensity⟩
  exact ⟨0, Metric.mem_ball_self hr, hermitianAngularFlagChart_zero⟩

end A3Research
