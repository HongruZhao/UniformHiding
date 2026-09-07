import LogdetLean.GramHafnian.ShiftedAnticoncentration.Experimental.GaussianPolar.EuclideanCircularDensity

/-!
# Exact polar product law for a literal circular Gaussian column

The source law is restricted to the nonzero subtype, on which Mathlib's
polar homeomorphism is defined.  The excluded origin is null for every
positive-dimensional circular Gaussian law.
-/

open MeasureTheory ProbabilityTheory Set Metric Function
open scoped ENNReal NNReal Real Pointwise

namespace LogdetLean.GramHafnian

noncomputable section

/-- Pulling a density back to a measurable subtype commutes with `comap`. -/
private theorem comap_subtype_withDensity
    {α : Type*} [MeasurableSpace α] {s : Set α} (hs : MeasurableSet s)
    (μ : Measure α) (f : α → ℝ≥0∞) (hf : Measurable f) :
    (μ.withDensity f).comap (Subtype.val : s → α) =
      (μ.comap (Subtype.val : s → α)).withDensity (f ∘ Subtype.val) := by
  ext t ht
  rw [(MeasurableEmbedding.subtype_coe hs).comap_apply,
    withDensity_apply _ ((MeasurableEmbedding.subtype_coe hs).measurableSet_image' ht),
    withDensity_apply _ ht]
  exact (setLIntegral_subtype hs t f).symm

/-- The radial weight remaining after the polar Jacobian is put into
`volumeIoiPow`. -/
def circularGaussianRadiusWeight (k : ℕ) (r : Ioi (0 : ℝ)) : ℝ≥0∞ :=
  ENNReal.ofReal ((Real.pi⁻¹) ^ k * Real.exp (-(r.1 ^ 2)))

@[fun_prop]
theorem measurable_circularGaussianRadiusWeight (k : ℕ) :
    Measurable (circularGaussianRadiusWeight k) := by
  unfold circularGaussianRadiusWeight
  fun_prop

/-- The unnormalized radial factor supplied by polar coordinates. -/
def circularGaussianPolarRadiusMeasure (k : ℕ) : Measure (Ioi (0 : ℝ)) :=
  (Measure.volumeIoiPow
      (Module.finrank ℝ (CircularEuclideanSpace k) - 1)).withDensity
    (circularGaussianRadiusWeight k)

private theorem polar_density_depends_only_on_radius
    {k : ℕ} (hk : 0 < k)
    (z : sphere (0 : CircularEuclideanSpace k) 1 × Ioi (0 : ℝ)) :
    circularGaussianEuclideanDensity k
        ((homeomorphUnitSphereProd (CircularEuclideanSpace k)).symm z) =
      circularGaussianRadiusWeight k z.2 := by
  unfold circularGaussianEuclideanDensity circularGaussianRadiusWeight
  congr 1
  rw [homeomorphUnitSphereProd_symm_apply_coe, norm_smul,
    Real.norm_eq_abs, abs_of_pos z.2.2]
  have hz : ‖(z.1 : CircularEuclideanSpace k)‖ = 1 := by
    simpa [mem_sphere_zero_iff_norm] using z.1.2
  rw [hz, mul_one]

/-- Exact radius-direction product law for one literal paper-normalized
circular complex Gaussian column.  The first factor is the spherical Haar
measure induced by transported product complex volume; the second factor is
the positive-radius measure containing the Gaussian radial density and the
polar Jacobian. -/
theorem map_polar_comap_circularGaussianEuclidean
    {k : ℕ} (hk : 0 < k) :
    Measure.map (homeomorphUnitSphereProd (CircularEuclideanSpace k))
        (((Measure.pi fun _ : Fin k ↦ circularGaussian).map (WithLp.toLp 2)).comap
          (Subtype.val : ({0}ᶜ : Set (CircularEuclideanSpace k)) →
            CircularEuclideanSpace k)) =
      (circularEuclideanVolume k).toSphere.prod
        (circularGaussianPolarRadiusMeasure k) := by
  let E := CircularEuclideanSpace k
  let μ : Measure E := circularEuclideanVolume k
  let d : E → ℝ≥0∞ := circularGaussianEuclideanDensity k
  let e : ({0}ᶜ : Set E) ≃ᵐ
      (sphere (0 : E) 1 × Ioi (0 : ℝ)) :=
    (homeomorphUnitSphereProd E).toMeasurableEquiv
  have hzero : MeasurableSet ({0}ᶜ : Set E) := measurableSet_singleton 0 |>.compl
  rw [circularGaussianEuclidean_eq_withDensity]
  rw [comap_subtype_withDensity hzero μ d
    (measurable_circularGaussianEuclideanDensity k)]
  change Measure.map e ((μ.comap Subtype.val).withDensity
      (d ∘ Subtype.val)) = _
  rw [map_measurableEquiv_withDensity_localAnticoncentration e
    (μ.comap Subtype.val) (d ∘ Subtype.val)]
  · have hmap : Measure.map e (μ.comap Subtype.val) =
        μ.toSphere.prod
          (Measure.volumeIoiPow (Module.finrank ℝ E - 1)) := by
      simpa [e] using
        (μ.measurePreserving_homeomorphUnitSphereProd).map_eq
    rw [hmap]
    change (μ.toSphere.prod
        (Measure.volumeIoiPow (Module.finrank ℝ E - 1))).withDensity
          ((d ∘ Subtype.val) ∘ e.symm) =
      μ.toSphere.prod (circularGaussianPolarRadiusMeasure k)
    symm
    unfold circularGaussianPolarRadiusMeasure
    change μ.toSphere.prod
        ((Measure.volumeIoiPow (Module.finrank ℝ E - 1)).withDensity
          (circularGaussianRadiusWeight k)) = _
    rw [prod_withDensity_right
      (measurable_circularGaussianRadiusWeight k)]
    congr 1
    funext z
    exact (polar_density_depends_only_on_radius hk z).symm
  · exact (measurable_circularGaussianEuclideanDensity k).comp
      measurable_subtype_coe

/-! ## Probability-normalized factors -/

/-- Uniform direction law induced by the transported complex volume. -/
def circularGaussianSphereProbability (k : ℕ) :
    Measure (sphere (0 : CircularEuclideanSpace k) 1) :=
  let S := (circularEuclideanVolume k).toSphere
  (S univ)⁻¹ • S

/-- Positive-radius marginal paired with `circularGaussianSphereProbability`. -/
def circularGaussianPositiveRadiusMeasure (k : ℕ) : Measure (Ioi (0 : ℝ)) :=
  let S := (circularEuclideanVolume k).toSphere
  (S univ) • circularGaussianPolarRadiusMeasure k

/-- The normalized spherical factor has total mass one in positive complex
dimension. -/
theorem circularGaussianSphereProbability_apply_univ
    {k : ℕ} (hk : 0 < k) :
    circularGaussianSphereProbability k univ = 1 := by
  let E := CircularEuclideanSpace k
  let μ : Measure E := circularEuclideanVolume k
  letI : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
  letI : Nontrivial E := inferInstance
  have hS0 : μ.toSphere univ ≠ 0 :=
    Measure.measure_univ_ne_zero.mpr (μ.toSphere_ne_zero)
  have hSt : μ.toSphere univ ≠ ∞ := ne_of_lt (measure_lt_top μ.toSphere univ)
  unfold circularGaussianSphereProbability
  change ((μ.toSphere univ)⁻¹ • μ.toSphere) univ = 1
  rw [Measure.smul_apply]
  change (μ.toSphere univ)⁻¹ * μ.toSphere univ = 1
  rw [ENNReal.inv_mul_cancel hS0 hSt]

/-- Probability-normalized exact polar independence: the literal circular
Gaussian direction and its positive radius form a product measure. -/
theorem map_polar_comap_circularGaussianEuclidean_normalized
    {k : ℕ} (hk : 0 < k) :
    Measure.map (homeomorphUnitSphereProd (CircularEuclideanSpace k))
        (((Measure.pi fun _ : Fin k ↦ circularGaussian).map (WithLp.toLp 2)).comap
          (Subtype.val : ({0}ᶜ : Set (CircularEuclideanSpace k)) →
            CircularEuclideanSpace k)) =
      (circularGaussianSphereProbability k).prod
        (circularGaussianPositiveRadiusMeasure k) := by
  rw [map_polar_comap_circularGaussianEuclidean hk]
  let E := CircularEuclideanSpace k
  let μ : Measure E := circularEuclideanVolume k
  let S : Measure (sphere (0 : E) 1) := μ.toSphere
  let R : Measure (Ioi (0 : ℝ)) := circularGaussianPolarRadiusMeasure k
  letI : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
  letI : Nontrivial E := inferInstance
  have hS0 : S univ ≠ 0 := by
    exact Measure.measure_univ_ne_zero.mpr (μ.toSphere_ne_zero)
  have hSt : S univ ≠ ∞ := ne_of_lt (measure_lt_top S univ)
  letI : SFinite R := by
    dsimp [R, circularGaussianPolarRadiusMeasure]
    infer_instance
  letI : SFinite (S univ • R) := inferInstance
  change S.prod R = ((S univ)⁻¹ • S).prod ((S univ) • R)
  rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
    ENNReal.inv_mul_cancel hS0 hSt, one_smul]

end

end LogdetLean.GramHafnian
