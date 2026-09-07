import LogdetLean.GramHafnian.ShiftedAnticoncentration.Experimental.GaussianPolar.CircularGaussianPolar
import LogdetLean.GramHafnian.ShiftedAnticoncentration.GaussianNormGamma

/-!
# Gamma identification of the polar radius
-/

open MeasureTheory ProbabilityTheory Set Metric Function
open scoped ENNReal NNReal Real Pointwise

namespace LogdetLean.GramHafnian

noncomputable section

theorem map_subtype_comap_circularGaussianEuclidean
    {k : ℕ} (hk : 0 < k) :
    Measure.map
        (Subtype.val : ({0}ᶜ : Set (CircularEuclideanSpace k)) →
          CircularEuclideanSpace k)
        (((Measure.pi fun _ : Fin k ↦ circularGaussian).map (WithLp.toLp 2)).comap
          (Subtype.val : ({0}ᶜ : Set (CircularEuclideanSpace k)) →
            CircularEuclideanSpace k)) =
      ((Measure.pi fun _ : Fin k ↦ circularGaussian).map (WithLp.toLp 2)) := by
  rw [map_comap_subtype_coe (measurableSet_singleton
    (0 : CircularEuclideanSpace k)).compl]
  rw [circularGaussianEuclidean_eq_withDensity]
  letI : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
  letI : Nontrivial (CircularEuclideanSpace k) := inferInstance
  letI : NullSingletonClass
      ((circularEuclideanVolume k).withDensity
        (circularGaussianEuclideanDensity k)) :=
    ⟨fun x ↦ by
      rw [withDensity_apply _ (measurableSet_singleton x)]
      simp⟩
  exact restrict_compl_singleton 0

/-- The positive radius is the second marginal of the normalized polar law. -/
theorem map_snd_polar_circularGaussianEuclidean
    {k : ℕ} (hk : 0 < k) :
    Measure.map Prod.snd
        (Measure.map (homeomorphUnitSphereProd (CircularEuclideanSpace k))
          (((Measure.pi fun _ : Fin k ↦ circularGaussian).map (WithLp.toLp 2)).comap
            (Subtype.val : ({0}ᶜ : Set (CircularEuclideanSpace k)) →
              CircularEuclideanSpace k))) =
      circularGaussianPositiveRadiusMeasure k := by
  letI : SFinite (circularGaussianPolarRadiusMeasure k) := by
    unfold circularGaussianPolarRadiusMeasure
    infer_instance
  letI : SFinite (circularGaussianPositiveRadiusMeasure k) := by
    unfold circularGaussianPositiveRadiusMeasure
    infer_instance
  rw [map_polar_comap_circularGaussianEuclidean_normalized hk,
    Measure.map_snd_prod,
    circularGaussianSphereProbability_apply_univ hk, one_smul]

/-- Reconstruct a Euclidean vector from its unit direction and positive
radius. -/
def circularGaussianPolarReconstruct (k : ℕ) :
    sphere (0 : CircularEuclideanSpace k) 1 × Ioi (0 : ℝ) →
      CircularEuclideanSpace k :=
  fun z ↦ ((homeomorphUnitSphereProd
    (CircularEuclideanSpace k)).symm z : CircularEuclideanSpace k)

@[fun_prop]
theorem measurable_circularGaussianPolarReconstruct (k : ℕ) :
    Measurable (circularGaussianPolarReconstruct k) := by
  unfold circularGaussianPolarReconstruct
  fun_prop

/-- Exact reconstruction law: an independent uniform direction and positive
Gaussian radius reconstruct one literal paper-normalized circular Gaussian
column. -/
theorem map_circularGaussianPolarReconstruct
    {k : ℕ} (hk : 0 < k) :
    Measure.map (circularGaussianPolarReconstruct k)
        ((circularGaussianSphereProbability k).prod
          (circularGaussianPositiveRadiusMeasure k)) =
      (Measure.pi fun _ : Fin k ↦ circularGaussian).map (WithLp.toLp 2) := by
  rw [← map_polar_comap_circularGaussianEuclidean_normalized hk]
  rw [Measure.map_map
    (measurable_circularGaussianPolarReconstruct k)
    (homeomorphUnitSphereProd (CircularEuclideanSpace k)).measurable]
  have hfun :
      circularGaussianPolarReconstruct k ∘
          (homeomorphUnitSphereProd (CircularEuclideanSpace k)) =
        (Subtype.val : ({0}ᶜ : Set (CircularEuclideanSpace k)) →
          CircularEuclideanSpace k) := by
    funext x
    simp [circularGaussianPolarReconstruct]
  rw [hfun, map_subtype_comap_circularGaussianEuclidean hk]

/-- Squaring the positive polar radius. -/
def circularGaussianSquaredRadiusMeasure (k : ℕ) : Measure ℝ :=
  (circularGaussianPositiveRadiusMeasure k).map
    (fun r : Ioi (0 : ℝ) ↦ r.1 ^ 2)

/-- Exact one-column squared-radius law.  In the project's existing Gamma
convention this is the image `u ↦ u/2` of shape `k`, rate `1/2`, equivalently
the usual shape `k`, rate `1` Gamma distribution. -/
theorem circularGaussianSquaredRadiusMeasure_eq_halfGamma
    {k : ℕ} (hk : 0 < k) :
    circularGaussianSquaredRadiusMeasure k =
      (gammaMeasure (k : ℝ) (1 / 2)).map (fun u : ℝ ↦ u / 2) := by
  let E := CircularEuclideanSpace k
  let P : Measure E :=
    (Measure.pi fun _ : Fin k ↦ circularGaussian).map (WithLp.toLp 2)
  let nz : Type := ({0}ᶜ : Set E)
  let polar := homeomorphUnitSphereProd E
  rw [← map_circularVectorNormSq_iid_circular_eq_half_gamma hk]
  unfold circularGaussianSquaredRadiusMeasure
  rw [← map_snd_polar_circularGaussianEuclidean hk]
  rw [Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  have hfun :
      ((fun r : Ioi (0 : ℝ) ↦ r.1 ^ 2) ∘ Prod.snd) ∘ polar =
        circularVectorNormSq ∘
          (Subtype.val : nz → E) := by
    funext x
    simp only [Function.comp_apply, circularVectorNormSq]
    rw [homeomorphUnitSphereProd_apply_snd_coe]
  rw [hfun]
  rw [← Measure.map_map measurable_circularVectorNormSq measurable_subtype_coe]
  rw [map_subtype_comap_circularGaussianEuclidean hk]

end

end LogdetLean.GramHafnian
