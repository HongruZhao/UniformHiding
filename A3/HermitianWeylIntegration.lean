import A3.HermitianWeylRadial
import A3.Shared.WeylIntegrationSeparatedDensity

open MeasureTheory MeasureTheory.Measure Set Function Metric
open scoped BigOperators ENNReal Matrix.Norms.Elementwise

noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

namespace A3Research

variable {n : ℕ} {K : Type*} [RCLike K]

/-- The raw Hermitian Weyl law uses the actual independent coordinate volume
and literal Hermitian spectrum. It applies to every measurable symmetric test. -/
structure HermitianWeylSymmetricIntegrationLaw (n : ℕ) (K : Type*) [RCLike K]
    [MeasureSpace K] [BorelSpace K] where
  orbitConstant : NNReal
  orbitConstant_pos : 0 < orbitConstant
  measurable_spectrum : Measurable (canonicalHermitianSpectrum : HermitianCoordinates n K → _)
  symmetric_flat_radial_law :
    ∀ {Y : Type} [MeasurableSpace Y] (F : (Fin n → ℝ) → Y),
      Measurable F →
      LogdetLean.GramHafnian.UltimateHiding.DenseScore.IsA2SymmetricTest F →
      Measure.map (F ∘ canonicalHermitianSpectrum) (hermitianCoordinateVolume n K) =
        (orbitConstant : ℝ≥0∞) • Measure.map F (hermitianFlatEigenvalueRadialMeasure n K)

/-- Complete Euclidean orbit integration assembly. All chart, derivative,
Jacobian, finite-cover and exact fiber hypotheses have been proved; only the
literal repeated-spectrum exceptional nullity is displayed for its independent
polynomial proof. -/
def hermitianWeylSymmetricIntegrationLaw_of_ae_regular
    (n : ℕ) (K : Type*) [RCLike K] [MeasureSpace K] [BorelSpace K] [PolishSpace K]
    [IsAddHaarMeasure (volume : Measure K)]
    (hae : ∀ᵐ x ∂hermitianCoordinateVolume n K, x ∈ regularHermitianCoordinateSet n K) :
    HermitianWeylSymmetricIntegrationLaw n K := by
  classical
  letI : IsAddHaarMeasure (hermitianCoordinateVolume n K) := by
    unfold hermitianCoordinateVolume
    exact prod.instIsAddHaarMeasure _ _
  let r := (exists_finite_hermitian_flag_atlas n K).choose
  let m := (exists_finite_hermitian_flag_atlas n K).choose_spec.choose
  let c := (exists_finite_hermitian_flag_atlas n K).choose_spec.choose_spec.choose
  rcases (exists_finite_hermitian_flag_atlas n K).choose_spec.choose_spec.choose_spec with
    ⟨hr, hdensity, hcont, hinj, hopen, hcover, hmeas⟩
  let phi := fun (i : Fin (m + 1)) (a : HermitianCoordinateIndex n → K) ↦
    flagAction (c i) (hermitianAngularFlagChart a)
  let bset := ball (0 : HermitianCoordinateIndex n → K) r
  let s := angularChartPiece bset phi
  refine ⟨hermitianAtlasOrbitConstant r m c,
    hermitianAtlasOrbitConstant_pos r hr m c hdensity,
    measurable_canonicalHermitianSpectrum, ?_⟩
  intro Y _ F hF hperm
  let S : HermitianCoordinates n K → Y := F ∘ canonicalHermitianSpectrum
  have hS : Measurable S := hF.comp measurable_canonicalHermitianSpectrum
  have he := measurePreserving_hermitianAngularRadialEquiv (n := n) (K := K)
  have hpos (i : Fin (m + 1)) (x : HermitianCoordinates n K)
      (hx : hermitianAngularRadialEquiv n K x ∈ s i ×ˢ regularHermitianRadii n) :
      0 < hermitianAngularDensity x.2 :=
    hdensity x.2 (ball_subset_closedBall (angularChartPiece_subset bset phi i hx.1))
  have hdet (i : Fin (m + 1)) (x : HermitianCoordinates n K)
      (hx : hermitianAngularRadialEquiv n K x ∈ s i ×ˢ regularHermitianRadii n) :
      (hermitianCayleyOrbitChartDerivative (c i) x).det ≠ 0 :=
    hermitianCayleyOrbitChartDerivative_det_ne_zero (c i) x (hpos i x hx) hx.2
  have himage (i : Fin (m + 1)) :
      hermitianCayleyOrbitChart (c i) ''
        ((hermitianAngularRadialEquiv n K) ⁻¹' (s i ×ˢ regularHermitianRadii n)) ⊆
          regularHermitianCoordinateSet n K := by
    rintro _ ⟨x, hx, rfl⟩
    exact hermitianOrbitCoordinates_mem_regular (c i * hermitianAngularCayley x.2) x.1 hx.2
  have hcard (y : HermitianCoordinates n K) (hy : y ∈ regularHermitianCoordinateSet n K) :
      Nonempty (chartFiber
        (fun i ↦ (hermitianAngularRadialEquiv n K) ⁻¹' (s i ×ˢ regularHermitianRadii n))
        (fun i ↦ hermitianCayleyOrbitChart (c i)) y ≃ Fin n.factorial) := by
    simpa only [phi, flagCoordinateEvaluation_translatedChart] using
      regularHermitianAtlasFiber_equiv_fin bset phi hinj hcover y hy
  have hsep (i : Fin (m + 1)) (x : HermitianCoordinates n K)
      (hx : hermitianAngularRadialEquiv n K x ∈ s i ×ˢ regularHermitianRadii n) :
      ENNReal.ofReal |(hermitianCayleyOrbitChartDerivative (c i) x).det| =
        ENNReal.ofReal (hermitianAngularDensity (hermitianAngularRadialEquiv n K x).1) *
          hermitianFlatEigenvalueDensity n K (hermitianAngularRadialEquiv n K x).2 := by
    rw [abs_det_hermitianCayleyOrbitChartDerivative]
    exact ENNReal.ofReal_mul (hpos i x hx).le
  have htest (i : Fin (m + 1)) (x : HermitianCoordinates n K)
      (_hx : hermitianAngularRadialEquiv n K x ∈ s i ×ˢ regularHermitianRadii n) :
      S (hermitianCayleyOrbitChart (c i) x) = F (hermitianAngularRadialEquiv n K x).2 :=
    invariant_test_hermitianOrbit F hperm (c i * hermitianAngularCayley x.2) x.1
  have hraw := map_test_eq_separated_regular_cover (hermitianCoordinateVolume n K)
    (volume : Measure (HermitianCoordinateIndex n → K)) (volume : Measure (Fin n → ℝ))
    (hermitianAngularRadialEquiv n K) he s (regularHermitianRadii n)
    hmeas (isOpen_regularHermitianRadii n).measurableSet
    (fun i ↦ hermitianCayleyOrbitChart (c i))
    (fun i ↦ hermitianCayleyOrbitChartDerivative (c i))
    (fun i ↦ (contDiff_hermitianCayleyOrbitChart (c i) 1).continuous.measurable)
    (fun i x _hx ↦ (contDiff_hermitianCayleyOrbitChart (c i) 1).contDiffAt)
    (fun i x _hx ↦ hasFDerivAt_hermitianCayleyOrbitChart (c i) x)
    hdet (regularHermitianCoordinateSet n K) measurableSet_regularHermitianCoordinateSet
    hae himage n.factorial n.factorial_pos hcard
    (fun a ↦ ENNReal.ofReal (hermitianAngularDensity a)) (hermitianFlatEigenvalueDensity n K)
    continuous_hermitianAngularDensity.measurable.ennreal_ofReal
    (measurable_hermitianFlatEigenvalueDensity n K) hsep S hS F hF htest
  rw [hermitianAtlasOrbitConstant_coe r hr m c hdensity]
  simpa only [tsum_fintype, regularHermitian_radial_withDensity_eq_flat,
    hermitianAtlasAngularMass, s, phi, bset, S] using hraw

end A3Research
