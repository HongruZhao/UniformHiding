import A2.OrbitMeasureTakagiAtlas
import A2.OrbitMeasureEuclideanFiber
import A2.WeylIntegrationSeparatedDensity
import A2.WeylIntegrationCayleyChart

open MeasureTheory MeasureTheory.Measure Set Function Metric
open scoped BigOperators ENNReal

noncomputable section

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- The integration proof from the actual Cayley orbit derivative. Every
measure, selector, finite atlas, exceptional set and fiber in this theorem
is the concrete object of the original target. The remaining calculus
inputs are displayed explicitly for discharge by the derivative module. -/
def takagiWeylSymmetricIntegrationLaw_of_orbit_derivative
    (N : ℕ)
    (D : Matrix.unitaryGroup (Fin N) ℂ → TakagiRealCoordinates N →
      TakagiRealCoordinates N →L[ℝ] TakagiRealCoordinates N)
    (hC1 : ∀ U x, (∀ i, 0 < (takagiAngularRadialCoordinatesEquiv N x).2 i) →
      ContDiffAt ℝ 1 (takagiCayleyOrbitChart U) x)
    (hD : ∀ U x, (∀ i, 0 < (takagiAngularRadialCoordinatesEquiv N x).2 i) →
      HasFDerivAt (takagiCayleyOrbitChart U) (D U x) x)
    (hJac : ∀ U x, (∀ i, 0 < (takagiAngularRadialCoordinatesEquiv N x).2 i) →
      |(D U x).det| =
        takagiCayleyAngularDensity (takagiAngularRadialCoordinatesEquiv N x).1 *
          H6DensityTransform.vandermondeAbs N (takagiAngularRadialCoordinatesEquiv N x).2) :
    TakagiWeylSymmetricIntegrationLaw N := by
  let n := (exists_finite_takagiCayley_atlas N).choose
  let c := (exists_finite_takagiCayley_atlas N).choose_spec.choose
  rcases (exists_finite_takagiCayley_atlas N).choose_spec.choose_spec with
    ⟨hcont, hinj, hopen, hcover, hmeas⟩
  let φ := fun (i : Fin (n + 1)) (a : TakagiAngularCoordinates N) ↦
    c i * takagiAngularCayley a
  let bset := ball (0 : TakagiAngularCoordinates N) 1
  let s := A2Research.angularChartPiece bset φ
  refine ⟨takagiAtlasOrbitConstant n c, takagiAtlasOrbitConstant_pos n c,
    measurable_canonicalGapSquaredSpectrum N, ?_⟩
  intro Y _ F hF hperm
  let S := F ∘ canonicalGapSquaredSpectrum N ∘ takagiMatrixOfRealCoordinates
  have hS : Measurable S := (hF.comp (measurable_canonicalGapSquaredSpectrum N)).comp
    (measurable_takagiMatrixOfRealCoordinates N)
  have he : MeasurePreserving (takagiAngularRadialCoordinatesEquiv N)
      (volume : Measure (TakagiRealCoordinates N))
      ((volume : Measure (TakagiAngularCoordinates N)).prod (volume : Measure (Fin N → ℝ))) :=
    volume_preserving_takagiAngularRadialCoordinatesEquiv N
  have hdet (i : Fin (n + 1)) (x : TakagiRealCoordinates N)
      (hx : takagiAngularRadialCoordinatesEquiv N x ∈ s i ×ˢ regularTakagiSquaredRadii N) :
      (D (c i) x).det ≠ 0 := by
    apply abs_pos.mp
    rw [hJac (c i) x hx.2.1]
    exact mul_pos (takagiCayleyAngularDensity_pos _)
      ((vandermondeAbs_pos_iff_injective _).mpr hx.2.2)
  have himage (i : Fin (n + 1)) :
      takagiCayleyOrbitChart (c i) ''
        ((takagiAngularRadialCoordinatesEquiv N) ⁻¹' (s i ×ˢ regularTakagiSquaredRadii N)) ⊆
          regularTakagiRealMatrixSet N := by
    rintro _ ⟨x, hx, rfl⟩
    exact takagiRealOrbitCoordinates_mem_regular
      (c i * takagiAngularCayley (takagiAngularRadialCoordinatesEquiv N x).1)
      (takagiAngularRadialCoordinatesEquiv N x).2 hx.2
  have hcard (y : TakagiRealCoordinates N) (hy : y ∈ regularTakagiRealMatrixSet N) :
      Nonempty (A2Research.chartFiber
        (fun i ↦ (takagiAngularRadialCoordinatesEquiv N) ⁻¹'
          (s i ×ˢ regularTakagiSquaredRadii N))
        (fun i ↦ takagiCayleyOrbitChart (c i)) y ≃ Fin (2 ^ N * N.factorial)) := by
    exact regularOrbitAtlasFiber_equiv_fin bset φ hinj hcover y hy
  have hsep (i : Fin (n + 1)) (x : TakagiRealCoordinates N)
      (hx : takagiAngularRadialCoordinatesEquiv N x ∈ s i ×ˢ regularTakagiSquaredRadii N) :
      ENNReal.ofReal |(D (c i) x).det| =
        ENNReal.ofReal (takagiCayleyAngularDensity (takagiAngularRadialCoordinatesEquiv N x).1) *
          takagiFlatEigenvalueDensity N (takagiAngularRadialCoordinatesEquiv N x).2 := by
    rw [hJac (c i) x hx.2.1]
    exact ENNReal.ofReal_mul (takagiCayleyAngularDensity_pos _).le
  have htest (i : Fin (n + 1)) (x : TakagiRealCoordinates N)
      (hx : takagiAngularRadialCoordinatesEquiv N x ∈ s i ×ˢ regularTakagiSquaredRadii N) :
      S (takagiCayleyOrbitChart (c i) x) = F (takagiAngularRadialCoordinatesEquiv N x).2 := by
    change F (canonicalGapSquaredSpectrum N (takagiMatrixOfRealCoordinates
      (takagiRealOrbitCoordinates
        (c i * takagiAngularCayley (takagiAngularRadialCoordinatesEquiv N x).1)
        (takagiAngularRadialCoordinatesEquiv N x).2))) = _
    rw [takagiMatrixOfRealCoordinates_takagiRealOrbitCoordinates]
    exact invariant_test_takagiOrbit F hperm _ _ (fun j ↦ (hx.2.1 j).le)
  have hk : 0 < 2 ^ N * N.factorial :=
    Nat.mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) N) N.factorial_pos
  have hraw := A2Research.map_test_eq_separated_regular_cover volume
    (volume : Measure (TakagiAngularCoordinates N)) (volume : Measure (Fin N → ℝ))
    (takagiAngularRadialCoordinatesEquiv N) he s (regularTakagiSquaredRadii N)
    hmeas (isOpen_regularTakagiSquaredRadii N).measurableSet
    (fun i ↦ takagiCayleyOrbitChart (c i)) (fun i ↦ D (c i))
    (fun i ↦ measurable_takagiCayleyOrbitChart (c i))
    (fun i x hx ↦ hC1 (c i) x hx.2.1) (fun i x hx ↦ hD (c i) x hx.2.1)
    hdet (regularTakagiRealMatrixSet N) (measurableSet_regularTakagiRealMatrixSet N)
    (ae_mem_regularTakagiRealMatrixSet N) himage (2 ^ N * N.factorial) hk hcard
    (fun a ↦ ENNReal.ofReal (takagiCayleyAngularDensity a)) (takagiFlatEigenvalueDensity N)
    (continuous_takagiCayleyAngularDensity N).measurable.ennreal_ofReal
    (a2_measurable_takagiFlatEigenvalueDensity N) hsep S hS F hF htest
  rw [map_invariant_test_matrixVolume_eq_realVolume F hF, takagiAtlasOrbitConstant_coe]
  simpa only [tsum_fintype, regular_radial_withDensity_eq_flat,
    takagiAtlasAngularMass, s, φ, bset, S] using hraw

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
