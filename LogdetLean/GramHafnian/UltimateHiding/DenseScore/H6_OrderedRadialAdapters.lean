import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H6_TakagiWeylAdapters
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H6_MuirheadAdapters

/-!
# Ordered-chamber radial adapters for H6

This module removes the artificial need to give the eigenvalues a random
unordered labelling.  Mathlib's canonical Hermitian eigenvalues are ordered
in decreasing order, so we restrict each raw radial measure to the strict
decreasing chamber.  The beta-to-beta-prime coordinate map is strictly
increasing on `(0,1)` and therefore preserves that chamber.

All results here are proved measure-theoretic adapters.  No Takagi coarea,
Weyl integration, Wishart density, H5, or H6 statement is assumed.
-/

open scoped ENNReal
open Set MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open H6CoordinateAlgebra H6VectorChangeOfVariables H6RadialMeasureAdapters

/-- The strict chamber matching Mathlib's decreasing eigenvalue convention. -/
def strictSpectralChamber (N : ℕ) : Set (Fin N → ℝ) :=
  ⋂ i : Fin N, ⋂ j : Fin N,
    if i < j then {x | x j < x i} else Set.univ

@[simp]
theorem mem_strictSpectralChamber_iff
    {N : ℕ} {x : Fin N → ℝ} :
    x ∈ strictSpectralChamber N ↔
      ∀ i j : Fin N, i < j → x j < x i := by
  simp [strictSpectralChamber]

theorem measurableSet_strictSpectralChamber (N : ℕ) :
    MeasurableSet (strictSpectralChamber N) := by
  unfold strictSpectralChamber
  refine MeasurableSet.iInter fun i ↦ MeasurableSet.iInter fun j ↦ ?_
  by_cases hij : i < j
  · simp only [hij, if_pos]
    exact measurableSet_lt (measurable_pi_apply j) (measurable_pi_apply i)
  · simp [hij]

/-- The scalar beta-to-beta-prime map is strictly increasing on `(0,1)`. -/
theorem strictMonoOn_betaPrimeForward_Ioo :
    StrictMonoOn betaPrimeForward (Ioo (0 : ℝ) 1) := by
  intro a ha b hb hab
  rw [← sub_pos]
  rw [betaPrimeForward_sub b a (ne_of_lt hb.2) (ne_of_lt ha.2)]
  exact div_pos (sub_pos.mpr hab)
    (mul_pos (sub_pos.mpr hb.2) (sub_pos.mpr ha.2))

/-- On the unit cube, the coordinatewise beta-prime map preserves and
reflects the strict decreasing chamber. -/
theorem betaPrimeForwardVector_mem_strictSpectralChamber_iff
    {N : ℕ} {lambda : Fin N → ℝ}
    (hlambda : lambda ∈ openUnitCube N) :
    betaPrimeForwardVector N lambda ∈ strictSpectralChamber N ↔
      lambda ∈ strictSpectralChamber N := by
  rw [mem_strictSpectralChamber_iff, mem_strictSpectralChamber_iff]
  constructor
  · intro h i j hij
    exact (strictMonoOn_betaPrimeForward_Ioo.lt_iff_lt
      (hlambda j) (hlambda i)).mp (h i j hij)
  · intro h i j hij
    exact strictMonoOn_betaPrimeForward_Ioo
      (hlambda j) (hlambda i) (h i j hij)

/-! ## Ordered raw and normalized radial measures -/

def orderedTakagiFlatEigenvalueRadialMeasure (N : ℕ) :
    Measure (Fin N → ℝ) :=
  (takagiFlatEigenvalueRadialMeasure N).restrict
    (strictSpectralChamber N)

def orderedCOEEigenvalueRadialMeasure (N K : ℕ) :
    Measure (Fin N → ℝ) :=
  (coeEigenvalueRadialMeasure N K).restrict (strictSpectralChamber N)

def orderedBetaPrimeEigenvalueRadialMeasure (N K : ℕ) :
    Measure (Fin N → ℝ) :=
  (betaPrimeEigenvalueRadialMeasure N K).restrict (strictSpectralChamber N)

def orderedRealBetaIIEigenvalueRadialMeasure (N m n : ℕ) :
    Measure (Fin N → ℝ) :=
  (realBetaIIEigenvalueRadialMeasure N m n).restrict
    (strictSpectralChamber N)

def normalizedOrderedCOEEigenvalueRadialMeasure (N K : ℕ) :
    Measure (Fin N → ℝ) :=
  ((orderedCOEEigenvalueRadialMeasure N K) Set.univ)⁻¹ •
    orderedCOEEigenvalueRadialMeasure N K

def normalizedOrderedBetaPrimeEigenvalueRadialMeasure (N K : ℕ) :
    Measure (Fin N → ℝ) :=
  ((orderedBetaPrimeEigenvalueRadialMeasure N K) Set.univ)⁻¹ •
    orderedBetaPrimeEigenvalueRadialMeasure N K

theorem orderedTakagiFlat_withDensity_boundary_eq_orderedCOE
    (N K : ℕ) :
    (orderedTakagiFlatEigenvalueRadialMeasure N).withDensity
        (coeTakagiBoundaryDensity N K) =
      orderedCOEEigenvalueRadialMeasure N K := by
  unfold orderedTakagiFlatEigenvalueRadialMeasure
    orderedCOEEigenvalueRadialMeasure
  rw [← restrict_withDensity (measurableSet_strictSpectralChamber N)]
  rw [takagiFlatRadial_withDensity_boundary_eq_coeRadial]

theorem orderedRealBetaIIEigenvalueRadialMeasure_specializes
    {N K : ℕ} (hNK : N ≤ K) :
    orderedRealBetaIIEigenvalueRadialMeasure N (N + 1) (K - N) =
      orderedBetaPrimeEigenvalueRadialMeasure N K := by
  unfold orderedRealBetaIIEigenvalueRadialMeasure
    orderedBetaPrimeEigenvalueRadialMeasure
  rw [realBetaIIEigenvalueRadialMeasure_specializes hNK]

theorem coeEigenvalueRadialMeasure_ae_openUnitCube_raw
    (N K : ℕ) :
    ∀ᵐ lambda ∂coeEigenvalueRadialMeasure N K,
      lambda ∈ openUnitCube N := by
  unfold coeEigenvalueRadialMeasure
  exact withDensity_restrict_ae_mem volume (openUnitCube N)
    (coeEigenvalueDensity N K) (measurableSet_openUnitCube_h6 N)

theorem betaPrimeEigenvalueRadialMeasure_ae_positive_raw
    (N K : ℕ) :
    ∀ᵐ x ∂betaPrimeEigenvalueRadialMeasure N K,
      x ∈ openPositiveOrthant N := by
  unfold betaPrimeEigenvalueRadialMeasure
  exact withDensity_restrict_ae_mem volume (openPositiveOrthant N)
    (betaPrimeEigenvalueDensity N K)
    (measurableSet_openPositiveOrthant_h6 N)

theorem orderedTakagiFlatEigenvalueRadialMeasure_ae_positive_ordered
    (N : ℕ) :
    ∀ᵐ lambda ∂orderedTakagiFlatEigenvalueRadialMeasure N,
      lambda ∈ openPositiveOrthant N ∧
        lambda ∈ strictSpectralChamber N := by
  have hpos : ∀ᵐ lambda ∂orderedTakagiFlatEigenvalueRadialMeasure N,
      lambda ∈ openPositiveOrthant N :=
    Measure.absolutelyContinuous_restrict.ae_le
      (takagiFlatEigenvalueRadialMeasure_ae_positive N)
  have hord : ∀ᵐ lambda ∂orderedTakagiFlatEigenvalueRadialMeasure N,
      lambda ∈ strictSpectralChamber N := by
    unfold orderedTakagiFlatEigenvalueRadialMeasure
    exact ae_restrict_mem (measurableSet_strictSpectralChamber N)
  exact hpos.and hord

theorem orderedCOEEigenvalueRadialMeasure_ae_unit_ordered
    (N K : ℕ) :
    ∀ᵐ lambda ∂orderedCOEEigenvalueRadialMeasure N K,
      lambda ∈ openUnitCube N ∧
        lambda ∈ strictSpectralChamber N := by
  have hcube : ∀ᵐ lambda ∂orderedCOEEigenvalueRadialMeasure N K,
      lambda ∈ openUnitCube N :=
    Measure.absolutelyContinuous_restrict.ae_le
      (coeEigenvalueRadialMeasure_ae_openUnitCube_raw N K)
  have hord : ∀ᵐ lambda ∂orderedCOEEigenvalueRadialMeasure N K,
      lambda ∈ strictSpectralChamber N := by
    unfold orderedCOEEigenvalueRadialMeasure
    exact ae_restrict_mem (measurableSet_strictSpectralChamber N)
  exact hcube.and hord

theorem orderedBetaPrimeEigenvalueRadialMeasure_ae_positive_ordered
    (N K : ℕ) :
    ∀ᵐ x ∂orderedBetaPrimeEigenvalueRadialMeasure N K,
      x ∈ openPositiveOrthant N ∧ x ∈ strictSpectralChamber N := by
  have hpos : ∀ᵐ x ∂orderedBetaPrimeEigenvalueRadialMeasure N K,
      x ∈ openPositiveOrthant N :=
    Measure.absolutelyContinuous_restrict.ae_le
      (betaPrimeEigenvalueRadialMeasure_ae_positive_raw N K)
  have hord : ∀ᵐ x ∂orderedBetaPrimeEigenvalueRadialMeasure N K,
      x ∈ strictSpectralChamber N := by
    unfold orderedBetaPrimeEigenvalueRadialMeasure
    exact ae_restrict_mem (measurableSet_strictSpectralChamber N)
  exact hpos.and hord

/-- Exact raw coordinate transport after restricting to the canonical strict
spectral chamber. -/
theorem map_orderedCOEEigenvalueRadialMeasure_eq_orderedBetaPrime
    {N K : ℕ} (hN : 1 ≤ N) :
    Measure.map (betaPrimeForwardVector N)
        (orderedCOEEigenvalueRadialMeasure N K) =
      orderedBetaPrimeEigenvalueRadialMeasure N K := by
  let mu := coeEigenvalueRadialMeasure N K
  let S := strictSpectralChamber N
  have hsupport : ∀ᵐ lambda ∂mu, lambda ∈ openUnitCube N := by
    simpa [mu] using coeEigenvalueRadialMeasure_ae_openUnitCube_raw N K
  have hpre :
      (betaPrimeForwardVector N ⁻¹' S) =ᵐ[mu] S := by
    filter_upwards [hsupport] with lambda hlambda
    apply propext
    change betaPrimeForwardVector N lambda ∈ S ↔ lambda ∈ S
    simpa [S] using
      (betaPrimeForwardVector_mem_strictSpectralChamber_iff hlambda)
  have hrestrict :
      mu.restrict (betaPrimeForwardVector N ⁻¹' S) =
        mu.restrict S :=
    Measure.restrict_congr_set hpre
  unfold orderedCOEEigenvalueRadialMeasure
    orderedBetaPrimeEigenvalueRadialMeasure
  change Measure.map (betaPrimeForwardVector N) (mu.restrict S) = _
  calc
    Measure.map (betaPrimeForwardVector N) (mu.restrict S) =
        Measure.map (betaPrimeForwardVector N)
          (mu.restrict (betaPrimeForwardVector N ⁻¹' S)) := by
      rw [hrestrict]
    _ = (Measure.map (betaPrimeForwardVector N) mu).restrict S :=
      (Measure.restrict_map (μ := mu)
        (measurable_betaPrimeForwardVector N)
        (measurableSet_strictSpectralChamber N)).symm
    _ = (betaPrimeEigenvalueRadialMeasure N K).restrict S := by
      rw [show Measure.map (betaPrimeForwardVector N) mu =
          betaPrimeEigenvalueRadialMeasure N K by
        simpa [mu] using
          (map_coeEigenvalueRadialMeasure_eq_betaPrime
            (N := N) (K := K) hN)]

/-- Canonical normalization commutes with the ordered coordinate transport. -/
theorem map_normalizedOrderedCOE_eq_normalizedOrderedBetaPrime
    {N K : ℕ} (hN : 1 ≤ N) :
    Measure.map (betaPrimeForwardVector N)
        (normalizedOrderedCOEEigenvalueRadialMeasure N K) =
      normalizedOrderedBetaPrimeEigenvalueRadialMeasure N K := by
  have hraw := map_orderedCOEEigenvalueRadialMeasure_eq_orderedBetaPrime
    (N := N) (K := K) hN
  have hmass :
      orderedCOEEigenvalueRadialMeasure N K Set.univ =
        orderedBetaPrimeEigenvalueRadialMeasure N K Set.univ := by
    rw [← hraw]
    rw [Measure.map_apply (measurable_betaPrimeForwardVector N)
      MeasurableSet.univ]
    simp
  unfold normalizedOrderedCOEEigenvalueRadialMeasure
    normalizedOrderedBetaPrimeEigenvalueRadialMeasure
  rw [Measure.map_smul, hraw, hmass]

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
