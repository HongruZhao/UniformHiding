import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H6_BetaJacobiCore
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H6_Conditional
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H6_VectorChangeOfVariables
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ConcreteCOEStatistics
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# H6 beta-Jacobi to beta-prime transport

This theorem-only module identifies the beta-Jacobi law with literal project
parameters

`n = N`, `a = 1`, `b = K - 2N`, `beta = 1`

with the canonically normalized squared-Takagi radial measure already used by
the frozen H6 reduction.  It then applies the independently proved odds chart
`lambda |-> lambda / (1-lambda)` to obtain the normalized beta-prime radial
measure.  No A2 or A3 source atom, project endpoint, or new axiom is used.

The last section exposes the exact first- and third-power-sum projections used
by H6 consumers.  Signed centered cubes and absolute third moments are kept as
different definitions and related only by an explicit absolute-value lemma.
-/

open scoped BigOperators ENNReal
open Set MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open H6CoordinateAlgebra H6DensityTransform H6VectorChangeOfVariables
open H6RadialMeasureAdapters

/-! ## Literal density and normalization identification -/

theorem h6_betaJacobi_right_exponent
    {N K : ℕ} (h2NK : 2 * N ≤ K) :
    (1 : ℝ) * ((((K - 2 * N : ℕ) : ℝ)) + 1) / 2 - 1 =
      coeEigenvalueExponent N K := by
  unfold coeEigenvalueExponent
  rw [Nat.cast_sub h2NK]
  push_cast
  ring

theorem h6_betaJacobiKernel_eq_coeEigenvalueDensity
    {N K : ℕ} (h2NK : 2 * N ≤ K)
    {lambda_i : Fin N → ℝ} (hlambda : lambda_i ∈ openUnitCube N) :
    betaJacobiKernel N 1 (((K - 2 * N : ℕ) : ℝ)) 1 lambda_i =
      coeEigenvalueDensity N K lambda_i := by
  classical
  have hexp := h6_betaJacobi_right_exponent (N := N) (K := K) h2NK
  have hvand :
      (∏ p ∈ a2StrictPairs N,
          (ENNReal.ofReal |lambda_i p.2 - lambda_i p.1|).rpow (1 : ℝ)) =
        ENNReal.ofReal (vandermondeAbs N lambda_i) := by
    rw [show a2StrictPairs N = strictPairs N by rfl]
    simp only [vandermondeAbs]
    rw [ENNReal.ofReal_prod_of_nonneg]
    · apply Finset.prod_congr rfl
      intro p hp
      change (ENNReal.ofReal |lambda_i p.2 - lambda_i p.1|) ^ (1 : ℝ) = _
      rw [ENNReal.rpow_one]
      rw [abs_sub_comm]
    · intro p hp
      exact abs_nonneg _
  have hboundary :
      (∏ i : Fin N,
          (ENNReal.ofReal (1 - lambda_i i)).rpow
            (coeEigenvalueExponent N K)) =
        ENNReal.ofReal
          (unitBoundaryRpowProduct N (coeEigenvalueExponent N K) lambda_i) := by
    unfold unitBoundaryRpowProduct
    rw [ENNReal.ofReal_prod_of_nonneg]
    · apply Finset.prod_congr rfl
      intro i hi
      exact ENNReal.ofReal_rpow_of_pos (sub_pos.mpr (hlambda i).2)
    · intro i hi
      exact Real.rpow_nonneg (sub_nonneg.mpr (le_of_lt (hlambda i).2)) _
  unfold betaJacobiKernel coeEigenvalueDensity coeEigenvalueWeight
  rw [hexp]
  have hleft : (1 : ℝ) * (1 + 1) / 2 - 1 = 0 := by norm_num
  rw [hleft]
  simp only [ENNReal.rpow_eq_pow, ENNReal.rpow_zero, one_mul]
  have hvand' :
      (∏ p ∈ a2StrictPairs N,
          (ENNReal.ofReal |lambda_i p.2 - lambda_i p.1|) ^ (1 : ℝ)) =
        ENNReal.ofReal (vandermondeAbs N lambda_i) := by
    simpa only [ENNReal.rpow_eq_pow] using hvand
  have hboundary' :
      (∏ i : Fin N,
          (ENNReal.ofReal (1 - lambda_i i)) ^
            (coeEigenvalueExponent N K)) =
        ENNReal.ofReal
          (unitBoundaryRpowProduct N (coeEigenvalueExponent N K) lambda_i) := by
    simpa only [ENNReal.rpow_eq_pow] using hboundary
  rw [hvand', hboundary']
  rw [ENNReal.ofReal_mul]
  · ac_rfl
  · classical
    unfold vandermondeAbs
    positivity

/-- At the H6 parameters, the displayed beta-Jacobi raw density is literally
the existing unnormalized squared-Takagi radial measure. -/
theorem betaJacobiRawMeasure_h6_eq_coeEigenvalueRadialMeasure
    {N K : ℕ} (h2NK : 2 * N ≤ K) :
    betaJacobiRawMeasure N 1 (((K - 2 * N : ℕ) : ℝ)) 1 =
      coeEigenvalueRadialMeasure N K := by
  unfold betaJacobiRawMeasure betaJacobiOpenCube
    coeEigenvalueRadialMeasure
  apply withDensity_congr_ae
  have hcube : MeasurableSet (openUnitCube N) := by
    simpa [← betaPrimeCoordVector_source] using
      (betaPrimeCoordVector N).open_source.measurableSet
  filter_upwards [ae_restrict_mem hcube] with lambda_i hlambda
  exact h6_betaJacobiKernel_eq_coeEigenvalueDensity h2NK hlambda

theorem betaJacobiNormalization_h6_eq_coeRadialMass
    {N K : ℕ} (h2NK : 2 * N ≤ K) :
    betaJacobiNormalization N 1 (((K - 2 * N : ℕ) : ℝ)) 1 =
      coeEigenvalueRadialMeasure N K Set.univ := by
  unfold betaJacobiNormalization
  rw [betaJacobiRawMeasure_h6_eq_coeEigenvalueRadialMeasure h2NK]

/-- No separate Selberg constant and no hidden `N!` occur: both sides are
the same full-cube raw measure normalized by its own total mass. -/
theorem betaJacobiProbabilityMeasure_h6_eq_normalizedCOERadial
    {N K : ℕ} (h2NK : 2 * N ≤ K) :
    betaJacobiProbabilityMeasure N 1
        (((K - 2 * N : ℕ) : ℝ)) 1 =
      normalizedCOEEigenvalueRadialMeasure N K := by
  unfold betaJacobiProbabilityMeasure normalizedCOEEigenvalueRadialMeasure
    normalizeMeasure
  rw [betaJacobiRawMeasure_h6_eq_coeEigenvalueRadialMeasure h2NK]

/-- Exact theorem-only beta-Jacobi to beta-prime transport used by the A3
route. -/
theorem map_betaPrimeForward_betaJacobiProbability_h6
    {N K : ℕ} (hN : 1 ≤ N) (h2NK : 2 * N ≤ K) :
    Measure.map (betaPrimeForwardVector N)
        (betaJacobiProbabilityMeasure N 1
          (((K - 2 * N : ℕ) : ℝ)) 1) =
      normalizedBetaPrimeEigenvalueRadialMeasure N K := by
  rw [betaJacobiProbabilityMeasure_h6_eq_normalizedCOERadial h2NK]
  exact map_normalizedCOEEigenvalueRadialMeasure_eq_normalizedBetaPrime hN

/-! ## Collision nullity, proved rather than contracted -/

theorem measurableSet_betaJacobiCollisionSet (N : ℕ) :
    MeasurableSet (betaJacobiCollisionSet N) := by
  classical
  unfold betaJacobiCollisionSet
  measurability

private theorem volume_coordinate_eq_zero
    {N : ℕ} {i j : Fin N} (hij : i ≠ j) :
    volume {x : Fin N → ℝ | x i = x j} = 0 := by
  classical
  let L : (Fin N → ℝ) →ₗ[ℝ] ℝ :=
    (LinearMap.proj i : (Fin N → ℝ) →ₗ[ℝ] ℝ) - LinearMap.proj j
  have hset : {x : Fin N → ℝ | x i = x j} = (L.ker : Set (Fin N → ℝ)) := by
    ext x
    simp [L, sub_eq_zero]
  rw [hset]
  apply Measure.addHaar_submodule volume L.ker
  intro htop
  have hmem : Pi.single i (1 : ℝ) ∈ L.ker := by
    rw [htop]
    trivial
  have hzero := LinearMap.mem_ker.mp hmem
  simp [L, hij] at hzero

theorem betaJacobiCollisionVolumeContract_internal (N : ℕ) :
    BetaJacobiCollisionVolumeContract N := by
  refine ⟨?_⟩
  rw [show betaJacobiCollisionSet N =
      ⋃ i : Fin N, ⋃ j : Fin N,
        {x : Fin N → ℝ | i ≠ j ∧ x i = x j} by
    ext x
    simp [betaJacobiCollisionSet]]
  apply measure_iUnion_null
  intro i
  apply measure_iUnion_null
  intro j
  by_cases hij : i = j
  · simp [hij]
  · exact measure_mono_null (by
      intro x hx
      exact hx.2) (volume_coordinate_eq_zero hij)

theorem betaJacobiProbabilityMeasure_h6_collision_null
    {N K : ℕ} :
    betaJacobiProbabilityMeasure N 1
        (((K - 2 * N : ℕ) : ℝ)) 1
        (betaJacobiCollisionSet N) = 0 :=
  (betaJacobiCollisionVolumeContract_internal N).betaJacobi_collision_null
    1 (((K - 2 * N : ℕ) : ℝ)) 1

theorem betaPrimeForwardVector_collision_iff
    {N : ℕ} {lambda_i : Fin N → ℝ}
    (hlambda : lambda_i ∈ openUnitCube N) :
    betaPrimeForwardVector N lambda_i ∈ betaJacobiCollisionSet N ↔
      lambda_i ∈ betaJacobiCollisionSet N := by
  constructor
  · rintro ⟨i, j, hij, heq⟩
    refine ⟨i, j, hij, ?_⟩
    apply_fun betaPrimeInverse at heq
    simpa [betaPrimeForwardVector,
      betaPrimeInverse_forward (ne_of_lt (hlambda i).2),
      betaPrimeInverse_forward (ne_of_lt (hlambda j).2)] using heq
  · rintro ⟨i, j, hij, heq⟩
    exact ⟨i, j, hij, congrArg betaPrimeForward heq⟩

theorem map_betaPrimeForward_betaJacobiProbability_h6_collision_null
    {N K : ℕ} :
    Measure.map (betaPrimeForwardVector N)
        (betaJacobiProbabilityMeasure N 1
          (((K - 2 * N : ℕ) : ℝ)) 1)
        (betaJacobiCollisionSet N) = 0 := by
  rw [Measure.map_apply (measurable_betaPrimeForwardVector N)
    (measurableSet_betaJacobiCollisionSet N)]
  have hcube : MeasurableSet (openUnitCube N) := by
    simpa [← betaPrimeCoordVector_source] using
      (betaPrimeCoordVector N).open_source.measurableSet
  have hsupport : ∀ᵐ lambda_i ∂(betaJacobiProbabilityMeasure N 1
      (((K - 2 * N : ℕ) : ℝ)) 1), lambda_i ∈ openUnitCube N := by
    unfold betaJacobiProbabilityMeasure betaJacobiRawMeasure
    exact normalizeMeasure_ae_of_ae
      (withDensity_restrict_ae_mem volume (openUnitCube N)
        (betaJacobiKernel N 1 (((K - 2 * N : ℕ) : ℝ)) 1) hcube)
  have hsets :
      (betaPrimeForwardVector N) ⁻¹' betaJacobiCollisionSet N =ᵐ[
        betaJacobiProbabilityMeasure N 1
          (((K - 2 * N : ℕ) : ℝ)) 1]
        betaJacobiCollisionSet N := by
    filter_upwards [hsupport] with lambda_i hlambda
    exact propext (betaPrimeForwardVector_collision_iff hlambda)
  rw [measure_congr hsets]
  exact betaJacobiProbabilityMeasure_h6_collision_null

/-! ## Unordered power sums and the first/third-moment interfaces -/

theorem a2SpectralPowerSumVector_eq_h6SpectralPowerSumVector
    (r N : ℕ) :
    a2SpectralPowerSumVector r N = spectralPowerSumVector r N := rfl

/-- The exact unordered trace-vector law after canonical normalization and
the beta-Jacobi odds map.  This is the theorem-only transport layer consumed
by the A3 source law; it is not the frozen H6 endpoint. -/
theorem H6_betaJacobi_to_betaPrime_unordered_traceVector
    {r N K : ℕ} (hN : 1 ≤ N) (h2NK : 2 * N ≤ K) :
    Measure.map (a2SpectralPowerSumVector r N)
        (Measure.map (betaPrimeForwardVector N)
          (betaJacobiProbabilityMeasure N 1
            (((K - 2 * N : ℕ) : ℝ)) 1)) =
      Measure.map (spectralPowerSumVector r N)
        (normalizedBetaPrimeEigenvalueRadialMeasure N K) := by
  rw [map_betaPrimeForward_betaJacobiProbability_h6 hN h2NK]
  rfl

/-- Direct nested-map handoff for U03's canonical A3 theorem.  This form does
not ask for a second measurability premise on the A3 coordinate map: it starts
from the exact vector-law equality already supplied by A3. -/
theorem H6_betaJacobi_mappedSourceLaw_to_betaPrime_unordered_traceVector
    {Ω : Type*} [MeasurableSpace Ω]
    {r N K : ℕ} (hN : 1 ≤ N) (h2NK : 2 * N ≤ K)
    (mu : Measure Ω) (coordinates : Ω → (Fin N → ℝ))
    (hlaw : Measure.map coordinates mu =
      betaJacobiProbabilityMeasure N 1
        (((K - 2 * N : ℕ) : ℝ)) 1) :
    Measure.map (a2SpectralPowerSumVector r N)
        (Measure.map (betaPrimeForwardVector N)
          (Measure.map coordinates mu)) =
      Measure.map (spectralPowerSumVector r N)
        (normalizedBetaPrimeEigenvalueRadialMeasure N K) := by
  rw [hlaw]
  exact H6_betaJacobi_to_betaPrime_unordered_traceVector hN h2NK

/-- U03-facing composition interface.  Any concrete measurable source whose
coordinate law is the project beta-Jacobi law inherits the same unordered
beta-prime trace-vector law.  In particular U03 can instantiate `coordinates`
with the squared generalized singular values supplied by approved atom A3. -/
theorem H6_betaJacobi_sourceLaw_to_betaPrime_unordered_traceVector
    {Ω : Type*} [MeasurableSpace Ω]
    {r N K : ℕ} (hN : 1 ≤ N) (h2NK : 2 * N ≤ K)
    (mu : Measure Ω) (coordinates : Ω → (Fin N → ℝ))
    (hcoordinates : Measurable coordinates)
    (hlaw : Measure.map coordinates mu =
      betaJacobiProbabilityMeasure N 1
        (((K - 2 * N : ℕ) : ℝ)) 1) :
    Measure.map
        (a2SpectralPowerSumVector r N ∘
          betaPrimeForwardVector N ∘ coordinates) mu =
      Measure.map (spectralPowerSumVector r N)
        (normalizedBetaPrimeEigenvalueRadialMeasure N K) := by
  have hpowers : Measurable (a2SpectralPowerSumVector r N) :=
    measurable_a2SpectralPowerSumVector r N
  have hodds : Measurable (betaPrimeForwardVector N) :=
    measurable_betaPrimeForwardVector N
  change Measure.map
      ((a2SpectralPowerSumVector r N ∘ betaPrimeForwardVector N) ∘
        coordinates) mu = _
  rw [← Measure.map_map (hpowers.comp hodds) hcoordinates]
  rw [hlaw]
  rw [← Measure.map_map hpowers hodds]
  exact H6_betaJacobi_to_betaPrime_unordered_traceVector hN h2NK

def h6BetaPrimeRadialTraceOne (N : ℕ) (x : Fin N → ℝ) : ℝ :=
  ∑ i, x i

def h6BetaPrimeRadialTraceThree (N : ℕ) (x : Fin N → ℝ) : ℝ :=
  ∑ i, (x i) ^ 3

def h6BetaPrimeRadialYTraceOne (N K : ℕ) (x : Fin N → ℝ) : ℝ :=
  concreteCOEExponent N K * h6BetaPrimeRadialTraceOne N x

def h6BetaPrimeRadialYTraceThree (N K : ℕ) (x : Fin N → ℝ) : ℝ :=
  concreteCOEExponent N K ^ 3 * h6BetaPrimeRadialTraceThree N x

def h6BetaPrimeRadialSignedCenteredTraceOneCube
    (N K : ℕ) (center : ℝ) (x : Fin N → ℝ) : ℝ :=
  (h6BetaPrimeRadialYTraceOne N K x - center) ^ 3

def h6BetaPrimeRadialAbsoluteCenteredTraceOneCube
    (N K : ℕ) (center : ℝ) (x : Fin N → ℝ) : ℝ :=
  |h6BetaPrimeRadialYTraceOne N K x - center| ^ 3

theorem measurable_h6BetaPrimeRadialTraceOne (N : ℕ) :
    Measurable (h6BetaPrimeRadialTraceOne N) := by
  unfold h6BetaPrimeRadialTraceOne
  fun_prop

theorem measurable_h6BetaPrimeRadialTraceThree (N : ℕ) :
    Measurable (h6BetaPrimeRadialTraceThree N) := by
  unfold h6BetaPrimeRadialTraceThree
  fun_prop

theorem measurable_h6BetaPrimeRadialYTraceOne (N K : ℕ) :
    Measurable (h6BetaPrimeRadialYTraceOne N K) := by
  unfold h6BetaPrimeRadialYTraceOne
  exact measurable_const.mul (measurable_h6BetaPrimeRadialTraceOne N)

theorem measurable_h6BetaPrimeRadialYTraceThree (N K : ℕ) :
    Measurable (h6BetaPrimeRadialYTraceThree N K) := by
  unfold h6BetaPrimeRadialYTraceThree
  exact measurable_const.mul (measurable_h6BetaPrimeRadialTraceThree N)

theorem measurable_h6BetaPrimeRadialSignedCenteredTraceOneCube
    (N K : ℕ) (center : ℝ) :
    Measurable (h6BetaPrimeRadialSignedCenteredTraceOneCube N K center) := by
  unfold h6BetaPrimeRadialSignedCenteredTraceOneCube
  exact ((measurable_h6BetaPrimeRadialYTraceOne N K).sub_const center).pow_const 3

theorem measurable_h6BetaPrimeRadialAbsoluteCenteredTraceOneCube
    (N K : ℕ) (center : ℝ) :
    Measurable (h6BetaPrimeRadialAbsoluteCenteredTraceOneCube N K center) := by
  unfold h6BetaPrimeRadialAbsoluteCenteredTraceOneCube
  exact (((measurable_h6BetaPrimeRadialYTraceOne N K).sub_const center).abs).pow_const 3

theorem h6BetaPrimeRadialTraceOne_eq_powerSum_zero
    (N : ℕ) (x : Fin N → ℝ) :
    h6BetaPrimeRadialTraceOne N x =
      a2SpectralPowerSumVector 4 N x ⟨0, by norm_num⟩ := by
  simp [h6BetaPrimeRadialTraceOne, a2SpectralPowerSumVector]

theorem h6BetaPrimeRadialTraceThree_eq_powerSum_two
    (N : ℕ) (x : Fin N → ℝ) :
    h6BetaPrimeRadialTraceThree N x =
      a2SpectralPowerSumVector 4 N x ⟨2, by norm_num⟩ := by
  simp [h6BetaPrimeRadialTraceThree, a2SpectralPowerSumVector]

theorem abs_h6BetaPrimeRadialSignedCenteredTraceOneCube
    (N K : ℕ) (center : ℝ) (x : Fin N → ℝ) :
    |h6BetaPrimeRadialSignedCenteredTraceOneCube N K center x| =
      h6BetaPrimeRadialAbsoluteCenteredTraceOneCube N K center x := by
  simp [h6BetaPrimeRadialSignedCenteredTraceOneCube,
    h6BetaPrimeRadialAbsoluteCenteredTraceOneCube, abs_pow]

/-- Generic Bochner-moment transport.  Specializing `F` gives every fixed
signed or absolute moment without conflating the two. -/
theorem integral_comp_betaPrimeForward_betaJacobiProbability_h6
    {N K : ℕ} (hN : 1 ≤ N) (h2NK : 2 * N ≤ K)
    (F : (Fin N → ℝ) → ℝ) (hF : StronglyMeasurable F) :
    (∫ lambda_i, F (betaPrimeForwardVector N lambda_i)
        ∂(betaJacobiProbabilityMeasure N 1
          (((K - 2 * N : ℕ) : ℝ)) 1)) =
      ∫ x, F x ∂(normalizedBetaPrimeEigenvalueRadialMeasure N K) := by
  rw [← integral_map_of_stronglyMeasurable
    (measurable_betaPrimeForwardVector N) hF]
  rw [map_betaPrimeForward_betaJacobiProbability_h6 hN h2NK]

/-- `L^p` membership pulls back from the normalized beta-prime radial law to
the project beta-Jacobi law through the odds map. -/
theorem memLp_comp_betaPrimeForward_betaJacobiProbability_h6
    {N K : ℕ} (hN : 1 ≤ N) (h2NK : 2 * N ≤ K)
    {p : ENNReal} {F : (Fin N → ℝ) → ℝ}
    (hF : MemLp F p (normalizedBetaPrimeEigenvalueRadialMeasure N K)) :
    MemLp (F ∘ betaPrimeForwardVector N) p
      (betaJacobiProbabilityMeasure N 1
        (((K - 2 * N : ℕ) : ℝ)) 1) := by
  apply MemLp.comp_of_map
  · rw [map_betaPrimeForward_betaJacobiProbability_h6 hN h2NK]
    exact hF
  · exact (measurable_betaPrimeForwardVector N).aemeasurable

/-- The real `L^p` seminorm is preserved by the same normalized transport. -/
theorem lpNorm_comp_betaPrimeForward_betaJacobiProbability_h6
    {N K : ℕ} (hN : 1 ≤ N) (h2NK : 2 * N ≤ K)
    {p : ENNReal} {F : (Fin N → ℝ) → ℝ}
    (hF : AEStronglyMeasurable F
      (normalizedBetaPrimeEigenvalueRadialMeasure N K)) :
    lpNorm (F ∘ betaPrimeForwardVector N) p
        (betaJacobiProbabilityMeasure N 1
          (((K - 2 * N : ℕ) : ℝ)) 1) =
      lpNorm F p (normalizedBetaPrimeEigenvalueRadialMeasure N K) := by
  let mu := betaJacobiProbabilityMeasure N 1
    (((K - 2 * N : ℕ) : ℝ)) 1
  let f := betaPrimeForwardVector N
  have hmap : Measure.map f mu =
      normalizedBetaPrimeEigenvalueRadialMeasure N K := by
    simpa only [mu, f] using
      map_betaPrimeForward_betaJacobiProbability_h6 hN h2NK
  have hFmap : AEStronglyMeasurable F (Measure.map f mu) := by
    simpa only [hmap] using hF
  have hf : AEMeasurable f mu :=
    (measurable_betaPrimeForwardVector N).aemeasurable
  change lpNorm (F ∘ f) p mu = _
  rw [← hmap, ← toReal_eLpNorm (hFmap.comp_aemeasurable hf),
    ← toReal_eLpNorm hFmap]
  exact congrArg ENNReal.toReal (eLpNorm_map_measure hFmap hf).symm

theorem integral_signedCenteredTraceOneCube_betaJacobi_eq_betaPrime
    {N K : ℕ} (hN : 1 ≤ N) (h2NK : 2 * N ≤ K) (center : ℝ) :
    (∫ lambda_i,
        h6BetaPrimeRadialSignedCenteredTraceOneCube N K center
          (betaPrimeForwardVector N lambda_i)
        ∂(betaJacobiProbabilityMeasure N 1
          (((K - 2 * N : ℕ) : ℝ)) 1)) =
      ∫ x, h6BetaPrimeRadialSignedCenteredTraceOneCube N K center x
        ∂(normalizedBetaPrimeEigenvalueRadialMeasure N K) := by
  exact integral_comp_betaPrimeForward_betaJacobiProbability_h6 hN h2NK _
    (measurable_h6BetaPrimeRadialSignedCenteredTraceOneCube N K center).stronglyMeasurable

theorem integral_YTraceOne_betaJacobi_eq_betaPrime
    {N K : ℕ} (hN : 1 ≤ N) (h2NK : 2 * N ≤ K) :
    (∫ lambda_i,
        h6BetaPrimeRadialYTraceOne N K (betaPrimeForwardVector N lambda_i)
        ∂(betaJacobiProbabilityMeasure N 1
          (((K - 2 * N : ℕ) : ℝ)) 1)) =
      ∫ x, h6BetaPrimeRadialYTraceOne N K x
        ∂(normalizedBetaPrimeEigenvalueRadialMeasure N K) := by
  exact integral_comp_betaPrimeForward_betaJacobiProbability_h6 hN h2NK _
    (measurable_h6BetaPrimeRadialYTraceOne N K).stronglyMeasurable

theorem integral_YTraceThree_betaJacobi_eq_betaPrime
    {N K : ℕ} (hN : 1 ≤ N) (h2NK : 2 * N ≤ K) :
    (∫ lambda_i,
        h6BetaPrimeRadialYTraceThree N K (betaPrimeForwardVector N lambda_i)
        ∂(betaJacobiProbabilityMeasure N 1
          (((K - 2 * N : ℕ) : ℝ)) 1)) =
      ∫ x, h6BetaPrimeRadialYTraceThree N K x
        ∂(normalizedBetaPrimeEigenvalueRadialMeasure N K) := by
  exact integral_comp_betaPrimeForward_betaJacobiProbability_h6 hN h2NK _
    (measurable_h6BetaPrimeRadialYTraceThree N K).stronglyMeasurable

theorem integral_absoluteCenteredTraceOneCube_betaJacobi_eq_betaPrime
    {N K : ℕ} (hN : 1 ≤ N) (h2NK : 2 * N ≤ K) (center : ℝ) :
    (∫ lambda_i,
        h6BetaPrimeRadialAbsoluteCenteredTraceOneCube N K center
          (betaPrimeForwardVector N lambda_i)
        ∂(betaJacobiProbabilityMeasure N 1
          (((K - 2 * N : ℕ) : ℝ)) 1)) =
      ∫ x, h6BetaPrimeRadialAbsoluteCenteredTraceOneCube N K center x
        ∂(normalizedBetaPrimeEigenvalueRadialMeasure N K) := by
  exact integral_comp_betaPrimeForward_betaJacobiProbability_h6 hN h2NK _
    (measurable_h6BetaPrimeRadialAbsoluteCenteredTraceOneCube N K center).stronglyMeasurable

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
