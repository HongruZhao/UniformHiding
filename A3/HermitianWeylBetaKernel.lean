import A3.HermitianWeylWeighted
import A3.BetaJacobiNormalization

open MeasureTheory MeasureTheory.Measure Set
open LogdetLean.GramHafnian.UltimateHiding.DenseScore
open scoped BigOperators ENNReal

noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

namespace A3Research

variable {n : ℕ} {K : Type*} [RCLike K]

theorem hermitianFlatEigenvalueDensity_eq_pair_rpow (lambda : Fin n → ℝ) :
    hermitianFlatEigenvalueDensity n K lambda =
      ∏ p ∈ a2StrictPairs n,
        (ENNReal.ofReal |lambda p.2 - lambda p.1|).rpow (Module.finrank ℝ K : ℝ) := by
  classical
  rw [hermitianFlatEigenvalueDensity, ENNReal.ofReal_pow (hermitianVandermonde_nonneg lambda),
    hermitianVandermonde_eq_strictPairs,
    ENNReal.ofReal_prod_of_nonneg (fun _ _ ↦ abs_nonneg _), ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro p _
  exact (ENNReal.rpow_natCast _ _).symm

def hermitianBetaEndpointDensity (n : ℕ) (a b beta : ℝ) (lambda : Fin n → ℝ) : ℝ≥0∞ :=
  ∏ i,
    (ENNReal.ofReal (lambda i)).rpow (beta * (a + 1) / 2 - 1) *
      (ENNReal.ofReal (1 - lambda i)).rpow (beta * (b + 1) / 2 - 1)

def hermitianBetaSpectralWeight (n : ℕ) (a b beta : ℝ) : (Fin n → ℝ) → ℝ≥0∞ :=
  (betaJacobiOpenCube n).indicator (hermitianBetaEndpointDensity n a b beta)

theorem measurable_hermitianBetaEndpointDensity (n : ℕ) (a b beta : ℝ) :
    Measurable (hermitianBetaEndpointDensity n a b beta) := by
  unfold hermitianBetaEndpointDensity
  simp only [ENNReal.rpow_eq_pow]
  fun_prop

theorem measurable_hermitianBetaSpectralWeight (n : ℕ) (a b beta : ℝ) :
    Measurable (hermitianBetaSpectralWeight n a b beta) :=
  (measurable_hermitianBetaEndpointDensity n a b beta).indicator
    (measurableSet_betaJacobiOpenCube n)

theorem hermitianBetaEndpointDensity_permutation (n : ℕ) (a b beta : ℝ) :
    IsA2SymmetricTest (hermitianBetaEndpointDensity n a b beta) := by
  intro sigma lambda
  exact Equiv.prod_comp sigma (fun i ↦
    (ENNReal.ofReal (lambda i)).rpow (beta * (a + 1) / 2 - 1) *
      (ENNReal.ofReal (1 - lambda i)).rpow (beta * (b + 1) / 2 - 1))

theorem mem_betaJacobiOpenCube_comp_perm_iff (lambda : Fin n → ℝ)
    (sigma : Equiv.Perm (Fin n)) :
    lambda ∘ sigma ∈ betaJacobiOpenCube n ↔ lambda ∈ betaJacobiOpenCube n := by
  change (∀ i, lambda (sigma i) ∈ Ioo 0 1) ↔ ∀ i, lambda i ∈ Ioo 0 1
  constructor
  · intro h i
    simpa only [Equiv.apply_symm_apply] using h (sigma.symm i)
  · intro h i
    exact h (sigma i)

theorem hermitianBetaSpectralWeight_permutation (n : ℕ) (a b beta : ℝ) :
    IsA2SymmetricTest (hermitianBetaSpectralWeight n a b beta) := by
  intro sigma lambda
  change hermitianBetaSpectralWeight n a b beta (lambda ∘ sigma) =
    hermitianBetaSpectralWeight n a b beta lambda
  unfold hermitianBetaSpectralWeight
  by_cases h : lambda ∈ betaJacobiOpenCube n
  · rw [indicator_of_mem ((mem_betaJacobiOpenCube_comp_perm_iff lambda sigma).mpr h),
      indicator_of_mem h]
    exact hermitianBetaEndpointDensity_permutation n a b beta sigma lambda
  · rw [indicator_of_notMem (fun hc ↦ h
      ((mem_betaJacobiOpenCube_comp_perm_iff lambda sigma).mp hc)), indicator_of_notMem h]

theorem hermitianBetaEndpointDensity_mul_flat_eq_kernel (a b : ℝ) (lambda : Fin n → ℝ) :
    hermitianBetaEndpointDensity n a b (Module.finrank ℝ K) lambda *
      hermitianFlatEigenvalueDensity n K lambda =
        betaJacobiKernel n a b (Module.finrank ℝ K) lambda := by
  rw [hermitianFlatEigenvalueDensity_eq_pair_rpow]
  rfl

/-- Multiplying the literal flat Weyl measure by the matrix-beta spectral
weight gives the exact beta-Jacobi raw kernel, including cube restriction. -/
theorem hermitianFlatRadial_weighted_beta_eq_raw (n : ℕ) (K : Type*) [RCLike K] (a b : ℝ) :
    (hermitianFlatEigenvalueRadialMeasure n K).withDensity
      (hermitianBetaSpectralWeight n a b (Module.finrank ℝ K)) =
        betaJacobiRawMeasure n a b (Module.finrank ℝ K) := by
  rw [hermitianFlatEigenvalueRadialMeasure,
    ← withDensity_mul _ (measurable_hermitianFlatEigenvalueDensity n K)
      (measurable_hermitianBetaSpectralWeight n a b (Module.finrank ℝ K))]
  have he : (fun lambda ↦ hermitianFlatEigenvalueDensity n K lambda *
      hermitianBetaSpectralWeight n a b (Module.finrank ℝ K) lambda) =
      (betaJacobiOpenCube n).indicator (betaJacobiKernel n a b (Module.finrank ℝ K)) := by
    funext lambda
    by_cases h : lambda ∈ betaJacobiOpenCube n
    · rw [hermitianBetaSpectralWeight, indicator_of_mem h, indicator_of_mem h, mul_comm]
      exact hermitianBetaEndpointDensity_mul_flat_eq_kernel (K := K) a b lambda
    · simp only [hermitianBetaSpectralWeight, indicator_of_notMem h, mul_zero]
  change volume.withDensity (fun lambda ↦ hermitianFlatEigenvalueDensity n K lambda *
    hermitianBetaSpectralWeight n a b (Module.finrank ℝ K) lambda) = _
  rw [he, withDensity_indicator (measurableSet_betaJacobiOpenCube n)]
  rfl

theorem hermitianWeyl_map_beta_spectral_density
    [MeasureSpace K] [BorelSpace K] [PolishSpace K]
    [IsAddHaarMeasure (volume : Measure K)]
    (a b : ℝ) {Y : Type} [MeasurableSpace Y] (F : (Fin n → ℝ) → Y)
    (hF : Measurable F) (hperm : IsA2SymmetricTest F) :
    Measure.map (F ∘ canonicalHermitianSpectrum)
      ((hermitianCoordinateVolume n K).withDensity
        (hermitianBetaSpectralWeight n a b (Module.finrank ℝ K) ∘ canonicalHermitianSpectrum)) =
      ((hermitianWeylSymmetricIntegrationLaw n K).orbitConstant : ℝ≥0∞) •
        Measure.map F (betaJacobiRawMeasure n a b (Module.finrank ℝ K)) := by
  rw [← hermitianFlatRadial_weighted_beta_eq_raw n K a b]
  exact hermitianWeyl_map_spectral_withDensity F hF hperm _
    (measurable_hermitianBetaSpectralWeight n a b (Module.finrank ℝ K))
    (hermitianBetaSpectralWeight_permutation n a b (Module.finrank ℝ K))

end A3Research
