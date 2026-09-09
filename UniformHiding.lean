import HidingStatement
import GBSHiding
import ComplexGramHafnians

open MeasureTheory
open LogdetLean.GramHafnian LogdetLean.GramHafnian.LocalAnticoncentration
open LogdetLean.GramHafnian.UltimateHiding
open LogdetLean.GramHafnian.ThreePaper
open LogdetLean.GramHafnian.ThreePaper.FairAbsoluteThresholdComparison

namespace UniformHiding
noncomputable section

/-- Theorem 2.1 for all `1 ≤ N,K ≤ M`, including `K < N`, conditional on
exactly the four cited literature axioms. -/
theorem theorem2_1 : Theorem21 := GBSHiding.normalizedHidingAllInputs

/-- The equivalent unnormalized product bound in Theorem 2.1. -/
theorem theorem2_1_unscaled
    (H : UnitaryHaarProbabilityFamily) (M N K : ℕ)
    (hN : 1 ≤ N) (hNM : N ≤ M) (hK : 1 ≤ K) (hKM : K ≤ M) :
    probabilityTotalVariationLE
      (scaledHaarTransposeGramLaw H M N K)
      (gaussianTransposeGramLaw N K)
      (min 1 (615172 * ultimateSquaredHidingRate M N)) :=
  unnormalizedProductMatrixHiding_of_normalized H hK
    (theorem2_1 H M N K hN hNM hK hKM)

/-- Corollary 2.2 follows directly from Theorem 2.1 by taking `N = 2*n`
and using `m ≥ n² / delta`. No assumption `2*n ≤ k` is used. -/
theorem corollary2_2 : Corollary22 := by
  intro H m n k hn hnm hk hkm delta hdelta hsize
  have hm : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hnd : (n : ℝ)^2 ≤ (m : ℝ) * delta :=
    (div_le_iff₀ hdelta).mp hsize
  have hrate : ultimateSquaredHidingRate m (2 * n) ≤ 4 * delta := by
    unfold ultimateSquaredHidingRate
    rw [div_le_iff₀ hm]
    push_cast
    nlinarith
  apply (theorem2_1_unscaled H m (2 * n) k (by omega) hnm hk hkm).mono
  calc
    min 1 (615172 * ultimateSquaredHidingRate m (2 * n)) ≤
        615172 * ultimateSquaredHidingRate m (2 * n) := min_le_right _ _
    _ ≤ 615172 * (4 * delta) := mul_le_mul_of_nonneg_left hrate (by norm_num)
    _ = 4 * 615172 * delta := by ring

/-- Compatibility name from the earlier version 1.2.0 preparation. The
all-input product bound is now part of Theorem 2.1 itself. -/
abbrev corollary2_2_unscaled := theorem2_1_unscaled

/-- Compatibility name for the unnormalized quantitative corollary. -/
abbrev corollary2_2_s62_scaled := corollary2_2

private theorem measurable_s62ScaleDown (m N : ℕ) :
    Measurable (s62ScaleDown m N) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  change Measurable fun A : Matrix (Fin N) (Fin N) ℂ ↦ (m : ℂ)⁻¹ * A i j
  have hi : Measurable
      (fun A : Matrix (Fin N) (Fin N) ℂ ↦ A i) := measurable_pi_apply i
  have hij : Measurable
      (fun A : Matrix (Fin N) (Fin N) ℂ ↦ A i j) :=
    (measurable_pi_apply j).comp hi
  exact hij.const_mul _

/-- Source-scale version of [10, Conjecture 1 and Supplemental Eq. (S62)].
The constant `4 * 615172` is independent of `m`, `n`, `k`, and `delta`. -/
theorem corollary2_2_s62 : Corollary22S62 := by
  intro H m n k hn hnm hk hkm delta hdelta hsize
  exact (corollary2_2 H m n k hn hnm hk hkm delta hdelta hsize).map
    (measurable_s62ScaleDown m (2 * n))

/-- The source-scale Haar law is literally the product of the selected
Haar block, rather than an abstract comparison measure. -/
theorem s62HaarProductLaw_eq_matrixLaw
    (H : UnitaryHaarProbabilityFamily) {m n k : ℕ}
    (hm : 0 < m) (hnm : 2 * n ≤ m) (hkm : k ≤ m) :
    s62HaarProductLaw H m n k =
      (H.law m).map (fun U ↦ rectangularTransposeGram
        (topLeftUnitaryBlock hnm hkm U)) := by
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  unfold s62HaarProductLaw
  rw [scaledHaarTransposeGramLaw, dif_pos ⟨hnm, hkm⟩]
  rw [Measure.map_map (measurable_s62ScaleDown m (2 * n))
    (measurable_scaledHaarTransposeGramMatrix hnm hkm)]
  congr 1
  funext U
  ext i j
  simp [s62ScaleDown, scaledHaarTransposeGramMatrix, hmC]

/-- The source-scale Gaussian law is literally the pushforward of the
standard rectangular Gaussian factor by `G ↦ (1/m) G Gᵀ`. -/
theorem s62GaussianProductLaw_eq_matrixLaw (m n k : ℕ) :
    s62GaussianProductLaw m n k =
      (standardComplexGaussianRectangularMeasure (2 * n) k).map
        (fun G ↦ (m : ℂ)⁻¹ • rectangularTransposeGram G) := by
  unfold s62GaussianProductLaw gaussianTransposeGramLaw
  rw [Measure.map_map (measurable_s62ScaleDown m (2 * n))
    (measurable_rectangularTransposeGram (2 * n) k)]
  rfl

/-- Route 1 disk transfer uses the public companion theorem directly. -/
theorem routeOneSmallBall
    (H : UnitaryHaarProbabilityFamily) {M n K : ℕ}
    (hn : 1 ≤ n) (hK : 4 * n ≤ K) (hKM : K ≤ M)
    (z : ℂ) (eps : ℝ) (heps : 0 ≤ eps) :
    (scaledHaarGramHafnianLaw H M n K).real
      (shiftedComplexDisk z (eps * gramHafnianSigma K n)) ≤
      min 1 (paperBkn K n * eps ^ 2 + deltaOne M n) := by
  have htv := (UniformMatrixHiding.matrixLaw.apply H
    (show 1 ≤ 2 * n by omega) (show 2 * n ≤ K by omega) hKM).map
      (measurable_hafnianMatrixObservable n)
  have htransfer := htv.event_le
    (measurableSet_shiftedComplexDisk z (eps * gramHafnianSigma K n))
  change (scaledHaarGramHafnianLaw H M n K).real _ ≤
    (gaussianGramHafnianLaw n K).real _ + deltaOne M n at htransfer
  rw [gaussianGramHafnianLaw_shiftedDisk_eq] at htransfer
  have hanti := (ComplexGramHafnians.theorem2_1 n K hn hK).shiftedSmallBall z eps heps
  let := scaledHaarGramHafnianLaw_isProbability H (show 2 * n ≤ M by omega) hKM
  apply le_min measureReal_le_one
  exact htransfer.trans (add_le_add (hanti.trans (min_le_right _ _)) le_rfl)

/-- Route 1 of Theorem 3.2 at the physical threshold tau. The marginal
hypothesis specifies the Haar amplitude on a joint space that may include
estimator randomness; no independence of the estimator is assumed. -/
theorem theorem3_2_route1
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (amplitude : Ω → ℂ) (hamplitude : Measurable amplitude) (deltaP : Ω → ℝ)
    (H : UnitaryHaarProbabilityFamily)
    {r : ℝ} (hr : 0 < r) {M n K : ℕ}
    (hn : 1 ≤ n) (hK : 4 * n ≤ K) (hKM : K ≤ M)
    {rho tau : ℝ} (hrho : 0 < rho) (htau : 0 ≤ tau)
    (hmarginal : Measure.map amplitude μ = scaledHaarGramHafnianLaw H M n K) :
    μ.real (relativeFailureEvent deltaP
      (fun ω ↦ gbsProbabilityFromScaledAmplitude r M K n (amplitude ω)) rho) ≤
      routeOneBound μ deltaP r M K n rho tau := by
  have hM : 0 < M := by omega
  have hp := RelativeAccuracy.gbsGaussianReferenceProbability_pos
    hr hM (show 0 < K by omega) n
  let eta := tau / gbsGaussianReferenceProbability r M K n
  have heta : 0 ≤ eta := div_nonneg htau hp.le
  have hscale : eta * gbsGaussianReferenceProbability r M K n = tau :=
    div_mul_cancel₀ tau hp.ne'
  have ht : 0 ≤ eta / rho := div_nonneg heta hrho.le
  have hhaar := routeOneSmallBall H hn hK hKM 0 (Real.sqrt (eta / rho)) (Real.sqrt_nonneg _)
  rw [← scaledAmplitudeSmallDenominatorSet_eq_shiftedComplexDisk hr hM K n ht] at hhaar
  rw [Real.sq_sqrt ht] at hhaar
  have hadd : μ.real (additiveFailureEvent deltaP eta
      (gbsGaussianReferenceProbability r M K n)) ≤
      μ.real (absoluteAdditiveFailureEvent deltaP tau) := by
    simp only [additiveFailureEvent, absoluteAdditiveFailureEvent, hscale, le_refl]
  have h := randomizedConversion_from_finiteHaarSmallDenominator
    μ amplitude hamplitude deltaP H hr hM K n heta hrho
    (measureReal_nonneg) hmarginal hadd (hhaar.trans (min_le_right _ _))
  have hratio : eta / rho = tau / (rho * gbsGaussianReferenceProbability r M K n) := by
    dsimp [eta]
    rw [div_div, mul_comm]
  simpa only [routeOneBound, hratio] using h

/-- Optimization in the Route 1 half of Theorem 3.2. -/
theorem theorem3_2_route1_optimized
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (amplitude : Ω → ℂ) (hamplitude : Measurable amplitude) (deltaP : Ω → ℝ)
    (H : UnitaryHaarProbabilityFamily)
    {r : ℝ} (hr : 0 < r) {M n K : ℕ}
    (hn : 1 ≤ n) (hK : 4 * n ≤ K) (hKM : K ≤ M)
    {rho : ℝ} (hrho : 0 < rho)
    (hmarginal : Measure.map amplitude μ = scaledHaarGramHafnianLaw H M n K) :
    μ.real (relativeFailureEvent deltaP
      (fun ω ↦ gbsProbabilityFromScaledAmplitude r M K n (amplitude ω)) rho) ≤
      optimizedRouteOneBound μ deltaP r M K n rho := by
  let : Nonempty {t : ℝ // 0 ≤ t} := ⟨⟨0, le_refl _⟩⟩
  apply le_ciInf
  intro tau
  exact theorem3_2_route1 μ amplitude hamplitude deltaP H hr hn hK hKM
    hrho tau.property hmarginal

/-- Route 2 is a conditional deduction. Its Shou comparison premise
is not proved or declared as a fifth axiom in this repository. -/
abbrev routeTwoConditional := @RelativeAccuracy.routeTwoFairRelativeFailure_of_shou

end
end UniformHiding
