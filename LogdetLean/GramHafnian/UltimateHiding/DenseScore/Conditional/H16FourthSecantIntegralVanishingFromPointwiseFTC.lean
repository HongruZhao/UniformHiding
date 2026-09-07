import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16ThirdFourthPointwiseFTC
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16FourthSecantL1VanishingH17H18Reduction
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# H16 fourth secant from the pointwise FTC

The literal third jet satisfies the scalar `J3 -> J4` fundamental theorem of
calculus at every coordinate point.  The fourth-jet orbit is already strongly
continuous in `L1`.  Fubini therefore bounds the normalized third-jet
remainder by the normalized primitive of the continuous `L1` modulus

`t \mapsto \|J4(t) - J4(0)\|_1`.

That primitive has derivative zero at the origin.  This closes the formerly
isolated local secant-integral limit without any additional scientific axiom.
-/

open Filter MeasureTheory Set
open scoped ENNReal Interval Topology

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

set_option maxHeartbeats 800000

private theorem integrable_h16CenteredFourthJetDifference_prod_uIoc
    (hH5 : H16ExactH5Family)
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (v : ComplexUnitSphere N) (a b : ℝ) :
    Integrable
      (fun p : ℝ × ComplexSymmetricCoordinates N ↦
        |h16CenteredTransportJet N K 4 v p.1 p.2 -
          h16CenteredTransportJet N K 4 v 0 p.2|)
      ((volume.restrict (Ι a b)).prod
        (complexSymmetricCoordinateVolume N)) := by
  letI : SFinite (complexSymmetricCoordinateVolume N) := by
    rw [show complexSymmetricCoordinateVolume N =
        (volume : Measure (ComplexSymmetricCoordinates N)) by
      unfold complexSymmetricCoordinateVolume
      exact MeasureTheory.volume_pi.symm]
    infer_instance
  let L : ℝ → H16CenteredCoordinateL1 N := fun t ↦
    h16CenteredDirectJetLp hH5 hN hboundary (4 : Fin 5) v t
  have hparam : Measurable
      (fun p : ℝ × ComplexSymmetricCoordinates N ↦ ((v, p.1), p.2)) :=
    (measurable_const.prodMk measurable_fst).prodMk measurable_snd
  have hJmeas : Measurable (fun p : ℝ × ComplexSymmetricCoordinates N ↦
      h16CenteredTransportJet N K 4 v p.1 p.2) := by
    have hcomp :=
      (measurable_h16CenteredTransportJet_four hN hboundary).comp hparam
    simpa only [Function.comp_def] using hcomp
  have hzeroParam : Measurable
      (fun p : ℝ × ComplexSymmetricCoordinates N ↦ ((v, (0 : ℝ)), p.2)) :=
    measurable_const.prodMk measurable_snd
  have hJzeroMeas : Measurable
      (fun p : ℝ × ComplexSymmetricCoordinates N ↦
        h16CenteredTransportJet N K 4 v 0 p.2) := by
    have hcomp :=
      (measurable_h16CenteredTransportJet_four hN hboundary).comp hzeroParam
    simpa only [Function.comp_def] using hcomp
  have hmeas : AEStronglyMeasurable
      (fun p : ℝ × ComplexSymmetricCoordinates N ↦
        |h16CenteredTransportJet N K 4 v p.1 p.2 -
          h16CenteredTransportJet N K 4 v 0 p.2|)
      ((volume.restrict (Ι a b)).prod
        (complexSymmetricCoordinateVolume N)) :=
    (hJmeas.sub hJzeroMeas).abs.aestronglyMeasurable
  refine (integrable_prod_iff hmeas).2 ⟨?_, ?_⟩
  · filter_upwards with t
    exact ((integrable_h16CenteredTransportJet_direct_exactH5
      hH5 hN hboundary (4 : Fin 5) v t).sub
        (integrable_h16CenteredTransportJet_direct_exactH5
          hH5 hN hboundary (4 : Fin 5) v 0)).abs
  · have hLcont : Continuous L := by
      simpa only [L] using
        continuous_h16CenteredDirectJetLp_fixedDirection
          hH5 hN hboundary (4 : Fin 5) v
    have hnormCont : Continuous (fun t : ℝ ↦ ‖L t - L 0‖) :=
      (hLcont.sub continuous_const).norm
    have hnormInt : IntegrableOn (fun t : ℝ ↦ ‖L t - L 0‖)
        (Ι a b) volume :=
      intervalIntegrable_iff.mp (hnormCont.intervalIntegrable a b)
    have hnormEq :
        (fun t : ℝ ↦ ∫ x,
          ‖|h16CenteredTransportJet N K 4 v t x -
            h16CenteredTransportJet N K 4 v 0 x|‖
          ∂(complexSymmetricCoordinateVolume N)) =
          (fun t : ℝ ↦ ‖L t - L 0‖) := by
      funext t
      rw [L1.norm_eq_integral_norm]
      apply integral_congr_ae
      filter_upwards
          [Lp.coeFn_sub (L t) (L 0),
            h16CenteredDirectJetLp_coeFn_ae
              hH5 hN hboundary (4 : Fin 5) v t,
            h16CenteredDirectJetLp_coeFn_ae
              hH5 hN hboundary (4 : Fin 5) v 0] with x hsub ht hzero
      simp only [Pi.sub_apply] at hsub
      rw [hsub, ht, hzero]
      simp only [Real.norm_eq_abs, abs_abs]
    rw [hnormEq]
    exact hnormInt

/-- The scalar local fourth-secant remainder vanishes at time zero. -/
theorem h16CenteredFourthLocalSecantIntegralVanishing_proved_exactH5
    (hH5 : H16ExactH5Family)
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K) :
    H16CenteredFourthLocalSecantIntegralVanishing N K := by
  intro v
  let μ := complexSymmetricCoordinateVolume N
  letI : SFinite μ := by
    rw [show μ = (volume : Measure (ComplexSymmetricCoordinates N)) by
      dsimp only [μ]
      unfold complexSymmetricCoordinateVolume
      exact MeasureTheory.volume_pi.symm]
    infer_instance
  let J3 : ℝ → ComplexSymmetricCoordinates N → ℝ := fun t x ↦
    h16CenteredTransportJet N K 3 v t x
  let J4 : ℝ → ComplexSymmetricCoordinates N → ℝ := fun t x ↦
    h16CenteredTransportJet N K 4 v t x
  let L4 : ℝ → H16CenteredCoordinateL1 N := fun t ↦
    h16CenteredDirectJetLp hH5 hN hboundary (4 : Fin 5) v t
  let φ : ℝ → ℝ := fun t ↦ ‖L4 t - L4 0‖
  have hL4cont : Continuous L4 := by
    simpa only [L4] using
      continuous_h16CenteredDirectJetLp_fixedDirection
        hH5 hN hboundary (4 : Fin 5) v
  have hφcont : Continuous φ := by
    exact (hL4cont.sub continuous_const).norm
  have hφzero : φ 0 = 0 := by simp [φ]
  have hprimitive : HasDerivAt (fun t : ℝ ↦ ∫ s in 0..t, φ s) 0 0 := by
    have h := intervalIntegral.integral_hasDerivAt_right
      (hφcont.intervalIntegrable 0 0)
      hφcont.aestronglyMeasurable.stronglyMeasurableAtFilter
      hφcont.continuousAt
    simpa only [hφzero] using h
  have hupperTendsto : Tendsto
      (fun t : ℝ ↦ ‖t‖⁻¹ * ‖∫ s in 0..t, φ s‖)
      (𝓝 0) (𝓝 0) := by
    have h := hasDerivAt_iff_tendsto.mp hprimitive
    simpa using h
  have hnonneg : ∀ t : ℝ,
      0 ≤ ∫ x, h16CenteredFourthLocalSecantRemainder N K v t x ∂μ := by
    intro t
    exact integral_nonneg fun x ↦
      h16CenteredFourthLocalSecantRemainder_nonnegative v t x
  have hupper : ∀ t : ℝ,
      (∫ x, h16CenteredFourthLocalSecantRemainder N K v t x ∂μ) ≤
        ‖t‖⁻¹ * ‖∫ s in 0..t, φ s‖ := by
    intro t
    by_cases ht : t ∈ Icc (-1 : ℝ) 1
    · have hprod :=
        integrable_h16CenteredFourthJetDifference_prod_uIoc
          hH5 hN hboundary v 0 t
      have hinnerInt : Integrable
          (fun x : ComplexSymmetricCoordinates N ↦
            ∫ s in Ι 0 t, |J4 s x - J4 0 x|)
          μ := by
        simpa only [J4, μ] using hprod.integral_prod_right
      have hboundInt : Integrable
          (fun x : ComplexSymmetricCoordinates N ↦
            ‖t‖⁻¹ * (∫ s in Ι 0 t, |J4 s x - J4 0 x|))
          μ := hinnerInt.const_mul ‖t‖⁻¹
      have hRint : Integrable
          (h16CenteredFourthLocalSecantRemainder N K v t) μ := by
        simpa only [μ] using
          integrable_h16CenteredFourthLocalSecantRemainder_exactH5
            hH5 hN hboundary v t
      calc
        (∫ x, h16CenteredFourthLocalSecantRemainder N K v t x ∂μ) ≤
            ∫ x, ‖t‖⁻¹ *
              (∫ s in Ι 0 t, |J4 s x - J4 0 x|) ∂μ := by
          apply integral_mono hRint hboundInt
          intro x
          rw [h16CenteredFourthLocalSecantRemainder, if_pos ht]
          apply mul_le_mul_of_nonneg_left _
            (inv_nonneg.mpr (norm_nonneg t))
          have hFTC :=
            intervalIntegrable_and_integral_h16CenteredTransportJet_four_eq_three_sub
              hN hboundary v x 0 t
          have hdiffInt : IntervalIntegrable (fun s : ℝ ↦ J4 s x - J4 0 x)
              volume 0 t := hFTC.1.sub intervalIntegrable_const
          have hremEq : J3 t x - J3 0 x - t * J4 0 x =
              ∫ s in 0..t, (J4 s x - J4 0 x) := by
            rw [intervalIntegral.integral_sub hFTC.1 intervalIntegrable_const]
            rw [hFTC.2]
            simp [J3, J4]
          rw [hremEq]
          rw [intervalIntegral.norm_intervalIntegral_eq]
          exact norm_integral_le_integral_norm _
        _ = ‖t‖⁻¹ *
            (∫ x, (∫ s in Ι 0 t, |J4 s x - J4 0 x| ∂volume) ∂μ) := by
          rw [integral_const_mul]
        _ = ‖t‖⁻¹ *
            (∫ s in Ι 0 t, (∫ x, |J4 s x - J4 0 x| ∂μ) ∂volume) := by
          congr 1
          simpa only [J4, μ, Function.uncurry_apply_pair] using
            (integral_integral_swap
              (μ := volume.restrict (Ι 0 t)) (ν := μ)
              (f := fun s x ↦ |J4 s x - J4 0 x|) hprod).symm
        _ = ‖t‖⁻¹ * (∫ s in Ι 0 t, φ s) := by
          congr 1
          apply integral_congr_ae
          filter_upwards with s
          change (∫ x, |J4 s x - J4 0 x| ∂μ) = ‖L4 s - L4 0‖
          rw [L1.norm_eq_integral_norm]
          apply integral_congr_ae
          filter_upwards
              [Lp.coeFn_sub (L4 s) (L4 0),
                h16CenteredDirectJetLp_coeFn_ae
                  hH5 hN hboundary (4 : Fin 5) v s,
                h16CenteredDirectJetLp_coeFn_ae
                  hH5 hN hboundary (4 : Fin 5) v 0] with x hsub hs hzero
          simp only [Pi.sub_apply] at hsub
          rw [hsub, hs, hzero]
          simp only [J4, Real.norm_eq_abs]
        _ = ‖t‖⁻¹ * ‖∫ s in 0..t, φ s‖ := by
          congr 1
          rw [intervalIntegral.norm_intervalIntegral_eq]
          rw [Real.norm_of_nonneg]
          exact integral_nonneg fun s ↦ norm_nonneg _
    · have hzeroFun :
          (fun x ↦ h16CenteredFourthLocalSecantRemainder N K v t x) =
            (fun _ : ComplexSymmetricCoordinates N ↦ (0 : ℝ)) := by
          funext x
          simp only [h16CenteredFourthLocalSecantRemainder, if_neg ht]
      rw [hzeroFun]
      simp only [integral_zero]
      exact mul_nonneg (inv_nonneg.mpr (norm_nonneg t)) (norm_nonneg _)
  have htend : Tendsto
      (fun t : ℝ ↦ ∫ x,
        h16CenteredFourthLocalSecantRemainder N K v t x ∂μ)
      (𝓝 0) (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hupperTendsto hnonneg hupper
  simpa only [μ] using htend

/-- Universal form of the proved local secant-integral limit. -/
theorem h16CenteredFourthLocalSecantIntegralVanishingFamily_proved
    (hH5 : H16ExactH5Family) :
    H16CenteredFourthLocalSecantIntegralVanishingFamily := by
  intro N K hN hboundary
  exact h16CenteredFourthLocalSecantIntegralVanishing_proved_exactH5
    hH5 hN hboundary

/-! ## Literal H16--H18 endpoints -/

/-- Literal fixed-direction H16, with exact H5 as its only scientific input. -/
theorem coeCorner_centeredFixedDirection_eventPath_derivative_H16_proved_exactH5
    (hH5 : H16ExactH5Family)
    {N K r : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (hr : r ≤ 4) (v : ComplexUnitSphere N)
    (event : Set (ConcreteMatrixState N)) (hevent : MeasurableSet event) :
    iteratedDeriv r (concreteCenteredRankOneCOEEventPath K v event) 0 =
      ∫ A, event.indicator
        (concreteCenteredDensityScore r N K v) A
        ∂(concreteScaledCOECornerLaw
          LogdetLean.GramHafnian.LocalAnticoncentration.canonicalUnitaryHaarProbabilityFamily
            N K) :=
  coeCorner_centeredFixedDirection_eventPath_derivative_H16_of_fourthSecantIntegralVanishing_exactH5
    hH5 (h16CenteredFourthLocalSecantIntegralVanishingFamily_proved hH5)
      hN hboundary hr v event hevent

/-- Literal projective `C⁴` endpoint H17, with exact H5 as its only
scientific input. -/
theorem coeCorner_centeredProjective_eventPath_contDiff_four_H17_proved_exactH5
    (hH5 : H16ExactH5Family)
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (event : Set (ConcreteMatrixState N)) (hevent : MeasurableSet event) :
    ContDiff ℝ 4
      (concreteProjectiveAveragedCenteredCOEEventPath N K event) :=
  coeCorner_centeredProjective_eventPath_contDiff_four_H17_of_fourthSecantIntegralVanishing_exactH5
    hH5 (h16CenteredFourthLocalSecantIntegralVanishingFamily_proved hH5)
      hN hboundary event hevent

/-- Literal derivative-interchange endpoint H18, with exact H5 as its only
scientific input. -/
theorem coeCorner_centeredProjective_eventPath_derivative_interchange_at_H18_proved_exactH5
    (hH5 : H16ExactH5Family)
    {N K r : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (hr : r ≤ 4) (event : Set (ConcreteMatrixState N))
    (hevent : MeasurableSet event) (y : ℝ) :
    iteratedDeriv r
        (concreteProjectiveAveragedCenteredCOEEventPath N K event) y =
      ∫ v : ComplexUnitSphere N,
        iteratedDeriv r
          (concreteCenteredRankOneCOEEventPath K v event) y
          ∂(complexUnitSphereProbabilityMeasure N) :=
  coeCorner_centeredProjective_eventPath_derivative_interchange_at_H18_of_fourthSecantIntegralVanishing_exactH5
    hH5 (h16CenteredFourthLocalSecantIntegralVanishingFamily_proved hH5)
      hN hboundary hr event hevent y

/-- Literal H16 from the already approved Friedman--Mello A1. -/
theorem coeCorner_centeredFixedDirection_eventPath_derivative_H16_proved_from_A1
    {N K r : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (hr : r ≤ 4) (v : ComplexUnitSphere N)
    (event : Set (ConcreteMatrixState N)) (hevent : MeasurableSet event) :
    iteratedDeriv r (concreteCenteredRankOneCOEEventPath K v event) 0 =
      ∫ A, event.indicator
        (concreteCenteredDensityScore r N K v) A
        ∂(concreteScaledCOECornerLaw
          LogdetLean.GramHafnian.LocalAnticoncentration.canonicalUnitaryHaarProbabilityFamily
            N K) :=
  coeCorner_centeredFixedDirection_eventPath_derivative_H16_from_A1_fourthSecantIntegralVanishing
    (h16CenteredFourthLocalSecantIntegralVanishingFamily_proved
      h16ExactH5Family_from_friedmanMello1985_A1)
    hN hboundary hr v event hevent

/-- Literal H17 from the already approved Friedman--Mello A1. -/
theorem coeCorner_centeredProjective_eventPath_contDiff_four_H17_proved_from_A1
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (event : Set (ConcreteMatrixState N)) (hevent : MeasurableSet event) :
    ContDiff ℝ 4
      (concreteProjectiveAveragedCenteredCOEEventPath N K event) :=
  coeCorner_centeredProjective_eventPath_contDiff_four_H17_from_A1_fourthSecantIntegralVanishing
    (h16CenteredFourthLocalSecantIntegralVanishingFamily_proved
      h16ExactH5Family_from_friedmanMello1985_A1)
    hN hboundary event hevent

/-- Literal H18 from the already approved Friedman--Mello A1. -/
theorem coeCorner_centeredProjective_eventPath_derivative_interchange_at_H18_proved_from_A1
    {N K r : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (hr : r ≤ 4) (event : Set (ConcreteMatrixState N))
    (hevent : MeasurableSet event) (y : ℝ) :
    iteratedDeriv r
        (concreteProjectiveAveragedCenteredCOEEventPath N K event) y =
      ∫ v : ComplexUnitSphere N,
        iteratedDeriv r
          (concreteCenteredRankOneCOEEventPath K v event) y
          ∂(complexUnitSphereProbabilityMeasure N) :=
  coeCorner_centeredProjective_eventPath_derivative_interchange_at_H18_from_A1_fourthSecantIntegralVanishing
    (h16CenteredFourthLocalSecantIntegralVanishingFamily_proved
      h16ExactH5Family_from_friedmanMello1985_A1)
    hN hboundary hr event hevent y

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
