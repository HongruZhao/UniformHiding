import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H14_CanonicalFourthScoreRewire
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CenteredCOERawExternal
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ConcreteCenteredQuadraticScore
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16FourthSecantIntegralVanishingFromPointwiseFTC
import Mathlib.Tactic

/-!
# H14-exact downstream quadratic-score rewire

The legacy order-two Fubini route used the former external H14 second-score
square moment.  This downstream module rebuilds that route from the exact
A1--A3 H14 theorem, then threads the new derivative identity through the
zero-centering argument and the concrete quadratic-density norm estimates.
The legacy modules and declarations remain unchanged.
-/

open MeasureTheory Set

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.LocalAnticoncentration

private theorem centeredScoreProductLaw_isFinite_H14Rewire
    {N K : ℕ} (hN : 1 ≤ N) (hNK : N ≤ K) :
    IsFiniteMeasure (concreteCenteredScoreProductLaw N K) := by
  let mu := concreteScaledCOECornerLaw
    canonicalUnitaryHaarProbabilityFamily N K
  let sphere := complexUnitSphereProbabilityMeasure N
  letI : IsProbabilityMeasure mu :=
    canonicalScaledCOECornerLaw_isProbability hNK
  letI : IsProbabilityMeasure sphere :=
    complexUnitSphereProbabilityMeasure_isProbability hN
  change IsFiniteMeasure (mu.prod sphere)
  infer_instance

private theorem centeredScoreProduct_ae_support_H14Rewire
    {N K : ℕ} (hN : 1 ≤ N) (h2NK : 2 * N ≤ K) :
    ∀ᵐ Av ∂(concreteCenteredScoreProductLaw N K),
      (unscaleCOECorner K Av.1).IsSymm ∧
        coeCornerSupport (unscaleCOECorner K Av.1) := by
  exact Measure.quasiMeasurePreserving_fst.ae
    (friedmanMello1985_scaledCOECorner_ae_support_from_density hN h2NK)

private theorem centeredDensityScoreTwoProduct_ae_eq_Bell_H14Rewire
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    (fun Av : ConcreteMatrixState N × ComplexUnitSphere N ↦
      concreteCenteredDensityScore 2 N K Av.2 Av.1) =ᵐ[
        concreteCenteredScoreProductLaw N K]
      (fun Av ↦ concreteCenteredEll 1 N K Av ^ 2 +
        concreteCenteredEll 2 N K Av) := by
  filter_upwards [centeredScoreProduct_ae_support_H14Rewire hN (by omega)]
    with Av hAv
  simpa only [concreteCenteredEll] using
    coeCorner_centeredDensityScore_two_eq_Bell
      hN Av.2 Av.1 hAv.2

private theorem centeredEllOne_memLp_four_H14Rewire
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (concreteCenteredEll 1 N K) 4
      (concreteCenteredScoreProductLaw N K) := by
  let law := concreteCenteredScoreProductLaw N K
  let ellOne := concreteCenteredEll 1 N K
  have hellMeas : AEStronglyMeasurable ellOne law :=
    (measurable_concreteCenteredEll_one hN).aestronglyMeasurable
  have hpow : MemLp (fun Av ↦ ellOne Av ^ 4) 1 law := by
    simpa only [ellOne, law] using
      centeredLogScore_oneFourth_memLp_one_proved_A1A2A3A4 hN hgap
  have hnormPow : MemLp
      (fun Av ↦ ‖ellOne Av‖ ^ (4 : ENNReal).toReal) 1 law := by
    convert hpow using 1
    funext Av
    rw [ENNReal.toReal_ofNat, Real.rpow_ofNat]
    change |ellOne Av| ^ 4 = ellOne Av ^ 4
    calc
      |ellOne Av| ^ 4 = (|ellOne Av| ^ 2) ^ 2 := by ring
      _ = (ellOne Av ^ 2) ^ 2 := by rw [sq_abs]
      _ = ellOne Av ^ 4 := by ring
  have hiff := memLp_norm_rpow_iff (p := (4 : ENNReal))
    hellMeas (q := (4 : ENNReal)) (by norm_num) (by norm_num)
  apply hiff.mp
  have hdiv : (4 : ENNReal) / 4 = 1 :=
    ENNReal.div_self (by norm_num) (by norm_num)
  simpa only [hdiv] using hnormPow

private theorem centeredEllTwo_memLp_two_H14Rewire
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (concreteCenteredEll 2 N K) 2
      (concreteCenteredScoreProductLaw N K) := by
  let law := concreteCenteredScoreProductLaw N K
  let ellTwo := concreteCenteredEll 2 N K
  have hellMeas : AEStronglyMeasurable ellTwo law :=
    (measurable_concreteCenteredEll_two hN).aestronglyMeasurable
  have hpow : MemLp (fun Av ↦ ellTwo Av ^ 2) 1 law := by
    simpa only [ellTwo, law] using
      centeredLogScore_twoSquare_memLp_one_proved_A1A2A3 hN hgap
  have hnormPow : MemLp
      (fun Av ↦ ‖ellTwo Av‖ ^ (2 : ENNReal).toReal) 1 law := by
    simpa [Real.norm_eq_abs, sq_abs] using hpow
  have hiff := memLp_norm_rpow_iff (p := (2 : ENNReal))
    hellMeas (q := (2 : ENNReal)) (by norm_num) (by norm_num)
  apply hiff.mp
  have hdiv : (2 : ENNReal) / 2 = 1 :=
    ENNReal.div_self (by norm_num) (by norm_num)
  simpa only [hdiv] using hnormPow

/-- H14-exact product `L^1` integrability of the literal second centered
density score. -/
theorem concreteCenteredDensityScoreTwoProduct_memLp_one_H14Rewire
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp
      (fun Av : ConcreteMatrixState N × ComplexUnitSphere N ↦
        concreteCenteredDensityScore 2 N K Av.2 Av.1) 1
      (concreteCenteredScoreProductLaw N K) := by
  letI : IsFiniteMeasure (concreteCenteredScoreProductLaw N K) :=
    centeredScoreProductLaw_isFinite_H14Rewire hN (by omega)
  let ellOne := concreteCenteredEll 1 N K
  let ellTwo := concreteCenteredEll 2 N K
  have hOne := centeredEllOne_memLp_four_H14Rewire hN hgap
  have hOneSq : MemLp (fun Av ↦ ellOne Av ^ 2) 2
      (concreteCenteredScoreProductLaw N K) := by
    have hnorm := hOne.norm_rpow_div (2 : ENNReal)
    have hdiv : (4 : ENNReal) / 2 = 2 := by
      symm
      rw [ENNReal.eq_div_iff (by norm_num) (by norm_num)]
      norm_num
    rw [hdiv] at hnorm
    simpa [Real.norm_eq_abs, sq_abs] using hnorm
  have hTwo : MemLp ellTwo 2 (concreteCenteredScoreProductLaw N K) := by
    simpa only [ellTwo] using centeredEllTwo_memLp_two_H14Rewire hN hgap
  have hbell : MemLp (fun Av ↦ ellOne Av ^ 2 + ellTwo Av) 2
      (concreteCenteredScoreProductLaw N K) := hOneSq.add hTwo
  have hscoreTwo : MemLp
      (fun Av : ConcreteMatrixState N × ComplexUnitSphere N ↦
        concreteCenteredDensityScore 2 N K Av.2 Av.1) 2
      (concreteCenteredScoreProductLaw N K) :=
    (memLp_congr_ae
      (centeredDensityScoreTwoProduct_ae_eq_Bell_H14Rewire hN hgap)).2 (by
        simpa only [ellOne, ellTwo] using hbell)
  exact hscoreTwo.mono_exponent (by norm_num)

/-- H14-exact order-two event-indicator Fubini theorem. -/
theorem coeCorner_centeredDensityScore_two_fubini_H14Rewire
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (event : Set (ConcreteMatrixState N)) (hevent : MeasurableSet event) :
    (∫ v : ComplexUnitSphere N,
      ∫ A, event.indicator (concreteCenteredDensityScore 2 N K v) A
        ∂(concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K)
      ∂(complexUnitSphereProbabilityMeasure N)) =
    ∫ A, event.indicator (fun A ↦
      ∫ v : ComplexUnitSphere N, concreteCenteredDensityScore 2 N K v A
        ∂(complexUnitSphereProbabilityMeasure N)) A
      ∂(concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K) := by
  exact coeCorner_centeredDensityScore_fubini_of_memLp hN (by omega)
    event hevent (by
      simpa only [concreteCenteredScoreProductLaw] using
        concreteCenteredDensityScoreTwoProduct_memLp_one_H14Rewire
          hN hgap)

/-- H14-exact literal order-two projective derivative formula. -/
theorem coeCorner_centeredProjective_eventPath_derivative_literal_two_H14Rewire
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (event : Set (ConcreteMatrixState N)) (hevent : MeasurableSet event) :
    iteratedDeriv 2
        (concreteProjectiveAveragedCenteredCOEEventPath N K event) 0 =
      ∫ A, event.indicator (fun A ↦
        ∫ v : ComplexUnitSphere N, concreteCenteredDensityScore 2 N K v A
          ∂(complexUnitSphereProbabilityMeasure N)) A
        ∂(concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K) := by
  rw [coeCorner_centeredProjective_eventPath_derivative_interchange_at_H18_proved_from_A1
    (r := 2) hN hboundary (by omega) event hevent 0]
  simp_rw [coeCorner_centeredFixedDirection_eventPath_derivative_H16_proved_from_A1
    (r := 2) hN hboundary (by omega) _ event hevent]
  exact coeCorner_centeredDensityScore_two_fubini_H14Rewire
    hN hboundary event hevent

/-- H14-exact raw order-two projective derivative formula. -/
theorem coeCorner_centeredProjective_secondRaw_H14Rewire
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (event : Set (ConcreteMatrixState N)) (hevent : MeasurableSet event) :
    iteratedDeriv 2
        (concreteProjectiveAveragedCenteredCOEEventPath N K event) 0 =
      ∫ A, event.indicator (fun A ↦
        ∫ v : ComplexUnitSphere N,
          concreteCenteredRankOneSecondDensityScore N K v A
            ∂(complexUnitSphereProbabilityMeasure N)) A
        ∂(concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K) := by
  rw [coeCorner_centeredProjective_eventPath_derivative_literal_two_H14Rewire
    hN hboundary event hevent]
  apply integral_congr_ae
  filter_upwards
    [friedmanMello1985_scaledCOECorner_ae_support_from_density hN (by omega)]
      with A hA
  rcases hA with ⟨hsymm, hsupport⟩
  by_cases hmem : A ∈ event
  · simp only [Set.indicator, hmem, if_true]
    apply integral_congr_ae
    filter_upwards [] with v
    exact coeCorner_centeredDensityScore_two_eq_explicit_external_derived
      hN hboundary v A hsymm hsupport
  · simp only [Set.indicator, hmem, if_false]

/-- Dense-range H14-exact identification of the second derivative with the
explicit quadratic-density indicator integral. -/
theorem concrete_projectiveAveraged_centered_second_derivative_eq_density_indicator_integral_H14Rewire
    {N K : ℕ} (hN : 1 ≤ N) (h16 : 16 * N ≤ K)
    (event : Set (ConcreteMatrixState N)) (hevent : MeasurableSet event) :
    iteratedDeriv 2
        (concreteProjectiveAveragedCenteredCOEEventPath N K event) 0 =
      ∫ A, event.indicator (concreteCenteredQuadraticDensity N K) A
        ∂(concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K) := by
  have hboundary : 2 * N + 8 ≤ K := by omega
  have hc : concreteCOEExponent N K ≠ 0 := by
    unfold concreteCOEExponent
    have hpos : 0 < (K : ℝ) - 2 * (N : ℝ) - 1 := by
      have h16r : (16 : ℝ) * (N : ℝ) ≤ (K : ℝ) := by
        exact_mod_cast h16
      have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      nlinarith
    exact ne_of_gt hpos
  have hcpos : 0 < concreteCOEExponent N K := by
    unfold concreteCOEExponent
    have h16r : (16 : ℝ) * (N : ℝ) ≤ (K : ℝ) := by
      exact_mod_cast h16
    have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    nlinarith
  rw [coeCorner_centeredProjective_secondRaw_H14Rewire
    hN hboundary event hevent]
  apply integral_congr_ae
  filter_upwards
    [friedmanMello1985_scaledCOECorner_ae_support_from_density hN (by omega)]
      with A hA
  rcases hA with ⟨hsymm, hsupport⟩
  by_cases hmem : A ∈ event
  · simp only [Set.indicator, hmem, if_true]
    exact integral_concreteCenteredRankOneSecondDensityScore_eq_density
      hN hc A
        (concreteCOERMatrix_isSymm_of_support A hsymm hsupport)
        (concreteCOEY_trace_im_eq_zero_of_support A hsupport)
        (concreteCOEY_sq_trace_im_eq_zero_of_support A hsupport)
        (concreteCOEWMatrix_trace_re A hc)
        (concreteCOEWMatrix_mul_Y_trace_re A hc)
        (concreteCOERMatrix_sq_trace_re A hcpos hsupport)
  · simp only [Set.indicator, hmem, if_false]

/-- Total-mass specialization of the H14-exact density identity. -/
theorem concrete_projectiveAveraged_centered_second_derivative_eq_density_integral_H14Rewire
    {N K : ℕ} (hN : 1 ≤ N) (h16 : 16 * N ≤ K) :
    iteratedDeriv 2
        (concreteProjectiveAveragedCenteredCOEEventPath N K Set.univ) 0 =
      ∫ A, concreteCenteredQuadraticDensity N K A
        ∂(concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K) := by
  simpa using
    concrete_projectiveAveraged_centered_second_derivative_eq_density_indicator_integral_H14Rewire
      hN h16 Set.univ MeasurableSet.univ

/-- H14-exact zero-mean identity for the concrete quadratic trace bracket. -/
theorem integral_concreteCenteredQuadraticTraceBracket_eq_zero_dense_H14Rewire
    {N K : ℕ} (hN : 1 ≤ N) (h16 : 16 * N ≤ K) :
    (∫ A, concreteCenteredQuadraticTraceBracket N K A
      ∂(concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K)) = 0 := by
  exact integral_concreteCenteredQuadraticTraceBracket_eq_zero_of_eventPath
    hN (by omega)
      (concrete_projectiveAveraged_centered_second_derivative_eq_density_integral_H14Rewire
        hN h16)

/-- The concrete centered quadratic density belongs to `L^2`, using the
H14-exact zero-centering theorem. -/
theorem concreteCenteredQuadraticDensity_memLp_two_H14Rewire
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    MemLp (concreteCenteredQuadraticDensity N K) 2
      (concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K) := by
  let mu := concreteScaledCOECornerLaw
    canonicalUnitaryHaarProbabilityFamily N K
  let tOne := concreteCOETraceOne N K
  let tTwo := concreteCOETraceTwo N K
  let meanOne := ∫ A, tOne A ∂mu
  let meanSquare := ∫ A, tOne A ^ 2 ∂mu
  let meanTwo := ∫ A, tTwo A ∂mu
  have H := concreteCOE_centeredQuadraticTraceInputs_of_bracket_zero
    hN hdense (integral_concreteCenteredQuadraticTraceBracket_eq_zero_dense_H14Rewire
      hN hdense)
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hc : concreteCOEExponent N K ≠ 0 := by
    unfold concreteCOEExponent
    have hdenseR : (16 : ℝ) * (N : ℝ) ≤ (K : ℝ) := by
      exact_mod_cast hdense
    have hNone : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    nlinarith
  let eTwo : ConcreteMatrixState N → ℝ := fun A ↦ tTwo A - meanTwo
  let eSquare : ConcreteMatrixState N → ℝ := fun A ↦ tOne A ^ 2 - meanSquare
  let eOne : ConcreteMatrixState N → ℝ := fun A ↦ tOne A - meanOne
  let a := quadraticTraceCoeffTwo (N : ℝ) (concreteCOEExponent N K)
  let b := quadraticTraceCoeffSquare (N : ℝ) (concreteCOEExponent N K)
  let d := quadraticTraceCoeffOne (N : ℝ)
  have hmean : a * meanTwo + b * meanSquare + d * meanOne = 0 := by
    simpa only [a, b, d, meanOne, meanSquare, meanTwo, tOne, tTwo, mu] using
      H.mean_identity hNr hc
  have hpoint : concreteCenteredQuadraticDensity N K =
      (4 / ((N : ℝ) * ((N : ℝ) + 1))) •
        (a • eTwo + b • eSquare + d • eOne) := by
    funext A
    change (4 / ((N : ℝ) * ((N : ℝ) + 1))) *
        centeredQuadraticTraceBracket (N : ℝ) (concreteCOEExponent N K)
          (tOne A) (tTwo A) =
      (4 / ((N : ℝ) * ((N : ℝ) + 1))) *
        (a * eTwo A + b * eSquare A + d * eOne A)
    congr 1
    exact centeredQuadraticTraceBracket_eq_centered_components hNr hc hmean
  rw [hpoint]
  have hTwo : MemLp eTwo 2 mu := by
    simpa only [eTwo, meanTwo, tTwo, mu] using H.centered_two_memLp
  have hSquare : MemLp eSquare 2 mu := by
    simpa only [eSquare, meanSquare, tOne, mu] using H.centered_square_memLp
  have hOne : MemLp eOne 2 mu := by
    simpa only [eOne, meanOne, tOne, mu] using H.centered_one_memLp
  exact (((hTwo.const_smul a).add (hSquare.const_smul b)).add
    (hOne.const_smul d)).const_smul
      (4 / ((N : ℝ) * ((N : ℝ) + 1)))

/-- Concrete `L^2` estimate with the H14-exact centering proof. -/
theorem concreteCenteredQuadraticDensity_lpNorm_two_le_H14Rewire
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (concreteCenteredQuadraticDensity N K) 2
      (concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K) ≤
      concreteOrbitalScoreTwoConstant := by
  have hNone : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hc : (N : ℝ) ≤ concreteCOEExponent N K := by
    unfold concreteCOEExponent
    have hdenseR : (16 : ℝ) * (N : ℝ) ≤ (K : ℝ) := by
      exact_mod_cast hdense
    linarith
  have H := concreteCOE_centeredQuadraticTraceInputs_of_bracket_zero
    hN hdense (integral_concreteCenteredQuadraticTraceBracket_eq_zero_dense_H14Rewire
      hN hdense)
  have hraw := H.normalized_bracket_lpNorm_two_le hNone hc
    (by norm_num [denseClassicalMomentConstant] : 0 ≤ denseClassicalMomentConstant)
    (by norm_num [denseClassicalMomentConstant] : 0 ≤ denseClassicalMomentConstant)
    (by norm_num [denseClassicalMomentConstant] : 0 ≤ denseClassicalMomentConstant)
  change lpNorm (fun omega ↦
      4 / ((N : ℝ) * ((N : ℝ) + 1)) *
        centeredQuadraticTraceBracket (N : ℝ) (concreteCOEExponent N K)
          (concreteCOETraceOne N K omega) (concreteCOETraceTwo N K omega)) 2
      (concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K) ≤
    28 * denseClassicalMomentConstant
  calc
    _ ≤ 4 * (2 * denseClassicalMomentConstant +
        2 * denseClassicalMomentConstant +
        3 * denseClassicalMomentConstant) := hraw
    _ = 28 * denseClassicalMomentConstant := by ring

/-- Eventwise `L^1` estimate with the H14-exact centering proof. -/
theorem concreteCenteredQuadraticDensity_lpNorm_one_le_H14Rewire
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (concreteCenteredQuadraticDensity N K) 1
      (concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K) ≤
      concreteOrbitalScoreTwoConstant := by
  let mu := concreteScaledCOECornerLaw
    canonicalUnitaryHaarProbabilityFamily N K
  letI : IsProbabilityMeasure mu :=
    canonicalScaledCOECornerLaw_isProbability (by omega)
  have hmem : MemLp (concreteCenteredQuadraticDensity N K) 2 mu := by
    simpa only [mu] using
      concreteCenteredQuadraticDensity_memLp_two_H14Rewire hN hdense
  exact (lpNorm_one_le_lpNorm_two_of_memLp hmem).trans <| by
    simpa only [mu] using
      concreteCenteredQuadraticDensity_lpNorm_two_le_H14Rewire hN hdense

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
