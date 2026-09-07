import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CenteredScoreFubini
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CenteredLikelihoodLowBellCalculus
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CenteredScoreLowMeasurability
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CenteredDensityScoreOneDerived
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CenteredDensityScoreTwoExternal
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ClassicalCenteredLogScoreMomentExternal
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H12_ExactMomentEndpointA4
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H14_ExactMomentClosure
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.FriedmanMelloSupportFromDensity
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Tactic

/-!
# First- and second-order centered-score Fubini

The existing fourth-order log-score moment packages already imply the
lower-order finiteness needed here.  The only extra work is the kernel-checked
Bell calculus and measurability of the explicit rational-matrix scores.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

private theorem centeredScoreProductLaw_isFinite
    {N K : ℕ} (hN : 1 ≤ N) (hNK : N ≤ K) :
    IsFiniteMeasure (concreteCenteredScoreProductLaw N K) := by
  let mu := concreteScaledCOECornerLaw
    LogdetLean.GramHafnian.CurrentPRL.canonicalUnitaryHaarProbabilityFamily N K
  let sphere := complexUnitSphereProbabilityMeasure N
  letI : IsProbabilityMeasure mu :=
    canonicalScaledCOECornerLaw_isProbability hNK
  letI : IsProbabilityMeasure sphere :=
    complexUnitSphereProbabilityMeasure_isProbability hN
  change IsFiniteMeasure (mu.prod sphere)
  infer_instance

private theorem centeredScoreProduct_ae_support
    {N K : ℕ} (hN : 1 ≤ N) (h2NK : 2 * N ≤ K) :
    ∀ᵐ Av ∂(concreteCenteredScoreProductLaw N K),
      (unscaleCOECorner K Av.1).IsSymm ∧
        coeCornerSupport (unscaleCOECorner K Av.1) := by
  exact Measure.quasiMeasurePreserving_fst.ae
    (friedmanMello1985_scaledCOECorner_ae_support_from_density hN h2NK)

private theorem centeredDensityScoreOneProduct_ae_eq_explicit
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    (fun Av : ConcreteMatrixState N × ComplexUnitSphere N ↦
      concreteCenteredDensityScore 1 N K Av.2 Av.1) =ᵐ[
        concreteCenteredScoreProductLaw N K]
      (fun Av ↦ concreteCenteredRankOneFirstDensityScore N K Av.2 Av.1) := by
  filter_upwards [centeredScoreProduct_ae_support hN (by omega)]
    with Av hAv
  exact coeCorner_centeredDensityScore_one_eq_explicit_external_derived
    hN hgap Av.2 Av.1 hAv.1 hAv.2

private theorem centeredDensityScoreTwoProduct_ae_eq_explicit
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    (fun Av : ConcreteMatrixState N × ComplexUnitSphere N ↦
      concreteCenteredDensityScore 2 N K Av.2 Av.1) =ᵐ[
        concreteCenteredScoreProductLaw N K]
      (fun Av ↦ concreteCenteredRankOneSecondDensityScore N K Av.2 Av.1) := by
  filter_upwards [centeredScoreProduct_ae_support hN (by omega)]
    with Av hAv
  exact coeCorner_centeredDensityScore_two_eq_explicit_external_derived
    hN hgap Av.2 Av.1 hAv.1 hAv.2

private theorem centeredDensityScoreOneProduct_ae_eq_ellOne
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    (fun Av : ConcreteMatrixState N × ComplexUnitSphere N ↦
      concreteCenteredDensityScore 1 N K Av.2 Av.1) =ᵐ[
        concreteCenteredScoreProductLaw N K]
      concreteCenteredEll 1 N K := by
  filter_upwards [centeredScoreProduct_ae_support hN (by omega)]
    with Av hAv
  simpa only [concreteCenteredEll] using
    coeCorner_centeredDensityScore_one_eq_logScore
      hN Av.2 Av.1 hAv.2

private theorem centeredDensityScoreTwoProduct_ae_eq_Bell
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    (fun Av : ConcreteMatrixState N × ComplexUnitSphere N ↦
      concreteCenteredDensityScore 2 N K Av.2 Av.1) =ᵐ[
        concreteCenteredScoreProductLaw N K]
      (fun Av ↦ concreteCenteredEll 1 N K Av ^ 2 +
        concreteCenteredEll 2 N K Av) := by
  filter_upwards [centeredScoreProduct_ae_support hN (by omega)]
    with Av hAv
  simpa only [concreteCenteredEll] using
    coeCorner_centeredDensityScore_two_eq_Bell
      hN Av.2 Av.1 hAv.2

private theorem centeredEllOne_memLp_four
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (concreteCenteredEll 1 N K) 4
      (concreteCenteredScoreProductLaw N K) := by
  let law := concreteCenteredScoreProductLaw N K
  let score : ConcreteMatrixState N × ComplexUnitSphere N → ℝ :=
    fun Av ↦ concreteCenteredDensityScore 1 N K Av.2 Av.1
  let ellOne := concreteCenteredEll 1 N K
  have hscoreExp := centeredDensityScoreOneProduct_ae_eq_explicit hN hgap
  have hscoreMeas : AEStronglyMeasurable score law := by
    exact (measurable_concreteCenteredRankOneFirstDensityScore_product N K
      |>.aestronglyMeasurable).congr (by simpa only [score, law] using hscoreExp.symm)
  have hscoreEll : score =ᵐ[law] ellOne := by
    simpa only [score, ellOne, law] using
      centeredDensityScoreOneProduct_ae_eq_ellOne hN hgap
  have hellMeas : AEStronglyMeasurable ellOne law :=
    hscoreMeas.congr hscoreEll
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

private theorem centeredEllTwo_memLp_two
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (concreteCenteredEll 2 N K) 2
      (concreteCenteredScoreProductLaw N K) := by
  let law := concreteCenteredScoreProductLaw N K
  let scoreOne : ConcreteMatrixState N × ComplexUnitSphere N → ℝ :=
    fun Av ↦ concreteCenteredDensityScore 1 N K Av.2 Av.1
  let scoreTwo : ConcreteMatrixState N × ComplexUnitSphere N → ℝ :=
    fun Av ↦ concreteCenteredDensityScore 2 N K Av.2 Av.1
  let ellOne := concreteCenteredEll 1 N K
  let ellTwo := concreteCenteredEll 2 N K
  have hscoreOneMeas : AEStronglyMeasurable scoreOne law := by
    exact (measurable_concreteCenteredRankOneFirstDensityScore_product N K
      |>.aestronglyMeasurable).congr (by
        simpa only [scoreOne, law] using
          (centeredDensityScoreOneProduct_ae_eq_explicit hN hgap).symm)
  have hscoreTwoMeas : AEStronglyMeasurable scoreTwo law := by
    exact (measurable_concreteCenteredRankOneSecondDensityScore_product N K
      |>.aestronglyMeasurable).congr (by
        simpa only [scoreTwo, law] using
          (centeredDensityScoreTwoProduct_ae_eq_explicit hN hgap).symm)
  have hscoreOneEll : scoreOne =ᵐ[law] ellOne := by
    simpa only [scoreOne, ellOne, law] using
      centeredDensityScoreOneProduct_ae_eq_ellOne hN hgap
  have hellOneMeas : AEStronglyMeasurable ellOne law :=
    hscoreOneMeas.congr hscoreOneEll
  have hbell : scoreTwo =ᵐ[law]
      (fun Av ↦ ellOne Av ^ 2 + ellTwo Av) := by
    simpa only [scoreTwo, ellOne, ellTwo, law] using
      centeredDensityScoreTwoProduct_ae_eq_Bell hN hgap
  have hellTwoMeas : AEStronglyMeasurable ellTwo law := by
    have hdiff : (fun Av ↦ scoreTwo Av - ellOne Av ^ 2) =ᵐ[law] ellTwo := by
      filter_upwards [hbell] with Av hAv
      rw [hAv]
      ring
    exact (hscoreTwoMeas.sub (hellOneMeas.pow 2)).congr hdiff
  have hpow : MemLp (fun Av ↦ ellTwo Av ^ 2) 1 law := by
    simpa only [ellTwo, law] using
      centeredLogScore_twoSquare_memLp_one_proved_A1A2A3 hN hgap
  have hnormPow : MemLp
      (fun Av ↦ ‖ellTwo Av‖ ^ (2 : ENNReal).toReal) 1 law := by
    simpa [Real.norm_eq_abs, sq_abs] using hpow
  have hiff := memLp_norm_rpow_iff (p := (2 : ENNReal))
    hellTwoMeas (q := (2 : ENNReal)) (by norm_num) (by norm_num)
  apply hiff.mp
  have hdiv : (2 : ENNReal) / 2 = 1 :=
    ENNReal.div_self (by norm_num) (by norm_num)
  simpa only [hdiv] using hnormPow

/-- Literal first centered density score is product `L¹`. -/
theorem concreteCenteredDensityScoreOneProduct_memLp_one
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp
      (fun Av : ConcreteMatrixState N × ComplexUnitSphere N ↦
        concreteCenteredDensityScore 1 N K Av.2 Av.1) 1
      (concreteCenteredScoreProductLaw N K) := by
  letI : IsFiniteMeasure (concreteCenteredScoreProductLaw N K) :=
    centeredScoreProductLaw_isFinite hN (by omega)
  have hell := (centeredEllOne_memLp_four hN hgap).mono_exponent
    (by norm_num : (1 : ENNReal) ≤ 4)
  exact (memLp_congr_ae
    (centeredDensityScoreOneProduct_ae_eq_ellOne hN hgap)).2 hell

/-- Literal second centered density score is product `L¹`. -/
theorem concreteCenteredDensityScoreTwoProduct_memLp_one
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp
      (fun Av : ConcreteMatrixState N × ComplexUnitSphere N ↦
        concreteCenteredDensityScore 2 N K Av.2 Av.1) 1
      (concreteCenteredScoreProductLaw N K) := by
  letI : IsFiniteMeasure (concreteCenteredScoreProductLaw N K) :=
    centeredScoreProductLaw_isFinite hN (by omega)
  let ellOne := concreteCenteredEll 1 N K
  let ellTwo := concreteCenteredEll 2 N K
  have hOne := centeredEllOne_memLp_four hN hgap
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
    simpa only [ellTwo] using centeredEllTwo_memLp_two hN hgap
  have hbell : MemLp (fun Av ↦ ellOne Av ^ 2 + ellTwo Av) 2
      (concreteCenteredScoreProductLaw N K) := hOneSq.add hTwo
  have hscoreTwo : MemLp
      (fun Av : ConcreteMatrixState N × ComplexUnitSphere N ↦
        concreteCenteredDensityScore 2 N K Av.2 Av.1) 2
      (concreteCenteredScoreProductLaw N K) :=
    (memLp_congr_ae
      (centeredDensityScoreTwoProduct_ae_eq_Bell hN hgap)).2 (by
        simpa only [ellOne, ellTwo] using hbell)
  exact hscoreTwo.mono_exponent (by norm_num)

/-- First-order event-indicator Fubini, derived from product `L¹`. -/
theorem coeCorner_centeredDensityScore_one_fubini
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (event : Set (ConcreteMatrixState N)) (hevent : MeasurableSet event) :
    (∫ v : ComplexUnitSphere N,
      ∫ A, event.indicator (concreteCenteredDensityScore 1 N K v) A
        ∂(concreteScaledCOECornerLaw
          LogdetLean.GramHafnian.CurrentPRL.canonicalUnitaryHaarProbabilityFamily
            N K)
      ∂(complexUnitSphereProbabilityMeasure N)) =
    ∫ A, event.indicator (fun A ↦
      ∫ v : ComplexUnitSphere N, concreteCenteredDensityScore 1 N K v A
        ∂(complexUnitSphereProbabilityMeasure N)) A
      ∂(concreteScaledCOECornerLaw
        LogdetLean.GramHafnian.CurrentPRL.canonicalUnitaryHaarProbabilityFamily
          N K) := by
  exact coeCorner_centeredDensityScore_fubini_of_memLp hN (by omega)
    event hevent (by
      simpa only [concreteCenteredScoreProductLaw] using
        concreteCenteredDensityScoreOneProduct_memLp_one hN hgap)

/-- Second-order event-indicator Fubini, derived from product `L¹`. -/
theorem coeCorner_centeredDensityScore_two_fubini
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (event : Set (ConcreteMatrixState N)) (hevent : MeasurableSet event) :
    (∫ v : ComplexUnitSphere N,
      ∫ A, event.indicator (concreteCenteredDensityScore 2 N K v) A
        ∂(concreteScaledCOECornerLaw
          LogdetLean.GramHafnian.CurrentPRL.canonicalUnitaryHaarProbabilityFamily
            N K)
      ∂(complexUnitSphereProbabilityMeasure N)) =
    ∫ A, event.indicator (fun A ↦
      ∫ v : ComplexUnitSphere N, concreteCenteredDensityScore 2 N K v A
        ∂(complexUnitSphereProbabilityMeasure N)) A
      ∂(concreteScaledCOECornerLaw
        LogdetLean.GramHafnian.CurrentPRL.canonicalUnitaryHaarProbabilityFamily
          N K) := by
  exact coeCorner_centeredDensityScore_fubini_of_memLp hN (by omega)
    event hevent (by
      simpa only [concreteCenteredScoreProductLaw] using
        concreteCenteredDensityScoreTwoProduct_memLp_one hN hgap)

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
