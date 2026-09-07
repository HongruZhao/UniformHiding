import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H14_RadialBetaPrimeClosureConditional
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.H14FourthRadialContracts
import LogdetLean.GramHafnian.WickRegrouping
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
import Mathlib.Tactic

/-!
# CONDITIONAL fourth-radial producer for H14

This file works only on the explicit independent Gaussian beta-prime source.
It proves the complete qualitative fourth-order layer at the sharp threshold
`2 * N + 8 ≤ K`: the fourth power of the first trace, the square of the
second trace, and hence the normalized radial remainder are integrable.

It also proves the exact finite eighth-coordinate Wick rule, expressed as
the number of compatible perfect matchings.  The two remaining contracts are
kept strictly below every H3--H18 endpoint:

* `H14FiniteGaussianFourthWickFormula` is the finite numerator contraction
  from the checked eighth-coordinate rule to two trace polynomials;
* `H14DenominatorFourthTracePolynomialBounds` is denominator-only and asks
  for dense bounds on those two explicit order-four inverse-Wishart trace
  polynomials.

The final theorem in this file is therefore `CONDITIONAL`.  It does not use
H6, an H8/H10/H14 endpoint, or the quarantined raw trace-two majorant.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08

noncomputable section

open LogdetLean.GramHafnian
open LogdetLean.GramHafnian.Wishart
open LogdetLean.GramHafnian.UltimateHiding.DenseScore

set_option maxHeartbeats 2400000

private theorem prod_standardRealGaussianMoment_eq_pairingCount_h14
    {I K : Type*} [Fintype I] [LinearOrder I]
    [Fintype K] [DecidableEq K] (c : I → K) :
    (∏ a, standardRealGaussianMoment (colorMultiplicity c a)) =
      (Nat.card (TypePerfectMatching.Compatible c) : ℝ) := by
  rw [Nat.card_eq_fintype_card,
    card_compatible_eq_prod_wickMultiplicity]
  push_cast
  apply Finset.prod_congr rfl
  intro a ha
  by_cases hEven : Even (colorMultiplicity c a)
  · simp [standardRealGaussianMoment, hEven]
  · simp [standardRealGaussianMoment, hEven]

/-- Exact finite eighth-coordinate Wick contraction.  The right side is the
number of pairings that match equal Gaussian coordinates. -/
theorem integral_standardRealGaussianVector_coordinate_eight_pairingCount_h14
    {p : ℕ} (c : Fin 8 → Fin p) :
    (∫ x : Fin p → ℝ, ∏ t : Fin 8, x (c t)
      ∂standardRealGaussianVectorMeasure p) =
      (Nat.card (TypePerfectMatching.Compatible c) : ℝ) := by
  calc
    (∫ x : Fin p → ℝ, ∏ t : Fin 8, x (c t)
      ∂standardRealGaussianVectorMeasure p) =
        ∫ x : Fin p → ℝ,
          realCoordinatePowerProduct (colorMultiplicity c) x
          ∂standardRealGaussianVectorMeasure p := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact prod_comp_eq_coordinatePowerProduct c x
    _ = ∏ a : Fin p,
          ∫ z : ℝ, z ^ colorMultiplicity c a ∂gaussianReal 0 1 := by
      exact integral_realCoordinatePowerProduct_pi
        (K := Fin p) (gaussianReal 0 1) (colorMultiplicity c)
    _ = ∏ a : Fin p,
          standardRealGaussianMoment (colorMultiplicity c a) := by
      simp_rw [integral_pow_gaussianReal_eq_standardRealGaussianMoment]
    _ = _ := prod_standardRealGaussianMoment_eq_pairingCount_h14 c

/-- The corresponding product of eight selected Gaussian coordinates is
integrable. -/
theorem integrable_standardRealGaussianVector_coordinate_eight_h14
    {p : ℕ} (c : Fin 8 → Fin p) :
    Integrable (fun x : Fin p → ℝ ↦ ∏ t : Fin 8, x (c t))
      (standardRealGaussianVectorMeasure p) := by
  simpa only [prod_comp_eq_coordinatePowerProduct] using
    (integrable_realColorProduct_standardGaussian c)

/-- Every coordinate of a finite standard-Gaussian matrix belongs to
`L^8`. -/
theorem standardRealGaussianMatrix_coordinate_memLp_eight_h14
    {rows p : ℕ} (a : Fin rows) (i : Fin p) :
    MemLp (fun R : Matrix (Fin rows) (Fin p) ℝ ↦ R a i) 8
      (standardRealGaussianMatrixMeasure rows p) := by
  have hscalar : MemLp (id : ℝ → ℝ) 8 (gaussianReal 0 1) :=
    memLp_id_gaussianReal' 8 (by norm_num)
  have hvector : MemLp (fun x : Fin p → ℝ ↦ x i) 8
      (standardRealGaussianVectorMeasure p) := by
    unfold standardRealGaussianVectorMeasure
    have h := hscalar.comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin p ↦ gaussianReal 0 1) i)
    change MemLp (fun x : Fin p → ℝ ↦ x i) 8
      (Measure.pi fun _ : Fin p ↦ gaussianReal 0 1) at h
    exact h
  have hcurried : MemLp (fun R : Fin rows → Fin p → ℝ ↦ R a i) 8
      (Measure.pi fun _ : Fin rows ↦ standardRealGaussianVectorMeasure p) := by
    have h := hvector.comp_measurePreserving
      (measurePreserving_eval
        (fun _ : Fin rows ↦ standardRealGaussianVectorMeasure p) a)
    change MemLp (fun R : Fin rows → Fin p → ℝ ↦ R a i) 8
      (Measure.pi fun _ : Fin rows ↦ standardRealGaussianVectorMeasure p) at h
    exact h
  rw [← show Measure.map (curriedMatrixMeasurableEquiv rows p)
      (Measure.pi fun _ : Fin rows ↦ standardRealGaussianVectorMeasure p) =
      standardRealGaussianMatrixMeasure rows p by
    unfold standardRealGaussianMatrixMeasure
    change Measure.map (id : (Fin rows → Fin p → ℝ) →
        (Fin rows → Fin p → ℝ))
      (Measure.pi fun _ : Fin rows ↦ standardRealGaussianVectorMeasure p) =
      Measure.pi fun _ : Fin rows ↦ standardRealGaussianVectorMeasure p
    exact Measure.map_id]
  have hcoordMeas : Measurable
      (fun R : Matrix (Fin rows) (Fin p) ℝ ↦ R a i) := by
    fun_prop
  apply (memLp_map_measure_iff hcoordMeas.aestronglyMeasurable
    (curriedMatrixMeasurableEquiv rows p).measurable.aemeasurable).2
  change MemLp (fun R : Fin rows → Fin p → ℝ ↦ R a i) 8
    (Measure.pi fun _ : Fin rows ↦ standardRealGaussianVectorMeasure p)
  exact hcurried

/-- Every entry of a finite variance-one real Wishart matrix belongs to
`L^4`; this is the eight-coordinate Gaussian input in `MemLp` form. -/
theorem realWishartGram_entry_memLp_four_h14
    {rows p : ℕ} (i j : Fin p) :
    MemLp (fun R : Matrix (Fin rows) (Fin p) ℝ ↦
        realWishartGram R i j) 4
      (standardRealGaussianMatrixMeasure rows p) := by
  have h884 : ENNReal.HolderTriple 8 8 4 :=
    ENNReal.HolderTriple.of_toReal (by constructor <;> norm_num)
  let _ := h884
  simp only [realWishartGram, Matrix.mul_apply, Matrix.transpose_apply]
  apply memLp_finsetSum Finset.univ
  intro a ha
  exact (standardRealGaussianMatrix_coordinate_memLp_eight_h14 a j).mul'
    (standardRealGaussianMatrix_coordinate_memLp_eight_h14 a i)

/-- A product of four prescribed real-Wishart entries is integrable. -/
theorem integrable_realWishartGram_entryProduct_four_h14
    {rows p : ℕ} (indices : Fin 4 → Fin p × Fin p) :
    Integrable
      (fun R : Matrix (Fin rows) (Fin p) ℝ ↦
        ∏ t : Fin 4, realWishartGram R (indices t).1 (indices t).2)
      (standardRealGaussianMatrixMeasure rows p) := by
  have h442 : ENNReal.HolderTriple 4 4 2 :=
    ENNReal.HolderTriple.of_toReal (by constructor <;> norm_num)
  let _ := h442
  have h01 : MemLp
      (fun R : Matrix (Fin rows) (Fin p) ℝ ↦
        realWishartGram R (indices 0).1 (indices 0).2 *
          realWishartGram R (indices 1).1 (indices 1).2) 2
      (standardRealGaussianMatrixMeasure rows p) :=
    (realWishartGram_entry_memLp_four_h14
      (indices 1).1 (indices 1).2).mul'
      (realWishartGram_entry_memLp_four_h14
        (indices 0).1 (indices 0).2)
  have h23 : MemLp
      (fun R : Matrix (Fin rows) (Fin p) ℝ ↦
        realWishartGram R (indices 2).1 (indices 2).2 *
          realWishartGram R (indices 3).1 (indices 3).2) 2
      (standardRealGaussianMatrixMeasure rows p) :=
    (realWishartGram_entry_memLp_four_h14
      (indices 3).1 (indices 3).2).mul'
      (realWishartGram_entry_memLp_four_h14
        (indices 2).1 (indices 2).2)
  have h221 : ENNReal.HolderTriple 2 2 1 :=
    ENNReal.HolderTriple.of_toReal (by constructor <;> norm_num)
  let _ := h221
  have hprod := memLp_one_iff_integrable.mp (h23.mul' h01)
  simpa [Fin.prod_univ_four, mul_assoc, mul_left_comm, mul_comm] using hprod

/-- One four-inverse/four-Wishart summand on the independent beta-prime
source is integrable. -/
theorem integrable_betaPrime_fourEntrySourceProduct_h14
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K)
    (cIndices wIndices : Fin 4 → Fin N × Fin N) :
    Integrable
      (fun source : BetaPrimeGaussianSource N K ↦
        ∏ t : Fin 4,
          scaledInverseWishartDenominator N K source
              (cIndices t).1 (cIndices t).2 *
            realWishartGram source.1 (wIndices t).1 (wIndices t).2)
      (realBetaPrimeGaussianSourceLaw N K) := by
  have hA := integrable_realWishartGram_entryProduct_four_h14
    (rows := N + 1) wIndices
  have hB :=
    integrable_betaPrimeDenominator_inverseEntryProduct_order_le_four
      hgap (by norm_num) cIndices
  have hprod := hA.mul_prod hB
  have hscaled := hprod.const_mul (concreteCOEExponent N K ^ 4)
  unfold realBetaPrimeGaussianSourceLaw
  apply hscaled.congr
  filter_upwards [] with source
  simp only [Function.uncurry, scaledInverseWishartDenominator,
    inverseWishartEntryProduct, Fin.prod_univ_four, Matrix.smul_apply,
    smul_eq_mul]
  ring

/-- The fourth power of the raw first beta-prime trace is integrable at the
exact order-four inverse-moment threshold. -/
theorem integrable_betaPrimeTraceOneSource_fourth_h14
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K) :
    Integrable (fun source ↦ betaPrimeTraceOneSource N K source ^ 4)
      (realBetaPrimeGaussianSourceLaw N K) := by
  have hfun : (fun source : BetaPrimeGaussianSource N K ↦
      betaPrimeTraceOneSource N K source ^ 4) =
      fun source ↦
        ∑ is : Fin 4 → Fin N, ∑ js : Fin 4 → Fin N,
          ∏ t : Fin 4,
            scaledInverseWishartDenominator N K source (is t) (js t) *
              realWishartGram source.1 (js t) (is t) := by
    funext source
    rw [betaPrimeTraceOneSource_eq_scaledInverseWishart_trace]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    rw [Fintype.sum_pow]
    apply Finset.sum_congr rfl
    intro is his
    rw [Fintype.prod_sum]
  rw [hfun]
  apply integrable_finsetSum Finset.univ
  intro is his
  apply integrable_finsetSum Finset.univ
  intro js hjs
  exact integrable_betaPrime_fourEntrySourceProduct_h14 hgap
    (fun t ↦ (is t, js t)) (fun t ↦ (js t, is t))

/-- The square of the raw second beta-prime trace is integrable at the same
sharp threshold. -/
theorem integrable_betaPrimeTraceTwoSource_square_h14
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K) :
    Integrable (fun source ↦ betaPrimeTraceTwoSource N K source ^ 2)
      (realBetaPrimeGaussianSourceLaw N K) := by
  let Q := Fin N × (Fin N × (Fin N × Fin N))
  let term : BetaPrimeGaussianSource N K → Q → ℝ := fun source q ↦
    scaledInverseWishartDenominator N K source q.1 q.2.2.2 *
      realWishartGram source.1 q.2.2.2 q.2.2.1 *
      scaledInverseWishartDenominator N K source q.2.2.1 q.2.1 *
      realWishartGram source.1 q.2.1 q.1
  have htrace (source : BetaPrimeGaussianSource N K) :
      betaPrimeTraceTwoSource N K source = ∑ q : Q, term source q := by
    rw [betaPrimeTraceTwoSource_eq_scaledInverseWishart_trace]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Finset.sum_mul]
    dsimp only [Q, term]
    simp only [Fintype.sum_prod_type]
  have hfun : (fun source : BetaPrimeGaussianSource N K ↦
      betaPrimeTraceTwoSource N K source ^ 2) =
      fun source ↦ ∑ qs : Fin 2 → Q, ∏ t : Fin 2, term source (qs t) := by
    funext source
    rw [htrace, Fintype.sum_pow]
  rw [hfun]
  apply integrable_finsetSum Finset.univ
  intro qs hqs
  let cIndices : Fin 4 → Fin N × Fin N :=
    ![((qs 0).1, (qs 0).2.2.2), ((qs 0).2.2.1, (qs 0).2.1),
      ((qs 1).1, (qs 1).2.2.2), ((qs 1).2.2.1, (qs 1).2.1)]
  let wIndices : Fin 4 → Fin N × Fin N :=
    ![((qs 0).2.2.2, (qs 0).2.2.1), ((qs 0).2.1, (qs 0).1),
      ((qs 1).2.2.2, (qs 1).2.2.1), ((qs 1).2.1, (qs 1).1)]
  have hmono := integrable_betaPrime_fourEntrySourceProduct_h14
    hgap cIndices wIndices
  apply hmono.congr
  filter_upwards [] with source
  simp [term, cIndices, wIndices, Fin.prod_univ_two,
    Fin.prod_univ_four]
  ring

/-- Axiom-free qualitative integrability of the normalized fourth radial
remainder on the literal Gaussian source. -/
theorem integrable_h14BetaPrimeNormalizedFourthRemainder_source_internal
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K) :
    Integrable
      (fun source : BetaPrimeGaussianSource N K ↦
        h14BetaPrimeNormalizedFourthRemainder N K
          (realBetaPrimeTracePowerVector 4 N K source))
      (realBetaPrimeGaussianSourceLaw N K) := by
  have hOne := integrable_betaPrimeTraceOneSource_fourth_h14 hgap
  have hTwo := integrable_betaPrimeTraceTwoSource_square_h14 hgap
  have hOneScaled := hOne.div_const
    ((N : ℝ) ^ 4 * concreteCOEExponent N K ^ 2)
  have hTwoScaled := hTwo.div_const
    ((N : ℝ) ^ 2 * concreteCOEExponent N K ^ 2)
  change Integrable
    (fun source ↦ betaPrimeTraceOneSource N K source ^ 4 /
        ((N : ℝ) ^ 4 * concreteCOEExponent N K ^ 2) +
      betaPrimeTraceTwoSource N K source ^ 2 /
        ((N : ℝ) ^ 2 * concreteCOEExponent N K ^ 2))
    (realBetaPrimeGaussianSourceLaw N K)
  exact hOneScaled.add hTwoScaled

/-- Axiom-free qualitative integrability of the normalized fourth radial
remainder on the exposed four-trace beta-prime law. -/
theorem integrable_h14BetaPrimeNormalizedFourthRemainder_internal
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K) :
    Integrable (h14BetaPrimeNormalizedFourthRemainder N K)
      (betaPrimeTraceFourLaw N K) := by
  have hmeas : Measurable
      (h14BetaPrimeNormalizedFourthRemainder N K) := by
    unfold h14BetaPrimeNormalizedFourthRemainder betaPrimeYTraceOne
      betaPrimeYTraceTwo
    fun_prop
  unfold betaPrimeTraceFourLaw
  apply (integrable_map_measure hmeas.aestronglyMeasurable
    (measurable_realBetaPrimeTracePowerVector_internal 4 N K).aemeasurable).2
  exact integrable_h14BetaPrimeNormalizedFourthRemainder_source_internal hgap

/-! ## Exact conditional producer interfaces -/

/-- The two conditional producer interfaces imply explicit source-level
fourth bounds.  This theorem is conditional and is not an endpoint. -/
theorem h14_explicitGaussianFourthSourceBounds_conditional
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K)
    (HWick : H14FiniteGaussianFourthWickFormula N K)
    (Hden : H14DenominatorFourthTracePolynomialBounds N K) :
    (16 * N ≤ K →
      (∫ source, betaPrimeTraceOneSource N K source ^ 4
        ∂realBetaPrimeGaussianSourceLaw N K) ≤
        (2 : ℝ) ^ 16 * (N : ℝ) ^ 8) ∧
    (16 * N ≤ K →
      (∫ source, betaPrimeTraceTwoSource N K source ^ 2
        ∂realBetaPrimeGaussianSourceLaw N K) ≤
        (2 : ℝ) ^ 16 * (N : ℝ) ^ 6) := by
  let muA := standardRealGaussianMatrixMeasure (N + 1) N
  let muB := standardRealGaussianMatrixMeasure (K - N) N
  letI : IsProbabilityMeasure muA :=
    standardRealGaussianMatrixMeasure_isProbability_internal _ _
  letI : IsProbabilityMeasure muB :=
    standardRealGaussianMatrixMeasure_isProbability_internal _ _
  have hOne := integrable_betaPrimeTraceOneSource_fourth_h14 hgap
  have hTwo := integrable_betaPrimeTraceTwoSource_square_h14 hgap
  constructor
  · intro hdense
    calc
      (∫ source, betaPrimeTraceOneSource N K source ^ 4
          ∂realBetaPrimeGaussianSourceLaw N K) =
          ∫ H, ∫ G, betaPrimeTraceOneSource N K (G, H) ^ 4 ∂muA ∂muB := by
        change (∫ source, betaPrimeTraceOneSource N K source ^ 4
          ∂muA.prod muB) = _
        exact integral_prod_symm _ hOne
      _ = ∫ H, h14TraceOneFourthWickPolynomial (N + 1)
          (scaledInverseWishartMatrix N K H) ∂muB := by
        apply integral_congr_ae
        filter_upwards [] with H
        exact HWick.traceOne_fourth_fiber_eq H
      _ ≤ _ := Hden.traceOne_polynomial_integral_le hdense
  · intro hdense
    calc
      (∫ source, betaPrimeTraceTwoSource N K source ^ 2
          ∂realBetaPrimeGaussianSourceLaw N K) =
          ∫ H, ∫ G, betaPrimeTraceTwoSource N K (G, H) ^ 2 ∂muA ∂muB := by
        change (∫ source, betaPrimeTraceTwoSource N K source ^ 2
          ∂muA.prod muB) = _
        exact integral_prod_symm _ hTwo
      _ = ∫ H, h14TraceTwoSquareWickPolynomial (N + 1)
          (scaledInverseWishartMatrix N K H) ∂muB := by
        apply integral_congr_ae
        filter_upwards [] with H
        exact HWick.traceTwo_square_fiber_eq H
      _ ≤ _ := Hden.traceTwo_polynomial_integral_le hdense

/-- **CONDITIONAL radial closure from the smallest explicit producers.**
Qualitative integrability is unconditional; only the finite trace
contraction and the denominator-only dense polynomial estimates are theorem
parameters. -/
theorem h14BetaPrimeNormalizedFourthRemainderExpectationContract_conditional
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (HWick : H14FiniteGaussianFourthWickFormula N K)
    (Hden : H14DenominatorFourthTracePolynomialBounds N K) :
    H14BetaPrimeNormalizedFourthRemainderExpectationContract N K := by
  refine ⟨integrable_h14BetaPrimeNormalizedFourthRemainder_internal hgap, ?_⟩
  intro hdense
  let n : ℝ := N
  let c : ℝ := concreteCOEExponent N K
  have hn : 0 < n := by
    dsimp only [n]
    exact_mod_cast (show 0 < N by omega)
  have hdenseR : (16 : ℝ) * n ≤ (K : ℝ) := by
    dsimp only [n]
    exact_mod_cast hdense
  have hc : n ≤ c := by
    have hNreal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    dsimp only [n] at hdenseR
    dsimp only [n, c]
    unfold concreteCOEExponent
    linarith
  have hcpos : 0 < c := hn.trans_le hc
  have hsource := h14_explicitGaussianFourthSourceBounds_conditional
    hgap HWick Hden
  have hOneBound := hsource.1 hdense
  have hTwoBound := hsource.2 hdense
  have hOneInt := integrable_betaPrimeTraceOneSource_fourth_h14 hgap
  have hTwoInt := integrable_betaPrimeTraceTwoSource_square_h14 hgap
  have hremSource :=
    integrable_h14BetaPrimeNormalizedFourthRemainder_source_internal hgap
  have hmapMeas : AEMeasurable (realBetaPrimeTracePowerVector 4 N K)
      (realBetaPrimeGaussianSourceLaw N K) :=
    (measurable_realBetaPrimeTracePowerVector_internal 4 N K).aemeasurable
  have hremMeas : AEStronglyMeasurable
      (h14BetaPrimeNormalizedFourthRemainder N K)
      (betaPrimeTraceFourLaw N K) :=
    (integrable_h14BetaPrimeNormalizedFourthRemainder_internal hgap).aestronglyMeasurable
  have hpush :
      (∫ u, h14BetaPrimeNormalizedFourthRemainder N K u
        ∂betaPrimeTraceFourLaw N K) =
      ∫ source,
        h14BetaPrimeNormalizedFourthRemainder N K
          (realBetaPrimeTracePowerVector 4 N K source)
        ∂realBetaPrimeGaussianSourceLaw N K := by
    unfold betaPrimeTraceFourLaw
    exact integral_map hmapMeas hremMeas
  rw [hpush]
  change (∫ source,
      betaPrimeTraceOneSource N K source ^ 4 /
          (n ^ 4 * c ^ 2) +
        betaPrimeTraceTwoSource N K source ^ 2 /
          (n ^ 2 * c ^ 2)
      ∂realBetaPrimeGaussianSourceLaw N K) ≤
        denseClassicalMomentConstant * n ^ 2
  have hOneDiv : Integrable
      (fun source ↦ betaPrimeTraceOneSource N K source ^ 4 /
        (n ^ 4 * c ^ 2))
      (realBetaPrimeGaussianSourceLaw N K) := by
    exact hOneInt.div_const (n ^ 4 * c ^ 2)
  have hTwoDiv : Integrable
      (fun source ↦ betaPrimeTraceTwoSource N K source ^ 2 /
        (n ^ 2 * c ^ 2))
      (realBetaPrimeGaussianSourceLaw N K) := by
    exact hTwoInt.div_const (n ^ 2 * c ^ 2)
  rw [integral_add hOneDiv hTwoDiv, integral_div, integral_div]
  have hdenOne : 0 < n ^ 4 * c ^ 2 := by positivity
  have hdenTwo : 0 < n ^ 2 * c ^ 2 := by positivity
  have hOneScaled :
      (∫ source, betaPrimeTraceOneSource N K source ^ 4
        ∂realBetaPrimeGaussianSourceLaw N K) / (n ^ 4 * c ^ 2) ≤
        (2 : ℝ) ^ 16 * n ^ 2 := by
    calc
      _ ≤ ((2 : ℝ) ^ 16 * n ^ 8) / (n ^ 4 * c ^ 2) :=
        (div_le_div_iff_of_pos_right hdenOne).2 (by simpa only [n] using hOneBound)
      _ = ((2 : ℝ) ^ 16 * n ^ 4) / c ^ 2 := by
        field_simp [hn.ne']
        <;> ring
      _ ≤ ((2 : ℝ) ^ 16 * n ^ 4) / n ^ 2 := by
        exact div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hn)
          (by nlinarith [sq_nonneg (c - n)])
      _ = (2 : ℝ) ^ 16 * n ^ 2 := by
        field_simp [hn.ne']
        <;> ring
  have hTwoScaled :
      (∫ source, betaPrimeTraceTwoSource N K source ^ 2
        ∂realBetaPrimeGaussianSourceLaw N K) / (n ^ 2 * c ^ 2) ≤
        (2 : ℝ) ^ 16 * n ^ 2 := by
    calc
      _ ≤ ((2 : ℝ) ^ 16 * n ^ 6) / (n ^ 2 * c ^ 2) :=
        (div_le_div_iff_of_pos_right hdenTwo).2 (by simpa only [n] using hTwoBound)
      _ = ((2 : ℝ) ^ 16 * n ^ 4) / c ^ 2 := by
        field_simp [hn.ne']
        <;> ring
      _ ≤ ((2 : ℝ) ^ 16 * n ^ 4) / n ^ 2 := by
        exact div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hn)
          (by nlinarith [sq_nonneg (c - n)])
      _ = (2 : ℝ) ^ 16 * n ^ 2 := by
        field_simp [hn.ne']
        <;> ring
  calc
    _ ≤ (2 : ℝ) ^ 16 * n ^ 2 + (2 : ℝ) ^ 16 * n ^ 2 :=
      add_le_add hOneScaled hTwoScaled
    _ ≤ denseClassicalMomentConstant * n ^ 2 := by
      rw [show (2 : ℝ) ^ 16 * n ^ 2 + (2 : ℝ) ^ 16 * n ^ 2 =
        (2 * (2 : ℝ) ^ 16) * n ^ 2 by ring]
      exact mul_le_mul_of_nonneg_right
        (by norm_num [denseClassicalMomentConstant]) (sq_nonneg n)

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08
