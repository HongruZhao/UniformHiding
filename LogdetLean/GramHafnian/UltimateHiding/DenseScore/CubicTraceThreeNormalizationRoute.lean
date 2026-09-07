import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CubicTraceThreeCoefficient
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H7ExactConcreteCenteredCubicIdentification
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CenteredScoreFubiniThirdInternal
import Mathlib.Tactic

/-!
# Normalization route for the raw third trace

This module proves the two exact facts needed before any remainder estimate:

* total mass forces the averaged centered third density to have integral zero;
* pointwise, that density is a positive explicit coefficient times `Tr Y³`
  plus a remainder containing no `Tr Y³` variable.

The remaining analytic task is only to bound that lower-trace remainder in
`L¹`.  No new external assumption is introduced here.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.LocalAnticoncentration

/-- The third derivative of the centered projective total-mass path is zero. -/
theorem
    concreteProjectiveAveragedCenteredCOEEventPath_univ_iteratedDeriv_three_eq_zero
    {N K : ℕ} (hN : 1 ≤ N) (hNK : N ≤ K) :
    iteratedDeriv 3
        (concreteProjectiveAveragedCenteredCOEEventPath N K Set.univ) 0 = 0 := by
  have hfun : concreteProjectiveAveragedCenteredCOEEventPath N K Set.univ =
      fun _ : ℝ ↦ 1 := by
    funext t
    exact concreteProjectiveAveragedCenteredCOEEventPath_univ_eq_one hN hNK t
  rw [hfun]
  simpa using
    (iteratedDeriv_const (n := 3) (c := (1 : ℝ)) (x := (0 : ℝ)))

/-- The exact averaged centered cubic density has zero integral by total-mass
normalization.  This uses only the already retained fixed-direction boundary,
projective interchange/Fubini, and fixed-state cubic witness. -/
theorem integral_concreteAveragedCenteredCubicDensity_eq_zero_internal
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    (∫ A, concreteAveragedCenteredCubicDensity N K A
      ∂(concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K)) = 0 := by
  have hboundary : 2 * N + 8 ≤ K := by omega
  have hNK : N ≤ K := by omega
  let mu := concreteScaledCOECornerLaw
    canonicalUnitaryHaarProbabilityFamily N K
  have hmass :=
    concreteProjectiveAveragedCenteredCOEEventPath_univ_iteratedDeriv_three_eq_zero
      hN hNK
  have hliteral :=
    coeCorner_centeredProjective_eventPath_derivative_literal_three_internal
      hN hboundary Set.univ MeasurableSet.univ
  rw [hmass] at hliteral
  have hidentify :
      (fun A : ConcreteMatrixState N ↦
        ∫ v : ComplexUnitSphere N,
          concreteCenteredDensityScore 3 N K v A
            ∂(complexUnitSphereProbabilityMeasure N)) =ᵐ[mu]
        concreteAveragedCenteredCubicDensity N K := by
    filter_upwards
      [friedmanMello1985_scaledCOECorner_ae_support_from_density hN (by omega)]
        with A hA
    exact integral_concreteCenteredDensityScoreThree_eq_density_of_H7Exact
      hN hdense A hA.1 hA.2
  have hintegral :
      (∫ A, (∫ v : ComplexUnitSphere N,
          concreteCenteredDensityScore 3 N K v A
            ∂(complexUnitSphereProbabilityMeasure N)) ∂mu) = 0 := by
    simpa only [Set.indicator_of_mem (Set.mem_univ _)] using hliteral.symm
  rw [integral_congr_ae hidentify] at hintegral
  simpa only [mu] using hintegral

/-- The lower-trace remainder obtained by setting the raw third-trace
coordinate to zero in the exact scalar polynomial. -/
def concreteAveragedCenteredCubicTraceThreeRemainder
    (N K : ℕ) (A : ConcreteMatrixState N) : ℝ :=
  scalarAveragedCenteredCubicDensity (N : ℝ) (concreteCOEExponent N K)
    (concreteCOETraceOne N K A) (concreteCOETraceTwo N K A) 0

/-- The concrete closed density agrees with its scalar trace polynomial. -/
theorem concreteAveragedCenteredCubicDensity_eq_scalar
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K)
    (A : ConcreteMatrixState N) :
    concreteAveragedCenteredCubicDensity N K A =
      scalarAveragedCenteredCubicDensity (N : ℝ) (concreteCOEExponent N K)
        (concreteCOETraceOne N K A) (concreteCOETraceTwo N K A)
        (concreteCOETraceThree N K A) := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hc : concreteCOEExponent N K ≠ 0 := by
    unfold concreteCOEExponent
    have hdenseR : (16 : ℝ) * (N : ℝ) ≤ (K : ℝ) := by
      exact_mod_cast hdense
    have hNreal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    nlinarith
  simp only [concreteAveragedCenteredCubicDensity,
    concreteAveragedRankOneCubicDensity,
    concreteMixedScalarQuadraticDensity,
    concreteCentralDerivativeCenteredQuadraticDensity,
    concreteCenteredQuadraticDensity,
    concreteCenteredQuadraticTraceBracket,
    concreteCentralLogScoreOne,
    concreteCentralDensityScoreThree_expansion,
    concreteCentralSOneTraceOne, concreteCentralSOneTraceTwo,
    concreteProjectiveMeanS, concreteProjectiveMeanSSquare,
    concreteProjectiveMeanSCube, concreteCOECenteredMatrixTraceOne,
    concreteCOECenteredMatrixTraceTwo, concreteCOECenteredMatrixTraceThree,
    concreteCOETraceZW, concreteCOETraceZTraceZW, concreteCOETraceZTwoW,
    scalarAveragedCenteredCubicDensity,
    scalarAveragedRankOneCubicDensity, scalarMixedScalarQuadraticDensity,
    scalarCentralDensityScoreThree, scalarCenteredTraceOne,
    scalarCenteredTraceTwo, scalarCenteredTraceThree,
    averagedCubicNonWExpression, averagedCubicWTraceExpression,
    cubicTraceCoefficientThree, cubicTraceCoefficientTwo,
    cubicTraceCoefficientOne, cubicTraceCoefficientZero,
    centeredQuadraticTraceBracket, centralDerivativeQuadraticTraceBracket,
    centralTraceOneDerivative, centralTraceTwoDerivative,
    quadraticTraceCoeffTwo, quadraticTraceCoeffSquare,
    quadraticTraceCoeffOne]

/-- Exact pointwise isolation of the raw third trace in the concrete density. -/
theorem concreteAveragedCenteredCubicDensity_extract_traceThree
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K)
    (A : ConcreteMatrixState N) :
    concreteAveragedCenteredCubicDensity N K A =
      averagedCenteredCubicTraceThreeCoefficient (N : ℝ)
          (concreteCOEExponent N K) * concreteCOETraceThree N K A +
        concreteAveragedCenteredCubicTraceThreeRemainder N K A := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hNpOne : (N : ℝ) + 1 ≠ 0 := by positivity
  have hNpTwo : (N : ℝ) + 2 ≠ 0 := by positivity
  have hc : concreteCOEExponent N K ≠ 0 := by
    unfold concreteCOEExponent
    have hdenseR : (16 : ℝ) * (N : ℝ) ≤ (K : ℝ) := by
      exact_mod_cast hdense
    have hNreal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    nlinarith
  rw [concreteAveragedCenteredCubicDensity_eq_scalar hN hdense A]
  exact scalarAveragedCenteredCubicDensity_extract_traceThree
    hNr hNpOne hNpTwo hc _ _ _

/-- In the headline dense range, the concrete raw-third coefficient is at
least `4/(3N³)`. -/
theorem concreteAveragedCenteredCubicTraceThreeCoefficient_lower_bound
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    4 / (3 * (N : ℝ) ^ 3) ≤
      averagedCenteredCubicTraceThreeCoefficient (N : ℝ)
        (concreteCOEExponent N K) := by
  apply averagedCenteredCubicTraceThreeCoefficient_lower_bound
    (by exact_mod_cast hN)
  unfold concreteCOEExponent
  have hdenseR : (16 : ℝ) * (N : ℝ) ≤ (K : ℝ) := by
    exact_mod_cast hdense
  have hNreal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  nlinarith

/-- The lower-trace remainder is `L¹`.  Product integrability of the literal
third score gives integrability of its projective average; the exact
fixed-state identification transfers this to the closed density, and the
positive-trace package supplies the raw third term. -/
theorem concreteAveragedCenteredCubicTraceThreeRemainder_memLp_one_internal
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    MemLp (concreteAveragedCenteredCubicTraceThreeRemainder N K) 1
      (concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K) := by
  have hgap : 2 * N + 8 ≤ K := by omega
  have h2NK : 2 * N ≤ K := by omega
  let mu := concreteScaledCOECornerLaw
    canonicalUnitaryHaarProbabilityFamily N K
  let sphere := complexUnitSphereProbabilityMeasure N
  let literal : ConcreteMatrixState N × ComplexUnitSphere N → ℝ :=
    fun Av ↦ concreteCenteredDensityScore 3 N K Av.2 Av.1
  let averaged : ConcreteMatrixState N → ℝ := fun A ↦
    ∫ v : ComplexUnitSphere N, concreteCenteredDensityScore 3 N K v A ∂sphere
  let closed := concreteAveragedCenteredCubicDensity N K
  let tThree := concreteCOETraceThree N K
  let rem := concreteAveragedCenteredCubicTraceThreeRemainder N K
  let alpha := averagedCenteredCubicTraceThreeCoefficient (N : ℝ)
    (concreteCOEExponent N K)
  letI : IsProbabilityMeasure mu :=
    canonicalScaledCOECornerLaw_isProbability (by omega)
  letI : IsProbabilityMeasure sphere :=
    complexUnitSphereProbabilityMeasure_isProbability hN
  have hliteral : MemLp literal 1 (mu.prod sphere) := by
    simpa only [literal, mu, sphere, concreteCenteredScoreProductLaw] using
      concreteCenteredDensityScoreThreeProduct_memLp_one_internal hN hgap
  have hliteralInt : Integrable literal (mu.prod sphere) :=
    memLp_one_iff_integrable.mp hliteral
  have havgInt : Integrable averaged mu := by
    simpa only [averaged, literal] using
      hliteralInt.integral_prod_left
  have havgMem : MemLp averaged 1 mu :=
    memLp_one_iff_integrable.mpr havgInt
  have hidentify : averaged =ᵐ[mu] closed := by
    filter_upwards
      [friedmanMello1985_scaledCOECorner_ae_support_from_density hN (by omega)]
        with A hA
    exact integral_concreteCenteredDensityScoreThree_eq_density_of_H7Exact
      hN hdense A hA.1 hA.2
  have hclosedMem : MemLp closed 1 mu :=
    (memLp_congr_ae hidentify).mp havgMem
  have htThreeMem : MemLp tThree 1 mu := by
    let f := concreteCOETracePowerVector 4 N K
    have heq : tThree = betaPrimeYTraceThree N K ∘ f := by
      funext A
      exact (concreteBetaPrimeYTraceThree_eq_concreteCOETraceThree N K A).symm
    rw [heq]
    simpa only [mu, f] using memLp_comp_concreteCOETracePowerVector hN h2NK
      (betaPrimeYTraceThree_memLp_one_positive_internal hN hgap)
  have hremEq : rem = closed - alpha • tThree := by
    funext A
    have hpoint :=
      concreteAveragedCenteredCubicDensity_extract_traceThree hN hdense A
    simp only [rem, closed, alpha, tThree, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]
    linarith
  change MemLp rem 1 mu
  rw [hremEq]
  exact hclosedMem.sub (htThreeMem.const_smul alpha)

/-- Once the lower-trace remainder is bounded by `C N`, normalization and
positivity give the sharp raw-third-trace bound automatically.  This theorem
isolates the sole remaining analytic obligation in the proposed axiom
elimination. -/
theorem concreteCOETraceThree_lpNorm_one_le_of_remainder
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K)
    {C : ℝ}
    (hremMem : MemLp
      (concreteAveragedCenteredCubicTraceThreeRemainder N K) 1
      (concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K))
    (hremNorm :
      lpNorm (concreteAveragedCenteredCubicTraceThreeRemainder N K) 1
          (concreteScaledCOECornerLaw
            canonicalUnitaryHaarProbabilityFamily N K) ≤
        C * (N : ℝ)) :
    lpNorm (concreteCOETraceThree N K) 1
        (concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K) ≤
      (3 * C / 4) * (N : ℝ) ^ 4 := by
  have hgap : 2 * N + 8 ≤ K := by omega
  have h2NK : 2 * N ≤ K := by omega
  let mu := concreteScaledCOECornerLaw
    canonicalUnitaryHaarProbabilityFamily N K
  let tThree := concreteCOETraceThree N K
  let rem := concreteAveragedCenteredCubicTraceThreeRemainder N K
  let alpha := averagedCenteredCubicTraceThreeCoefficient (N : ℝ)
    (concreteCOEExponent N K)
  letI : IsProbabilityMeasure mu :=
    canonicalScaledCOECornerLaw_isProbability (by omega)
  have htThreeMem : MemLp tThree 1 mu := by
    let f := concreteCOETracePowerVector 4 N K
    have heq : tThree = betaPrimeYTraceThree N K ∘ f := by
      funext A
      exact (concreteBetaPrimeYTraceThree_eq_concreteCOETraceThree N K A).symm
    rw [heq]
    simpa only [mu, f] using memLp_comp_concreteCOETracePowerVector hN h2NK
      (betaPrimeYTraceThree_memLp_one_positive_internal hN hgap)
  have htThreeNonneg : ∀ᵐ A ∂mu, 0 ≤ tThree A := by
    filter_upwards
      [friedmanMello1985_scaledCOECorner_ae_support_from_density hN (by omega)]
        with A hA
    exact concreteCOETraceThree_nonneg_of_support hgap A hA.2
  have htThreeInt : Integrable tThree mu :=
    memLp_one_iff_integrable.mp htThreeMem
  have hremInt : Integrable rem mu := by
    apply memLp_one_iff_integrable.mp
    simpa only [rem, mu] using hremMem
  have hdecomp : concreteAveragedCenteredCubicDensity N K =
      alpha • tThree + rem := by
    funext A
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, alpha, tThree, rem]
    exact concreteAveragedCenteredCubicDensity_extract_traceThree hN hdense A
  have hzero := integral_concreteAveragedCenteredCubicDensity_eq_zero_internal
    hN hdense
  have halphaIntegral : alpha * (∫ A, tThree A ∂mu) +
      ∫ A, rem A ∂mu = 0 := by
    rw [hdecomp] at hzero
    change (∫ A, alpha * tThree A + rem A ∂mu) = 0 at hzero
    rw [integral_add (htThreeInt.const_mul alpha) hremInt,
      integral_const_mul] at hzero
    simpa only [mu, alpha, tThree, rem] using hzero
  have hremIntegralAbs : |∫ A, rem A ∂mu| ≤ lpNorm rem 1 mu := by
    calc
      |∫ A, rem A ∂mu| ≤ ∫ A, |rem A| ∂mu :=
        abs_integral_le_integral_abs
      _ = lpNorm rem 1 mu := by
        rw [lpNorm_one_eq_integral_norm hremMem.aestronglyMeasurable]
        rfl
  have hIntegralNonneg : 0 ≤ ∫ A, tThree A ∂mu :=
    integral_nonneg_of_ae htThreeNonneg
  have halphaLower : 4 / (3 * (N : ℝ) ^ 3) ≤ alpha := by
    simpa only [alpha] using
      concreteAveragedCenteredCubicTraceThreeCoefficient_lower_bound hN hdense
  have halphaIntegralUpper :
      alpha * (∫ A, tThree A ∂mu) ≤ C * (N : ℝ) := by
    calc
      alpha * (∫ A, tThree A ∂mu) = -(∫ A, rem A ∂mu) := by
        linarith
      _ ≤ |∫ A, rem A ∂mu| := neg_le_abs _
      _ ≤ lpNorm rem 1 mu := hremIntegralAbs
      _ ≤ C * (N : ℝ) := by simpa only [rem, mu] using hremNorm
  have hlowerIntegral :
      (4 / (3 * (N : ℝ) ^ 3)) * (∫ A, tThree A ∂mu) ≤
        C * (N : ℝ) := by
    exact (mul_le_mul_of_nonneg_right halphaLower hIntegralNonneg).trans
      halphaIntegralUpper
  have hNr : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hcoef : 0 < 4 / (3 * (N : ℝ) ^ 3) := by positivity
  have hintegralBound :
      (∫ A, tThree A ∂mu) ≤ (3 * C / 4) * (N : ℝ) ^ 4 := by
    calc
      (∫ A, tThree A ∂mu) ≤
          (C * (N : ℝ)) / (4 / (3 * (N : ℝ) ^ 3)) :=
        (le_div_iff₀ hcoef).2 (by simpa [mul_comm] using hlowerIntegral)
      _ = (3 * C / 4) * (N : ℝ) ^ 4 := by
        field_simp [ne_of_gt hNr]
  rw [lpNorm_one_eq_integral_norm htThreeMem.aestronglyMeasurable]
  calc
    (∫ A, ‖tThree A‖ ∂mu) = ∫ A, tThree A ∂mu := by
      apply integral_congr_ae
      filter_upwards [htThreeNonneg] with A hA
      rw [Real.norm_eq_abs, abs_of_nonneg hA]
    _ ≤ (3 * C / 4) * (N : ℝ) ^ 4 := hintegralBound

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
