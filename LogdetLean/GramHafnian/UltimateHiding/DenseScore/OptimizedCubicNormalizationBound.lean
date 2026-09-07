import LogdetLean.GramHafnian.UltimateHiding.DenseScore.OptimizedLowerTraceMomentBounds
import LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep.ConcreteOrbitalCubicScore
import Mathlib.Tactic

/-!
# Optimized cubic normalization bound

This module reruns the five-monomial lower-trace remainder argument using the
unrelaxed H9/H10 constants.  Its exact ledger is

`100 * 9218^3 + 600 * 9218^2 + 600 * (9218 * 8212) +
  1000 * 20 + 400 * 9218 = 78423156374400`.

Total-mass normalization and positivity then give the raw-third-trace
constant `3R/4`, and the coefficient bound `600/N^3` gives the centered cubic
constant `600 * (3R/4) + R = 451R`.  The final section propagates this number
to the literal event-path third derivative at the origin.
-/

open MeasureTheory Set

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.CurrentPRL

/-- Exact five-monomial remainder budget from the optimized lower traces. -/
def optimizedRawTraceThreeRemainderConstant : ℝ :=
  100 * optimizedRawTraceOneCubeConstant +
    600 * optimizedRawTraceOneSquareConstant +
    600 * optimizedRawTraceOneTwoConstant +
    1000 * optimizedRawTraceTwoL1Constant +
    400 * optimizedRawTraceOneL3Constant

theorem optimizedRawTraceThreeRemainderConstant_eq :
    optimizedRawTraceThreeRemainderConstant = 78423156374400 := by
  norm_num [optimizedRawTraceThreeRemainderConstant,
    optimizedRawTraceOneCubeConstant,
    optimizedRawTraceOneSquareConstant,
    optimizedRawTraceOneTwoConstant,
    optimizedRawTraceOneL3Constant,
    optimizedRawTraceTwoL2Constant,
    optimizedRawTraceTwoL1Constant]

/-- Product-`L¹` closure of the five-monomial remainder using the optimized
lower-trace moment packages. -/
theorem betaPrimeAveragedCenteredCubicTraceThreeRemainder_memLp_one_optimized
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    MemLp (betaPrimeAveragedCenteredCubicTraceThreeRemainder N K) 1
      (betaPrimeTraceFourLaw N K) := by
  have hgap : 2 * N + 8 ≤ K := by omega
  let mu := betaPrimeTraceFourLaw N K
  let f1 := fun u ↦ betaPrimeYTraceOne N K u ^ 3
  let f2 := fun u ↦ betaPrimeYTraceOne N K u ^ 2
  let f3 := fun u ↦ betaPrimeYTraceOne N K u * betaPrimeYTraceTwo N K u
  let f4 := betaPrimeYTraceTwo N K
  let f5 := betaPrimeYTraceOne N K
  let a1 := cubicTraceThreeRemainderCoeffCube (N : ℝ)
    (concreteCOEExponent N K)
  let a2 := cubicTraceThreeRemainderCoeffSquare (N : ℝ)
    (concreteCOEExponent N K)
  let a3 := cubicTraceThreeRemainderCoeffMixed (N : ℝ)
    (concreteCOEExponent N K)
  let a4 := cubicTraceThreeRemainderCoeffTwo (N : ℝ)
    (concreteCOEExponent N K)
  let a5 := cubicTraceThreeRemainderCoeffOne (N : ℝ)
    (concreteCOEExponent N K)
  have hf1 : MemLp f1 1 mu := by
    simpa only [f1, mu] using
      (betaPrimeYTraceOneCube_momentPackage_optimized hN hgap).1
  have hf2 : MemLp f2 1 mu := by
    simpa only [f2, mu] using
      (betaPrimeYTraceOneSquare_momentPackage_optimized hN hgap).1
  have hf3 : MemLp f3 1 mu := by
    simpa only [f3, mu] using
      (betaPrimeYTraceOneTwo_momentPackage_optimized hN hgap).1
  have hf4 : MemLp f4 1 mu := by
    simpa only [f4, mu] using
      betaPrimeYTraceTwo_memLp_one_positive_internal hN hgap
  have hf5 : MemLp f5 1 mu := by
    simpa only [f5, mu] using
      betaPrimeYTraceOne_memLp_one_proved_allDimensions hN hgap
  rw [betaPrimeAveragedCenteredCubicTraceThreeRemainder_eq_lowerTracePolynomial
    hN hdense]
  change MemLp (a1 • f1 + a2 • f2 + a3 • f3 + a4 • f4 + a5 • f5) 1 mu
  exact ((((hf1.const_smul a1).add (hf2.const_smul a2)).add
    (hf3.const_smul a3)).add (hf4.const_smul a4)).add
      (hf5.const_smul a5)

/-- The five coefficient bounds and optimized raw moments give exactly
`R * N` for the lower-trace remainder. -/
theorem betaPrimeAveragedCenteredCubicTraceThreeRemainder_lpNorm_one_le_optimized
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (betaPrimeAveragedCenteredCubicTraceThreeRemainder N K) 1
        (betaPrimeTraceFourLaw N K) ≤
      optimizedRawTraceThreeRemainderConstant * (N : ℝ) := by
  have hgap : 2 * N + 8 ≤ K := by omega
  let mu := betaPrimeTraceFourLaw N K
  let x : ℝ := N
  let c := concreteCOEExponent N K
  let f1 := fun u ↦ betaPrimeYTraceOne N K u ^ 3
  let f2 := fun u ↦ betaPrimeYTraceOne N K u ^ 2
  let f3 := fun u ↦ betaPrimeYTraceOne N K u * betaPrimeYTraceTwo N K u
  let f4 := betaPrimeYTraceTwo N K
  let f5 := betaPrimeYTraceOne N K
  let a1 := cubicTraceThreeRemainderCoeffCube x c
  let a2 := cubicTraceThreeRemainderCoeffSquare x c
  let a3 := cubicTraceThreeRemainderCoeffMixed x c
  let a4 := cubicTraceThreeRemainderCoeffTwo x c
  let a5 := cubicTraceThreeRemainderCoeffOne x c
  have hx : 1 ≤ x := by
    change (1 : ℝ) ≤ (N : ℝ)
    exact_mod_cast hN
  have hc : x ≤ c := by
    dsimp only [x, c]
    unfold concreteCOEExponent
    have hdenseR : (16 : ℝ) * (N : ℝ) ≤ (K : ℝ) := by
      exact_mod_cast hdense
    nlinarith
  have hf1 : MemLp f1 1 mu := by
    simpa only [f1, mu] using
      (betaPrimeYTraceOneCube_momentPackage_optimized hN hgap).1
  have hf2 : MemLp f2 1 mu := by
    simpa only [f2, mu] using
      (betaPrimeYTraceOneSquare_momentPackage_optimized hN hgap).1
  have hf3 : MemLp f3 1 mu := by
    simpa only [f3, mu] using
      (betaPrimeYTraceOneTwo_momentPackage_optimized hN hgap).1
  have hf4 : MemLp f4 1 mu := by
    simpa only [f4, mu] using
      betaPrimeYTraceTwo_memLp_one_positive_internal hN hgap
  have hf5 : MemLp f5 1 mu := by
    simpa only [f5, mu] using
      betaPrimeYTraceOne_memLp_one_proved_allDimensions hN hgap
  have hf1Norm : lpNorm f1 1 mu ≤
      optimizedRawTraceOneCubeConstant * x ^ 6 := by
    simpa only [f1, mu, x] using
      (betaPrimeYTraceOneCube_momentPackage_optimized hN hgap).2 hdense
  have hf2Norm : lpNorm f2 1 mu ≤
      optimizedRawTraceOneSquareConstant * x ^ 4 := by
    simpa only [f2, mu, x] using
      (betaPrimeYTraceOneSquare_momentPackage_optimized hN hgap).2 hdense
  have hf3Norm : lpNorm f3 1 mu ≤
      optimizedRawTraceOneTwoConstant * x ^ 5 := by
    simpa only [f3, mu, x] using
      (betaPrimeYTraceOneTwo_momentPackage_optimized hN hgap).2 hdense
  have hf4Norm : lpNorm f4 1 mu ≤
      optimizedRawTraceTwoL1Constant * x ^ 3 := by
    simpa only [f4, mu, x] using
      betaPrimeYTraceTwo_lpNorm_one_le_optimized hN hdense
  have hf5Norm : lpNorm f5 1 mu ≤
      optimizedRawTraceOneL3Constant * x ^ 2 := by
    simpa only [f5, mu, x] using
      betaPrimeYTraceOne_lpNorm_one_le_optimized hN hdense
  have ha1 : |a1| ≤ 100 / x ^ 5 := by
    simpa only [a1] using cubicTraceThreeRemainderCoeffCube_abs_le hx hc
  have ha2 : |a2| ≤ 600 / x ^ 3 := by
    simpa only [a2] using cubicTraceThreeRemainderCoeffSquare_abs_le hx hc
  have ha3 : |a3| ≤ 600 / x ^ 4 := by
    simpa only [a3] using cubicTraceThreeRemainderCoeffMixed_abs_le hx hc
  have ha4 : |a4| ≤ 1000 / x ^ 2 := by
    simpa only [a4] using cubicTraceThreeRemainderCoeffTwo_abs_le hx hc
  have ha5 : |a5| ≤ 400 / x := by
    simpa only [a5] using cubicTraceThreeRemainderCoeffOne_abs_le hx hc
  have hC1 : 0 ≤ optimizedRawTraceOneCubeConstant := by
    norm_num [optimizedRawTraceOneCubeConstant,
      optimizedRawTraceOneL3Constant]
  have hC2 : 0 ≤ optimizedRawTraceOneSquareConstant := by
    norm_num [optimizedRawTraceOneSquareConstant,
      optimizedRawTraceOneL3Constant]
  have hC3 : 0 ≤ optimizedRawTraceOneTwoConstant := by
    norm_num [optimizedRawTraceOneTwoConstant,
      optimizedRawTraceOneL3Constant, optimizedRawTraceTwoL2Constant]
  have hC4 : 0 ≤ optimizedRawTraceTwoL1Constant := by
    norm_num [optimizedRawTraceTwoL1Constant]
  have hC5 : 0 ≤ optimizedRawTraceOneL3Constant := by
    norm_num [optimizedRawTraceOneL3Constant]
  have h12 : MemLp (a1 • f1 + a2 • f2) 1 mu :=
    (hf1.const_smul a1).add (hf2.const_smul a2)
  have h123 : MemLp (a1 • f1 + a2 • f2 + a3 • f3) 1 mu :=
    h12.add (hf3.const_smul a3)
  have h1234 : MemLp (a1 • f1 + a2 • f2 + a3 • f3 + a4 • f4) 1 mu :=
    h123.add (hf4.const_smul a4)
  have htri :
      lpNorm (a1 • f1 + a2 • f2 + a3 • f3 + a4 • f4 + a5 • f5) 1 mu ≤
        lpNorm (a1 • f1) 1 mu + lpNorm (a2 • f2) 1 mu +
          lpNorm (a3 • f3) 1 mu + lpNorm (a4 • f4) 1 mu +
            lpNorm (a5 • f5) 1 mu := by
    calc
      _ ≤ lpNorm (a1 • f1 + a2 • f2 + a3 • f3 + a4 • f4) 1 mu +
          lpNorm (a5 • f5) 1 mu :=
        lpNorm_add_le h1234 (p := (1 : ENNReal)) (by norm_num)
      _ ≤ (lpNorm (a1 • f1 + a2 • f2 + a3 • f3) 1 mu +
            lpNorm (a4 • f4) 1 mu) + lpNorm (a5 • f5) 1 mu := by
        gcongr
        exact lpNorm_add_le h123 (p := (1 : ENNReal)) (by norm_num)
      _ ≤ ((lpNorm (a1 • f1 + a2 • f2) 1 mu + lpNorm (a3 • f3) 1 mu) +
            lpNorm (a4 • f4) 1 mu) + lpNorm (a5 • f5) 1 mu := by
        gcongr
        exact lpNorm_add_le h12 (p := (1 : ENNReal)) (by norm_num)
      _ ≤ (((lpNorm (a1 • f1) 1 mu + lpNorm (a2 • f2) 1 mu) +
            lpNorm (a3 • f3) 1 mu) + lpNorm (a4 • f4) 1 mu) +
            lpNorm (a5 • f5) 1 mu := by
        gcongr
        exact lpNorm_add_le (hf1.const_smul a1) (p := (1 : ENNReal))
          (by norm_num)
  rw [betaPrimeAveragedCenteredCubicTraceThreeRemainder_eq_lowerTracePolynomial
    hN hdense]
  change lpNorm (a1 • f1 + a2 • f2 + a3 • f3 + a4 • f4 + a5 • f5) 1 mu ≤ _
  calc
    _ ≤ lpNorm (a1 • f1) 1 mu + lpNorm (a2 • f2) 1 mu +
          lpNorm (a3 • f3) 1 mu + lpNorm (a4 • f4) 1 mu +
            lpNorm (a5 • f5) 1 mu := htri
    _ = |a1| * lpNorm f1 1 mu + |a2| * lpNorm f2 1 mu +
          |a3| * lpNorm f3 1 mu + |a4| * lpNorm f4 1 mu +
            |a5| * lpNorm f5 1 mu := by
      simp only [lpNorm_const_smul, coe_nnnorm, Real.norm_eq_abs]
    _ ≤ (100 / x ^ 5) * (optimizedRawTraceOneCubeConstant * x ^ 6) +
          (600 / x ^ 3) * (optimizedRawTraceOneSquareConstant * x ^ 4) +
          (600 / x ^ 4) * (optimizedRawTraceOneTwoConstant * x ^ 5) +
          (1000 / x ^ 2) * (optimizedRawTraceTwoL1Constant * x ^ 3) +
          (400 / x) * (optimizedRawTraceOneL3Constant * x ^ 2) := by
      have hx0 : 0 ≤ x := zero_le_one.trans hx
      exact add_le_add
        (add_le_add
          (add_le_add
            (add_le_add
              (mul_le_mul ha1 hf1Norm lpNorm_nonneg (by positivity))
              (mul_le_mul ha2 hf2Norm lpNorm_nonneg (by positivity)))
            (mul_le_mul ha3 hf3Norm lpNorm_nonneg (by positivity)))
          (mul_le_mul ha4 hf4Norm lpNorm_nonneg (by positivity)))
        (mul_le_mul ha5 hf5Norm lpNorm_nonneg (by positivity))
    _ = optimizedRawTraceThreeRemainderConstant * x := by
      have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
      unfold optimizedRawTraceThreeRemainderConstant
      field_simp [ne_of_gt hxpos]

/-- Transport the optimized beta-prime remainder package to the concrete
scaled-COE matrix law. -/
theorem concreteAveragedCenteredCubicTraceThreeRemainder_memLp_one_optimized
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    MemLp (concreteAveragedCenteredCubicTraceThreeRemainder N K) 1
      (concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K) := by
  have hpull := memLp_comp_concreteCOETracePowerVector hN (by omega)
    (betaPrimeAveragedCenteredCubicTraceThreeRemainder_memLp_one_optimized
      hN hdense)
  rw [betaPrimeAveragedCenteredCubicTraceThreeRemainder_comp_traceVector]
    at hpull
  exact hpull

theorem concreteAveragedCenteredCubicTraceThreeRemainder_lpNorm_one_le_optimized
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (concreteAveragedCenteredCubicTraceThreeRemainder N K) 1
        (concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K) ≤
      optimizedRawTraceThreeRemainderConstant * (N : ℝ) := by
  have hmem :=
    betaPrimeAveragedCenteredCubicTraceThreeRemainder_memLp_one_optimized
      hN hdense
  have hpull := lpNorm_comp_concreteCOETracePowerVector hN (by omega)
    (p := (1 : ENNReal)) hmem.aestronglyMeasurable
  rw [betaPrimeAveragedCenteredCubicTraceThreeRemainder_comp_traceVector]
    at hpull
  rw [hpull]
  exact
    betaPrimeAveragedCenteredCubicTraceThreeRemainder_lpNorm_one_le_optimized
      hN hdense

/-- Optimized raw-third-trace constant supplied by normalization and
positivity. -/
def optimizedRawTraceThreeConstant : ℝ :=
  3 * optimizedRawTraceThreeRemainderConstant / 4

theorem optimizedRawTraceThreeConstant_eq :
    optimizedRawTraceThreeConstant = 58817367280800 := by
  rw [optimizedRawTraceThreeConstant,
    optimizedRawTraceThreeRemainderConstant_eq]
  norm_num

/-- Concrete raw `T3` package obtained from the optimized remainder and the
existing total-mass/positivity reducer. -/
theorem concreteCOETraceThree_momentPackage_optimized
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (concreteCOETraceThree N K) 1
        (concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K) ∧
      (16 * N ≤ K →
        lpNorm (concreteCOETraceThree N K) 1
            (concreteScaledCOECornerLaw
              canonicalUnitaryHaarProbabilityFamily N K) ≤
          optimizedRawTraceThreeConstant * (N : ℝ) ^ 4) := by
  constructor
  · exact concreteCOETraceThree_memLp_one_internal hN hgap
  · intro hdense
    simpa only [optimizedRawTraceThreeConstant] using
      concreteCOETraceThree_lpNorm_one_le_of_remainder hN hdense
        (concreteAveragedCenteredCubicTraceThreeRemainder_memLp_one_optimized
          hN hdense)
        (concreteAveragedCenteredCubicTraceThreeRemainder_lpNorm_one_le_optimized
          hN hdense)

/-- Beta-prime raw `T3` package with the same optimized constant. -/
theorem betaPrimeYTraceThree_momentPackage_optimized
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (betaPrimeYTraceThree N K) 1 (betaPrimeTraceFourLaw N K) ∧
      (16 * N ≤ K →
        lpNorm (betaPrimeYTraceThree N K) 1
            (betaPrimeTraceFourLaw N K) ≤
          optimizedRawTraceThreeConstant * (N : ℝ) ^ 4) := by
  constructor
  · exact betaPrimeYTraceThree_memLp_one_positive_internal hN hgap
  · intro hdense
    have hconcrete :=
      (concreteCOETraceThree_momentPackage_optimized hN hgap).2 hdense
    have htransport := lpNorm_comp_concreteCOETracePowerVector hN (by omega)
      (p := (1 : ENNReal))
      (betaPrimeYTraceThree_memLp_one_positive_internal hN hgap).aestronglyMeasurable
    have hfun : betaPrimeYTraceThree N K ∘
        concreteCOETracePowerVector 4 N K = concreteCOETraceThree N K := by
      funext A
      change concreteBetaPrimeYTraceThree N K A = concreteCOETraceThree N K A
      exact concreteBetaPrimeYTraceThree_eq_concreteCOETraceThree N K A
    rw [hfun] at htransport
    rw [← htransport]
    exact hconcrete

/-- Optimized normalization constant for the averaged centered cubic
density: exactly `451R`. -/
def optimizedAveragedCenteredCubicNormalizationConstant : ℝ :=
  600 * optimizedRawTraceThreeConstant +
    optimizedRawTraceThreeRemainderConstant

theorem optimizedAveragedCenteredCubicNormalizationConstant_eq :
    optimizedAveragedCenteredCubicNormalizationConstant =
      35368843524854400 := by
  rw [optimizedAveragedCenteredCubicNormalizationConstant,
    optimizedRawTraceThreeConstant_eq,
    optimizedRawTraceThreeRemainderConstant_eq]
  norm_num

theorem concreteAveragedCenteredCubicDensity_memLp_one_optimized
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    MemLp (concreteAveragedCenteredCubicDensity N K) 1
      (concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K) := by
  let mu := concreteScaledCOECornerLaw
    canonicalUnitaryHaarProbabilityFamily N K
  let alpha := averagedCenteredCubicTraceThreeCoefficient (N : ℝ)
    (concreteCOEExponent N K)
  let tThree := concreteCOETraceThree N K
  let rem := concreteAveragedCenteredCubicTraceThreeRemainder N K
  have ht : MemLp tThree 1 mu := by
    simpa only [tThree, mu] using
      (concreteCOETraceThree_momentPackage_optimized hN (by omega)).1
  have hr : MemLp rem 1 mu := by
    simpa only [rem, mu] using
      concreteAveragedCenteredCubicTraceThreeRemainder_memLp_one_optimized
        hN hdense
  have heq : concreteAveragedCenteredCubicDensity N K =
      alpha • tThree + rem := by
    funext A
    simp only [alpha, tThree, rem, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact concreteAveragedCenteredCubicDensity_extract_traceThree hN hdense A
  rw [heq]
  exact (ht.const_smul alpha).add hr

theorem concreteAveragedCenteredCubicDensity_lpNorm_one_le_optimized
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (concreteAveragedCenteredCubicDensity N K) 1
        (concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K) ≤
      optimizedAveragedCenteredCubicNormalizationConstant * (N : ℝ) := by
  let mu := concreteScaledCOECornerLaw
    canonicalUnitaryHaarProbabilityFamily N K
  let x : ℝ := N
  let alpha := averagedCenteredCubicTraceThreeCoefficient x
    (concreteCOEExponent N K)
  let tThree := concreteCOETraceThree N K
  let rem := concreteAveragedCenteredCubicTraceThreeRemainder N K
  have hx : 1 ≤ x := by
    change (1 : ℝ) ≤ (N : ℝ)
    exact_mod_cast hN
  have ht : MemLp tThree 1 mu := by
    simpa only [tThree, mu] using
      (concreteCOETraceThree_momentPackage_optimized hN (by omega)).1
  have hr : MemLp rem 1 mu := by
    simpa only [rem, mu] using
      concreteAveragedCenteredCubicTraceThreeRemainder_memLp_one_optimized
        hN hdense
  have htNorm : lpNorm tThree 1 mu ≤
      optimizedRawTraceThreeConstant * x ^ 4 := by
    simpa only [tThree, mu, x] using
      (concreteCOETraceThree_momentPackage_optimized hN (by omega)).2 hdense
  have hrNorm : lpNorm rem 1 mu ≤
      optimizedRawTraceThreeRemainderConstant * x := by
    simpa only [rem, mu, x] using
      concreteAveragedCenteredCubicTraceThreeRemainder_lpNorm_one_le_optimized
        hN hdense
  have halpha : |alpha| ≤ 600 / x ^ 3 := by
    simpa only [alpha, x] using
      concreteAveragedCenteredCubicTraceThreeCoefficient_abs_le hN hdense
  have heq : concreteAveragedCenteredCubicDensity N K =
      alpha • tThree + rem := by
    funext A
    simp only [alpha, tThree, rem, x, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact concreteAveragedCenteredCubicDensity_extract_traceThree hN hdense A
  rw [heq]
  calc
    lpNorm (alpha • tThree + rem) 1 mu ≤
        lpNorm (alpha • tThree) 1 mu + lpNorm rem 1 mu :=
      lpNorm_add_le (ht.const_smul alpha) (p := (1 : ENNReal)) (by norm_num)
    _ = |alpha| * lpNorm tThree 1 mu + lpNorm rem 1 mu := by
      rw [lpNorm_const_smul]
      simp only [coe_nnnorm, Real.norm_eq_abs]
    _ ≤ (600 / x ^ 3) *
          (optimizedRawTraceThreeConstant * x ^ 4) +
        optimizedRawTraceThreeRemainderConstant * x := by
      exact add_le_add
        (mul_le_mul halpha htNorm lpNorm_nonneg (by positivity)) hrNorm
    _ = optimizedAveragedCenteredCubicNormalizationConstant * x := by
      have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
      unfold optimizedAveragedCenteredCubicNormalizationConstant
      field_simp [ne_of_gt hxpos]

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore

namespace LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.UltimateHiding.DenseScore
open LogdetLean.GramHafnian.CurrentPRL

/-- Event-path third derivative at the origin with the optimized cubic
normalization constant. -/
theorem abs_iteratedDeriv_three_concreteSharedBetaOrbitalEventPath_zero_le_optimized
    {m N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K)
    (q : ℝ) (event : Set (ConcreteMatrixState N))
    (hevent : MeasurableSet event) :
    |iteratedDeriv 3
        (concreteSharedBetaOrbitalEventPath m N
          (concreteScaledCOECornerLaw
            canonicalUnitaryHaarProbabilityFamily N K)
          q event) 0| ≤
      optimizedAveragedCenteredCubicNormalizationConstant * (N : ℝ) := by
  let mu := concreteScaledCOECornerLaw
    canonicalUnitaryHaarProbabilityFamily N K
  let preevent := concreteCentralMatrixUpdate N
    (oneColumnCenteredScalarLog m N q) ⁻¹' event
  have hpre : MeasurableSet preevent :=
    (measurable_concreteCentralMatrixUpdate N _) hevent
  have hfun : concreteSharedBetaOrbitalEventPath m N mu q event =
      concreteProjectiveAveragedCenteredCOEEventPath N K preevent := by
    funext t
    exact concreteSharedBetaOrbitalEventPath_eq_projectiveCenteredCOE
      hN (by omega) q event hevent t
  rw [hfun,
    coeCorner_centeredProjective_eventPath_derivative_literal_three_internal
      hN (by omega) preevent hpre]
  have hclosed : (fun A ↦ preevent.indicator (fun A ↦
        ∫ v : ComplexUnitSphere N,
          concreteCenteredDensityScore 3 N K v A
            ∂(complexUnitSphereProbabilityMeasure N)) A) =ᵐ[mu]
      preevent.indicator (concreteAveragedCenteredCubicDensity N K) := by
    filter_upwards
      [friedmanMello1985_scaledCOECorner_ae_support_from_density hN (by omega)]
        with A hA
    rcases hA with ⟨hsymm, hsupport⟩
    by_cases hmem : A ∈ preevent
    · simp only [Set.indicator, hmem, if_true]
      exact integral_concreteCenteredDensityScoreThree_eq_density_of_H7Exact
        hN hdense A hsymm hsupport
    · simp only [Set.indicator, hmem, if_false]
  rw [integral_congr_ae hclosed]
  exact (abs_integral_indicator_le_lpNorm_one
      (concreteAveragedCenteredCubicDensity_memLp_one_optimized hN hdense)
      hpre).trans
    (concreteAveragedCenteredCubicDensity_lpNorm_one_le_optimized hN hdense)

end

end LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep
