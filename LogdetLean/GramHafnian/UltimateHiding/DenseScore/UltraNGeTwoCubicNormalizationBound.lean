import LogdetLean.GramHafnian.UltimateHiding.DenseScore.UltraNGeTwoRawMomentBounds
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.UltraDenseCubicCoefficientBounds
import Mathlib.Tactic

/-!
# Dimension-split ultra cubic normalization bound

The centered orbital direction is zero when `N = 1`.  For `N >= 2`, the
ultra coefficient ledger `36, 26, 52, 24, 8` combines with the rational
raw moment bounds `1147/475`, `7439/793`, `533/108`, and `3/2`.  The resulting
lower-trace remainder is `115724477938672/58837359375`.  Total-mass normalization
and positivity cost exactly a factor two; rounding the final rational once
gives the all-dimensional cubic density and origin-event constant `3934`.
-/

open MeasureTheory Set

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.LocalAnticoncentration

def ultraNGeTwoRawTraceThreeRemainderConstant : ℝ :=
  36 * ultraNGeTwoRawTraceOneCubeConstant +
    26 * ultraNGeTwoRawTraceOneSquareConstant +
    52 * ultraNGeTwoRawTraceOneTwoConstant +
    24 * ultraNGeTwoRawTraceTwoL1Constant +
    8 * ultraNGeTwoRawTraceOneL1Constant

theorem ultraNGeTwoRawTraceThreeRemainderConstant_eq :
    ultraNGeTwoRawTraceThreeRemainderConstant =
      115724477938672 / 58837359375 := by
  norm_num [ultraNGeTwoRawTraceThreeRemainderConstant,
    ultraNGeTwoRawTraceOneCubeConstant,
    ultraNGeTwoRawTraceOneSquareConstant,
    ultraNGeTwoRawTraceOneTwoConstant,
    ultraNGeTwoRawTraceOneL4Constant,
    ultraNGeTwoRawTraceTwoL2Constant,
    ultraNGeTwoRawTraceTwoL1Constant,
    ultraNGeTwoRawTraceOneL1Constant]

/-- The exact five-monomial remainder bound in dimensions at least two. -/
theorem betaPrimeAveragedCenteredCubicTraceThreeRemainder_lpNorm_one_le_ultraNGeTwo
    {N K : ℕ} (hN : 2 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (betaPrimeAveragedCenteredCubicTraceThreeRemainder N K) 1
        (betaPrimeTraceFourLaw N K) ≤
      ultraNGeTwoRawTraceThreeRemainderConstant * (N : ℝ) := by
  have hgap : 2 * N + 8 ≤ K := by omega
  let mu := betaPrimeTraceFourLaw N K
  letI : IsProbabilityMeasure mu := betaPrimeTraceFourLaw_isProbability N K
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
    exact_mod_cast (show 1 ≤ N by omega)
  have hc13 : 13 * x ≤ c := by
    simpa only [x, c] using
      U08.thirteen_mul_dimension_le_concreteCOEExponent_of_dense
        (show 1 ≤ N by omega) hdense
  have hf1 : MemLp f1 1 mu := by
    simpa only [f1, mu] using
      (betaPrimeYTraceOneCube_momentPackage_ultraNGeTwo hN hgap).1
  have hf2 : MemLp f2 1 mu := by
    simpa only [f2, mu] using
      (betaPrimeYTraceOneSquare_momentPackage_ultraNGeTwo hN hgap).1
  have hf3 : MemLp f3 1 mu := by
    simpa only [f3, mu] using
      (betaPrimeYTraceOneTwo_momentPackage_ultraNGeTwo hN hgap).1
  have hf4 : MemLp f4 1 mu := by
    have htwo := (betaPrimeYTraceTwo_two_momentPackage_ultraNGeTwo hN hgap).1
    simpa only [f4, mu] using htwo.mono_exponent (by norm_num)
  have hf5 : MemLp f5 1 mu := by
    have hfour := (betaPrimeYTraceOne_four_momentPackage_ultraNGeTwo hN hgap).1
    simpa only [f5, mu] using hfour.mono_exponent (by norm_num)
  have hf1Norm : lpNorm f1 1 mu ≤
      ultraNGeTwoRawTraceOneCubeConstant * x ^ 6 := by
    simpa only [f1, mu, x] using
      (betaPrimeYTraceOneCube_momentPackage_ultraNGeTwo hN hgap).2 hdense
  have hf2Norm : lpNorm f2 1 mu ≤
      ultraNGeTwoRawTraceOneSquareConstant * x ^ 4 := by
    simpa only [f2, mu, x] using
      (betaPrimeYTraceOneSquare_momentPackage_ultraNGeTwo hN hgap).2 hdense
  have hf3Norm : lpNorm f3 1 mu ≤
      ultraNGeTwoRawTraceOneTwoConstant * x ^ 5 := by
    simpa only [f3, mu, x] using
      (betaPrimeYTraceOneTwo_momentPackage_ultraNGeTwo hN hgap).2 hdense
  have hf4Norm : lpNorm f4 1 mu ≤
      ultraNGeTwoRawTraceTwoL1Constant * x ^ 3 := by
    simpa only [f4, mu, x] using
      betaPrimeYTraceTwo_lpNorm_one_le_ultraNGeTwo hN hdense
  have hf5Norm : lpNorm f5 1 mu ≤
      ultraNGeTwoRawTraceOneL1Constant * x ^ 2 := by
    simpa only [f5, mu, x] using
      betaPrimeYTraceOne_lpNorm_one_le_ultraNGeTwo hN hdense
  have ha1 : |a1| ≤ 36 / x ^ 5 := by
    simpa only [a1] using cubicTraceThreeRemainderCoeffCube_abs_le_ultra hx hc13
  have ha2 : |a2| ≤ 26 / x ^ 3 := by
    simpa only [a2] using cubicTraceThreeRemainderCoeffSquare_abs_le_ultra hx hc13
  have ha3 : |a3| ≤ 52 / x ^ 4 := by
    simpa only [a3] using cubicTraceThreeRemainderCoeffMixed_abs_le_ultra hx hc13
  have ha4 : |a4| ≤ 24 / x ^ 2 := by
    simpa only [a4] using cubicTraceThreeRemainderCoeffTwo_abs_le_ultra hx hc13
  have ha5 : |a5| ≤ 8 / x := by
    simpa only [a5] using cubicTraceThreeRemainderCoeffOne_abs_le_ultra hx hc13
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
    (show 1 ≤ N by omega) hdense]
  change lpNorm (a1 • f1 + a2 • f2 + a3 • f3 + a4 • f4 + a5 • f5) 1 mu ≤ _
  calc
    _ ≤ lpNorm (a1 • f1) 1 mu + lpNorm (a2 • f2) 1 mu +
          lpNorm (a3 • f3) 1 mu + lpNorm (a4 • f4) 1 mu +
            lpNorm (a5 • f5) 1 mu := htri
    _ = |a1| * lpNorm f1 1 mu + |a2| * lpNorm f2 1 mu +
          |a3| * lpNorm f3 1 mu + |a4| * lpNorm f4 1 mu +
            |a5| * lpNorm f5 1 mu := by
      simp only [lpNorm_const_smul, coe_nnnorm, Real.norm_eq_abs]
    _ ≤ (36 / x ^ 5) * (ultraNGeTwoRawTraceOneCubeConstant * x ^ 6) +
          (26 / x ^ 3) * (ultraNGeTwoRawTraceOneSquareConstant * x ^ 4) +
          (52 / x ^ 4) * (ultraNGeTwoRawTraceOneTwoConstant * x ^ 5) +
          (24 / x ^ 2) * (ultraNGeTwoRawTraceTwoL1Constant * x ^ 3) +
          (8 / x) * (ultraNGeTwoRawTraceOneL1Constant * x ^ 2) := by
      exact add_le_add
        (add_le_add
          (add_le_add
            (add_le_add
              (mul_le_mul ha1 hf1Norm lpNorm_nonneg (by positivity))
              (mul_le_mul ha2 hf2Norm lpNorm_nonneg (by positivity)))
            (mul_le_mul ha3 hf3Norm lpNorm_nonneg (by positivity)))
          (mul_le_mul ha4 hf4Norm lpNorm_nonneg (by positivity)))
        (mul_le_mul ha5 hf5Norm lpNorm_nonneg (by positivity))
    _ = ultraNGeTwoRawTraceThreeRemainderConstant * x := by
      have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
      unfold ultraNGeTwoRawTraceThreeRemainderConstant
      field_simp [ne_of_gt hxpos]

theorem concreteAveragedCenteredCubicTraceThreeRemainder_lpNorm_one_le_ultraNGeTwo
    {N K : ℕ} (hN : 2 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (concreteAveragedCenteredCubicTraceThreeRemainder N K) 1
        (concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K) ≤
      ultraNGeTwoRawTraceThreeRemainderConstant * (N : ℝ) := by
  have hmem :=
    betaPrimeAveragedCenteredCubicTraceThreeRemainder_memLp_one_optimized
      (show 1 ≤ N by omega) hdense
  have hpull := lpNorm_comp_concreteCOETracePowerVector
    (show 1 ≤ N by omega) (by omega)
    (p := (1 : ENNReal)) hmem.aestronglyMeasurable
  rw [betaPrimeAveragedCenteredCubicTraceThreeRemainder_comp_traceVector]
    at hpull
  rw [hpull]
  exact betaPrimeAveragedCenteredCubicTraceThreeRemainder_lpNorm_one_le_ultraNGeTwo
    hN hdense

def ultraNGeTwoAveragedCenteredCubicNormalizationConstant : ℝ :=
  3934

theorem ultraNGeTwoAveragedCenteredCubicNormalizationConstant_eq :
    ultraNGeTwoAveragedCenteredCubicNormalizationConstant = 3934 := rfl

theorem two_mul_ultraNGeTwoRawTraceThreeRemainderConstant_le :
    2 * ultraNGeTwoRawTraceThreeRemainderConstant ≤
      ultraNGeTwoAveragedCenteredCubicNormalizationConstant := by
  norm_num [ultraNGeTwoRawTraceThreeRemainderConstant,
    ultraNGeTwoAveragedCenteredCubicNormalizationConstant,
    ultraNGeTwoRawTraceOneCubeConstant,
    ultraNGeTwoRawTraceOneSquareConstant,
    ultraNGeTwoRawTraceOneTwoConstant,
    ultraNGeTwoRawTraceOneL4Constant,
    ultraNGeTwoRawTraceTwoL2Constant,
    ultraNGeTwoRawTraceTwoL1Constant,
    ultraNGeTwoRawTraceOneL1Constant]

/-- Ratio-free normalization in dimensions at least two. -/
private theorem concreteAveragedCenteredCubicDensity_lpNorm_one_le_ultraNGeTwo_of_two_le
    {N K : ℕ} (hN : 2 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (concreteAveragedCenteredCubicDensity N K) 1
        (concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K) ≤
      ultraNGeTwoAveragedCenteredCubicNormalizationConstant * (N : ℝ) := by
  have hNOne : 1 ≤ N := by omega
  have hgap : 2 * N + 8 ≤ K := by omega
  let mu := concreteScaledCOECornerLaw
    canonicalUnitaryHaarProbabilityFamily N K
  let x : ℝ := N
  let alpha := averagedCenteredCubicTraceThreeCoefficient x
    (concreteCOEExponent N K)
  let tThree := concreteCOETraceThree N K
  let rem := concreteAveragedCenteredCubicTraceThreeRemainder N K
  let closed := concreteAveragedCenteredCubicDensity N K
  have ht : MemLp tThree 1 mu := by
    simpa only [tThree, mu] using
      concreteCOETraceThree_memLp_one_internal hNOne hgap
  have hr : MemLp rem 1 mu := by
    simpa only [rem, mu] using
      concreteAveragedCenteredCubicTraceThreeRemainder_memLp_one_optimized
        hNOne hdense
  have hrNorm : lpNorm rem 1 mu ≤
      ultraNGeTwoRawTraceThreeRemainderConstant * x := by
    simpa only [rem, mu, x] using
      concreteAveragedCenteredCubicTraceThreeRemainder_lpNorm_one_le_ultraNGeTwo
        hN hdense
  have htNonneg : ∀ᵐ A ∂mu, 0 ≤ tThree A := by
    filter_upwards
      [friedmanMello1985_scaledCOECorner_ae_support_from_density hNOne (by omega)]
        with A hA
    exact concreteCOETraceThree_nonneg_of_support hgap A hA.2
  have halphaNonneg : 0 ≤ alpha := by
    have hlower : 4 / (3 * (N : ℝ) ^ 3) ≤ alpha := by
      simpa only [alpha, x] using
        concreteAveragedCenteredCubicTraceThreeCoefficient_lower_bound
          hNOne hdense
    exact (by positivity : (0 : ℝ) ≤ 4 / (3 * (N : ℝ) ^ 3)).trans
      hlower
  have htInt : Integrable tThree mu := memLp_one_iff_integrable.mp ht
  have hrInt : Integrable rem mu := memLp_one_iff_integrable.mp hr
  have heq : closed = alpha • tThree + rem := by
    funext A
    simp only [closed, alpha, tThree, rem, x, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    exact concreteAveragedCenteredCubicDensity_extract_traceThree hNOne hdense A
  have hzero := integral_concreteAveragedCenteredCubicDensity_eq_zero_internal
    hNOne hdense
  have hbalance : alpha * (∫ A, tThree A ∂mu) + ∫ A, rem A ∂mu = 0 := by
    change (∫ A, closed A ∂mu) = 0 at hzero
    rw [heq] at hzero
    change (∫ A, alpha * tThree A + rem A ∂mu) = 0 at hzero
    rw [integral_add (htInt.const_mul alpha) hrInt,
      integral_const_mul] at hzero
    exact hzero
  have hremIntegralAbs : |∫ A, rem A ∂mu| ≤ lpNorm rem 1 mu := by
    calc
      |∫ A, rem A ∂mu| ≤ ∫ A, |rem A| ∂mu :=
        abs_integral_le_integral_abs
      _ = lpNorm rem 1 mu := by
        rw [lpNorm_one_eq_integral_norm hr.aestronglyMeasurable]
        rfl
  have hrawNorm : lpNorm (alpha • tThree) 1 mu =
      alpha * (∫ A, tThree A ∂mu) := by
    rw [lpNorm_one_eq_integral_norm
      (ht.const_smul alpha).aestronglyMeasurable]
    calc
      (∫ A, ‖(alpha • tThree) A‖ ∂mu) =
          ∫ A, alpha * tThree A ∂mu := by
        apply integral_congr_ae
        filter_upwards [htNonneg] with A hA
        simp only [Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs]
        rw [abs_of_nonneg (mul_nonneg halphaNonneg hA)]
      _ = alpha * (∫ A, tThree A ∂mu) := by
        rw [integral_const_mul]
  have hrawNormLe : lpNorm (alpha • tThree) 1 mu ≤
      ultraNGeTwoRawTraceThreeRemainderConstant * x := by
    calc
      lpNorm (alpha • tThree) 1 mu =
          alpha * (∫ A, tThree A ∂mu) := hrawNorm
      _ = -(∫ A, rem A ∂mu) := by linarith
      _ ≤ |∫ A, rem A ∂mu| := neg_le_abs _
      _ ≤ lpNorm rem 1 mu := hremIntegralAbs
      _ ≤ ultraNGeTwoRawTraceThreeRemainderConstant * x := hrNorm
  change lpNorm closed 1 mu ≤ _
  rw [heq]
  calc
    lpNorm (alpha • tThree + rem) 1 mu ≤
        lpNorm (alpha • tThree) 1 mu + lpNorm rem 1 mu :=
      lpNorm_add_le (ht.const_smul alpha) (p := (1 : ENNReal)) (by norm_num)
    _ ≤ ultraNGeTwoRawTraceThreeRemainderConstant * x +
        ultraNGeTwoRawTraceThreeRemainderConstant * x :=
      add_le_add hrawNormLe hrNorm
    _ = (2 * ultraNGeTwoRawTraceThreeRemainderConstant) * x := by ring
    _ ≤ ultraNGeTwoAveragedCenteredCubicNormalizationConstant * x :=
      mul_le_mul_of_nonneg_right
        two_mul_ultraNGeTwoRawTraceThreeRemainderConstant_le (by positivity)

/-- All-dimensional density bound: the `N=1` branch is exactly zero and the
`N>=2` branch has constant `3934`. -/
theorem concreteAveragedCenteredCubicDensity_lpNorm_one_le_ultraNGeTwo
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (concreteAveragedCenteredCubicDensity N K) 1
        (concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K) ≤
      ultraNGeTwoAveragedCenteredCubicNormalizationConstant * (N : ℝ) := by
  rcases hN.eq_or_lt with hNone | hNlt
  · subst N
    let mu := concreteScaledCOECornerLaw
      canonicalUnitaryHaarProbabilityFamily 1 K
    have hzero : concreteAveragedCenteredCubicDensity 1 K =ᵐ[mu]
        (0 : ConcreteMatrixState 1 → ℝ) := by
      filter_upwards
        [friedmanMello1985_scaledCOECorner_ae_support_from_density
          (show 1 ≤ 1 by omega) (by omega)] with A hA
      have hid := integral_concreteCenteredDensityScoreThree_eq_density_of_H7Exact
        (show 1 ≤ 1 by omega) hdense A hA.1 hA.2
      rw [integral_concreteCenteredDensityScoreThree_fin_one_eq_zero] at hid
      exact hid.symm
    have hmem : MemLp (concreteAveragedCenteredCubicDensity 1 K) 1 mu := by
      simpa only [mu] using
        concreteAveragedCenteredCubicDensity_memLp_one_optimized
          (show 1 ≤ 1 by omega) hdense
    have hnorm : lpNorm (concreteAveragedCenteredCubicDensity 1 K) 1 mu = 0 :=
      (lpNorm_eq_zero hmem (by norm_num)).2 hzero
    change lpNorm (concreteAveragedCenteredCubicDensity 1 K) 1 mu ≤ _
    rw [hnorm]
    norm_num [ultraNGeTwoAveragedCenteredCubicNormalizationConstant,
      ultraNGeTwoRawTraceThreeRemainderConstant,
      ultraNGeTwoRawTraceOneCubeConstant,
      ultraNGeTwoRawTraceOneSquareConstant,
      ultraNGeTwoRawTraceOneTwoConstant,
      ultraNGeTwoRawTraceOneL4Constant,
      ultraNGeTwoRawTraceTwoL2Constant,
      ultraNGeTwoRawTraceTwoL1Constant,
      ultraNGeTwoRawTraceOneL1Constant]
  · exact concreteAveragedCenteredCubicDensity_lpNorm_one_le_ultraNGeTwo_of_two_le
      (by omega) hdense

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore

namespace LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.UltimateHiding.DenseScore
open LogdetLean.GramHafnian.LocalAnticoncentration

/-- Event-path third derivative at the origin with the all-dimensional
dimension-split constant `3934`. -/
theorem abs_iteratedDeriv_three_concreteSharedBetaOrbitalEventPath_zero_le_ultraNGeTwo
    {m N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K)
    (q : ℝ) (event : Set (ConcreteMatrixState N))
    (hevent : MeasurableSet event) :
    |iteratedDeriv 3
        (concreteSharedBetaOrbitalEventPath m N
          (concreteScaledCOECornerLaw
            canonicalUnitaryHaarProbabilityFamily N K)
          q event) 0| ≤
      ultraNGeTwoAveragedCenteredCubicNormalizationConstant * (N : ℝ) := by
  rcases hN.eq_or_lt with hNone | hNlt
  · subst N
    let mu := concreteScaledCOECornerLaw
      canonicalUnitaryHaarProbabilityFamily 1 K
    let preevent := concreteCentralMatrixUpdate 1
      (oneColumnCenteredScalarLog m 1 q) ⁻¹' event
    have hpre : MeasurableSet preevent :=
      (measurable_concreteCentralMatrixUpdate 1 _) hevent
    have hfun : concreteSharedBetaOrbitalEventPath m 1 mu q event =
        concreteProjectiveAveragedCenteredCOEEventPath 1 K preevent := by
      funext t
      exact concreteSharedBetaOrbitalEventPath_eq_projectiveCenteredCOE
        (show 1 ≤ 1 by omega) (by omega) q event hevent t
    rw [hfun,
      coeCorner_centeredProjective_eventPath_derivative_literal_three_internal
        (show 1 ≤ 1 by omega) (by omega) preevent hpre]
    have hpoint : (fun A : ConcreteMatrixState 1 ↦
        preevent.indicator (fun A ↦
          ∫ v : ComplexUnitSphere 1,
            concreteCenteredDensityScore 3 1 K v A
              ∂(complexUnitSphereProbabilityMeasure 1)) A) = 0 := by
      funext A
      simp only [Pi.zero_apply]
      by_cases hmem : A ∈ preevent
      · simp only [Set.indicator, hmem, if_true]
        exact integral_concreteCenteredDensityScoreThree_fin_one_eq_zero A
      · simp only [Set.indicator, hmem, if_false]
    rw [hpoint]
    change |(∫ _A : ConcreteMatrixState 1, (0 : ℝ) ∂mu)| ≤ _
    rw [integral_zero, abs_zero]
    norm_num [ultraNGeTwoAveragedCenteredCubicNormalizationConstant,
      ultraNGeTwoRawTraceThreeRemainderConstant,
      ultraNGeTwoRawTraceOneCubeConstant,
      ultraNGeTwoRawTraceOneSquareConstant,
      ultraNGeTwoRawTraceOneTwoConstant,
      ultraNGeTwoRawTraceOneL4Constant,
      ultraNGeTwoRawTraceTwoL2Constant,
      ultraNGeTwoRawTraceTwoL1Constant,
      ultraNGeTwoRawTraceOneL1Constant]
  · have hNtwo : 2 ≤ N := by omega
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
      (concreteAveragedCenteredCubicDensity_lpNorm_one_le_ultraNGeTwo
        hN hdense)

end

end LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep
