import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H9_Proof

/-!
# H9 conditional transfer through the exact H6 trace-vector law

`betaPrimeYTraceOne_centered_three_momentPackage_of_sourceL4` is a theorem on
the literal Gaussian beta-prime source.  This file transfers it to the
concrete scaled COE-corner law.  The full, exact H6 proposition is an explicit
theorem parameter; this module does not call the project's external H6
declaration.

Status: **CONDITIONAL** on exact H6 and on the two source-level `L^4`
packages displayed in the theorem signature.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/--
**CONDITIONAL exact H9.**  Two primitive source-level `L^4` packages imply
the exact original H9 proposition.  The first function is the conditional
numerator fluctuation; the second depends only on the denominator Wishart
matrix.  Thus neither parameter is equivalent to the assigned conclusion.
-/
theorem betaPrimeYTraceOne_centered_three_momentPackage_of_sourceL4
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (hNumeratorMemLp :
      MemLp (h9SourceNumeratorFluctuation N K) 4
        (realBetaPrimeGaussianSourceLaw N K))
    (hDenominatorMemLp :
      MemLp (h9SourceDenominatorFluctuation N K) 4
        (realBetaPrimeGaussianSourceLaw N K))
    (hNumeratorDense : 16 * N ≤ K →
      lpNorm (h9SourceNumeratorFluctuation N K) 4
          (realBetaPrimeGaussianSourceLaw N K) ≤
        denseClassicalMomentConstant / 2 * (N : ℝ))
    (hDenominatorDense : 16 * N ≤ K →
      lpNorm (h9SourceDenominatorFluctuation N K) 4
          (realBetaPrimeGaussianSourceLaw N K) ≤
        denseClassicalMomentConstant / 2 * (N : ℝ)) :
    MemLp (fun u ↦ betaPrimeYTraceOne N K u -
      ∫ z, betaPrimeYTraceOne N K z ∂(betaPrimeTraceFourLaw N K)) 3
        (betaPrimeTraceFourLaw N K) ∧
      (16 * N ≤ K →
        lpNorm (fun u ↦ betaPrimeYTraceOne N K u -
          ∫ z, betaPrimeYTraceOne N K z ∂(betaPrimeTraceFourLaw N K)) 3
            (betaPrimeTraceFourLaw N K) ≤
          denseClassicalMomentConstant * (N : ℝ)) := by
  let μ := realBetaPrimeGaussianSourceLaw N K
  let g := h9BetaPrimeTraceOneFixedCenter N K
  let f := realBetaPrimeTracePowerVector 4 N K
  have hsourceFour : MemLp
      (h9SourceNumeratorFluctuation N K +
        h9SourceDenominatorFluctuation N K) 4 μ := by
    exact hNumeratorMemLp.add hDenominatorMemLp
  have hdecomp : g ∘ f =
      h9SourceNumeratorFluctuation N K +
        h9SourceDenominatorFluctuation N K := by
    simpa only [g, f] using h9BetaPrimeTraceOneFixedCenter_comp_source N K
  have hgMeas : AEStronglyMeasurable g (betaPrimeTraceFourLaw N K) := by
    simpa [g] using
      (measurable_h9BetaPrimeTraceOneFixedCenter N K).aestronglyMeasurable
  have hfMeas : AEMeasurable f μ := by
    exact (measurable_realBetaPrimeTracePowerVector_external 4 N K).aemeasurable
  have hfixedFour : MemLp g 4 (betaPrimeTraceFourLaw N K) := by
    unfold betaPrimeTraceFourLaw
    refine (memLp_map_measure_iff ?_ hfMeas).2 ?_
    · exact hgMeas
    · rw [hdecomp]
      exact hsourceFour
  letI : IsProbabilityMeasure (betaPrimeTraceFourLaw N K) :=
    betaPrimeTraceFourLaw_isProbability N K
  have hfixedThree : MemLp g 3 (betaPrimeTraceFourLaw N K) :=
    hfixedFour.mono_exponent (by norm_num)
  have hmean :
      (∫ u, betaPrimeYTraceOne N K u ∂(betaPrimeTraceFourLaw N K)) =
        (N : ℝ) * ((N : ℝ) + 1) :=
    betaPrimeYTraceOne_integral_external hN (by omega)
  have hcenter :
      (fun u ↦ betaPrimeYTraceOne N K u -
        ∫ z, betaPrimeYTraceOne N K z ∂(betaPrimeTraceFourLaw N K)) =
        h9BetaPrimeTraceOneFixedCenter N K := by
    funext u
    rw [hmean]
    rfl
  constructor
  · rw [hcenter]
    simpa [g] using hfixedThree
  · intro hdense
    have hfourTriangle :
        lpNorm (h9SourceNumeratorFluctuation N K +
            h9SourceDenominatorFluctuation N K) 4 μ ≤
          lpNorm (h9SourceNumeratorFluctuation N K) 4 μ +
            lpNorm (h9SourceDenominatorFluctuation N K) 4 μ :=
      lpNorm_add_le hNumeratorMemLp (by norm_num)
    have hfourBudget :
        lpNorm (h9SourceNumeratorFluctuation N K +
            h9SourceDenominatorFluctuation N K) 4 μ ≤
          denseClassicalMomentConstant * (N : ℝ) := by
      calc
        _ ≤ lpNorm (h9SourceNumeratorFluctuation N K) 4 μ +
              lpNorm (h9SourceDenominatorFluctuation N K) 4 μ :=
            hfourTriangle
        _ ≤ denseClassicalMomentConstant / 2 * (N : ℝ) +
              denseClassicalMomentConstant / 2 * (N : ℝ) :=
            add_le_add (hNumeratorDense hdense) (hDenominatorDense hdense)
        _ = denseClassicalMomentConstant * (N : ℝ) := by ring
    have hmapNorm : lpNorm g 4 (betaPrimeTraceFourLaw N K) =
        lpNorm (h9SourceNumeratorFluctuation N K +
          h9SourceDenominatorFluctuation N K) 4 μ := by
      rw [← hdecomp]
      exact h9_lpNorm_source_map hgMeas
    have hfixedFourBound :
        lpNorm g 4 (betaPrimeTraceFourLaw N K) ≤
          denseClassicalMomentConstant * (N : ℝ) := by
      rw [hmapNorm]
      exact hfourBudget
    have hfixedThreeBound :
        lpNorm g 3 (betaPrimeTraceFourLaw N K) ≤
          denseClassicalMomentConstant * (N : ℝ) :=
      (h9_lpNorm_le_of_exponent_le hfixedFour (by norm_num)).trans
        hfixedFourBound
    rw [hcenter]
    simpa [g] using hfixedThreeBound

/-- Coordinate one after pulling the beta-prime trace observable back to the
concrete scaled COE corner. -/
def h9ConcreteTraceOne (N K : ℕ) (A : ConcreteMatrixState N) : ℝ :=
  betaPrimeYTraceOne N K (concreteCOETracePowerVector 4 N K A)

/-- The pulled-back coordinate is literally the concrete `Tr Y`. -/
@[simp] theorem h9ConcreteTraceOne_eq_concreteCOETraceOne
    (N K : ℕ) (A : ConcreteMatrixState N) :
    h9ConcreteTraceOne N K A = concreteCOETraceOne N K A := by
  unfold h9ConcreteTraceOne betaPrimeYTraceOne concreteCOETracePowerVector
    concreteCOETraceOne concreteCOEY concreteRealTrace
  simp [pow_succ, Complex.mul_re]

/--
**CONDITIONAL H6 transfer.**  The parameter `hH6` has exactly the quantifiers
and conclusion of H6 (`coeTakagiMuirhead_traceVector_betaPrime_external`).
No weakening to a moment statement, and no use of that external declaration,
occurs here.
-/
theorem concreteCOETraceOne_centered_three_momentPackage_of_H6_sourceL4
    (hH6 : ∀ {r N K : ℕ}, 1 ≤ N → 2 * N ≤ K →
      Measure.map (concreteCOETracePowerVector r N K)
          (concreteScaledCOECornerLaw
            canonicalUnitaryHaarProbabilityFamily N K) =
        Measure.map (realBetaPrimeTracePowerVector r N K)
          (realBetaPrimeGaussianSourceLaw N K))
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (hNumeratorMemLp :
      MemLp (h9SourceNumeratorFluctuation N K) 4
        (realBetaPrimeGaussianSourceLaw N K))
    (hDenominatorMemLp :
      MemLp (h9SourceDenominatorFluctuation N K) 4
        (realBetaPrimeGaussianSourceLaw N K))
    (hNumeratorDense : 16 * N ≤ K →
      lpNorm (h9SourceNumeratorFluctuation N K) 4
          (realBetaPrimeGaussianSourceLaw N K) ≤
        denseClassicalMomentConstant / 2 * (N : ℝ))
    (hDenominatorDense : 16 * N ≤ K →
      lpNorm (h9SourceDenominatorFluctuation N K) 4
          (realBetaPrimeGaussianSourceLaw N K) ≤
        denseClassicalMomentConstant / 2 * (N : ℝ)) :
    MemLp (fun A ↦ concreteCOETraceOne N K A -
      ∫ B, concreteCOETraceOne N K B
        ∂(concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K)) 3
        (concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K) ∧
      (16 * N ≤ K →
        lpNorm (fun A ↦ concreteCOETraceOne N K A -
          ∫ B, concreteCOETraceOne N K B
            ∂(concreteScaledCOECornerLaw
              canonicalUnitaryHaarProbabilityFamily N K)) 3
            (concreteScaledCOECornerLaw
              canonicalUnitaryHaarProbabilityFamily N K) ≤
          denseClassicalMomentConstant * (N : ℝ)) := by
  let μ := concreteScaledCOECornerLaw
    canonicalUnitaryHaarProbabilityFamily N K
  let f := concreteCOETracePowerVector 4 N K
  let g := fun u ↦ betaPrimeYTraceOne N K u -
    ∫ z, betaPrimeYTraceOne N K z ∂(betaPrimeTraceFourLaw N K)
  have hbeta :=
    betaPrimeYTraceOne_centered_three_momentPackage_of_sourceL4
      hN hgap hNumeratorMemLp hDenominatorMemLp
      hNumeratorDense hDenominatorDense
  have hmap : Measure.map f μ = betaPrimeTraceFourLaw N K := by
    simpa only [f, μ, betaPrimeTraceFourLaw] using
      (hH6 (r := 4) hN (by omega))
  have hfMeas : AEMeasurable f μ := by
    exact (measurable_concreteCOETracePowerVector_external 4 N K).aemeasurable
  have hgMeas : AEStronglyMeasurable g (betaPrimeTraceFourLaw N K) := by
    exact hbeta.1.aestronglyMeasurable
  have hgMapMeas : AEStronglyMeasurable g (Measure.map f μ) := by
    simpa only [hmap] using hgMeas
  have hcompMem : MemLp (g ∘ f) 3 μ := by
    apply MemLp.comp_of_map
    · simpa only [hmap] using hbeta.1
    · exact hfMeas
  have hrawMeas : AEStronglyMeasurable (betaPrimeYTraceOne N K)
      (betaPrimeTraceFourLaw N K) := by
    apply Measurable.aestronglyMeasurable
    unfold betaPrimeYTraceOne
    fun_prop
  have hrawMapMeas : AEStronglyMeasurable (betaPrimeYTraceOne N K)
      (Measure.map f μ) := by
    simpa only [hmap] using hrawMeas
  have hintegral :
      (∫ A, betaPrimeYTraceOne N K (f A) ∂μ) =
        ∫ u, betaPrimeYTraceOne N K u ∂(betaPrimeTraceFourLaw N K) := by
    simpa only [Function.comp_apply, hmap] using
      (integral_map hfMeas hrawMapMeas).symm
  have hrawComp : betaPrimeYTraceOne N K ∘ f =
      concreteCOETraceOne N K := by
    funext A
    exact h9ConcreteTraceOne_eq_concreteCOETraceOne N K A
  have hcoeIntegral :
      (∫ A, concreteCOETraceOne N K A ∂μ) =
        ∫ u, betaPrimeYTraceOne N K u ∂(betaPrimeTraceFourLaw N K) := by
    rw [← hrawComp]
    exact hintegral
  have hcenterComp : g ∘ f = fun A ↦ concreteCOETraceOne N K A -
      ∫ B, concreteCOETraceOne N K B ∂μ := by
    funext A
    simp only [Function.comp_apply, g]
    rw [hcoeIntegral]
    change h9ConcreteTraceOne N K A - _ = _
    rw [h9ConcreteTraceOne_eq_concreteCOETraceOne]
  have hnorm : lpNorm (g ∘ f) 3 μ =
      lpNorm g 3 (betaPrimeTraceFourLaw N K) := by
    rw [← toReal_eLpNorm (hgMapMeas.comp_aemeasurable hfMeas),
      ← toReal_eLpNorm hgMeas]
    have he := eLpNorm_map_measure (p := (3 : ENNReal)) hgMapMeas hfMeas
    rw [hmap] at he
    exact congrArg ENNReal.toReal he.symm
  constructor
  · rw [hcenterComp] at hcompMem
    exact hcompMem
  · intro hdense
    rw [hcenterComp] at hnorm
    rw [hnorm]
    exact hbeta.2 hdense

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
