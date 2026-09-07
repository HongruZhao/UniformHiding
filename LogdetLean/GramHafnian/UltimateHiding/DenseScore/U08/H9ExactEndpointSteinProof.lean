import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.H9ThirdTracePowerSteinProof
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H9_ExactCenteredTraceReduction
import Mathlib.Tactic

/-!
# Literal H9 endpoint from the proved third-entry Stein recursion

The direct fixed-denominator Gaussian Wick theorem supplies the numerator
package, while `H9ThirdTracePowerSteinProof` supplies the denominator package.
This closes the original H9 statement throughout its stated moment range;
the quantitative assertion remains conditional on the stated dense regime.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open U08

private theorem lpNorm_comp_measurePreserving_h9_endpoint
    {Alpha Beta E : Type*} [MeasurableSpace Alpha] [MeasurableSpace Beta]
    [NormedAddCommGroup E] {mu : Measure Alpha} {nu : Measure Beta}
    {p : ENNReal} {f : Alpha → Beta} {g : Beta → E}
    (hg : AEStronglyMeasurable g nu) (hf : MeasurePreserving f mu nu) :
    lpNorm (g ∘ f) p mu = lpNorm g p nu := by
  have hgf : AEStronglyMeasurable (g ∘ f) mu :=
    (hf.map_eq ▸ hg).comp_aemeasurable hf.aemeasurable
  have he := congrArg ENNReal.toReal
    (eLpNorm_comp_measurePreserving (p := p) hg hf)
  simpa only [toReal_eLpNorm hgf, toReal_eLpNorm hg] using he

/-- Product-marginal transport for the internally proved denominator
package.  This is the same deterministic scaling used by the exact H9
reduction, restated publicly here so the final closure has no conditional
module dependency. -/
theorem h9SourceDenominatorPackage_internal
    {N K : ℕ} (hN : 1 ≤ N)
    (hinv : H9InverseWishartDenominatorPackage N K) :
    MemLp (h9SourceDenominatorFluctuation N K) 4
        (realBetaPrimeGaussianSourceLaw N K) ∧
      (16 * N ≤ K →
        lpNorm (h9SourceDenominatorFluctuation N K) 4
            (realBetaPrimeGaussianSourceLaw N K) ≤
          8192 * (N : ℝ)) := by
  let muG := standardRealGaussianMatrixMeasure (N + 1) N
  let muB := standardRealGaussianMatrixMeasure (K - N) N
  let x := h9CenteredInverseTrace N K
  letI : IsProbabilityMeasure muG :=
    standardRealGaussianMatrixMeasure_isProbability_internal _ _
  letI : IsProbabilityMeasure muB :=
    standardRealGaussianMatrixMeasure_isProbability_internal _ _
  have hx : MemLp x 4 muB := by
    simpa only [x, muB, h9InverseWishartDenominatorLaw] using
      hinv.centeredTrace_memLp_four
  have hcomp : MemLp
      (fun p : H9BetaPrimeGaussianSource N K => x p.2) 4
      (muG.prod muB) := hx.comp_snd muG
  have hpoint : h9SourceDenominatorFluctuation N K =
      fun p : H9BetaPrimeGaussianSource N K =>
        (((N + 1 : ℕ) : ℝ)) * x p.2 := by
    funext p
    simp [h9SourceDenominatorFluctuation, h9CenteredInverseTrace,
      h9ScaledInverseWishart, h9SourceInverseTrace, x, Matrix.trace_smul]
  have hnormComp :
      lpNorm (fun p : H9BetaPrimeGaussianSource N K => x p.2) 4
          (muG.prod muB) = lpNorm x 4 muB := by
    have hpres : MeasurePreserving
        (Prod.snd : H9BetaPrimeGaussianSource N K →
          H9InverseWishartSample N K) (muG.prod muB) muB := by
      exact measurePreserving_snd
    change lpNorm
      (x ∘ (Prod.snd : H9BetaPrimeGaussianSource N K →
        H9InverseWishartSample N K)) 4 (muG.prod muB) = lpNorm x 4 muB
    exact lpNorm_comp_measurePreserving_h9_endpoint
      (p := (4 : ENNReal)) hx.aestronglyMeasurable hpres
  constructor
  · rw [hpoint]
    simpa only [muG, muB, realBetaPrimeGaussianSourceLaw] using
      hcomp.const_mul (((N + 1 : ℕ) : ℝ))
  · intro hdense
    have hxBound : lpNorm x 4 muB ≤ 4096 := by
      simpa only [x, muB, h9InverseWishartDenominatorLaw,
        h9InverseWishartMomentConstant] using (hinv.dense_bounds hdense).1
    have hscaleNorm :
        lpNorm (h9SourceDenominatorFluctuation N K) 4
            (muG.prod muB) =
          (((N + 1 : ℕ) : ℝ)) * lpNorm x 4 muB := by
      rw [hpoint]
      calc
        lpNorm (fun p : H9BetaPrimeGaussianSource N K =>
            (((N + 1 : ℕ) : ℝ)) * x p.2) 4 (muG.prod muB) =
            (((N + 1 : ℕ) : ℝ)) *
              lpNorm (fun p : H9BetaPrimeGaussianSource N K => x p.2) 4
                (muG.prod muB) := by
          simpa using lpNorm_fun_natCast_mul (N + 1)
            (fun p : H9BetaPrimeGaussianSource N K => x p.2)
            4 (muG.prod muB)
        _ = _ := by rw [hnormComp]
    have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    simpa only [muG, muB, realBetaPrimeGaussianSourceLaw] using
      (show lpNorm (h9SourceDenominatorFluctuation N K) 4 (muG.prod muB) ≤
          8192 * (N : ℝ) by
        rw [hscaleNorm]
        calc
          (((N + 1 : ℕ) : ℝ)) * lpNorm x 4 muB ≤
              (((N + 1 : ℕ) : ℝ)) * 4096 :=
            mul_le_mul_of_nonneg_left hxBound (by positivity)
          _ ≤ 8192 * (N : ℝ) := by
            push_cast
            nlinarith)

/-- Internal proof of the literal proposition formerly supplied by
`betaPrimeYTraceOne_centered_three_momentPackage_external`. -/
theorem betaPrimeYTraceOne_centered_three_momentPackage_proved_allDimensions
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (fun u ↦ betaPrimeYTraceOne N K u -
      ∫ z, betaPrimeYTraceOne N K z ∂(betaPrimeTraceFourLaw N K)) 3
        (betaPrimeTraceFourLaw N K) ∧
      (16 * N ≤ K →
        lpNorm (fun u ↦ betaPrimeYTraceOne N K u -
          ∫ z, betaPrimeYTraceOne N K z ∂(betaPrimeTraceFourLaw N K)) 3
            (betaPrimeTraceFourLaw N K) ≤
          denseClassicalMomentConstant * (N : ℝ)) := by
  let hinv : H9InverseWishartDenominatorPackage N K :=
    h9InverseWishartDenominatorPackage_internal_allDimensions hN hgap
  obtain ⟨hNumMem, hNumDense⟩ :=
    h9SourceNumeratorPackage_of_fixedGaussianWick hN hgap hinv
  obtain ⟨hDenMem, hDenDense⟩ :=
    h9SourceDenominatorPackage_internal hN hinv
  apply betaPrimeYTraceOne_centered_three_momentPackage_of_sourceL4
    hN hgap hNumMem hDenMem
  · intro hdense
    calc
      lpNorm (h9SourceNumeratorFluctuation N K) 4
          (realBetaPrimeGaussianSourceLaw N K) ≤
        1024 * (N : ℝ) := hNumDense hdense
      _ ≤ denseClassicalMomentConstant / 2 * (N : ℝ) := by
        unfold denseClassicalMomentConstant
        have hN0 : 0 ≤ (N : ℝ) := by positivity
        nlinarith
  · intro hdense
    calc
      lpNorm (h9SourceDenominatorFluctuation N K) 4
          (realBetaPrimeGaussianSourceLaw N K) ≤
        8192 * (N : ℝ) := hDenDense hdense
      _ ≤ denseClassicalMomentConstant / 2 * (N : ℝ) := by
        unfold denseClassicalMomentConstant
        have hN0 : 0 ≤ (N : ℝ) := by positivity
        nlinarith

/-- Internal H9 integrability theorem with the same statement as the
external projection. -/
theorem betaPrimeYTraceOne_centered_memLp_three_proved_allDimensions
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (fun u ↦ betaPrimeYTraceOne N K u -
      ∫ z, betaPrimeYTraceOne N K z ∂(betaPrimeTraceFourLaw N K)) 3
      (betaPrimeTraceFourLaw N K) :=
  (betaPrimeYTraceOne_centered_three_momentPackage_proved_allDimensions
    hN hgap).1

/-- Internal H9 dense norm bound with the same statement as the external
projection. -/
theorem betaPrimeYTraceOne_centered_lpNorm_three_le_proved_allDimensions
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (fun u ↦ betaPrimeYTraceOne N K u -
      ∫ z, betaPrimeYTraceOne N K z ∂(betaPrimeTraceFourLaw N K)) 3
        (betaPrimeTraceFourLaw N K) ≤
      denseClassicalMomentConstant * (N : ℝ) := by
  have hgap : 2 * N + 8 ≤ K := by omega
  exact (betaPrimeYTraceOne_centered_three_momentPackage_proved_allDimensions
    hN hgap).2 hdense

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
