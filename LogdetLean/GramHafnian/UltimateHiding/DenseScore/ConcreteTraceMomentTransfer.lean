import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ClassicalMomentBoundsExternal
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.MixedScalarQuadraticClosure
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.PositiveTraceMomentInternal
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H6_A2Prime_A1TraceTransport
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.H9MomentRewire
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.H8H10MomentRewire
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ConcreteBetaPrimeTraceCoordinates

/-!
# Transfer of the classical beta-prime moments to the concrete COE law

The external moment boundary is stated on a four-coordinate real beta-prime
trace vector.  This file performs the measure-theoretic pushforward step into
the actual, correctly unscaled, square COE-corner law.  No new moment, score,
event derivative, total-variation, or hiding statement is assumed here.

Keeping the functions as compositions with `concreteCOETracePowerVector`
makes the exact use of the Takagi--Muirhead distributional identity visible.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.CurrentPRL

/-- The concrete four-trace vector under the scaled square COE law has the
literal beta-prime trace law. -/
theorem map_concreteCOETracePowerVector_eq_betaPrimeTraceFourLaw
    {N K : ℕ} (hN : 1 ≤ N) (h2NK : 2 * N ≤ K) :
    Measure.map (concreteCOETracePowerVector 4 N K)
        (concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K) =
      betaPrimeTraceFourLaw N K := by
  simpa only [betaPrimeTraceFourLaw] using
    (coeTakagiMuirhead_traceVector_betaPrime_A1A2PrimeA3
      (r := 4) hN h2NK)

/-- `L^p` membership pulls back exactly along the concrete trace map. -/
theorem memLp_comp_concreteCOETracePowerVector
    {N K : ℕ} (hN : 1 ≤ N) (h2NK : 2 * N ≤ K)
    {p : ENNReal} {g : (Fin 4 → ℝ) → ℝ}
    (hg : MemLp g p (betaPrimeTraceFourLaw N K)) :
    MemLp (g ∘ concreteCOETracePowerVector 4 N K) p
      (concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K) := by
  apply MemLp.comp_of_map
  · simpa only [map_concreteCOETracePowerVector_eq_betaPrimeTraceFourLaw
      hN h2NK] using hg
  · exact (measurable_concreteCOETracePowerVector_external 4 N K).aemeasurable

/-- The real `lpNorm` is preserved by the same pushforward. -/
theorem lpNorm_comp_concreteCOETracePowerVector
    {N K : ℕ} (hN : 1 ≤ N) (h2NK : 2 * N ≤ K)
    {p : ENNReal} {g : (Fin 4 → ℝ) → ℝ}
    (hg : AEStronglyMeasurable g (betaPrimeTraceFourLaw N K)) :
    lpNorm (g ∘ concreteCOETracePowerVector 4 N K) p
        (concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K) =
      lpNorm g p (betaPrimeTraceFourLaw N K) := by
  let mu := concreteScaledCOECornerLaw
    canonicalUnitaryHaarProbabilityFamily N K
  let f := concreteCOETracePowerVector 4 N K
  have hmap : Measure.map f mu = betaPrimeTraceFourLaw N K := by
    simpa only [mu, f] using
      map_concreteCOETracePowerVector_eq_betaPrimeTraceFourLaw hN h2NK
  have hgf : AEStronglyMeasurable g (Measure.map f mu) := by
    simpa only [hmap] using hg
  have hf : AEMeasurable f mu :=
    (measurable_concreteCOETracePowerVector_external 4 N K).aemeasurable
  rw [← hmap, ← toReal_eLpNorm (hgf.comp_aemeasurable hf),
    ← toReal_eLpNorm hgf]
  exact congrArg ENNReal.toReal (eLpNorm_map_measure hgf hf).symm

/-- Integrals of measurable functions of the trace vector also transfer
exactly. -/
theorem integral_comp_concreteCOETracePowerVector
    {N K : ℕ} (hN : 1 ≤ N) (h2NK : 2 * N ≤ K)
    {g : (Fin 4 → ℝ) → ℝ}
    (hg : AEStronglyMeasurable g (betaPrimeTraceFourLaw N K)) :
    (∫ A, g (concreteCOETracePowerVector 4 N K A)
        ∂(concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K)) =
      ∫ u, g u ∂(betaPrimeTraceFourLaw N K) := by
  let mu := concreteScaledCOECornerLaw
    canonicalUnitaryHaarProbabilityFamily N K
  let f := concreteCOETracePowerVector 4 N K
  have hmap : Measure.map f mu = betaPrimeTraceFourLaw N K := by
    simpa only [mu, f] using
      map_concreteCOETracePowerVector_eq_betaPrimeTraceFourLaw hN h2NK
  have hgf : AEStronglyMeasurable g (Measure.map f mu) := by
    simpa only [hmap] using hg
  have hf : AEMeasurable f mu :=
    (measurable_concreteCOETracePowerVector_external 4 N K).aemeasurable
  simpa only [mu, f, Function.comp_apply, hmap] using
    (integral_map hf hgf).symm

/-! ## Concrete compositions -/

/-! ## Low-order concrete projections

These projections deliberately avoid the larger five-field derivative input
record.  Low-order score consumers should use them when they need only
`Tr Y`, `Tr Y²`, or `(Tr Y)²`; doing so prevents an unused raw-third moment
field from entering their axiom closure. -/

theorem concreteCOETraceOne_memLp_one_internal
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (concreteCOETraceOne N K) 1
      (concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K) := by
  have h := memLp_comp_concreteCOETracePowerVector hN (by omega)
    (betaPrimeYTraceOne_memLp_one_proved_allDimensions hN hgap)
  have hfun : betaPrimeYTraceOne N K ∘
      concreteCOETracePowerVector 4 N K = concreteCOETraceOne N K := by
    funext A
    change concreteBetaPrimeYTraceOne N K A = concreteCOETraceOne N K A
    exact concreteBetaPrimeYTraceOne_eq_concreteCOETraceOne N K A
  rw [hfun] at h
  exact h

theorem concreteCOETraceOne_lpNorm_one_le_internal
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (concreteCOETraceOne N K) 1
        (concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K) ≤
      derivedRawTraceOneConstant * (N : ℝ) ^ 2 := by
  have hgap : 2 * N + 8 ≤ K := by omega
  have hmem := betaPrimeYTraceOne_memLp_one_proved_allDimensions hN hgap
  have htransport := lpNorm_comp_concreteCOETracePowerVector hN (by omega)
    (p := (1 : ENNReal)) hmem.aestronglyMeasurable
  have hfun : betaPrimeYTraceOne N K ∘
      concreteCOETracePowerVector 4 N K = concreteCOETraceOne N K := by
    funext A
    change concreteBetaPrimeYTraceOne N K A = concreteCOETraceOne N K A
    exact concreteBetaPrimeYTraceOne_eq_concreteCOETraceOne N K A
  rw [hfun] at htransport
  rw [htransport]
  exact betaPrimeYTraceOne_lpNorm_one_le_proved_allDimensions hN hdense

theorem concreteCOETraceTwo_memLp_one_internal
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (concreteCOETraceTwo N K) 1
      (concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K) := by
  have h := memLp_comp_concreteCOETracePowerVector hN (by omega)
    (betaPrimeYTraceTwo_memLp_one_positive_internal hN hgap)
  have hfun : betaPrimeYTraceTwo N K ∘
      concreteCOETracePowerVector 4 N K = concreteCOETraceTwo N K := by
    funext A
    change concreteBetaPrimeYTraceTwo N K A = concreteCOETraceTwo N K A
    exact concreteBetaPrimeYTraceTwo_eq_concreteCOETraceTwo N K A
  rw [hfun] at h
  exact h

theorem concreteCOETraceTwo_lpNorm_one_le_internal
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (concreteCOETraceTwo N K) 1
        (concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K) ≤
      derivedPositiveRawTraceTwoConstant * (N : ℝ) ^ 3 := by
  have hgap : 2 * N + 8 ≤ K := by omega
  have hmem := betaPrimeYTraceTwo_memLp_one_positive_internal hN hgap
  have htransport := lpNorm_comp_concreteCOETracePowerVector hN (by omega)
    (p := (1 : ENNReal)) hmem.aestronglyMeasurable
  have hfun : betaPrimeYTraceTwo N K ∘
      concreteCOETracePowerVector 4 N K = concreteCOETraceTwo N K := by
    funext A
    change concreteBetaPrimeYTraceTwo N K A = concreteCOETraceTwo N K A
    exact concreteBetaPrimeYTraceTwo_eq_concreteCOETraceTwo N K A
  rw [hfun] at htransport
  rw [htransport]
  exact betaPrimeYTraceTwo_lpNorm_one_le_positive_internal hN hdense

theorem concreteCOETraceOneSquare_memLp_one_internal
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (fun A ↦ concreteCOETraceOne N K A ^ 2) 1
      (concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K) := by
  have h := memLp_comp_concreteCOETracePowerVector hN (by omega)
    (betaPrimeYTraceOneSquare_memLp_one_proved_allDimensions hN hgap)
  have hfun : (fun u ↦ betaPrimeYTraceOne N K u ^ 2) ∘
      concreteCOETracePowerVector 4 N K =
        fun A ↦ concreteCOETraceOne N K A ^ 2 := by
    funext A
    simp only [Function.comp_apply]
    rw [show betaPrimeYTraceOne N K
        (concreteCOETracePowerVector 4 N K A) = concreteCOETraceOne N K A by
      exact concreteBetaPrimeYTraceOne_eq_concreteCOETraceOne N K A]
  rw [hfun] at h
  exact h

theorem concreteCOETraceOneSquare_lpNorm_one_le_internal
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (fun A ↦ concreteCOETraceOne N K A ^ 2) 1
        (concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K) ≤
      derivedRawTraceProductConstant * (N : ℝ) ^ 4 := by
  have hgap : 2 * N + 8 ≤ K := by omega
  have hmem :=
    betaPrimeYTraceOneSquare_memLp_one_proved_allDimensions hN hgap
  have htransport := lpNorm_comp_concreteCOETracePowerVector hN (by omega)
    (p := (1 : ENNReal)) hmem.aestronglyMeasurable
  have hfun : (fun u ↦ betaPrimeYTraceOne N K u ^ 2) ∘
      concreteCOETracePowerVector 4 N K =
        fun A ↦ concreteCOETraceOne N K A ^ 2 := by
    funext A
    simp only [Function.comp_apply]
    rw [show betaPrimeYTraceOne N K
        (concreteCOETracePowerVector 4 N K A) = concreteCOETraceOne N K A by
      exact concreteBetaPrimeYTraceOne_eq_concreteCOETraceOne N K A]
  rw [hfun] at htransport
  rw [htransport]
  exact betaPrimeYTraceOneSquare_lpNorm_one_le_proved_allDimensions hN hdense

/-! ## Centered quadratic trace inputs -/

/-- Exact transfer of the first-trace mean. -/
theorem integral_concreteCOETraceOne_eq_betaPrime
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    (∫ A, concreteCOETraceOne N K A
      ∂(concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K)) =
      ∫ u, betaPrimeYTraceOne N K u ∂(betaPrimeTraceFourLaw N K) := by
  have h2NK : 2 * N ≤ K := by omega
  have hraw := integral_comp_concreteCOETracePowerVector hN h2NK
    (betaPrimeYTraceOne_memLp_one_proved_allDimensions hN hgap).aestronglyMeasurable
  calc
    (∫ A, concreteCOETraceOne N K A
        ∂(concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K)) =
        ∫ A, betaPrimeYTraceOne N K
          (concreteCOETracePowerVector 4 N K A)
          ∂(concreteScaledCOECornerLaw
            canonicalUnitaryHaarProbabilityFamily N K) := by
      apply integral_congr_ae
      filter_upwards [] with A
      exact (concreteBetaPrimeYTraceOne_eq_concreteCOETraceOne N K A).symm
    _ = _ := hraw

/-- Exact transfer of the squared first-trace mean. -/
theorem integral_concreteCOETraceOne_sq_eq_betaPrime
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    (∫ A, concreteCOETraceOne N K A ^ 2
      ∂(concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K)) =
      ∫ u, betaPrimeYTraceOne N K u ^ 2
        ∂(betaPrimeTraceFourLaw N K) := by
  have h2NK : 2 * N ≤ K := by omega
  have hraw := integral_comp_concreteCOETracePowerVector hN h2NK
    (betaPrimeYTraceOneSquare_memLp_one_proved_allDimensions
      hN hgap).aestronglyMeasurable
  calc
    (∫ A, concreteCOETraceOne N K A ^ 2
        ∂(concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K)) =
        ∫ A, betaPrimeYTraceOne N K
          (concreteCOETracePowerVector 4 N K A) ^ 2
          ∂(concreteScaledCOECornerLaw
            canonicalUnitaryHaarProbabilityFamily N K) := by
      apply integral_congr_ae
      filter_upwards [] with A
      rw [show betaPrimeYTraceOne N K
          (concreteCOETracePowerVector 4 N K A) =
          concreteCOETraceOne N K A by
        exact concreteBetaPrimeYTraceOne_eq_concreteCOETraceOne N K A]
    _ = _ := hraw

/-- Exact transfer of the second-trace mean. -/
theorem integral_concreteCOETraceTwo_eq_betaPrime
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    (∫ A, concreteCOETraceTwo N K A
      ∂(concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K)) =
      ∫ u, betaPrimeYTraceTwo N K u ∂(betaPrimeTraceFourLaw N K) := by
  have h2NK : 2 * N ≤ K := by omega
  have hraw := integral_comp_concreteCOETracePowerVector hN h2NK
    (betaPrimeYTraceTwo_memLp_one_positive_internal hN hgap).aestronglyMeasurable
  calc
    (∫ A, concreteCOETraceTwo N K A
        ∂(concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K)) =
        ∫ A, betaPrimeYTraceTwo N K
          (concreteCOETracePowerVector 4 N K A)
          ∂(concreteScaledCOECornerLaw
            canonicalUnitaryHaarProbabilityFamily N K) := by
      apply integral_congr_ae
      filter_upwards [] with A
      exact (concreteBetaPrimeYTraceTwo_eq_concreteCOETraceTwo N K A).symm
    _ = _ := hraw

/-- The primitive centered trace estimates, attached to the concrete square
COE law.  The R30 zero-mean identity is an explicit hypothesis and is meant
to be discharged by `QuadraticCenteringFromMass`; it is not imported as a
Wishart moment. -/
theorem concreteCOE_centeredQuadraticTraceInputs_of_bracket_zero
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K)
    (hzero :
      (∫ A, concreteCenteredQuadraticTraceBracket N K A
        ∂(concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K)) = 0) :
    CenteredQuadraticTraceInputs
      (concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K)
      (N : ℝ) (concreteCOEExponent N K)
      denseClassicalMomentConstant denseClassicalMomentConstant
      denseClassicalMomentConstant
      (concreteCOETraceOne N K) (concreteCOETraceTwo N K)
      (∫ A, concreteCOETraceOne N K A
        ∂(concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K))
      (∫ A, concreteCOETraceOne N K A ^ 2
        ∂(concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K))
      (∫ A, concreteCOETraceTwo N K A
        ∂(concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K)) := by
  have hgap : 2 * N + 8 ≤ K := by omega
  have h2NK : 2 * N ≤ K := by omega
  let mu := concreteScaledCOECornerLaw
    canonicalUnitaryHaarProbabilityFamily N K
  let f := concreteCOETracePowerVector 4 N K
  let gOne : (Fin 4 → ℝ) → ℝ := fun u ↦ betaPrimeYTraceOne N K u -
    ∫ z, betaPrimeYTraceOne N K z ∂(betaPrimeTraceFourLaw N K)
  let gSquare : (Fin 4 → ℝ) → ℝ := fun u ↦ betaPrimeYTraceOne N K u ^ 2 -
    ∫ z, betaPrimeYTraceOne N K z ^ 2 ∂(betaPrimeTraceFourLaw N K)
  let gTwo : (Fin 4 → ℝ) → ℝ := fun u ↦ betaPrimeYTraceTwo N K u -
    ∫ z, betaPrimeYTraceTwo N K z ∂(betaPrimeTraceFourLaw N K)
  have hMeanOne := integral_concreteCOETraceOne_eq_betaPrime hN hgap
  have hMeanSquare := integral_concreteCOETraceOne_sq_eq_betaPrime hN hgap
  have hMeanTwo := integral_concreteCOETraceTwo_eq_betaPrime hN hgap
  have hOneMemBeta :=
    betaPrimeYTraceOne_centered_memLp_two_proved_allDimensions hN hgap
  have hSquareMemBeta :=
    betaPrimeYTraceOneSquare_centered_memLp_two_proved_allDimensions hN hgap
  have hTwoMemBeta :=
    betaPrimeYTraceTwo_centered_memLp_two_proved_allDimensions hN hgap
  have hOneMem : MemLp (gOne ∘ f) 2 mu := by
    exact memLp_comp_concreteCOETracePowerVector hN h2NK hOneMemBeta
  have hSquareMem : MemLp (gSquare ∘ f) 2 mu := by
    exact memLp_comp_concreteCOETracePowerVector hN h2NK hSquareMemBeta
  have hTwoMem : MemLp (gTwo ∘ f) 2 mu := by
    exact memLp_comp_concreteCOETracePowerVector hN h2NK hTwoMemBeta
  have hOneNorm : lpNorm (gOne ∘ f) 2 mu ≤
      denseClassicalMomentConstant * (N : ℝ) := by
    rw [lpNorm_comp_concreteCOETracePowerVector hN h2NK
      hOneMemBeta.aestronglyMeasurable]
    exact betaPrimeYTraceOne_centered_lpNorm_two_le_proved_allDimensions hN hdense
  have hSquareNorm : lpNorm (gSquare ∘ f) 2 mu ≤
      denseClassicalMomentConstant * (N : ℝ) ^ 3 := by
    rw [lpNorm_comp_concreteCOETracePowerVector hN h2NK
      hSquareMemBeta.aestronglyMeasurable]
    exact
      betaPrimeYTraceOneSquare_centered_lpNorm_two_le_proved_allDimensions hN hdense
  have hTwoNorm : lpNorm (gTwo ∘ f) 2 mu ≤
      denseClassicalMomentConstant * (N : ℝ) ^ 2 := by
    rw [lpNorm_comp_concreteCOETracePowerVector hN h2NK
      hTwoMemBeta.aestronglyMeasurable]
    exact betaPrimeYTraceTwo_centered_lpNorm_two_le_proved_allDimensions hN hdense
  have hOneFun : gOne ∘ f = fun A ↦ concreteCOETraceOne N K A -
      ∫ A, concreteCOETraceOne N K A ∂mu := by
    funext A
    simp only [gOne, f, Function.comp_apply]
    rw [show betaPrimeYTraceOne N K
        (concreteCOETracePowerVector 4 N K A) =
        concreteCOETraceOne N K A by
      exact concreteBetaPrimeYTraceOne_eq_concreteCOETraceOne N K A,
      hMeanOne]
  have hSquareFun : gSquare ∘ f = fun A ↦ concreteCOETraceOne N K A ^ 2 -
      ∫ A, concreteCOETraceOne N K A ^ 2 ∂mu := by
    funext A
    simp only [gSquare, f, Function.comp_apply]
    rw [show betaPrimeYTraceOne N K
        (concreteCOETracePowerVector 4 N K A) =
        concreteCOETraceOne N K A by
      exact concreteBetaPrimeYTraceOne_eq_concreteCOETraceOne N K A,
      hMeanSquare]
  have hTwoFun : gTwo ∘ f = fun A ↦ concreteCOETraceTwo N K A -
      ∫ A, concreteCOETraceTwo N K A ∂mu := by
    funext A
    simp only [gTwo, f, Function.comp_apply]
    rw [show betaPrimeYTraceTwo N K
        (concreteCOETracePowerVector 4 N K A) =
        concreteCOETraceTwo N K A by
      exact concreteBetaPrimeYTraceTwo_eq_concreteCOETraceTwo N K A,
      hMeanTwo]
  letI : IsProbabilityMeasure
      (scaledHaarTransposeGramLaw
        canonicalUnitaryHaarProbabilityFamily K N K) :=
    scaledHaarTransposeGramLaw_isProbability _ (by omega) le_rfl
  letI : IsProbabilityMeasure mu := by
    dsimp only [mu, concreteScaledCOECornerLaw, concreteHaarAmbientLaw,
      normalizedHaarTransposeGramLaw]
    exact Measure.isProbabilityMeasure_map
      (measurable_normalizeTransposeGram N K).aemeasurable
  have hRawOne : MemLp (concreteCOETraceOne N K) 1 mu := by
    simpa only [mu] using concreteCOETraceOne_memLp_one_internal hN hgap
  have hRawSquare : MemLp (fun A ↦ concreteCOETraceOne N K A ^ 2) 1 mu := by
    simpa only [mu] using concreteCOETraceOneSquare_memLp_one_internal hN hgap
  have hRawTwo : MemLp (concreteCOETraceTwo N K) 1 mu := by
    simpa only [mu] using concreteCOETraceTwo_memLp_one_internal hN hgap
  refine
    { trace_one_integrable := hRawOne.integrable (by norm_num),
      trace_square_integrable := hRawSquare.integrable (by norm_num),
      trace_two_integrable := hRawTwo.integrable (by norm_num),
      mean_one_eq := rfl, mean_square_eq := rfl, mean_two_eq := rfl,
      bracket_integral_zero := hzero,
      centered_one_memLp := ?_, centered_square_memLp := ?_,
      centered_two_memLp := ?_, centered_one_lpNorm_le := ?_,
      centered_square_lpNorm_le := ?_, centered_two_lpNorm_le := ?_ }
  · rw [← hOneFun]
    exact hOneMem
  · rw [← hSquareFun]
    exact hSquareMem
  · rw [← hTwoFun]
    exact hTwoMem
  · rw [← hOneFun]
    exact hOneNorm
  · rw [← hSquareFun]
    exact hSquareNorm
  · rw [← hTwoFun]
    exact hTwoNorm

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
