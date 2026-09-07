import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ClassicalMomentBoundsExternal

/-!
# CONDITIONAL H6 transport for U08

This module does not invoke the project declaration
`coeTakagiMuirhead_traceVector_betaPrime_external`.  Instead, its exact
all-degree proposition is exposed as the explicit theorem parameter
`H6ExactContract`.

The transport lemmas deliberately route through the concrete COE trace law.
Thus a consumer can see, in the theorem type, exactly where H6 is used while
all `L^p` algebra remains independent of any project scientific axiom.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.CurrentPRL

/-- **CONDITIONAL H6 contract.**  This is the proposition of
`coeTakagiMuirhead_traceVector_betaPrime_external`, including all of its
quantifiers and hypotheses, but it is a theorem parameter rather than an
axiom used by this module. -/
abbrev H6ExactContract : Prop :=
  ∀ {r N K : ℕ} (hN : 1 ≤ N) (h2NK : 2 * N ≤ K),
    Measure.map (concreteCOETracePowerVector r N K)
        (concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K) =
      Measure.map (realBetaPrimeTracePowerVector r N K)
        (realBetaPrimeGaussianSourceLaw N K)

/-- H6 identifies the literal beta-prime four-trace law with the concrete
COE four-trace law. -/
theorem betaPrimeTraceFourLaw_eq_map_concrete_of_h6
    (hH6 : H6ExactContract)
    {N K : ℕ} (hN : 1 ≤ N) (h2NK : 2 * N ≤ K) :
    betaPrimeTraceFourLaw N K =
      Measure.map (concreteCOETracePowerVector 4 N K)
        (concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K) := by
  unfold betaPrimeTraceFourLaw
  exact (hH6 (r := 4) hN h2NK).symm

/-- Pull an `L^p` statement from the literal Gaussian beta-prime source to
the beta-prime trace law, explicitly routing the law equality through H6. -/
theorem memLp_betaPrime_of_source_comp_via_h6
    (hH6 : H6ExactContract)
    {N K : ℕ} (hN : 1 ≤ N) (h2NK : 2 * N ≤ K)
    {p : ENNReal} {g : (Fin 4 → ℝ) → ℝ}
    (hg : AEStronglyMeasurable g (betaPrimeTraceFourLaw N K))
    (hsource : MemLp
      (g ∘ realBetaPrimeTracePowerVector 4 N K) p
      (realBetaPrimeGaussianSourceLaw N K)) :
    MemLp g p (betaPrimeTraceFourLaw N K) := by
  have hrealMap :
      Measure.map (realBetaPrimeTracePowerVector 4 N K)
          (realBetaPrimeGaussianSourceLaw N K) =
        betaPrimeTraceFourLaw N K := by
    rfl
  have hgMap : AEStronglyMeasurable g
      (Measure.map (realBetaPrimeTracePowerVector 4 N K)
        (realBetaPrimeGaussianSourceLaw N K)) := by
    simpa only [hrealMap] using hg
  have hreal : MemLp g p
      (Measure.map (realBetaPrimeTracePowerVector 4 N K)
        (realBetaPrimeGaussianSourceLaw N K)) :=
    (memLp_map_measure_iff hgMap
      (measurable_realBetaPrimeTracePowerVector_external 4 N K).aemeasurable).2
      hsource
  have hcoe : MemLp g p
      (Measure.map (concreteCOETracePowerVector 4 N K)
        (concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K)) := by
    rw [hH6 (r := 4) hN h2NK]
    exact hreal
  rw [betaPrimeTraceFourLaw_eq_map_concrete_of_h6 hH6 hN h2NK]
  exact hcoe

/-- Exact `lpNorm` transport from the literal Gaussian beta-prime source,
again routed through the H6 equality rather than the project H6 axiom. -/
theorem lpNorm_betaPrime_eq_source_comp_via_h6
    (hH6 : H6ExactContract)
    {N K : ℕ} (hN : 1 ≤ N) (h2NK : 2 * N ≤ K)
    {p : ENNReal} {g : (Fin 4 → ℝ) → ℝ}
    (hg : AEStronglyMeasurable g (betaPrimeTraceFourLaw N K)) :
    lpNorm g p (betaPrimeTraceFourLaw N K) =
      lpNorm (g ∘ realBetaPrimeTracePowerVector 4 N K) p
        (realBetaPrimeGaussianSourceLaw N K) := by
  let f := realBetaPrimeTracePowerVector 4 N K
  let mu := realBetaPrimeGaussianSourceLaw N K
  have hrealMap : Measure.map f mu = betaPrimeTraceFourLaw N K := by
    rfl
  have hgMap : AEStronglyMeasurable g (Measure.map f mu) := by
    simpa only [hrealMap] using hg
  have hf : AEMeasurable f mu :=
    (measurable_realBetaPrimeTracePowerVector_external 4 N K).aemeasurable
  have hreal : lpNorm g p (Measure.map f mu) = lpNorm (g ∘ f) p mu := by
    rw [← toReal_eLpNorm hgMap,
      ← toReal_eLpNorm (hgMap.comp_aemeasurable hf)]
    exact congrArg ENNReal.toReal (eLpNorm_map_measure hgMap hf)
  have hcoeToReal :
      Measure.map (concreteCOETracePowerVector 4 N K)
          (concreteScaledCOECornerLaw
            canonicalUnitaryHaarProbabilityFamily N K) =
        Measure.map f mu := by
    simpa only [f, mu] using hH6 (r := 4) hN h2NK
  calc
    lpNorm g p (betaPrimeTraceFourLaw N K) =
        lpNorm g p
          (Measure.map (concreteCOETracePowerVector 4 N K)
            (concreteScaledCOECornerLaw
              canonicalUnitaryHaarProbabilityFamily N K)) := by
      rw [betaPrimeTraceFourLaw_eq_map_concrete_of_h6 hH6 hN h2NK]
    _ = lpNorm g p (Measure.map f mu) := by rw [hcoeToReal]
    _ = lpNorm (g ∘ f) p mu := hreal

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08
