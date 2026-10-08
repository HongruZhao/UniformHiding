import Mathlib.Probability.Moments.ComplexMGF

open MeasureTheory ProbabilityTheory Filter Set Topology Complex

namespace A4Research

/-- Local real exponential transforms determine scalar distributions.
This analytic lemma is intended for directional tests of a Wishart law;
it does not assert the Wishart density or either moment formula in A4. -/
theorem map_eq_of_mgf_eventually_eq
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {ν : Measure Ω'} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {X : Ω → ℝ} {Y : Ω' → ℝ}
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y ν)
    (hX0 : 0 ∈ interior (integrableExpSet X μ))
    (hY0 : 0 ∈ interior (integrableExpSet Y ν))
    (hmgf : ∀ᶠ t : ℝ in 𝓝 0, mgf X μ t = mgf Y ν t) :
    μ.map X = ν.map Y := by
  let s : Set ℝ := interior (integrableExpSet X μ) ∩
    interior (integrableExpSet Y ν)
  have hs0 : (0 : ℝ) ∈ s := ⟨hX0, hY0⟩
  have hXa : AnalyticOnNhd ℂ (complexMGF X μ) {z | z.re ∈ s} :=
    analyticOnNhd_complexMGF.mono (fun z hz ↦ hz.1)
  have hYa : AnalyticOnNhd ℂ (complexMGF Y ν) {z | z.re ∈ s} :=
    analyticOnNhd_complexMGF.mono (fun z hz ↦ hz.2)
  have hreal : ∃ᶠ t : ℝ in 𝓝[≠] 0,
      complexMGF X μ t = complexMGF Y ν t := by
    apply Filter.Eventually.frequently
    filter_upwards [hmgf.filter_mono nhdsWithin_le_nhds] with t ht
    rw [complexMGF_ofReal, complexMGF_ofReal, ht]
  have hcplx : ∃ᶠ z : ℂ in 𝓝[≠] 0,
      complexMGF X μ z = complexMGF Y ν z := by
    rw [frequently_iff_seq_forall] at hreal ⊢
    obtain ⟨xs, hxs, heq⟩ := hreal
    refine ⟨fun n ↦ (xs n : ℂ), ?_, heq⟩
    rw [tendsto_nhdsWithin_iff] at hxs ⊢
    constructor
    · simpa only [Function.comp_def, Complex.ofReal_zero] using
        (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp hxs.1
    · simpa using hxs.2
  have hsconv : Convex ℝ s :=
    (convex_integrableExpSet (X := X) (μ := μ)).interior.inter
      (convex_integrableExpSet (X := Y) (μ := ν)).interior
  have heq : Set.EqOn (complexMGF X μ) (complexMGF Y ν) {z | z.re ∈ s} :=
    AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq hXa hYa
      (hsconv.linear_preimage reLm).isPreconnected
      (z₀ := 0) (by simpa using hs0) hcplx
  apply Measure.ext_of_charFun
  funext t
  rw [← complexMGF_mul_I hX, ← complexMGF_mul_I hY]
  apply heq
  simpa using hs0

/-- Local exponential transforms in all continuous linear directions determine
a finite measure on a separable real Banach space. The neighborhoods may depend
on the direction. In particular this applies to finite-dimensional matrix
coordinate spaces once the directional transform hypotheses are proved. -/
theorem measure_eq_of_directional_mgf_eventually_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
    {μ ν : Measure E} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ L : StrongDual ℝ E, 0 ∈ interior (integrableExpSet L μ))
    (hν : ∀ L : StrongDual ℝ E, 0 ∈ interior (integrableExpSet L ν))
    (hmgf : ∀ L : StrongDual ℝ E,
      ∀ᶠ t : ℝ in 𝓝 0, mgf L μ t = mgf L ν t) :
    μ = ν := by
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_eq_charFun_map_one, charFunDual_eq_charFun_map_one]
  have hmap : μ.map L = ν.map L :=
    map_eq_of_mgf_eventually_eq L.continuous.measurable.aemeasurable
      L.continuous.measurable.aemeasurable (hμ L) (hν L) (hmgf L)
  rw [hmap]

end A4Research
