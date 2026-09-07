import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Measure adapters for the H6 radial reductions

This file is purely measure theoretic.  It proves the density-pushforward,
support, and normalization steps used on both sides of H6.  In particular,
an unknown positive finite radial constant is eliminated after canonical
normalization; no Selberg or multivariate-beta constant is evaluated.
-/

open scoped ENNReal
open Set MeasureTheory

namespace H6RadialMeasureAdapters

noncomputable section

/-- Canonical totalized normalization used throughout the H6 development. -/
def normalizeMeasure {α : Type*} [MeasurableSpace α]
    (μ : Measure α) : Measure α :=
  (μ Set.univ)⁻¹ • μ

/-- Pushing forward a density which factors through the map is the same as
first pushing forward and then applying that density.  The density only needs
to be almost-everywhere measurable for the pushed-forward measure. -/
theorem map_withDensity_comp
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (f : α → β) (v : β → ℝ≥0∞)
    (hf : Measurable f) (hv : AEMeasurable v (Measure.map f μ)) :
    Measure.map f (μ.withDensity (v ∘ f)) =
      (Measure.map f μ).withDensity v := by
  apply Measure.ext_of_lintegral _
  intro g hg
  calc
    (∫⁻ b, g b ∂Measure.map f (μ.withDensity (v ∘ f))) =
        ∫⁻ a, g (f a) ∂μ.withDensity (v ∘ f) :=
      lintegral_map hg hf
    _ = ∫⁻ a, (v ∘ f) a * (g ∘ f) a ∂μ :=
      lintegral_withDensity_eq_lintegral_mul₀
        (hv.comp_measurable hf) (hg.comp hf).aemeasurable
    _ = ∫⁻ a, (v * g) (f a) ∂μ := by rfl
    _ = ∫⁻ b, (v * g) b ∂Measure.map f μ :=
      (lintegral_map' (hv.fun_mul hg.aemeasurable) hf.aemeasurable).symm
    _ = ∫⁻ b, g b ∂(Measure.map f μ).withDensity v :=
      (lintegral_withDensity_eq_lintegral_mul₀ hv hg.aemeasurable).symm

/-- A positive finite unknown orbit constant cancels under canonical
normalization.  Taking the mass of the raw pushforward supplies the only
scalar identity needed by the proof. -/
theorem map_normalizeMeasure_of_map_eq_nnreal_smul
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) (f : α → β) (c : NNReal)
    (hf : Measurable f) (hc : c ≠ 0)
    (hmap : Measure.map f μ = (c : ℝ≥0∞) • ν) :
    Measure.map f (normalizeMeasure μ) = normalizeMeasure ν := by
  have hcE : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc
  have hcTop : (c : ℝ≥0∞) ≠ ∞ := ENNReal.coe_ne_top
  have hmass : μ Set.univ = (c : ℝ≥0∞) * ν Set.univ := by
    calc
      μ Set.univ = Measure.map f μ Set.univ := by
        rw [Measure.map_apply hf MeasurableSet.univ]
        simp
      _ = ((c : ℝ≥0∞) • ν) Set.univ :=
        congrArg (fun m : Measure β ↦ m Set.univ) hmap
      _ = (c : ℝ≥0∞) * ν Set.univ := by
        rw [Measure.smul_apply]
        rfl
  unfold normalizeMeasure
  rw [Measure.map_smul, hmap, smul_smul]
  congr 1
  rw [hmass, ENNReal.mul_inv (Or.inl hcE) (Or.inl hcTop)]
  calc
    (c : ℝ≥0∞)⁻¹ * (ν Set.univ)⁻¹ * (c : ℝ≥0∞) =
        (ν Set.univ)⁻¹ * ((c : ℝ≥0∞)⁻¹ * (c : ℝ≥0∞)) := by
      ac_rfl
    _ = (ν Set.univ)⁻¹ := by
      rw [ENNReal.inv_mul_cancel hcE hcTop, mul_one]

/-- A density over a restricted measure remains almost surely in the
restricting set. -/
theorem withDensity_restrict_ae_mem
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (s : Set α) (v : α → ℝ≥0∞) (hs : MeasurableSet s) :
    ∀ᵐ x ∂(μ.restrict s).withDensity v, x ∈ s :=
  (withDensity_absolutelyContinuous (μ.restrict s) v).ae_le
    (ae_restrict_mem hs)

/-- Canonical normalization does not enlarge almost-sure support. -/
theorem normalizeMeasure_ae_of_ae
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : α → Prop}
    (h : ∀ᵐ x ∂μ, p x) : ∀ᵐ x ∂normalizeMeasure μ, p x :=
  (Measure.smul_absolutelyContinuous).ae_le h

end

end H6RadialMeasureAdapters
