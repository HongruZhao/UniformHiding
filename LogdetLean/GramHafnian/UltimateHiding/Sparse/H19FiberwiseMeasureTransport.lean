import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Fiberwise transport of product measures

An elementary Fubini lemma for triangular maps.  It avoids constructing a
global measurable equivalence when the map on the second coordinate is an
equivalence only for almost every first coordinate.
-/

open MeasureTheory Filter
open scoped ENNReal

namespace LogdetLean.GramHafnian.UltimateHiding.Sparse

noncomputable section

/-- A measurable family of fixed-fiber pushforward identities assembles into
the corresponding triangular pushforward identity. -/
theorem map_prod_fiberwise_withDensity
    {alpha beta : Type*}
    [MeasurableSpace alpha] [MeasurableSpace beta]
    (mu : Measure alpha) (nu kappa : Measure beta)
    [SFinite mu] [SFinite nu] [SFinite kappa]
    (T : alpha → beta → beta)
    (q : alpha × beta → ℝ≥0∞)
    (hT : Measurable fun z : alpha × beta ↦ T z.1 z.2)
    (hq : Measurable q)
    (hfiber : ∀ᵐ a ∂mu,
      Measure.map (T a) nu =
        kappa.withDensity (fun x ↦ q (a, x))) :
    Measure.map (fun z : alpha × beta ↦ (z.1, T z.1 z.2))
        (mu.prod nu) =
      (mu.prod kappa).withDensity q := by
  let F : alpha × beta → alpha × beta :=
    fun z ↦ (z.1, T z.1 z.2)
  have hF : Measurable F := measurable_fst.prodMk hT
  refine Measure.ext_of_lintegral _ fun phi hphi ↦ ?_
  rw [lintegral_map' hphi.aemeasurable hF.aemeasurable]
  rw [lintegral_prod (fun z ↦ phi (F z)) (hphi.comp hF).aemeasurable]
  rw [lintegral_withDensity_eq_lintegral_mul _ hq hphi]
  rw [lintegral_prod (fun z ↦ (q * phi) z) (hq.mul hphi).aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [hfiber] with a ha
  have hTa : Measurable (T a) :=
    hT.comp (measurable_const.prodMk measurable_id)
  have hphia : Measurable (fun x : beta ↦ phi (a, x)) :=
    hphi.comp (measurable_const.prodMk measurable_id)
  have hqa : Measurable (fun x : beta ↦ q (a, x)) :=
    hq.comp (measurable_const.prodMk measurable_id)
  calc
    ∫⁻ b, phi (F (a, b)) ∂nu =
        ∫⁻ x, phi (a, x) ∂Measure.map (T a) nu := by
      rw [lintegral_map' hphia.aemeasurable hTa.aemeasurable]
    _ = ∫⁻ x, phi (a, x) ∂kappa.withDensity (fun x ↦ q (a, x)) := by
      rw [ha]
    _ = ∫⁻ x, q (a, x) * phi (a, x) ∂kappa := by
      rw [lintegral_withDensity_eq_lintegral_mul _ hqa hphia]
      rfl
    _ = ∫⁻ b, (q * phi) (a, b) ∂kappa := by rfl

#print axioms map_prod_fiberwise_withDensity

end

end LogdetLean.GramHafnian.UltimateHiding.Sparse
