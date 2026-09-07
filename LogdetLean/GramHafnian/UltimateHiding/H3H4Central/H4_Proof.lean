import LogdetLean.GramHafnian.UltimateHiding.H3H4Central.H3_Proof

/-!
# Exact H4 closure from approved A1

The frozen external declaration is preserved and is not invoked. This file
adds only its literal conclusion, substituting the kernel-checked A1-derived
exact H5 theorem into the checked deterministic order-two derivative adapter.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.H3H4Central

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep
open LogdetLean.GramHafnian.UltimateHiding.DenseScore
open LogdetLean.GramHafnian.CurrentPRL

theorem coeCorner_centralEventPath_derivatives_external_derived_of_A1
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (event : Set (ConcreteMatrixState N)) (hevent : MeasurableSet event) :
    iteratedDeriv 1
        (concreteCentralEventPath N
          (concreteScaledCOECornerLaw
            canonicalUnitaryHaarProbabilityFamily N K) event) 0 =
      ∫ A, event.indicator (concreteCentralLogScoreOne N K) A
        ∂(concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K) ∧
    iteratedDeriv 2
        (concreteCentralEventPath N
          (concreteScaledCOECornerLaw
            canonicalUnitaryHaarProbabilityFamily N K) event) 0 =
      ∫ A, event.indicator (concreteCentralDensityScoreTwo N K) A
        ∂(concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K) := by
  have h2NK : 2 * N ≤ K := by omega
  exact
    coeCorner_centralEventPath_derivatives_external_derived_orderTwo_conditional
      hN hboundary
        (friedmanMello1985_unscaledCOECornerLaw_eq_determinantDensity_of_A1
          hN h2NK)
        event hevent

end

end LogdetLean.GramHafnian.UltimateHiding.H3H4Central
