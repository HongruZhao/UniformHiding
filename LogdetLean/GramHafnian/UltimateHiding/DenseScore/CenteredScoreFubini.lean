import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ConcreteCenteredLikelihood
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ConcreteScaledCOECornerProbability
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# Fubini for an integrable literal centered score

This file discharges the measure-theoretic part of the centered-score
interchange.  The only substantive premise is the exact one Fubini needs:
the literal score belongs to `L¹` on the COE-corner/projective product law.
No score integrability or moment estimate is hidden in this lemma.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- Product `L¹` integrability of a literal centered score implies the exact
event-indicator Fubini interchange. -/
theorem coeCorner_centeredDensityScore_fubini_of_memLp
    {N K r : ℕ} (hN : 1 ≤ N) (hNK : N ≤ K)
    (event : Set (ConcreteMatrixState N))
    (hevent : MeasurableSet event)
    (hscore : MemLp
      (fun Av : ConcreteMatrixState N × ComplexUnitSphere N ↦
        concreteCenteredDensityScore r N K Av.2 Av.1) 1
      ((concreteScaledCOECornerLaw
          LogdetLean.GramHafnian.LocalAnticoncentration.canonicalUnitaryHaarProbabilityFamily
            N K).prod (complexUnitSphereProbabilityMeasure N))) :
    (∫ v : ComplexUnitSphere N,
      ∫ A, event.indicator (concreteCenteredDensityScore r N K v) A
        ∂(concreteScaledCOECornerLaw
          LogdetLean.GramHafnian.LocalAnticoncentration.canonicalUnitaryHaarProbabilityFamily
            N K)
      ∂(complexUnitSphereProbabilityMeasure N)) =
    ∫ A, event.indicator (fun A ↦
      ∫ v : ComplexUnitSphere N, concreteCenteredDensityScore r N K v A
        ∂(complexUnitSphereProbabilityMeasure N)) A
      ∂(concreteScaledCOECornerLaw
        LogdetLean.GramHafnian.LocalAnticoncentration.canonicalUnitaryHaarProbabilityFamily
          N K) := by
  let mu := concreteScaledCOECornerLaw
    LogdetLean.GramHafnian.LocalAnticoncentration.canonicalUnitaryHaarProbabilityFamily N K
  let sphere := complexUnitSphereProbabilityMeasure N
  let score : ConcreteMatrixState N × ComplexUnitSphere N → ℝ :=
    fun Av ↦ concreteCenteredDensityScore r N K Av.2 Av.1
  let selected : ConcreteMatrixState N × ComplexUnitSphere N → ℝ :=
    fun Av ↦ event.indicator (fun A ↦
      concreteCenteredDensityScore r N K Av.2 A) Av.1
  letI : IsProbabilityMeasure mu :=
    canonicalScaledCOECornerLaw_isProbability hNK
  letI : IsProbabilityMeasure sphere :=
    complexUnitSphereProbabilityMeasure_isProbability hN
  have hscoreInt : Integrable score (mu.prod sphere) :=
    memLp_one_iff_integrable.mp hscore
  have hselected : selected =
      ((fun Av : ConcreteMatrixState N × ComplexUnitSphere N ↦ Av.1) ⁻¹'
        event).indicator score := by
    funext Av
    by_cases hmem : Av.1 ∈ event <;>
      simp [selected, score, Set.indicator, hmem]
  have hmeas : MeasurableSet
      ((fun Av : ConcreteMatrixState N × ComplexUnitSphere N ↦ Av.1) ⁻¹'
        event) :=
    measurable_fst hevent
  have hselectedInt : Integrable selected (mu.prod sphere) := by
    rw [hselected]
    exact hscoreInt.indicator hmeas
  have hswap := integral_prod_symm selected hselectedInt
  have hnative := integral_prod selected hselectedInt
  calc
    (∫ v : ComplexUnitSphere N,
      ∫ A, event.indicator (concreteCenteredDensityScore r N K v) A
        ∂mu ∂sphere) =
        ∫ v, ∫ A, selected (A, v) ∂mu ∂sphere := by rfl
    _ = ∫ z, selected z ∂(mu.prod sphere) := hswap.symm
    _ = ∫ A, ∫ v, selected (A, v) ∂sphere ∂mu := hnative
    _ = ∫ A, event.indicator (fun A ↦
        ∫ v : ComplexUnitSphere N, concreteCenteredDensityScore r N K v A
          ∂sphere) A ∂mu := by
      apply integral_congr_ae
      filter_upwards [] with A
      by_cases hmem : A ∈ event <;>
        simp [selected, Set.indicator, hmem]

/-! ## The zeroth-order case -/

/-- At time zero the literal centered likelihood is exactly one, including
on the totalized zero-determinant branch. -/
theorem concreteCenteredLikelihoodCore_zero
    {N K : ℕ} (v : ComplexUnitSphere N) (A : ConcreteMatrixState N) :
    concreteCenteredLikelihoodCore K v 0 A = 1 := by
  unfold concreteCenteredLikelihoodCore
  split_ifs with hbase
  · rfl
  · have hinverse : concreteCOECenteredInverseDeterminant K v 0 A =
        concreteCOEBaseDeterminant K A := by
      simp [concreteCOECenteredInverseDeterminant,
        concreteCOEBaseDeterminant]
    rw [hinverse, div_self hbase]
    exact Real.one_rpow _

/-- Consequently the literal zeroth score is product `L¹`. -/
theorem concreteCenteredDensityScoreZeroProduct_memLp_one
    {N K : ℕ} (hN : 1 ≤ N) (hNK : N ≤ K) :
    MemLp
      (fun Av : ConcreteMatrixState N × ComplexUnitSphere N ↦
        concreteCenteredDensityScore 0 N K Av.2 Av.1) 1
      ((concreteScaledCOECornerLaw
          LogdetLean.GramHafnian.LocalAnticoncentration.canonicalUnitaryHaarProbabilityFamily
            N K).prod (complexUnitSphereProbabilityMeasure N)) := by
  let mu := concreteScaledCOECornerLaw
    LogdetLean.GramHafnian.LocalAnticoncentration.canonicalUnitaryHaarProbabilityFamily N K
  let sphere := complexUnitSphereProbabilityMeasure N
  letI : IsProbabilityMeasure mu :=
    canonicalScaledCOECornerLaw_isProbability hNK
  letI : IsProbabilityMeasure sphere :=
    complexUnitSphereProbabilityMeasure_isProbability hN
  have hone : MemLp
      (fun _ : ConcreteMatrixState N × ComplexUnitSphere N ↦ (1 : ℝ)) 1
      (mu.prod sphere) := memLp_const 1
  apply hone.ae_eq
  filter_upwards [] with Av
  simp only [concreteCenteredDensityScore, iteratedDeriv_zero]
  exact (concreteCenteredLikelihoodCore_zero (K := K) Av.2 Av.1).symm

/-- Zeroth-order Fubini is therefore completely internal. -/
theorem coeCorner_centeredDensityScore_zero_fubini
    {N K : ℕ} (hN : 1 ≤ N) (hNK : N ≤ K)
    (event : Set (ConcreteMatrixState N)) (hevent : MeasurableSet event) :
    (∫ v : ComplexUnitSphere N,
      ∫ A, event.indicator (concreteCenteredDensityScore 0 N K v) A
        ∂(concreteScaledCOECornerLaw
          LogdetLean.GramHafnian.LocalAnticoncentration.canonicalUnitaryHaarProbabilityFamily
            N K)
      ∂(complexUnitSphereProbabilityMeasure N)) =
    ∫ A, event.indicator (fun A ↦
      ∫ v : ComplexUnitSphere N, concreteCenteredDensityScore 0 N K v A
        ∂(complexUnitSphereProbabilityMeasure N)) A
      ∂(concreteScaledCOECornerLaw
        LogdetLean.GramHafnian.LocalAnticoncentration.canonicalUnitaryHaarProbabilityFamily
          N K) := by
  exact coeCorner_centeredDensityScore_fubini_of_memLp hN hNK event hevent
    (concreteCenteredDensityScoreZeroProduct_memLp_one hN hNK)

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
