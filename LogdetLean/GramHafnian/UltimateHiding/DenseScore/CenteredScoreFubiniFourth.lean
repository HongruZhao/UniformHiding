import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CenteredScoreFubini
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ConcreteCenteredFourthScore
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.FriedmanMelloSupportFromDensity
import Mathlib.Tactic

/-!
# Fourth centered-score Fubini from the existing product moments

The fourth-order interchange needs no separate Fubini assumption.  The five
literal Bell-monomial moment inputs already imply product `L¹`; the standard
product-integral theorem then supplies the interchange.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- Finiteness-only Bell-four closure at the sharp moment threshold. -/
theorem concreteCenteredBellFourProduct_memLp_one_of_gap
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (concreteCenteredBellFourProduct N K) 1
      (concreteCenteredScoreProductLaw N K) := by
  let ellOne := concreteCenteredEll 1 N K
  let ellTwo := concreteCenteredEll 2 N K
  let ellThree := concreteCenteredEll 3 N K
  let ellFour := concreteCenteredEll 4 N K
  have hpoint : concreteCenteredBellFourProduct N K =
      (fun p ↦ ellOne p ^ 4) +
      (6 : ℝ) • (fun p ↦ ellOne p ^ 2 * ellTwo p) +
      (3 : ℝ) • (fun p ↦ ellTwo p ^ 2) +
      (4 : ℝ) • (fun p ↦ ellOne p * ellThree p) + ellFour := by
    funext p
    simp only [concreteCenteredBellFourProduct, densityBellFour,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, ellOne, ellTwo, ellThree,
      ellFour]
    ring
  rw [hpoint]
  exact ((((centeredLogScore_oneFourth_memLp_one_proved_A1A2A3A4 hN hgap).add
      ((centeredLogScore_oneSquareTwo_memLp_one_internal hN hgap).const_smul
        (6 : ℝ))).add
      (((centeredLogScore_twoSquare_momentPackage_proved_A1A2A3
        hN hgap).1).const_smul
        (3 : ℝ))).add
      (((centeredLogScore_oneThree_momentPackage_proved_A1A2A3A4
        hN hgap).1).const_smul
        (4 : ℝ))).add
      (centeredLogScore_four_momentPackage_proved_A1A2A3A4 hN hgap).1

/-- The literal fourth density score equals the integrable Bell polynomial
almost everywhere on the COE/projective product. -/
theorem concreteCenteredDensityScoreFourProduct_ae_eq_Bell_of_gap
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    (fun Av : ConcreteMatrixState N × ComplexUnitSphere N ↦
      concreteCenteredDensityScore 4 N K Av.2 Av.1) =ᵐ[
        concreteCenteredScoreProductLaw N K]
      concreteCenteredBellFourProduct N K := by
  have hsupportA :=
    friedmanMello1985_scaledCOECorner_ae_support_from_density
      hN (by omega : 2 * N ≤ K)
  have hsupport : ∀ᵐ Av ∂(concreteCenteredScoreProductLaw N K),
      (unscaleCOECorner K Av.1).IsSymm ∧
        coeCornerSupport (unscaleCOECorner K Av.1) :=
    Measure.quasiMeasurePreserving_fst.ae hsupportA
  filter_upwards [hsupport] with Av hAv
  rcases hAv with ⟨hsymm, hsupp⟩
  simpa [concreteCenteredBellFourProduct, concreteCenteredEll] using
    coeCorner_centeredDensityScore_four_eq_Bell_external_derived
      hN hgap Av.2 Av.1 hsymm hsupp

/-- Literal fourth-score product integrability at `K ≥ 2N+8`. -/
theorem concreteCenteredDensityScoreFourProduct_memLp_one_of_gap
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp
      (fun Av : ConcreteMatrixState N × ComplexUnitSphere N ↦
        concreteCenteredDensityScore 4 N K Av.2 Av.1) 1
      (concreteCenteredScoreProductLaw N K) := by
  exact (memLp_congr_ae
    (concreteCenteredDensityScoreFourProduct_ae_eq_Bell_of_gap hN hgap)).2
      (concreteCenteredBellFourProduct_memLp_one_of_gap hN hgap)

/-- Fourth-order event-indicator Fubini, derived rather than assumed. -/
theorem coeCorner_centeredDensityScore_four_fubini
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (event : Set (ConcreteMatrixState N)) (hevent : MeasurableSet event) :
    (∫ v : ComplexUnitSphere N,
      ∫ A, event.indicator (concreteCenteredDensityScore 4 N K v) A
        ∂(concreteScaledCOECornerLaw
          LogdetLean.GramHafnian.LocalAnticoncentration.canonicalUnitaryHaarProbabilityFamily
            N K)
      ∂(complexUnitSphereProbabilityMeasure N)) =
    ∫ A, event.indicator (fun A ↦
      ∫ v : ComplexUnitSphere N, concreteCenteredDensityScore 4 N K v A
        ∂(complexUnitSphereProbabilityMeasure N)) A
      ∂(concreteScaledCOECornerLaw
        LogdetLean.GramHafnian.LocalAnticoncentration.canonicalUnitaryHaarProbabilityFamily
          N K) := by
  have hNK : N ≤ K := by omega
  exact coeCorner_centeredDensityScore_fubini_of_memLp hN hNK event hevent
    (by
      simpa [concreteCenteredScoreProductLaw] using
        concreteCenteredDensityScoreFourProduct_memLp_one_of_gap hN hgap)

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
