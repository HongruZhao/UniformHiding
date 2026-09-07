import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H14_ExactMomentClosure
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CenteredLogScoreOneSquareTwoDerived
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H12_ExactMomentEndpointA4
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H13_OneThreeRelaxedProjectiveClosure
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H11_FourthMomentClosureA1A4
import LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep.ProjectiveCenteredPathAt
import Mathlib.Tactic

/-!
# Exact downstream fourth-score rewire

This module reassembles the downstream Bell-score path from the proved
A1--A4 moment packages.  The canonical consumer uses the exact H11, H12, H13,
and H14 endpoints and therefore no longer depends on their historical moment
declarations.
-/

open MeasureTheory Filter Set

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep

/-- The mixed first/second moment package, now derived from the exact H14
second-square package. -/
theorem centeredLogScore_oneSquareTwo_momentPackage_proved_A1A2A3
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (fun p ↦ concreteCenteredEll 1 N K p ^ 2 *
      concreteCenteredEll 2 N K p) 1
        (concreteCenteredScoreProductLaw N K) ∧
      (16 * N ≤ K →
        lpNorm (fun p ↦ concreteCenteredEll 1 N K p ^ 2 *
          concreteCenteredEll 2 N K p) 1
            (concreteCenteredScoreProductLaw N K) ≤
          centeredLogScoreFourthMomentConstant * (N : ℝ) ^ 2) :=
  centeredLogScore_oneSquareTwo_momentPackage_of_twoSquare hN hgap
    (centeredLogScore_twoSquare_momentPackage_proved_A1A2A3 hN hgap)

/-- The same mixed package rebuilt from the exact H12 and H14 packages, so it
uses only A1--A4 rather than the legacy H12 declaration. -/
theorem centeredLogScore_oneSquareTwo_momentPackage_proved_A1A2A3A4
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (fun p ↦ concreteCenteredEll 1 N K p ^ 2 *
      concreteCenteredEll 2 N K p) 1
        (concreteCenteredScoreProductLaw N K) ∧
      (16 * N ≤ K →
        lpNorm (fun p ↦ concreteCenteredEll 1 N K p ^ 2 *
          concreteCenteredEll 2 N K p) 1
            (concreteCenteredScoreProductLaw N K) ≤
          centeredLogScoreFourthMomentConstant * (N : ℝ) ^ 2) := by
  let μ := concreteCenteredScoreProductLaw N K
  let f : ConcreteMatrixState N × ComplexUnitSphere N → ℝ :=
    fun p => concreteCenteredEll 1 N K p ^ 4
  let g : ConcreteMatrixState N × ComplexUnitSphere N → ℝ :=
    fun p => concreteCenteredEll 2 N K p ^ 2
  let mixed : ConcreteMatrixState N × ComplexUnitSphere N → ℝ :=
    fun p => concreteCenteredEll 1 N K p ^ 2 *
      concreteCenteredEll 2 N K p
  let majorant : ConcreteMatrixState N × ComplexUnitSphere N → ℝ :=
    (1 / 2 : ℝ) • f + (1 / 2 : ℝ) • g
  have hOne :=
    centeredLogScore_oneFourth_momentPackage_proved_A1A2A3A4 hN hgap
  have hTwo :=
    centeredLogScore_twoSquare_momentPackage_proved_A1A2A3 hN hgap
  have hf : MemLp f 1 μ := hOne.1
  have hg : MemLp g 1 μ := hTwo.1
  have hmajorant : MemLp majorant 1 μ := by
    exact (hf.const_smul (1 / 2 : ℝ)).add
      (hg.const_smul (1 / 2 : ℝ))
  have hmixedMeas : AEStronglyMeasurable mixed μ := by
    have hOneMeas := measurable_concreteCenteredEll_one (N := N) (K := K) hN
    have hTwoMeas := measurable_concreteCenteredEll_two (N := N) (K := K) hN
    exact ((hOneMeas.pow_const 2).mul hTwoMeas).aestronglyMeasurable
  have hYoung : ∀ p, ‖mixed p‖ ≤ majorant p := by
    intro p
    simp only [mixed, majorant, f, g, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg
      (sq_nonneg (concreteCenteredEll 1 N K p))]
    nlinarith [sq_nonneg
      (concreteCenteredEll 1 N K p ^ 2 -
        |concreteCenteredEll 2 N K p|),
      sq_abs (concreteCenteredEll 2 N K p)]
  have hMajorantNonneg : ∀ p, 0 ≤ majorant p := by
    intro p
    simp only [majorant, f, g, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    positivity
  have hYoungNorm : ∀ p, ‖mixed p‖ ≤ ‖majorant p‖ := by
    intro p
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hMajorantNonneg p)] using
      hYoung p
  have hmixed : MemLp mixed 1 μ :=
    hmajorant.of_le hmixedMeas (Eventually.of_forall hYoungNorm)
  constructor
  · exact hmixed
  · intro hdense
    have hfBound : lpNorm f 1 μ ≤
        centeredLogScoreFourthMomentConstant * (N : ℝ) ^ 2 :=
      hOne.2 hdense
    have hgBound : lpNorm g 1 μ ≤
        centeredLogScoreFourthMomentConstant * (N : ℝ) ^ 2 :=
      hTwo.2 hdense
    have hmono : lpNorm mixed 1 μ ≤ lpNorm majorant 1 μ :=
      lpNorm_mono_real hmajorant hYoung
    have hadd : lpNorm majorant 1 μ ≤
        lpNorm ((1 / 2 : ℝ) • f) 1 μ +
          lpNorm ((1 / 2 : ℝ) • g) 1 μ := by
      exact lpNorm_add_le (hf.const_smul (1 / 2 : ℝ)) (by norm_num)
    have hscaleF : lpNorm ((1 / 2 : ℝ) • f) 1 μ =
        (1 / 2 : ℝ) * lpNorm f 1 μ := by
      rw [lpNorm_const_smul]
      norm_num
    have hscaleG : lpNorm ((1 / 2 : ℝ) • g) 1 μ =
        (1 / 2 : ℝ) * lpNorm g 1 μ := by
      rw [lpNorm_const_smul]
      norm_num
    change lpNorm mixed 1 μ ≤ _
    calc
      lpNorm mixed 1 μ ≤ lpNorm majorant 1 μ := hmono
      _ ≤ lpNorm ((1 / 2 : ℝ) • f) 1 μ +
          lpNorm ((1 / 2 : ℝ) • g) 1 μ := hadd
      _ = (1 / 2 : ℝ) * lpNorm f 1 μ +
          (1 / 2 : ℝ) * lpNorm g 1 μ := by rw [hscaleF, hscaleG]
      _ ≤ centeredLogScoreFourthMomentConstant * (N : ℝ) ^ 2 := by
        nlinarith

/-- The five-field fourth-log-score bundle assembled entirely from the proved
H11--H14 moment endpoints. -/
theorem concreteCenteredFourthLogScoreProductMoments_H14Rewire
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    FourthLogScoreProductMoments
      (concreteCenteredScoreProductLaw N K)
      (N : ℝ)
      centeredLogScoreFourthMomentConstant
      centeredLogScoreFourthMomentConstant
      centeredLogScoreFourthMomentConstant
      centeredLogScoreFourthMomentConstant
      centeredLogScoreFourthMomentConstant
      (concreteCenteredEll 1 N K)
      (concreteCenteredEll 2 N K)
      (concreteCenteredEll 3 N K)
      (concreteCenteredEll 4 N K) := by
  have hgap : 2 * N + 8 ≤ K := by omega
  exact
    { oneFourth_memLp :=
        centeredLogScore_oneFourth_memLp_one_proved_A1A2A3A4 hN hgap
      oneSquareTwo_memLp :=
        (centeredLogScore_oneSquareTwo_momentPackage_proved_A1A2A3A4
          hN hgap).1
      twoSquare_memLp :=
        centeredLogScore_twoSquare_memLp_one_proved_A1A2A3 hN hgap
      oneThree_memLp :=
        (centeredLogScore_oneThree_momentPackage_proved_A1A2A3A4
          hN hgap).1
      four_memLp :=
        (centeredLogScore_four_momentPackage_proved_A1A2A3A4
          hN hgap).1
      oneFourth_lpNorm_le :=
        centeredLogScore_oneFourth_lpNorm_one_le_proved_A1A2A3A4 hN hdense
      oneSquareTwo_lpNorm_le :=
        (centeredLogScore_oneSquareTwo_momentPackage_proved_A1A2A3A4
          hN hgap).2 hdense
      twoSquare_lpNorm_le :=
        centeredLogScore_twoSquare_lpNorm_one_le_proved_A1A2A3 hN hdense
      oneThree_lpNorm_le :=
        (centeredLogScore_oneThree_momentPackage_proved_A1A2A3A4
          hN hgap).2 hdense
      four_lpNorm_le :=
        (centeredLogScore_four_momentPackage_proved_A1A2A3A4
          hN hgap).2 hdense }

/-- H14-exact `L^1` closure for the literal Bell-four product. -/
theorem concreteCenteredBellFourProduct_memLp_one_H14Rewire
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    MemLp (concreteCenteredBellFourProduct N K) 1
      (concreteCenteredScoreProductLaw N K) := by
  let ellOne := concreteCenteredEll 1 N K
  let ellTwo := concreteCenteredEll 2 N K
  let ellThree := concreteCenteredEll 3 N K
  let ellFour := concreteCenteredEll 4 N K
  have H := concreteCenteredFourthLogScoreProductMoments_H14Rewire hN hdense
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
  exact ((((H.oneFourth_memLp.add
      (H.oneSquareTwo_memLp.const_smul (6 : ℝ))).add
      (H.twoSquare_memLp.const_smul (3 : ℝ))).add
      (H.oneThree_memLp.const_smul (4 : ℝ))).add H.four_memLp)

/-- H14-exact `O(N^2)` norm closure for the literal Bell-four product. -/
theorem concreteCenteredBellFourProduct_lpNorm_one_le_H14Rewire
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (concreteCenteredBellFourProduct N K) 1
        (concreteCenteredScoreProductLaw N K) ≤
      concreteCenteredScoreFourConstant * (N : ℝ) ^ 2 := by
  have H := concreteCenteredFourthLogScoreProductMoments_H14Rewire hN hdense
  have h := H.bellFour_lpNorm_one_le
  change lpNorm (fun p ↦ densityBellFour
      (concreteCenteredEll 1 N K p)
      (concreteCenteredEll 2 N K p)
      (concreteCenteredEll 3 N K p)
      (concreteCenteredEll 4 N K p)) 1
        (concreteCenteredScoreProductLaw N K) ≤ _
  calc
    _ ≤ (centeredLogScoreFourthMomentConstant +
          6 * centeredLogScoreFourthMomentConstant +
          3 * centeredLogScoreFourthMomentConstant +
          4 * centeredLogScoreFourthMomentConstant +
          centeredLogScoreFourthMomentConstant) * (N : ℝ) ^ 2 := h
    _ = concreteCenteredScoreFourConstant * (N : ℝ) ^ 2 := by
      unfold concreteCenteredScoreFourConstant
      ring

/-- H14-exact product-`L^1` closure for the literal fourth density score. -/
theorem concreteCenteredDensityScoreFourProduct_memLp_one_H14Rewire
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    MemLp
      (fun Av : ConcreteMatrixState N × ComplexUnitSphere N ↦
        concreteCenteredDensityScore 4 N K Av.2 Av.1) 1
      (concreteCenteredScoreProductLaw N K) := by
  exact (memLp_congr_ae
    (concreteCenteredDensityScoreFourProduct_ae_eq_Bell hN hdense)).2
      (concreteCenteredBellFourProduct_memLp_one_H14Rewire hN hdense)

/-- H14-exact `O(N^2)` bound for the literal fourth density score. -/
theorem concreteCenteredDensityScoreFourProduct_lpNorm_one_le_H14Rewire
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm
        (fun Av : ConcreteMatrixState N × ComplexUnitSphere N ↦
          concreteCenteredDensityScore 4 N K Av.2 Av.1) 1
        (concreteCenteredScoreProductLaw N K) ≤
      concreteCenteredScoreFourConstant * (N : ℝ) ^ 2 := by
  let score : ConcreteMatrixState N × ComplexUnitSphere N → ℝ :=
    fun Av ↦ concreteCenteredDensityScore 4 N K Av.2 Av.1
  let bell := concreteCenteredBellFourProduct N K
  let law := concreteCenteredScoreProductLaw N K
  have heq : score =ᵐ[law] bell :=
    concreteCenteredDensityScoreFourProduct_ae_eq_Bell hN hdense
  have hscore : MemLp score 1 law :=
    concreteCenteredDensityScoreFourProduct_memLp_one_H14Rewire hN hdense
  have hbell : MemLp bell 1 law :=
    concreteCenteredBellFourProduct_memLp_one_H14Rewire hN hdense
  have hnorm : lpNorm score 1 law = lpNorm bell 1 law := by
    rw [lpNorm_one_eq_integral_norm hscore.aestronglyMeasurable,
      lpNorm_one_eq_integral_norm hbell.aestronglyMeasurable]
    exact integral_congr_ae <| heq.mono fun Av hAv ↦ congrArg norm hAv
  rw [hnorm]
  exact concreteCenteredBellFourProduct_lpNorm_one_le_H14Rewire hN hdense

/-- H14-exact uniform fourth-derivative bound for the projectively averaged
centered COE event path. -/
theorem abs_iteratedDeriv_four_concreteProjectiveAveragedCenteredCOE_le_H14Rewire
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K)
    (event : Set (ConcreteMatrixState N)) (hevent : MeasurableSet event)
    (y : ℝ) :
    |iteratedDeriv 4
        (concreteProjectiveAveragedCenteredCOEEventPath N K event) y| ≤
      concreteCenteredScoreFourConstant * (N : ℝ) ^ 2 := by
  have hraw :=
    abs_coeCorner_centeredProjective_eventPath_derivative_at_le_lpNorm_one
      hN (by omega) (by omega) event hevent y
      (concreteCenteredDensityScoreFourProduct_memLp_one_H14Rewire hN hdense)
  exact hraw.trans
    (concreteCenteredDensityScoreFourProduct_lpNorm_one_le_H14Rewire
      hN hdense)

/-- H14-exact uniform fourth-derivative bound for the same-beta orbital
event path. -/
theorem abs_iteratedDeriv_four_concreteSharedBetaOrbitalEventPath_le_H14Rewire
    {m N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K)
    (q : ℝ) (event : Set (ConcreteMatrixState N))
    (hevent : MeasurableSet event) (y : ℝ) :
    |iteratedDeriv 4
        (concreteSharedBetaOrbitalEventPath m N
            (concreteScaledCOECornerLaw
              LogdetLean.GramHafnian.CurrentPRL.canonicalUnitaryHaarProbabilityFamily
                N K)
            q event) y| ≤
      concreteCenteredScoreFourConstant * (N : ℝ) ^ 2 := by
  let preevent := concreteCentralMatrixUpdate N
    (oneColumnCenteredScalarLog m N q) ⁻¹' event
  have hpre : MeasurableSet preevent :=
    (measurable_concreteCentralMatrixUpdate N _) hevent
  have hfun :
      concreteSharedBetaOrbitalEventPath m N
          (concreteScaledCOECornerLaw
            LogdetLean.GramHafnian.CurrentPRL.canonicalUnitaryHaarProbabilityFamily
              N K)
          q event =
        concreteProjectiveAveragedCenteredCOEEventPath N K preevent := by
    funext t
    exact concreteSharedBetaOrbitalEventPath_eq_projectiveCenteredCOE
        hN (by omega) q event hevent t
  rw [hfun]
  exact
    abs_iteratedDeriv_four_concreteProjectiveAveragedCenteredCOE_le_H14Rewire
      hN hdense preevent hpre y

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
