import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H14_CanonicalFourthScoreRewire
import Mathlib.Tactic

/-!
# Fourth-score consumer core for the proved H11/H13 packages

This module contains the downstream rewire independently of the still-moving
H11 and H13 producer files.  Its sole explicit input is the pair of concrete
moment packages that those files will export.  Once the no-premise H11/H13
endpoints are available, the final adapter is therefore only a structure
literal followed by the theorems below.

No legacy H11 or H13 declaration is used by any theorem in this file.
-/

open MeasureTheory Filter Set

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep

/-- The exact two fields still needed after the internal H12/H14 closures:
the mixed `ell_1 ell_3` moment and the fourth log-score moment. -/
structure ConcreteCenteredH11H13MomentPackage (N K : ℕ) : Prop where
  oneThree_memLp :
    MemLp (fun p ↦ concreteCenteredEll 1 N K p *
      concreteCenteredEll 3 N K p) 1
        (concreteCenteredScoreProductLaw N K)
  four_memLp :
    MemLp (concreteCenteredEll 4 N K) 1
      (concreteCenteredScoreProductLaw N K)
  oneThree_lpNorm_le :
    lpNorm (fun p ↦ concreteCenteredEll 1 N K p *
      concreteCenteredEll 3 N K p) 1
        (concreteCenteredScoreProductLaw N K) ≤
      centeredLogScoreFourthMomentConstant * (N : ℝ) ^ 2
  four_lpNorm_le :
    lpNorm (concreteCenteredEll 4 N K) 1
        (concreteCenteredScoreProductLaw N K) ≤
      centeredLogScoreFourthMomentConstant * (N : ℝ) ^ 2

/-- A dimension-uniform producer of the two remaining concrete packages. -/
def ConcreteCenteredH11H13MomentPackageFamily : Prop :=
  ∀ {N K : ℕ}, 1 ≤ N → 16 * N ≤ K →
    ConcreteCenteredH11H13MomentPackage N K

/-- Assemble the two-field package from the conjunction-shaped public H13 and
H11 endpoint statements. -/
theorem concreteCenteredH11H13MomentPackage_of_momentPackages
    {N K : ℕ} (hdense : 16 * N ≤ K)
    (hOneThree :
      MemLp (fun p ↦ concreteCenteredEll 1 N K p *
        concreteCenteredEll 3 N K p) 1
          (concreteCenteredScoreProductLaw N K) ∧
        (16 * N ≤ K →
          lpNorm (fun p ↦ concreteCenteredEll 1 N K p *
            concreteCenteredEll 3 N K p) 1
              (concreteCenteredScoreProductLaw N K) ≤
            centeredLogScoreFourthMomentConstant * (N : ℝ) ^ 2))
    (hFour :
      MemLp (concreteCenteredEll 4 N K) 1
          (concreteCenteredScoreProductLaw N K) ∧
        (16 * N ≤ K →
          lpNorm (concreteCenteredEll 4 N K) 1
              (concreteCenteredScoreProductLaw N K) ≤
            centeredLogScoreFourthMomentConstant * (N : ℝ) ^ 2)) :
    ConcreteCenteredH11H13MomentPackage N K :=
  { oneThree_memLp := hOneThree.1
    four_memLp := hFour.1
    oneThree_lpNorm_le := hOneThree.2 hdense
    four_lpNorm_le := hFour.2 hdense }

/-- Reassemble all five Bell-four monomial moments using the proved H12/H14
packages and an explicit H11/H13 package. -/
theorem concreteCenteredFourthLogScoreProductMoments_of_H11H13
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K)
    (H : ConcreteCenteredH11H13MomentPackage N K) :
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
        (centeredLogScore_oneFourth_momentPackage_proved_A1A2A3A4
          hN hgap).1
      oneSquareTwo_memLp :=
        (centeredLogScore_oneSquareTwo_momentPackage_proved_A1A2A3A4
          hN hgap).1
      twoSquare_memLp :=
        (centeredLogScore_twoSquare_momentPackage_proved_A1A2A3
          hN hgap).1
      oneThree_memLp := H.oneThree_memLp
      four_memLp := H.four_memLp
      oneFourth_lpNorm_le :=
        (centeredLogScore_oneFourth_momentPackage_proved_A1A2A3A4
          hN hgap).2 hdense
      oneSquareTwo_lpNorm_le :=
        (centeredLogScore_oneSquareTwo_momentPackage_proved_A1A2A3A4
          hN hgap).2 hdense
      twoSquare_lpNorm_le :=
        (centeredLogScore_twoSquare_momentPackage_proved_A1A2A3
          hN hgap).2 hdense
      oneThree_lpNorm_le := H.oneThree_lpNorm_le
      four_lpNorm_le := H.four_lpNorm_le }

/-- Bell-four product integrability after substituting explicit H11/H13
packages. -/
theorem concreteCenteredBellFourProduct_memLp_one_of_H11H13
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K)
    (H : ConcreteCenteredH11H13MomentPackage N K) :
    MemLp (concreteCenteredBellFourProduct N K) 1
      (concreteCenteredScoreProductLaw N K) := by
  let ellOne := concreteCenteredEll 1 N K
  let ellTwo := concreteCenteredEll 2 N K
  let ellThree := concreteCenteredEll 3 N K
  let ellFour := concreteCenteredEll 4 N K
  have HM := concreteCenteredFourthLogScoreProductMoments_of_H11H13
    hN hdense H
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
  exact ((((HM.oneFourth_memLp.add
      (HM.oneSquareTwo_memLp.const_smul (6 : ℝ))).add
      (HM.twoSquare_memLp.const_smul (3 : ℝ))).add
      (HM.oneThree_memLp.const_smul (4 : ℝ))).add HM.four_memLp)

/-- Bell-four `L¹` bound after substituting explicit H11/H13 packages. -/
theorem concreteCenteredBellFourProduct_lpNorm_one_le_of_H11H13
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K)
    (H : ConcreteCenteredH11H13MomentPackage N K) :
    lpNorm (concreteCenteredBellFourProduct N K) 1
        (concreteCenteredScoreProductLaw N K) ≤
      concreteCenteredScoreFourConstant * (N : ℝ) ^ 2 := by
  have HM := concreteCenteredFourthLogScoreProductMoments_of_H11H13
    hN hdense H
  have h := HM.bellFour_lpNorm_one_le
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

/-- Literal fourth density-score integrability after substituting explicit
H11/H13 packages. -/
theorem concreteCenteredDensityScoreFourProduct_memLp_one_of_H11H13
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K)
    (H : ConcreteCenteredH11H13MomentPackage N K) :
    MemLp
      (fun Av : ConcreteMatrixState N × ComplexUnitSphere N ↦
        concreteCenteredDensityScore 4 N K Av.2 Av.1) 1
      (concreteCenteredScoreProductLaw N K) := by
  exact (memLp_congr_ae
    (concreteCenteredDensityScoreFourProduct_ae_eq_Bell hN hdense)).2
      (concreteCenteredBellFourProduct_memLp_one_of_H11H13
        hN hdense H)

/-- Literal fourth density-score `L¹` bound after substituting explicit
H11/H13 packages. -/
theorem concreteCenteredDensityScoreFourProduct_lpNorm_one_le_of_H11H13
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K)
    (H : ConcreteCenteredH11H13MomentPackage N K) :
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
    concreteCenteredDensityScoreFourProduct_memLp_one_of_H11H13
      hN hdense H
  have hbell : MemLp bell 1 law :=
    concreteCenteredBellFourProduct_memLp_one_of_H11H13 hN hdense H
  have hnorm : lpNorm score 1 law = lpNorm bell 1 law := by
    rw [lpNorm_one_eq_integral_norm hscore.aestronglyMeasurable,
      lpNorm_one_eq_integral_norm hbell.aestronglyMeasurable]
    exact integral_congr_ae <| heq.mono fun Av hAv ↦ congrArg norm hAv
  rw [hnorm]
  exact concreteCenteredBellFourProduct_lpNorm_one_le_of_H11H13
    hN hdense H

/-- Uniform fourth derivative of the projectively averaged event path from
the explicit H11/H13 packages. -/
theorem abs_iteratedDeriv_four_concreteProjectiveAveragedCenteredCOE_le_of_H11H13
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K)
    (H : ConcreteCenteredH11H13MomentPackage N K)
    (event : Set (ConcreteMatrixState N)) (hevent : MeasurableSet event)
    (y : ℝ) :
    |iteratedDeriv 4
        (concreteProjectiveAveragedCenteredCOEEventPath N K event) y| ≤
      concreteCenteredScoreFourConstant * (N : ℝ) ^ 2 := by
  have hraw :=
    abs_coeCorner_centeredProjective_eventPath_derivative_at_le_lpNorm_one
      hN (by omega) (by omega) event hevent y
      (concreteCenteredDensityScoreFourProduct_memLp_one_of_H11H13
        hN hdense H)
  exact hraw.trans
    (concreteCenteredDensityScoreFourProduct_lpNorm_one_le_of_H11H13
      hN hdense H)

/-- Uniform fourth derivative of the same-beta orbital event path from the
explicit H11/H13 packages. -/
theorem abs_iteratedDeriv_four_concreteSharedBetaOrbitalEventPath_le_of_H11H13
    {m N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K)
    (H : ConcreteCenteredH11H13MomentPackage N K)
    (q : ℝ) (event : Set (ConcreteMatrixState N))
    (hevent : MeasurableSet event) (y : ℝ) :
    |iteratedDeriv 4
        (concreteSharedBetaOrbitalEventPath m N
            (concreteScaledCOECornerLaw
              LogdetLean.GramHafnian.LocalAnticoncentration.canonicalUnitaryHaarProbabilityFamily
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
            LogdetLean.GramHafnian.LocalAnticoncentration.canonicalUnitaryHaarProbabilityFamily
              N K)
          q event =
        concreteProjectiveAveragedCenteredCOEEventPath N K preevent := by
    funext t
    exact concreteSharedBetaOrbitalEventPath_eq_projectiveCenteredCOE
        hN (by omega) q event hevent t
  rw [hfun]
  exact
    abs_iteratedDeriv_four_concreteProjectiveAveragedCenteredCOE_le_of_H11H13
      hN hdense H preevent hpre y

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
