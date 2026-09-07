import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CenteredLogScoreOneSquareTwoInternalClosure
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H13_OneThreeRelaxedProjectiveClosure
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H11_FourthMomentClosureA1A4
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.FourthBellMomentClosure
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CenteredFourthScoreSanity
import Mathlib.Tactic

/-!
# Concrete centered fourth Bell score

The four retained classical inputs in
`ClassicalCenteredLogScoreMomentExternal`, together with the internally
derived first-square/second mixed moment, are instantiated here in the
literal fourth Bell polynomial.  The density-score closure and its
`O(N^2)` product-law estimate are derived internally.  There is no event,
total-variation, local-step, or hiding atom in this module.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- Literal fourth Bell polynomial on the joint COE-corner/projective law. -/
def concreteCenteredBellFourProduct (N K : ℕ) :
    ConcreteMatrixState N × ComplexUnitSphere N → ℝ :=
  fun p ↦ densityBellFour
    (concreteCenteredEll 1 N K p)
    (concreteCenteredEll 2 N K p)
    (concreteCenteredEll 3 N K p)
    (concreteCenteredEll 4 N K p)

/-- Explicit constant inherited mechanically from the five monomial
budgets and the Bell coefficients `1,6,3,4,1`. -/
def concreteCenteredScoreFourConstant : ℝ :=
  15 * centeredLogScoreFourthMomentConstant

/-- The exact five-field input bundle for the internal Bell closure. -/
theorem concreteCenteredFourthLogScoreProductMoments
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
        centeredLogScore_oneSquareTwo_memLp_one_internal hN hgap
      twoSquare_memLp :=
        (centeredLogScore_twoSquare_momentPackage_proved_A1A2A3 hN hgap).1
      oneThree_memLp :=
        (centeredLogScore_oneThree_momentPackage_proved_A1A2A3A4 hN hgap).1
      four_memLp :=
        (centeredLogScore_four_momentPackage_proved_A1A2A3A4 hN hgap).1
      oneFourth_lpNorm_le :=
        centeredLogScore_oneFourth_lpNorm_one_le_proved_A1A2A3A4 hN hdense
      oneSquareTwo_lpNorm_le :=
        centeredLogScore_oneSquareTwo_lpNorm_one_le_internal hN hdense
      twoSquare_lpNorm_le :=
        (centeredLogScore_twoSquare_momentPackage_proved_A1A2A3
          hN hgap).2 hdense
      oneThree_lpNorm_le :=
        (centeredLogScore_oneThree_momentPackage_proved_A1A2A3A4
          hN hgap).2 hdense
      four_lpNorm_le :=
        (centeredLogScore_four_momentPackage_proved_A1A2A3A4
          hN hgap).2 hdense }

/-- The literal Bell-four product function belongs to `L^1`. -/
theorem concreteCenteredBellFourProduct_memLp_one
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    MemLp (concreteCenteredBellFourProduct N K) 1
      (concreteCenteredScoreProductLaw N K) := by
  let ellOne := concreteCenteredEll 1 N K
  let ellTwo := concreteCenteredEll 2 N K
  let ellThree := concreteCenteredEll 3 N K
  let ellFour := concreteCenteredEll 4 N K
  have H := concreteCenteredFourthLogScoreProductMoments hN hdense
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

/-- Internally assembled `L^1=O(N^2)` fourth Bell bound. -/
theorem concreteCenteredBellFourProduct_lpNorm_one_le
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (concreteCenteredBellFourProduct N K) 1
        (concreteCenteredScoreProductLaw N K) ≤
      concreteCenteredScoreFourConstant * (N : ℝ) ^ 2 := by
  have H := concreteCenteredFourthLogScoreProductMoments hN hdense
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

/-- The product Bell function vanishes pointwise for `N=1`; this is inherited
from the literal centered likelihood, not from a moment estimate. -/
theorem concreteCenteredBellFourProduct_fin_one_eq_zero
    (K : ℕ) (p : ConcreteMatrixState 1 × ComplexUnitSphere 1) :
    concreteCenteredBellFourProduct 1 K p = 0 := by
  exact concreteCenteredDensityBellFour_fin_one_eq_zero K p.2 p.1

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
