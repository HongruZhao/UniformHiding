import LogdetLean.GramHafnian.UltimateHiding.Basic

/-!
# All-regime stitch for the sharpened hiding rate

This file contains only the exact finite case split for the proposed theorem
`d_TV <= min {1, C N^2/M}`.  The sparse and dense analytic branches remain
explicit arguments until their concrete probability proofs are supplied.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding

noncomputable section

open LocalAnticoncentration

/-- Nontrivial large-ambient dense branch at the sharpened rate. -/
def LargeAmbientDenseSquaredBranchAt (C : ℝ) (kappa : ℕ) : Prop :=
  ∀ (H : UnitaryHaarProbabilityFamily) (M N K : ℕ),
    1 <= N -> N <= K -> K <= M -> N ^ 2 <= M -> kappa * N <= K ->
    probabilityTotalVariationLE
      (scaledHaarTransposeGramLaw H M N K)
      (gaussianTransposeGramLaw N K)
      (min 1 (C * ultimateSquaredHidingRate M N))

/-- Nontrivial large-ambient bounded-aspect branch at the sharpened rate. -/
def LargeAmbientSparseSquaredBranchAt (C : ℝ) (kappa : ℕ) : Prop :=
  ∀ (H : UnitaryHaarProbabilityFamily) (M N K : ℕ),
    1 <= N -> N <= K -> K <= M -> N ^ 2 <= M -> K < kappa * N ->
    probabilityTotalVariationLE
      (scaledHaarTransposeGramLaw H M N K)
      (gaussianTransposeGramLaw N K)
      (min 1 (C * ultimateSquaredHidingRate M N))

theorem one_le_ultimateSquaredHidingRate_of_le_sq
    {M N : ℕ} (hM : 1 <= M) (hMN : M <= N ^ 2) :
    1 <= ultimateSquaredHidingRate M N := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hMN' : (M : ℝ) <= (N : ℝ) ^ 2 := by exact_mod_cast hMN
  rw [ultimateSquaredHidingRate]
  exact (le_div_iff₀ hMR).2 (by simpa using hMN')

theorem min_one_mul_ultimateSquaredHidingRate_eq_one_of_le_sq
    {C : ℝ} (hC : 1 <= C) {M N : ℕ}
    (hM : 1 <= M) (hMN : M <= N ^ 2) :
    min 1 (C * ultimateSquaredHidingRate M N) = 1 := by
  have hrate := one_le_ultimateSquaredHidingRate_of_le_sq hM hMN
  have hrate0 := ultimateSquaredHidingRate_nonneg M N
  have hone : 1 <= C * ultimateSquaredHidingRate M N := by
    calc
      1 <= 1 * ultimateSquaredHidingRate M N := by simpa using hrate
      _ <= C * ultimateSquaredHidingRate M N :=
        mul_le_mul_of_nonneg_right hC hrate0
  exact min_eq_left hone

/-- Once the two genuine large-ambient analytic branches are proved with a
common coefficient `C >= 1`, the small-ambient range follows from the automatic
probability bound one. -/
theorem uniformProductMatrixHidingSquaredAt_of_largeAmbientBranches
    {C : ℝ} (hC : 1 <= C) (kappa : ℕ)
    (hdense : LargeAmbientDenseSquaredBranchAt C kappa)
    (hsparse : LargeAmbientSparseSquaredBranchAt C kappa) :
    UniformProductMatrixHidingSquaredAt C := by
  refine ⟨(by linarith), ?_⟩
  intro H M N K hN hNK hKM
  by_cases hlarge : N ^ 2 <= M
  · by_cases hd : kappa * N <= K
    · exact hdense H M N K hN hNK hKM hlarge hd
    · exact hsparse H M N K hN hNK hKM hlarge (Nat.lt_of_not_ge hd)
  · have hM : 1 <= M := by omega
    have hsmall : M <= N ^ 2 := by omega
    letI : IsProbabilityMeasure (scaledHaarTransposeGramLaw H M N K) :=
      scaledHaarTransposeGramLaw_isProbability H (hNK.trans hKM) hKM
    rw [min_one_mul_ultimateSquaredHidingRate_eq_one_of_le_sq hC hM hsmall]
    exact probabilityTotalVariationLE_one _ _

theorem uniformProductMatrixHidingSquared_of_largeAmbientBranches
    {C : ℝ} (hC : 1 <= C) (kappa : ℕ)
    (hdense : LargeAmbientDenseSquaredBranchAt C kappa)
    (hsparse : LargeAmbientSparseSquaredBranchAt C kappa) :
    UniformProductMatrixHidingSquared :=
  ⟨C, uniformProductMatrixHidingSquaredAt_of_largeAmbientBranches
    hC kappa hdense hsparse⟩

end

end LogdetLean.GramHafnian.UltimateHiding
