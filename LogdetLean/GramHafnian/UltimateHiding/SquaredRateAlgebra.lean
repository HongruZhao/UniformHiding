import LogdetLean.GramHafnian.UltimateHiding.SquaredStitch
import LogdetLean.GramHafnian.UltimateHiding.RectangularHidingRate

/-!
# Comparison of the squared and square-root hiding rates

In the only nontrivial range `N^2 <= M`, the proposed rate `N^2/M` is no
larger than the earlier endpoint rate `N/sqrt M`.  The statements below make
that comparison literal and kernel checked.
-/

namespace LogdetLean.GramHafnian.UltimateHiding

open MeasureTheory CurrentPRL

theorem ultimateSquaredHidingRate_eq_sq_ultimateHidingRate
    {M N : ℕ} (hM : 1 <= M) :
    ultimateSquaredHidingRate M N = (ultimateHidingRate M N) ^ 2 := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  rw [ultimateSquaredHidingRate, ultimateHidingRate, div_pow]
  congr 1
  exact (Real.sq_sqrt (le_of_lt hM0)).symm

theorem ultimateHidingRate_le_one_of_sq_le
    {M N : ℕ} (hM : 1 <= M) (hNM : N ^ 2 <= M) :
    ultimateHidingRate M N <= 1 := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hcast : (N : ℝ) ^ 2 <= (M : ℝ) := by exact_mod_cast hNM
  have hN_le_sqrt : (N : ℝ) <= Real.sqrt (M : ℝ) :=
    (sq_le_sq₀ (Nat.cast_nonneg N) (Real.sqrt_nonneg _)).mp <| by
      simpa [Real.sq_sqrt (le_of_lt hM0)] using hcast
  rw [ultimateHidingRate]
  exact (div_le_one (Real.sqrt_pos.2 hM0)).2 hN_le_sqrt

theorem ultimateSquaredHidingRate_le_ultimateHidingRate
    {M N : ℕ} (hM : 1 <= M) (hNM : N ^ 2 <= M) :
    ultimateSquaredHidingRate M N <= ultimateHidingRate M N := by
  rw [ultimateSquaredHidingRate_eq_sq_ultimateHidingRate hM]
  have h0 := ultimateHidingRate_nonneg M N
  have h1 := ultimateHidingRate_le_one_of_sq_le hM hNM
  nlinarith

theorem min_squaredHidingRate_le_min_hidingRate
    {C : ℝ} (hC : 0 <= C) {M N : ℕ}
    (hM : 1 <= M) (hNM : N ^ 2 <= M) :
    min 1 (C * ultimateSquaredHidingRate M N) <=
      min 1 (C * ultimateHidingRate M N) := by
  exact min_le_min_left 1 <|
    mul_le_mul_of_nonneg_left
      (ultimateSquaredHidingRate_le_ultimateHidingRate hM hNM) hC

/-- The endpoint rate `N/sqrt M` is no larger than the older rectangular
rate `sqrt(NK/M)` whenever `N <= K`. -/
theorem ultimateHidingRate_le_rectangularHidingRate
    {M N K : ℕ} (hM : 1 <= M) (hNK : N <= K) :
    ultimateHidingRate M N <= rectangularHidingRate M N K := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hNKcast : (N : ℝ) <= (K : ℝ) := by exact_mod_cast hNK
  have hleft0 := ultimateHidingRate_nonneg M N
  have hright0 : 0 <= rectangularHidingRate M N K := Real.sqrt_nonneg _
  apply (sq_le_sq₀ hleft0 hright0).mp
  rw [← ultimateSquaredHidingRate_eq_sq_ultimateHidingRate hM]
  unfold rectangularHidingRate ultimateSquaredHidingRate
  rw [Real.sq_sqrt]
  · have hMcast : (0 : ℝ) <= M := hM0.le
    have hNcast : (0 : ℝ) <= (N : ℝ) := Nat.cast_nonneg N
    have hprod : (N : ℝ) ^ 2 <= (N : ℝ) * (K : ℝ) := by
      nlinarith
    simpa only [Nat.cast_mul] using
      (div_le_div_of_nonneg_right hprod hMcast)
  · positivity

/-- After the probability truncation, the new `N^2/M` rate is uniformly no
worse than `sqrt(NK/M)` on the entire finite range `N <= K <= M`.  The
small-ambient case is exactly one on both sides; the nontrivial case uses the
two preceding rate comparisons. -/
theorem min_squaredHidingRate_le_min_rectangularHidingRate
    {C : ℝ} (hC : 1 <= C) {M N K : ℕ}
    (hM : 1 <= M) (hNK : N <= K) :
    min 1 (C * ultimateSquaredHidingRate M N) <=
      min 1 (C * rectangularHidingRate M N K) := by
  by_cases hlarge : N ^ 2 <= M
  · exact min_le_min_left 1 <| mul_le_mul_of_nonneg_left
      ((ultimateSquaredHidingRate_le_ultimateHidingRate hM hlarge).trans
        (ultimateHidingRate_le_rectangularHidingRate hM hNK))
      (by linarith)
  · have hsmall : M <= N ^ 2 := by omega
    have hleft :=
      min_one_mul_ultimateSquaredHidingRate_eq_one_of_le_sq hC hM hsmall
    have hrectOne : 1 <= C * rectangularHidingRate M N K := by
      have hsquare := one_le_ultimateSquaredHidingRate_of_le_sq hM hsmall
      rw [ultimateSquaredHidingRate_eq_sq_ultimateHidingRate hM] at hsquare
      have hbase : 1 <= ultimateHidingRate M N := by
        nlinarith [ultimateHidingRate_nonneg M N]
      have hcompare := ultimateHidingRate_le_rectangularHidingRate hM hNK
      have hrect : 1 <= rectangularHidingRate M N K := hbase.trans hcompare
      have hnonneg : 0 <= rectangularHidingRate M N K := Real.sqrt_nonneg _
      calc
        1 <= 1 * rectangularHidingRate M N K := by simpa using hrect
        _ <= C * rectangularHidingRate M N K :=
          mul_le_mul_of_nonneg_right hC hnonneg
    rw [hleft, min_eq_left hrectOne]

theorem one_le_ultimateHidingRate_of_le_sq
    {M N : ℕ} (hM : 1 <= M) (hMN : M <= N ^ 2) :
    1 <= ultimateHidingRate M N := by
  have hsq := one_le_ultimateSquaredHidingRate_of_le_sq hM hMN
  rw [ultimateSquaredHidingRate_eq_sq_ultimateHidingRate hM] at hsq
  have h0 := ultimateHidingRate_nonneg M N
  nlinarith

theorem min_one_mul_ultimateHidingRate_eq_one_of_le_sq
    {C : ℝ} (hC : 1 <= C) {M N : ℕ}
    (hM : 1 <= M) (hMN : M <= N ^ 2) :
    min 1 (C * ultimateHidingRate M N) = 1 := by
  have hrate := one_le_ultimateHidingRate_of_le_sq hM hMN
  have hrate0 := ultimateHidingRate_nonneg M N
  have hone : 1 <= C * ultimateHidingRate M N := by
    calc
      1 <= 1 * ultimateHidingRate M N := by simpa using hrate
      _ <= C * ultimateHidingRate M N :=
        mul_le_mul_of_nonneg_right hC hrate0
  exact min_eq_left hone

/-- The sharper theorem recovers the earlier square-root-rate statement with
the same constant, provided the harmless normalization `C >= 1` is made. -/
theorem UniformProductMatrixHidingSquaredAt.to_sqrtRate
    {C : ℝ} (hhide : UniformProductMatrixHidingSquaredAt C) (hC : 1 <= C) :
    UniformProductMatrixHidingAt C := by
  refine ⟨hhide.constant_nonneg, ?_⟩
  intro H M N K hN hNK hKM
  have hM : 1 <= M := by omega
  by_cases hlarge : N ^ 2 <= M
  · exact (hhide.apply H hN hNK hKM).mono
      (min_squaredHidingRate_le_min_hidingRate hhide.constant_nonneg hM hlarge)
  · have hsmall : M <= N ^ 2 := by omega
    letI : IsProbabilityMeasure (scaledHaarTransposeGramLaw H M N K) :=
      scaledHaarTransposeGramLaw_isProbability H (hNK.trans hKM) hKM
    rw [min_one_mul_ultimateHidingRate_eq_one_of_le_sq hC hM hsmall]
    exact probabilityTotalVariationLE_one _ _

end LogdetLean.GramHafnian.UltimateHiding
