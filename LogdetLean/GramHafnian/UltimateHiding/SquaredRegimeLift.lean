import LogdetLean.GramHafnian.UltimateHiding.SquaredStitch

/-!
# Lifting the genuinely analytic regimes to the finite branches

The score proof is needed only once `M >= C0*N^2`.  Below that threshold a
coefficient `C >= C0` makes the truncated right hand side equal to one.  In
the bounded-aspect branch the same threshold also guarantees `K+N <= M`, the
dimension range of the rectangular Haar-corner density.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding

noncomputable section

open CurrentPRL

def VeryLargeDenseSquaredBranchAt (C : ℝ) (C0 kappa : ℕ) : Prop :=
  ∀ (H : UnitaryHaarProbabilityFamily) (M N K : ℕ),
    1 <= N -> N <= K -> K <= M -> C0 * N ^ 2 <= M -> kappa * N <= K ->
    probabilityTotalVariationLE
      (scaledHaarTransposeGramLaw H M N K)
      (gaussianTransposeGramLaw N K)
      (min 1 (C * ultimateSquaredHidingRate M N))

def VeryLargeSparseSquaredBranchAt (C : ℝ) (C0 kappa : ℕ) : Prop :=
  ∀ (H : UnitaryHaarProbabilityFamily) (M N K : ℕ),
    1 <= N -> N <= K -> K <= M -> C0 * N ^ 2 <= M ->
      K < kappa * N -> K + N <= M ->
    probabilityTotalVariationLE
      (scaledHaarTransposeGramLaw H M N K)
      (gaussianTransposeGramLaw N K)
      (min 1 (C * ultimateSquaredHidingRate M N))

theorem min_one_mul_ultimateSquaredHidingRate_eq_one_of_const_sq_le
    {C : ℝ} {C0 M N : ℕ} (hC : (C0 : ℝ) <= C)
    (hM : 1 <= M) (hbound : M <= C0 * N ^ 2) :
    min 1 (C * ultimateSquaredHidingRate M N) = 1 := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hboundR : (M : ℝ) <= (C0 : ℝ) * (N : ℝ) ^ 2 := by
    exact_mod_cast hbound
  have hCN : (M : ℝ) <= C * (N : ℝ) ^ 2 := by
    calc
      (M : ℝ) <= (C0 : ℝ) * (N : ℝ) ^ 2 := hboundR
      _ <= C * (N : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hC (sq_nonneg _)
  have hone : 1 <= C * ultimateSquaredHidingRate M N := by
    rw [ultimateSquaredHidingRate]
    have hone' : 1 <= (C * (N : ℝ) ^ 2) / (M : ℝ) :=
      (le_div_iff₀ hMR).2 (by simpa using hCN)
    simpa [mul_div_assoc] using hone'
  exact min_eq_left hone

theorem LargeAmbientDenseSquaredBranchAt.of_veryLarge
    {C : ℝ} {C0 kappa : ℕ} (hC : (C0 : ℝ) <= C)
    (hcore : VeryLargeDenseSquaredBranchAt C C0 kappa) :
    LargeAmbientDenseSquaredBranchAt C kappa := by
  intro H M N K hN hNK hKM _hlarge hdense
  by_cases hvery : C0 * N ^ 2 <= M
  · exact hcore H M N K hN hNK hKM hvery hdense
  · have hM : 1 <= M := by omega
    have hsmall : M <= C0 * N ^ 2 := by omega
    letI : IsProbabilityMeasure (scaledHaarTransposeGramLaw H M N K) :=
      scaledHaarTransposeGramLaw_isProbability H (hNK.trans hKM) hKM
    rw [min_one_mul_ultimateSquaredHidingRate_eq_one_of_const_sq_le
      hC hM hsmall]
    exact probabilityTotalVariationLE_one _ _

theorem boundedAspect_dimensions
    {C0 kappa M N K : ℕ} (hN : 1 <= N)
    (hC0 : kappa + 1 <= C0) (hM : C0 * N ^ 2 <= M)
    (hK : K < kappa * N) :
    K + N <= M := by
  have hNN : N <= N ^ 2 := by nlinarith
  calc
    K + N <= kappa * N + N := Nat.add_le_add_right (Nat.le_of_lt hK) N
    _ = (kappa + 1) * N := by rw [Nat.add_mul, one_mul]
    _ <= (kappa + 1) * N ^ 2 := Nat.mul_le_mul_left _ hNN
    _ <= C0 * N ^ 2 := Nat.mul_le_mul_right _ hC0
    _ <= M := hM

theorem LargeAmbientSparseSquaredBranchAt.of_veryLarge
    {C : ℝ} {C0 kappa : ℕ}
    (hC : (C0 : ℝ) <= C) (hC0 : kappa + 1 <= C0)
    (hcore : VeryLargeSparseSquaredBranchAt C C0 kappa) :
    LargeAmbientSparseSquaredBranchAt C kappa := by
  intro H M N K hN hNK hKM _hlarge hsparse
  by_cases hvery : C0 * N ^ 2 <= M
  · exact hcore H M N K hN hNK hKM hvery hsparse
      (boundedAspect_dimensions hN hC0 hvery hsparse)
  · have hM : 1 <= M := by omega
    have hsmall : M <= C0 * N ^ 2 := by omega
    letI : IsProbabilityMeasure (scaledHaarTransposeGramLaw H M N K) :=
      scaledHaarTransposeGramLaw_isProbability H (hNK.trans hKM) hKM
    rw [min_one_mul_ultimateSquaredHidingRate_eq_one_of_const_sq_le
      hC hM hsmall]
    exact probabilityTotalVariationLE_one _ _

end

end LogdetLean.GramHafnian.UltimateHiding
