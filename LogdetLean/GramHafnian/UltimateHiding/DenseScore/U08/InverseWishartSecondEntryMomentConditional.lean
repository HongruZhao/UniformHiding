import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.InverseWishartEntryProductIntegrability
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.InverseWishartSecondMomentLedger
import Mathlib.Tactic

/-!
# CONDITIONAL inverse-Wishart second-entry moment contract

This module gives the smallest remaining analytic input needed to identify
the already kernel-checked second-moment ledger with the literal Gaussian
denominator law.  It declares no axiom: consumers receive the formula as an
explicit theorem parameter.

For `p=N`, `nu=K-N`, and `c=nu-p-1=K-2N-1`, the normalization is the
variance-one real Wishart law and `C=c B^{-1}`.  The formula below is the
order-two entry identity; order-four *existence* has already been proved in
`InverseWishartEntryProductIntegrability` at `2*N+8 <= K`.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08

noncomputable section

open LogdetLean.GramHafnian.Wishart

/-- Real-valued Kronecker delta used in the entry-moment tensor. -/
def realKroneckerDelta {alpha : Type*} [DecidableEq alpha]
    (i j : alpha) : ℝ :=
  if i = j then 1 else 0

@[simp]
theorem realKroneckerDelta_self {alpha : Type*} [DecidableEq alpha]
    (i : alpha) : realKroneckerDelta i i = 1 := by
  simp [realKroneckerDelta]

@[simp]
theorem realKroneckerDelta_mul_swap {alpha : Type*} [DecidableEq alpha]
    (i j : alpha) :
    realKroneckerDelta i j * realKroneckerDelta j i =
      realKroneckerDelta i j := by
  by_cases h : i = j
  · subst j
    simp
  · have h' : j ≠ i := fun hji ↦ h hji.symm
    simp [realKroneckerDelta, h, h']

@[simp]
theorem realKroneckerDelta_sq {alpha : Type*} [DecidableEq alpha]
    (i j : alpha) :
    realKroneckerDelta i j * realKroneckerDelta i j =
      realKroneckerDelta i j := by
  by_cases h : i = j <;> simp [realKroneckerDelta, h]

@[simp]
theorem sum_realKroneckerDelta_left {N : ℕ} (i : Fin N) :
    ∑ j : Fin N, realKroneckerDelta i j = 1 := by
  simp [realKroneckerDelta]

@[simp]
theorem sum_realKroneckerDelta_right {N : ℕ} (i : Fin N) :
    ∑ j : Fin N, realKroneckerDelta j i = 1 := by
  simp [realKroneckerDelta]

/-- Finite contraction of an affine Kronecker-delta row. -/
theorem sum_affine_realKroneckerDelta {N : ℕ} (i : Fin N) (a b : ℝ) :
    (∑ j : Fin N, (a + b * realKroneckerDelta i j)) =
      (N : ℝ) * a + b := by
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
    Finset.card_univ, Fintype.card_fin, ← Finset.mul_sum,
    sum_realKroneckerDelta_left]
  ring

/-- The denominator-only scaled inverse-Wishart matrix `C=c(HᵀH)^{-1}`. -/
def scaledInverseWishartMatrix (N K : ℕ)
    (H : Matrix (Fin (K - N)) (Fin N) ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  concreteCOEExponent N K • (realWishartGram H)⁻¹

/-- **CONDITIONAL scientific input.** Exact second product of entries of
`C=c(HᵀH)^{-1}` under the literal variance-one Gaussian matrix law.

This is strictly smaller than H8, H10, H12, or H14: it is a single
denominator-only tensor identity and contains no score or centered-moment
conclusion. -/
structure ScaledInverseWishartSecondEntryMomentFormula
    (N K : ℕ) : Prop where
  entry_product_integral_eq : ∀ i j k l : Fin N,
    (∫ H,
        scaledInverseWishartMatrix N K H i j *
          scaledInverseWishartMatrix N K H k l
      ∂(standardRealGaussianMatrixMeasure (K - N) N)) =
      (concreteCOEExponent N K * (concreteCOEExponent N K - 1) *
            realKroneckerDelta i j * realKroneckerDelta k l +
          concreteCOEExponent N K *
            (realKroneckerDelta i k * realKroneckerDelta j l +
              realKroneckerDelta i l * realKroneckerDelta j k)) /
        inverseWishartSecondMomentDenominator
          (concreteCOEExponent N K)

/-- Global form of the same lower-level contract in the exact qualitative
H8/H10 range. -/
abbrev ScaledInverseWishartSecondEntryMomentContract : Prop :=
  ∀ {N K : ℕ}, 1 ≤ N → 2 * N + 8 ≤ K →
    ScaledInverseWishartSecondEntryMomentFormula N K

/-- The exact qualitative threshold implies `c >= 7`, hence the displayed
second-moment denominator is strictly positive. -/
theorem inverseWishartSecondMomentDenominator_pos_of_gap
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K) :
    0 < inverseWishartSecondMomentDenominator
      (concreteCOEExponent N K) := by
  have hgapR : ((2 * N + 8 : ℕ) : ℝ) ≤ (K : ℝ) := by
    exact_mod_cast hgap
  push_cast at hgapR
  unfold inverseWishartSecondMomentDenominator concreteCOEExponent
  nlinarith

/-- In the dense regime, the scaled inverse-Wishart parameter satisfies the
ledger inequality `13N <= c`. -/
theorem thirteen_mul_dimension_le_concreteCOEExponent_of_dense
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    13 * (N : ℝ) ≤ concreteCOEExponent N K := by
  have hdenseR : ((16 * N : ℕ) : ℝ) ≤ (K : ℝ) := by
    exact_mod_cast hdense
  have hNreal : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  push_cast at hdenseR
  unfold concreteCOEExponent
  linarith

/-! ## Axiom-free contractions of the conditional tensor formula -/

/-- Integrability of a product of two entries of the scaled denominator;
this is already unconditional at the stronger order-four threshold. -/
theorem integrable_scaledInverseWishartMatrix_entry_mul_entry
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K) (i j k l : Fin N) :
    Integrable
      (fun H : Matrix (Fin (K - N)) (Fin N) ℝ ↦
        scaledInverseWishartMatrix N K H i j *
          scaledInverseWishartMatrix N K H k l)
      (standardRealGaussianMatrixMeasure (K - N) N) := by
  let indices : Fin 2 → Fin N × Fin N := ![(i, j), (k, l)]
  have h := integrable_betaPrimeDenominator_inverseEntryProduct_order_le_four
    hgap (by norm_num) indices
  have hscaled := h.const_mul (concreteCOEExponent N K ^ 2)
  simpa [scaledInverseWishartMatrix, indices, inverseWishartEntryProduct,
    pow_two, smul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using hscaled

/-- Contracting the conditional entry tensor gives the exact denominator
mean `E tr(C^2)` already recorded by the ledger. -/
theorem scaledInverseWishartTraceTwo_integral_eq_ledger_conditional
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K)
    (Hmom : ScaledInverseWishartSecondEntryMomentFormula N K) :
    (∫ H, Matrix.trace ((scaledInverseWishartMatrix N K H) ^ 2)
      ∂(standardRealGaussianMatrixMeasure (K - N) N)) =
      scaledInverseWishartTraceTwoMeanLedger (N : ℝ)
        (concreteCOEExponent N K) := by
  simp only [Matrix.trace, Matrix.diag_apply, pow_two, Matrix.mul_apply]
  have hrow (i : Fin N) :
      (∫ H, ∑ j : Fin N,
          scaledInverseWishartMatrix N K H i j *
            scaledInverseWishartMatrix N K H j i
        ∂(standardRealGaussianMatrixMeasure (K - N) N)) =
        (concreteCOEExponent N K ^ 2 +
            (N : ℝ) * concreteCOEExponent N K) /
          inverseWishartSecondMomentDenominator
            (concreteCOEExponent N K) := by
    rw [integral_finset_sum]
    · calc
        ∑ j : Fin N, ∫ H,
            scaledInverseWishartMatrix N K H i j *
              scaledInverseWishartMatrix N K H j i
            ∂(standardRealGaussianMatrixMeasure (K - N) N) =
            ∑ j : Fin N,
              (concreteCOEExponent N K *
                    (concreteCOEExponent N K - 1) *
                    realKroneckerDelta i j * realKroneckerDelta j i +
                  concreteCOEExponent N K *
                    (realKroneckerDelta i j * realKroneckerDelta j i +
                      realKroneckerDelta i i * realKroneckerDelta j j)) /
                inverseWishartSecondMomentDenominator
                  (concreteCOEExponent N K) :=
          Finset.sum_congr rfl fun j _ ↦
            Hmom.entry_product_integral_eq i j j i
        _ = ∑ j : Fin N,
              (concreteCOEExponent N K ^ 2 * realKroneckerDelta i j +
                  concreteCOEExponent N K) /
                inverseWishartSecondMomentDenominator
                  (concreteCOEExponent N K) := by
          apply Finset.sum_congr rfl
          intro j hj
          by_cases hij : i = j
          · subst j
            simp
            ring
          · have hji : j ≠ i := fun h ↦ hij h.symm
            simp [realKroneckerDelta, hij, hji]
        _ = _ := by
          calc
            ∑ j : Fin N,
                (concreteCOEExponent N K ^ 2 * realKroneckerDelta i j +
                    concreteCOEExponent N K) /
                  inverseWishartSecondMomentDenominator
                    (concreteCOEExponent N K) =
                ∑ j : Fin N,
                  (concreteCOEExponent N K *
                        (inverseWishartSecondMomentDenominator
                          (concreteCOEExponent N K))⁻¹ +
                    (concreteCOEExponent N K ^ 2 *
                        (inverseWishartSecondMomentDenominator
                          (concreteCOEExponent N K))⁻¹) *
                      realKroneckerDelta i j) := by
              apply Finset.sum_congr rfl
              intro j hj
              simp only [div_eq_mul_inv]
              ring
            _ = (N : ℝ) *
                    (concreteCOEExponent N K *
                      (inverseWishartSecondMomentDenominator
                        (concreteCOEExponent N K))⁻¹) +
                  concreteCOEExponent N K ^ 2 *
                    (inverseWishartSecondMomentDenominator
                      (concreteCOEExponent N K))⁻¹ :=
              sum_affine_realKroneckerDelta i _ _
            _ = _ := by
              simp only [div_eq_mul_inv]
              ring
    · intro j hj
      exact integrable_scaledInverseWishartMatrix_entry_mul_entry hgap i j j i
  rw [integral_finset_sum]
  · simp_rw [hrow]
    simp [scaledInverseWishartTraceTwoMeanLedger]
    ring
  · intro i hi
    exact integrable_finsetSum Finset.univ fun j _ ↦
      integrable_scaledInverseWishartMatrix_entry_mul_entry hgap i j j i

/-- The second contraction gives the exact denominator mean
`E (tr C)^2`. -/
theorem scaledInverseWishartTraceOneSquare_integral_eq_ledger_conditional
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K)
    (Hmom : ScaledInverseWishartSecondEntryMomentFormula N K) :
    (∫ H, Matrix.trace (scaledInverseWishartMatrix N K H) ^ 2
      ∂(standardRealGaussianMatrixMeasure (K - N) N)) =
      scaledInverseWishartTraceOneSquareMeanLedger (N : ℝ)
        (concreteCOEExponent N K) := by
  rw [show (fun H ↦ Matrix.trace (scaledInverseWishartMatrix N K H) ^ 2) =
      (fun H ↦ ∑ i : Fin N, ∑ j : Fin N,
        scaledInverseWishartMatrix N K H i i *
          scaledInverseWishartMatrix N K H j j) by
    funext H
    simp only [Matrix.trace, Matrix.diag_apply, pow_two]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]]
  have hrow (i : Fin N) :
      (∫ H, ∑ j : Fin N,
          scaledInverseWishartMatrix N K H i i *
            scaledInverseWishartMatrix N K H j j
        ∂(standardRealGaussianMatrixMeasure (K - N) N)) =
        ((N : ℝ) * concreteCOEExponent N K *
              (concreteCOEExponent N K - 1) +
            2 * concreteCOEExponent N K) /
          inverseWishartSecondMomentDenominator
            (concreteCOEExponent N K) := by
    rw [integral_finset_sum]
    · calc
        ∑ j : Fin N, ∫ H,
            scaledInverseWishartMatrix N K H i i *
              scaledInverseWishartMatrix N K H j j
            ∂(standardRealGaussianMatrixMeasure (K - N) N) =
            ∑ j : Fin N,
              (concreteCOEExponent N K *
                    (concreteCOEExponent N K - 1) *
                    realKroneckerDelta i i * realKroneckerDelta j j +
                  concreteCOEExponent N K *
                    (realKroneckerDelta i j * realKroneckerDelta i j +
                      realKroneckerDelta i j * realKroneckerDelta i j)) /
                inverseWishartSecondMomentDenominator
                  (concreteCOEExponent N K) :=
          Finset.sum_congr rfl fun j _ ↦
            Hmom.entry_product_integral_eq i i j j
        _ = ∑ j : Fin N,
              (concreteCOEExponent N K *
                    (concreteCOEExponent N K - 1) +
                  2 * concreteCOEExponent N K *
                    realKroneckerDelta i j) /
                inverseWishartSecondMomentDenominator
                  (concreteCOEExponent N K) := by
          apply Finset.sum_congr rfl
          intro j hj
          by_cases hij : i = j
          · subst j
            simp
            ring
          · simp [realKroneckerDelta, hij]
        _ = _ := by
          calc
            ∑ j : Fin N,
                (concreteCOEExponent N K *
                      (concreteCOEExponent N K - 1) +
                    2 * concreteCOEExponent N K *
                      realKroneckerDelta i j) /
                  inverseWishartSecondMomentDenominator
                    (concreteCOEExponent N K) =
                ∑ j : Fin N,
                  (concreteCOEExponent N K *
                        (concreteCOEExponent N K - 1) *
                        (inverseWishartSecondMomentDenominator
                          (concreteCOEExponent N K))⁻¹ +
                    (2 * concreteCOEExponent N K *
                        (inverseWishartSecondMomentDenominator
                          (concreteCOEExponent N K))⁻¹) *
                      realKroneckerDelta i j) := by
              apply Finset.sum_congr rfl
              intro j hj
              simp only [div_eq_mul_inv]
              ring
            _ = (N : ℝ) *
                    (concreteCOEExponent N K *
                      (concreteCOEExponent N K - 1) *
                      (inverseWishartSecondMomentDenominator
                        (concreteCOEExponent N K))⁻¹) +
                  2 * concreteCOEExponent N K *
                    (inverseWishartSecondMomentDenominator
                      (concreteCOEExponent N K))⁻¹ :=
              sum_affine_realKroneckerDelta i _ _
            _ = _ := by
              simp only [div_eq_mul_inv]
              ring
    · intro j hj
      exact integrable_scaledInverseWishartMatrix_entry_mul_entry hgap i i j j
  rw [integral_finset_sum]
  · simp_rw [hrow]
    simp [scaledInverseWishartTraceOneSquareMeanLedger]
    ring
  · intro i hi
    exact integrable_finsetSum Finset.univ fun j _ ↦
      integrable_scaledInverseWishartMatrix_entry_mul_entry hgap i i j j

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08
