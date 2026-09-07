import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H9_InverseMomentConditional
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.H14_DenominatorFourthTraceContraction
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.InverseWishartTraceFourthMoment

/-!
# R-H9-INVERSE-WISHART: exact reduction of the U08 contract

This module works only on `H9U08InverseWishartContract N K`.  The existing
U08 fourth-entry/Stein machinery proves both qualitative moment fields and
the dense `L^2` bound for `Tr(D^2)`, where

`D = (K - 2N - 1) (B.transpose * B)^{-1}`.

Consequently the exact H9 U08 contract is equivalent to one scalar
dimension-free estimate: the dense `L^4` bound for `Tr(D) - N`.  That
estimate is kept as an explicit non-endpoint contract so cancellation is not
replaced by a raw trace majorant.

No H3--H18 endpoint, A7 interface, raw `O(N^2)` majorant, or manuscript
declaration is imported.  The approved A4 axiom is not consumed: the
trace-four producer used below is the foundations-only checked Stein
contraction already present in U08.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.DenseScore
open LogdetLean.GramHafnian.Wishart

-- Preserve the frozen U09/U08 target spelling without importing its U03 queue.
local notation "H9U08InverseWishartContract" =>
  H9InverseWishartDenominatorPackage

/-- The sole scalar inequality left after the exact U08 reduction. -/
structure H9U08CenteredTraceFourthBound (N K : ℕ) : Prop where
  lpNorm_four_le : 16 * N ≤ K ->
    lpNorm (h9CenteredInverseTrace N K) 4
        (h9InverseWishartDenominatorLaw N K) ≤
      h9InverseWishartMomentConstant

/-- The H9 denominator law is literally U08's variance-one Gaussian law. -/
theorem h9InverseWishartDenominatorLaw_eq_u08StandardGaussian
    (N K : ℕ) :
    h9InverseWishartDenominatorLaw N K =
      standardRealGaussianMatrixMeasure (K - N) N := by
  rfl

/-- H9 and U08 use the same scaled inverse-Wishart matrix pointwise. -/
theorem h9ScaledInverseWishart_eq_u08ScaledInverseWishartMatrix
    (N K : ℕ) (B : H9InverseWishartSample N K) :
    h9ScaledInverseWishart N K B = scaledInverseWishartMatrix N K B := by
  rfl

/-- The centered first trace is qualitatively in `L^4` at the exact global
order-four threshold. -/
theorem h9CenteredInverseTrace_memLp_four_internal
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K) :
    MemLp (h9CenteredInverseTrace N K) 4
      (h9InverseWishartDenominatorLaw N K) := by
  letI : IsProbabilityMeasure (h9InverseWishartDenominatorLaw N K) :=
    h9InverseWishartDenominatorLaw_isProbability N K
  have hraw := inverseWishartTrace_memLp_four_standardGaussian
    (k := K - N) (p := N) (by omega : N + 8 ≤ K - N)
  have hscaled : MemLp
      (fun B : H9InverseWishartSample N K =>
        Matrix.trace (h9ScaledInverseWishart N K B)) 4
      (h9InverseWishartDenominatorLaw N K) := by
    have hfun :
        (fun B : H9InverseWishartSample N K =>
          Matrix.trace (h9ScaledInverseWishart N K B)) =
        concreteCOEExponent N K •
          (fun B : H9InverseWishartSample N K =>
            Matrix.trace (realWishartGram B)⁻¹) := by
      funext B
      simp only [h9ScaledInverseWishart, Matrix.trace_smul, Pi.smul_apply]
    rw [hfun, h9InverseWishartDenominatorLaw]
    exact hraw.const_smul (concreteCOEExponent N K)
  have hcenter :
      h9CenteredInverseTrace N K =
        (fun B : H9InverseWishartSample N K =>
          Matrix.trace (h9ScaledInverseWishart N K B)) -
        (fun _ : H9InverseWishartSample N K => (N : ℝ)) := by
    funext B
    rfl
  rw [hcenter]
  exact hscaled.sub (memLp_const (N : ℝ))

/-- `Tr(D^2)` is qualitatively in `L^2` at the same exact threshold. -/
theorem h9InverseTraceSquare_memLp_two_internal
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K) :
    MemLp (h9InverseTraceSquare N K) 2
      (h9InverseWishartDenominatorLaw N K) := by
  have hraw := inverseWishartTraceSquare_memLp_two_standardGaussian
    (k := K - N) (p := N) (by omega : N + 8 ≤ K - N)
  have hfun :
      h9InverseTraceSquare N K =
        concreteCOEExponent N K ^ 2 •
          (fun B : H9InverseWishartSample N K =>
            Matrix.trace ((realWishartGram B)⁻¹ ^ 2)) := by
    funext B
    simp only [h9InverseTraceSquare, h9ScaledInverseWishart,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, smul_smul,
      Pi.smul_apply, pow_two]
  rw [hfun, h9InverseWishartDenominatorLaw]
  exact hraw.const_smul (concreteCOEExponent N K ^ 2)

private theorem lpNorm_two_sq_eq_integral_sq_h9
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {f : Omega -> ℝ}
    (hf : MemLp f 2 mu) :
    lpNorm f 2 mu ^ 2 = ∫ x, f x ^ 2 ∂mu := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (p := (2 : ENNReal))
    (by norm_num) (by norm_num) hf.aestronglyMeasurable]
  norm_num
  have hnonneg : 0 ≤ ∫ x, f x ^ 2 ∂mu :=
    integral_nonneg fun _ => sq_nonneg _
  rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hnonneg]

/-- The second H9 quantitative field is already a theorem: U08's checked
fourth-trace Stein ledger gives `128 N^2` for its squared `L^2` norm, far
inside H9's allowed `(4096 N)^2` envelope. -/
theorem h9InverseTraceSquare_lpNorm_two_le_internal
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (h9InverseTraceSquare N K) 2
        (h9InverseWishartDenominatorLaw N K) ≤
      h9InverseWishartMomentConstant * (N : ℝ) := by
  have hgap : 2 * N + 8 ≤ K := by omega
  have hmem := h9InverseTraceSquare_memLp_two_internal hgap
  have L : H14ScaledInverseFourthTraceMomentLedger N K :=
    h14_scaledInverseFourthTraceMomentLedger_of_matsumotoTraceFour_conditional
      hN hdense (h14MatsumotoIdentityTraceFourBoundContract_internal N K)
  have hintegral :
      (∫ B : H9InverseWishartSample N K,
          h9InverseTraceSquare N K B ^ 2
          ∂h9InverseWishartDenominatorLaw N K) ≤
        128 * (N : ℝ) ^ 2 := by
    simpa only [h9InverseWishartDenominatorLaw, h9InverseTraceSquare,
      h9ScaledInverseWishart, scaledInverseWishartMatrix, pow_two] using
        L.traceTwoSquare_integral_le
  have hnormSq :
      lpNorm (h9InverseTraceSquare N K) 2
          (h9InverseWishartDenominatorLaw N K) ^ 2 ≤
        128 * (N : ℝ) ^ 2 := by
    rw [lpNorm_two_sq_eq_integral_sq_h9 hmem]
    exact hintegral
  change lpNorm (h9InverseTraceSquare N K) 2
      (h9InverseWishartDenominatorLaw N K) ≤ 4096 * (N : ℝ)
  apply le_of_sq_le_sq
  · calc
      lpNorm (h9InverseTraceSquare N K) 2
          (h9InverseWishartDenominatorLaw N K) ^ 2 ≤
        128 * (N : ℝ) ^ 2 := hnormSq
      _ ≤ (4096 * (N : ℝ)) ^ 2 := by
        nlinarith [sq_nonneg (N : ℝ)]
  · positivity

/-- Exact constructor for the frozen U09/U08 alias.  Only the centered first
trace bound is supplied; every other field is proved above. -/
theorem h9U08InverseWishartContract_of_centeredTraceFourthBound
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (H : H9U08CenteredTraceFourthBound N K) :
    H9U08InverseWishartContract N K := by
  change H9InverseWishartDenominatorPackage N K
  refine
    { centeredTrace_memLp_four :=
        h9CenteredInverseTrace_memLp_four_internal hgap
      traceSquare_memLp_two := h9InverseTraceSquare_memLp_two_internal hgap
      dense_bounds := ?_ }
  intro hdense
  exact ⟨H.lpNorm_four_le hdense,
    h9InverseTraceSquare_lpNorm_two_le_internal hN hdense⟩

/-- Strongest exact reduction: the audited H9 U08 blocker is equivalent to
one scalar centered-trace cancellation bound. -/
theorem h9U08InverseWishartContract_iff_centeredTraceFourthBound
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    H9U08InverseWishartContract N K ↔
      H9U08CenteredTraceFourthBound N K := by
  constructor
  · intro H
    exact ⟨fun hdense => (H.dense_bounds hdense).1⟩
  · exact h9U08InverseWishartContract_of_centeredTraceFourthBound hN hgap

/-! Focused transitive audit for this single exact module. -/

#print H9U08CenteredTraceFourthBound
#print h9U08InverseWishartContract_iff_centeredTraceFourthBound
#print axioms h9InverseWishartDenominatorLaw_eq_u08StandardGaussian
#print axioms h9ScaledInverseWishart_eq_u08ScaledInverseWishartMatrix
#print axioms h9CenteredInverseTrace_memLp_four_internal
#print axioms h9InverseTraceSquare_memLp_two_internal
#print axioms h9InverseTraceSquare_lpNorm_two_le_internal
#print axioms h9U08InverseWishartContract_of_centeredTraceFourthBound
#print axioms h9U08InverseWishartContract_iff_centeredTraceFourthBound

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08
