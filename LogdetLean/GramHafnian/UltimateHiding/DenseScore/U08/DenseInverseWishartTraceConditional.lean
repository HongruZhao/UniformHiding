import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.H8_Proof
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.BetaPrimeMomentInputsConditional

/-!
# CONDITIONAL dense inverse-Wishart trace layer

This file makes the remaining denominator probability input smaller than the
H8/H10 endpoints.  From the two trace fluctuation estimates in (10.11), all
denominator-drift algebra and the exact `2^13`, `2^26`, and `2^28` constants
are derived internally.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08

noncomputable section

/-- **CONDITIONAL denominator contract.**  This is exactly the pair of
inverse-Wishart trace fluctuation estimates (10.11), plus the qualitative
integrability needed for integral linearity. -/
structure DenseInverseWishartTraceInputs (N K : ℕ) : Prop where
  traceOne_integral_eq :
    (∫ source, denominatorTraceOneSource N K source
      ∂(realBetaPrimeGaussianSourceLaw N K)) = (N : ℝ)
  traceOne_centered_memLp_four :
    MemLp (fun source ↦ denominatorTraceOneSource N K source - (N : ℝ)) 4
      (realBetaPrimeGaussianSourceLaw N K)
  traceOne_square_integrable :
    Integrable (fun source ↦ denominatorTraceOneSource N K source ^ 2)
      (realBetaPrimeGaussianSourceLaw N K)
  traceTwo_integrable :
    Integrable (denominatorTraceTwoSource N K)
      (realBetaPrimeGaussianSourceLaw N K)
  traceTwo_centered_memLp_two :
    MemLp (fun source ↦ denominatorTraceTwoSource N K source -
      ∫ z, denominatorTraceTwoSource N K z
        ∂(realBetaPrimeGaussianSourceLaw N K)) 2
      (realBetaPrimeGaussianSourceLaw N K)
  traceOne_centered_lpNorm_four_le : 16 * N ≤ K →
    lpNorm (fun source ↦ denominatorTraceOneSource N K source - (N : ℝ)) 4
        (realBetaPrimeGaussianSourceLaw N K) ≤ (2 : ℝ) ^ 12
  traceTwo_centered_lpNorm_two_le : 16 * N ≤ K →
    lpNorm (fun source ↦ denominatorTraceTwoSource N K source -
      ∫ z, denominatorTraceTwoSource N K z
        ∂(realBetaPrimeGaussianSourceLaw N K)) 2
        (realBetaPrimeGaussianSourceLaw N K) ≤ (2 : ℝ) ^ 16

/-- Global denominator contract at the exact H8/H10 qualitative threshold. -/
abbrev DenseInverseWishartTraceContract : Prop :=
  ∀ {N K : ℕ}, 1 ≤ N → 2 * N + 8 ≤ K →
    DenseInverseWishartTraceInputs N K

/-- The first-trace denominator drift is exactly `(N+1)(tr C₀-N)`. -/
theorem traceOneDenominatorDrift_eq
    {N K : ℕ} :
    traceOneDenominatorDriftSource N K =
      ((N + 1 : ℕ) : ℝ) •
        (fun source ↦ denominatorTraceOneSource N K source - (N : ℝ)) := by
  funext source
  simp only [traceOneDenominatorDriftSource, traceOneConditionalMeanSource,
    Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

/-- The denominator half of the H8 source contract follows from (10.11),
including the exact `2^13 N` constant. -/
theorem traceOneDenominatorDrift_momentPackage_of_inverseTrace
    {N K : ℕ} (hN : 1 ≤ N)
    (H : DenseInverseWishartTraceInputs N K) :
    MemLp (traceOneDenominatorDriftSource N K) 4
        (realBetaPrimeGaussianSourceLaw N K) ∧
      (16 * N ≤ K →
        lpNorm (traceOneDenominatorDriftSource N K) 4
            (realBetaPrimeGaussianSourceLaw N K) ≤
          (2 : ℝ) ^ 13 * (N : ℝ)) := by
  rw [traceOneDenominatorDrift_eq]
  refine ⟨H.traceOne_centered_memLp_four.const_smul _, ?_⟩
  intro hdense
  rw [lpNorm_const_smul]
  change ‖((N + 1 : ℕ) : ℝ)‖ *
      lpNorm (fun source ↦ denominatorTraceOneSource N K source - (N : ℝ)) 4
        (realBetaPrimeGaussianSourceLaw N K) ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hn : (((N + 1 : ℕ) : ℝ)) ≤ 2 * (N : ℝ) := by
    exact_mod_cast (show N + 1 ≤ 2 * N by omega)
  have htrace := H.traceOne_centered_lpNorm_four_le hdense
  have hnonneg : 0 ≤ lpNorm
      (fun source ↦ denominatorTraceOneSource N K source - (N : ℝ)) 4
      (realBetaPrimeGaussianSourceLaw N K) := lpNorm_nonneg
  calc
    (((N + 1 : ℕ) : ℝ)) * lpNorm
        (fun source ↦ denominatorTraceOneSource N K source - (N : ℝ)) 4
        (realBetaPrimeGaussianSourceLaw N K) ≤
      (2 * (N : ℝ)) * (2 : ℝ) ^ 12 :=
        mul_le_mul hn htrace hnonneg (by positivity)
    _ = (2 : ℝ) ^ 13 * (N : ℝ) := by ring

/-- Integral linearity turns the Wick conditional mean into the two
centered denominator trace components. -/
theorem traceTwoDenominatorDrift_eq_centered_traces
    {N K : ℕ} (H : DenseInverseWishartTraceInputs N K) :
    traceTwoDenominatorDriftSource N K =
      (((N + 1 : ℕ) : ℝ) * ((N + 2 : ℕ) : ℝ)) •
          (fun source ↦ denominatorTraceTwoSource N K source -
            ∫ z, denominatorTraceTwoSource N K z
              ∂(realBetaPrimeGaussianSourceLaw N K)) +
        ((N + 1 : ℕ) : ℝ) •
          (fun source ↦ denominatorTraceOneSource N K source ^ 2 -
            ∫ z, denominatorTraceOneSource N K z ^ 2
              ∂(realBetaPrimeGaussianSourceLaw N K)) := by
  let sourceMu := realBetaPrimeGaussianSourceLaw N K
  let a : ℝ := ((N + 1 : ℕ) : ℝ) * ((N + 2 : ℕ) : ℝ)
  let n : ℝ := ((N + 1 : ℕ) : ℝ)
  have hIntegral :
      (∫ source, traceTwoConditionalMeanSource N K source ∂sourceMu) =
        a * (∫ source, denominatorTraceTwoSource N K source ∂sourceMu) +
          n * (∫ source, denominatorTraceOneSource N K source ^ 2
            ∂sourceMu) := by
    dsimp only [traceTwoConditionalMeanSource, a, n]
    rw [integral_add (H.traceTwo_integrable.const_mul _)
      (H.traceOne_square_integrable.const_mul _),
      integral_const_mul, integral_const_mul]
  funext source
  simp only [traceTwoDenominatorDriftSource, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  rw [hIntegral]
  simp only [traceTwoConditionalMeanSource]
  dsimp only [a, n, sourceMu]
  push_cast
  ring

/-- Qualitative square-integrability of the H10 denominator drift requires
no dense estimate once the two inverse-trace `MemLp` facts are available. -/
theorem traceTwoDenominatorDrift_memLp_of_inverseTraces
    {N K : ℕ} (H : DenseInverseWishartTraceInputs N K) :
    MemLp (traceTwoDenominatorDriftSource N K) 2
      (realBetaPrimeGaussianSourceLaw N K) := by
  let sourceMu := realBetaPrimeGaussianSourceLaw N K
  letI : IsProbabilityMeasure sourceMu :=
    realBetaPrimeGaussianSourceLaw_isProbability N K
  have hSquare := (centered_square_two_momentPackage_of_centered_four
    (mu := sourceMu) H.traceOne_centered_memLp_four (by
      simpa only [sourceMu] using H.traceOne_integral_eq)).1
  rw [traceTwoDenominatorDrift_eq_centered_traces H]
  exact
    (H.traceTwo_centered_memLp_two.const_smul
      (((N + 1 : ℕ) : ℝ) * ((N + 2 : ℕ) : ℝ))).add
      (hSquare.const_smul ((N + 1 : ℕ) : ℝ))

/-- The centered square of `tr C₀` has the exact human-proof
`2^26 N` bound, derived from the `2^12` fourth-moment input. -/
theorem denominatorTraceOneSquare_centered_momentPackage
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K)
    (H : DenseInverseWishartTraceInputs N K) :
    MemLp (fun source ↦ denominatorTraceOneSource N K source ^ 2 -
      ∫ z, denominatorTraceOneSource N K z ^ 2
        ∂(realBetaPrimeGaussianSourceLaw N K)) 2
        (realBetaPrimeGaussianSourceLaw N K) ∧
      lpNorm (fun source ↦ denominatorTraceOneSource N K source ^ 2 -
        ∫ z, denominatorTraceOneSource N K z ^ 2
          ∂(realBetaPrimeGaussianSourceLaw N K)) 2
          (realBetaPrimeGaussianSourceLaw N K) ≤
        (2 : ℝ) ^ 26 * (N : ℝ) := by
  let sourceMu := realBetaPrimeGaussianSourceLaw N K
  letI : IsProbabilityMeasure sourceMu :=
    realBetaPrimeGaussianSourceLaw_isProbability N K
  have hbase := centered_square_two_momentPackage_of_centered_four
    (mu := sourceMu) H.traceOne_centered_memLp_four (by
      simpa only [sourceMu] using H.traceOne_integral_eq)
  refine ⟨by simpa only [sourceMu] using hbase.1, ?_⟩
  have hA := H.traceOne_centered_lpNorm_four_le hdense
  have hNreal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  calc
    lpNorm (fun source ↦ denominatorTraceOneSource N K source ^ 2 -
        ∫ z, denominatorTraceOneSource N K z ^ 2 ∂sourceMu) 2 sourceMu ≤
      2 * lpNorm
          (fun source ↦ denominatorTraceOneSource N K source - (N : ℝ))
          4 sourceMu ^ 2 +
        2 * (N : ℝ) * lpNorm
          (fun source ↦ denominatorTraceOneSource N K source - (N : ℝ))
          4 sourceMu := by
      have hNnonneg : 0 ≤ (N : ℝ) := by positivity
      simpa only [abs_of_nonneg hNnonneg] using hbase.2
    _ ≤ (2 : ℝ) ^ 26 * (N : ℝ) :=
      h10_denominator_trace_square_constant hNreal lpNorm_nonneg hA

/-- The denominator half of H10 follows from (10.11), with the exact
`2^28 N²` constant. -/
theorem traceTwoDenominatorDrift_momentPackage_of_inverseTraces
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K)
    (H : DenseInverseWishartTraceInputs N K) :
    MemLp (traceTwoDenominatorDriftSource N K) 2
        (realBetaPrimeGaussianSourceLaw N K) ∧
      lpNorm (traceTwoDenominatorDriftSource N K) 2
          (realBetaPrimeGaussianSourceLaw N K) ≤
        (2 : ℝ) ^ 28 * (N : ℝ) ^ 2 := by
  let sourceMu := realBetaPrimeGaussianSourceLaw N K
  let centeredTwo : BetaPrimeGaussianSource N K → ℝ := fun source ↦
    denominatorTraceTwoSource N K source -
      ∫ z, denominatorTraceTwoSource N K z ∂sourceMu
  let centeredSquare : BetaPrimeGaussianSource N K → ℝ := fun source ↦
    denominatorTraceOneSource N K source ^ 2 -
      ∫ z, denominatorTraceOneSource N K z ^ 2 ∂sourceMu
  let a : ℝ := ((N + 1 : ℕ) : ℝ) * ((N + 2 : ℕ) : ℝ)
  let n : ℝ := ((N + 1 : ℕ) : ℝ)
  have hSquare := denominatorTraceOneSquare_centered_momentPackage hN hdense H
  have hEq : traceTwoDenominatorDriftSource N K =
      a • centeredTwo + n • centeredSquare := by
    simpa only [a, n, centeredTwo, centeredSquare, sourceMu] using
      traceTwoDenominatorDrift_eq_centered_traces H
  have hTwoMem : MemLp centeredTwo 2 sourceMu := by
    simpa only [centeredTwo, sourceMu] using H.traceTwo_centered_memLp_two
  have hSquareMem : MemLp centeredSquare 2 sourceMu := by
    simpa only [centeredSquare, sourceMu] using hSquare.1
  refine ⟨?_, ?_⟩
  · rw [hEq]
    exact (hTwoMem.const_smul a).add (hSquareMem.const_smul n)
  rw [hEq]
  have htri := lpNorm_add_le (g := n • centeredSquare)
    (hTwoMem.const_smul a) (by norm_num)
  have hTwoNorm : lpNorm centeredTwo 2 sourceMu ≤ (2 : ℝ) ^ 16 := by
    simpa only [centeredTwo, sourceMu] using
      H.traceTwo_centered_lpNorm_two_le hdense
  have hSquareNorm : lpNorm centeredSquare 2 sourceMu ≤
      (2 : ℝ) ^ 26 * (N : ℝ) := by
    simpa only [centeredSquare, sourceMu] using hSquare.2
  have haNonneg : 0 ≤ a := by dsimp only [a]; positivity
  have hnNonneg : 0 ≤ n := by dsimp only [n]; positivity
  calc
    lpNorm (a • centeredTwo + n • centeredSquare) 2 sourceMu ≤
        lpNorm (a • centeredTwo) 2 sourceMu +
          lpNorm (n • centeredSquare) 2 sourceMu := htri
    _ = |a| * lpNorm centeredTwo 2 sourceMu +
        |n| * lpNorm centeredSquare 2 sourceMu := by
      simp only [lpNorm_const_smul]
      change ‖a‖ * lpNorm centeredTwo 2 sourceMu +
          ‖n‖ * lpNorm centeredSquare 2 sourceMu = _
      simp only [Real.norm_eq_abs]
    _ = a * lpNorm centeredTwo 2 sourceMu +
        n * lpNorm centeredSquare 2 sourceMu := by
      rw [abs_of_nonneg haNonneg, abs_of_nonneg hnNonneg]
    _ ≤ a * (2 : ℝ) ^ 16 +
        n * ((2 : ℝ) ^ 26 * (N : ℝ)) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hTwoNorm haNonneg)
        (mul_le_mul_of_nonneg_left hSquareNorm hnNonneg)
    _ ≤ (2 : ℝ) ^ 28 * (N : ℝ) ^ 2 := by
      dsimp only [a, n]
      push_cast
      exact h10_denominator_drift_constant (N := (N : ℝ))
        (by exact_mod_cast hN)

/-! ## Smaller split contracts consumed by the endpoint assembly -/

/-- **CONDITIONAL numerator contract for H8.**  This is only the centered
quadratic Gaussian chaos estimate conditional on the denominator. -/
structure H8GaussianInnovationInputs (N K : ℕ) : Prop where
  memLp_four : MemLp (traceOneInnovationSource N K) 4
    (realBetaPrimeGaussianSourceLaw N K)
  lpNorm_four_le : 16 * N ≤ K →
    lpNorm (traceOneInnovationSource N K) 4
      (realBetaPrimeGaussianSourceLaw N K) ≤ (2 : ℝ) ^ 10 * (N : ℝ)

/-- Global numerator-chaos contract for H8. -/
abbrev H8GaussianInnovationContract : Prop :=
  ∀ {N K : ℕ}, 1 ≤ N → 2 * N + 8 ≤ K →
    H8GaussianInnovationInputs N K

/-- Assemble the H8 source contract from its numerator Gaussian-chaos input
and the genuinely denominator-only inverse-Wishart trace input. -/
theorem H8SourceMomentInputs.of_split
    {N K : ℕ} (hN : 1 ≤ N)
    (Hnum : H8GaussianInnovationInputs N K)
    (Hden : DenseInverseWishartTraceInputs N K) :
    H8SourceMomentInputs N K := by
  have hden := traceOneDenominatorDrift_momentPackage_of_inverseTrace hN Hden
  exact
    { innovation_memLp_four := Hnum.memLp_four
      denominator_drift_memLp_four := hden.1
      innovation_lpNorm_four_le := Hnum.lpNorm_four_le
      denominator_drift_lpNorm_four_le := hden.2 }

/-- **CONDITIONAL numerator contract for H10.**  The first field is the
finite Wick conditional-mean identity and the other two fields are only the
Gaussian Poincare innovation estimate. -/
structure H10GaussianInnovationInputs (N K : ℕ) : Prop where
  conditional_mean_integral_eq :
    (∫ source, betaPrimeTraceTwoSource N K source
      ∂(realBetaPrimeGaussianSourceLaw N K)) =
      ∫ source, traceTwoConditionalMeanSource N K source
        ∂(realBetaPrimeGaussianSourceLaw N K)
  memLp_two : MemLp (traceTwoInnovationSource N K) 2
    (realBetaPrimeGaussianSourceLaw N K)
  lpNorm_two_le : 16 * N ≤ K →
    lpNorm (traceTwoInnovationSource N K) 2
      (realBetaPrimeGaussianSourceLaw N K) ≤
        (2 : ℝ) ^ 23 * (N : ℝ) ^ 2

/-- Global Wick/Poincare numerator contract for H10. -/
abbrev H10GaussianInnovationContract : Prop :=
  ∀ {N K : ℕ}, 1 ≤ N → 2 * N + 8 ≤ K →
    H10GaussianInnovationInputs N K

/-- Assemble the H10 source contract from the numerator Wick/Poincare input
and the denominator-only inverse-Wishart trace input. -/
theorem H10SourceMomentInputs.of_split
    {N K : ℕ} (hN : 1 ≤ N)
    (Hnum : H10GaussianInnovationInputs N K)
    (Hden : DenseInverseWishartTraceInputs N K) :
    H10SourceMomentInputs N K := by
  exact
    { conditional_mean_integral_eq := Hnum.conditional_mean_integral_eq
      innovation_memLp_two := Hnum.memLp_two
      denominator_drift_memLp_two :=
        traceTwoDenominatorDrift_memLp_of_inverseTraces Hden
      innovation_lpNorm_two_le := Hnum.lpNorm_two_le
      denominator_drift_lpNorm_two_le := fun hdense ↦
        (traceTwoDenominatorDrift_momentPackage_of_inverseTraces
          hN hdense Hden).2 }

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08
