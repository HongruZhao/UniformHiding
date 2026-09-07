import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.H9InverseWishartContractReduction
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.MixedScalarQuadraticClosure
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.H8_Proof

/-!
# H9 centered inverse-trace closure from one scalar Stein contraction

All qualitative order-four facts and the dimension-sharp `L^2` estimate for
`Tr(D^2)` are already kernel checked.  This file proves that the remaining
H9 centered-trace estimate follows from one scalar inequality,

`c E[(Tr D - N)^4] <= 6 E[(Tr D - N)^2 Tr(D^2)]`,

where `c = K - 2N - 1`.  The inverse-Wishart entrywise Stein recursion is
expected to give equality.  Keeping only the displayed inequality isolates
the weakest sufficient analytic statement and makes the large numerical
slack in H9 explicit.

No H3--H18 endpoint, literature atom, or replacement scientific axiom is
used below.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.DenseScore

/-- The single scalar contraction still needed for the centered inverse
trace.  The exact inverse-Wishart Stein calculation gives this with equality;
the one-sided form here is the weakest input consumed by the norm closure. -/
structure H9CenteredTraceSteinContraction (N K : ℕ) : Prop where
  centeredFourth_le_mixedTraceTwo :
    concreteCOEExponent N K *
        (∫ B : H9InverseWishartSample N K,
          h9CenteredInverseTrace N K B ^ 4
            ∂h9InverseWishartDenominatorLaw N K) ≤
      6 * (∫ B : H9InverseWishartSample N K,
        h9CenteredInverseTrace N K B ^ 2 *
          h9InverseTraceSquare N K B
            ∂h9InverseWishartDenominatorLaw N K)

private theorem lpNorm_two_sq_eq_integral_sq_h9_centered
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {f : Omega → ℝ}
    (hf : MemLp f 2 mu) :
    lpNorm f 2 mu ^ 2 = ∫ x, f x ^ 2 ∂mu := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (p := (2 : ENNReal))
    (by norm_num) (by norm_num) hf.aestronglyMeasurable]
  norm_num
  have hnonneg : 0 ≤ ∫ x, f x ^ 2 ∂mu :=
    integral_nonneg fun _ => sq_nonneg _
  rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hnonneg]

/-- The fourth integral of a real `L^4` function is its fourth `lpNorm`
power.  This is routed through the already checked square-norm identity. -/
theorem lpNorm_four_pow_four_eq_integral_pow_four_h9
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {f : Omega → ℝ}
    (hf : MemLp f 4 mu) :
    lpNorm f 4 mu ^ 4 = ∫ x, f x ^ 4 ∂mu := by
  have hsq : MemLp (fun x => f x ^ 2) 2 mu :=
    memLp_sq_two_of_memLp_four hf
  calc
    lpNorm f 4 mu ^ 4 = (lpNorm f 4 mu ^ 2) ^ 2 := by ring
    _ = lpNorm (fun x => f x ^ 2) 2 mu ^ 2 := by
      rw [lpNorm_sq_two_eq_sq_lpNorm_four hf]
    _ = ∫ x, (f x ^ 2) ^ 2 ∂mu :=
      lpNorm_two_sq_eq_integral_sq_h9_centered hsq
    _ = ∫ x, f x ^ 4 ∂mu := by
      apply integral_congr_ae
      filter_upwards [] with x
      ring

/-- Cauchy--Schwarz controls the mixed contraction by the squared centered
`L^4` norm and the `L^2` norm of `Tr(D^2)`. -/
theorem h9_centeredSquare_mul_traceSquare_integral_le
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K) :
    (∫ B : H9InverseWishartSample N K,
        h9CenteredInverseTrace N K B ^ 2 *
          h9InverseTraceSquare N K B
          ∂h9InverseWishartDenominatorLaw N K) ≤
      lpNorm (h9CenteredInverseTrace N K) 4
          (h9InverseWishartDenominatorLaw N K) ^ 2 *
        lpNorm (h9InverseTraceSquare N K) 2
          (h9InverseWishartDenominatorLaw N K) := by
  let mu := h9InverseWishartDenominatorLaw N K
  let x := h9CenteredInverseTrace N K
  let y := h9InverseTraceSquare N K
  have hx : MemLp x 4 mu :=
    h9CenteredInverseTrace_memLp_four_internal hgap
  have hy : MemLp y 2 mu :=
    h9InverseTraceSquare_memLp_two_internal hgap
  have hxSq : MemLp (fun B => x B ^ 2) 2 mu :=
    memLp_sq_two_of_memLp_four hx
  have hprod : MemLp (fun B => x B ^ 2 * y B) 1 mu :=
    hy.mul' hxSq
  have hholder := lpNorm_mul_le_lpNorm_two_mul hxSq hy
  have hnonneg : ∀ B, 0 ≤ x B ^ 2 * y B := by
    intro B
    exact mul_nonneg (sq_nonneg _) (h9InverseTraceSquare_nonneg hgap B)
  calc
    (∫ B, x B ^ 2 * y B ∂mu) =
        ∫ B, ‖x B ^ 2 * y B‖ ∂mu := by
          apply integral_congr_ae
          filter_upwards [] with B
          rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg B)]
    _ = lpNorm (fun B => x B ^ 2 * y B) 1 mu := by
      rw [lpNorm_one_eq_integral_norm hprod.aestronglyMeasurable]
    _ ≤ lpNorm (fun B => x B ^ 2) 2 mu * lpNorm y 2 mu := hholder
    _ = lpNorm x 4 mu ^ 2 * lpNorm y 2 mu := by
      rw [lpNorm_sq_two_eq_sq_lpNorm_four hx]

/-- The one scalar centered Stein contraction closes the previously isolated
dimension-free H9 denominator bound.  The proved `Tr(D^2)` estimate is
`4096 N`; the dense gap `c >= 13N` leaves far more slack than needed. -/
theorem h9CenteredInverseTrace_lpNorm_four_le_of_steinContraction
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K)
    (H : H9CenteredTraceSteinContraction N K) :
    lpNorm (h9CenteredInverseTrace N K) 4
        (h9InverseWishartDenominatorLaw N K) ≤
      h9InverseWishartMomentConstant := by
  have hgap : 2 * N + 8 ≤ K := by omega
  let mu := h9InverseWishartDenominatorLaw N K
  let x := h9CenteredInverseTrace N K
  let y := h9InverseTraceSquare N K
  let a := lpNorm x 4 mu
  let b := lpNorm y 2 mu
  let c := concreteCOEExponent N K
  have hx : MemLp x 4 mu :=
    h9CenteredInverseTrace_memLp_four_internal hgap
  have ha0 : 0 ≤ a := lpNorm_nonneg
  have hb0 : 0 ≤ b := lpNorm_nonneg
  have hc0 : 0 < c := by
    exact h9InverseWishart_exponent_pos hgap
  have hcLower : 13 * (N : ℝ) ≤ c := by
    have hKR : (16 : ℝ) * (N : ℝ) ≤ (K : ℝ) := by
      exact_mod_cast hdense
    have hNR : (1 : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast hN
    dsimp only [c, concreteCOEExponent]
    linarith
  have hb : b ≤ 4096 * (N : ℝ) := by
    simpa only [b, y, mu, h9InverseWishartMomentConstant] using
      h9InverseTraceSquare_lpNorm_two_le_internal hN hdense
  have hfour : a ^ 4 = ∫ B, x B ^ 4 ∂mu :=
    lpNorm_four_pow_four_eq_integral_pow_four_h9 hx
  have hmixed :
      (∫ B, x B ^ 2 * y B ∂mu) ≤ a ^ 2 * b := by
    simpa only [x, y, mu, a, b] using
      h9_centeredSquare_mul_traceSquare_integral_le (N := N) (K := K) hgap
  have hrec : c * a ^ 4 ≤ 6 * (a ^ 2 * b) := by
    calc
      c * a ^ 4 = c * (∫ B, x B ^ 4 ∂mu) := by rw [hfour]
      _ ≤ 6 * (∫ B, x B ^ 2 * y B ∂mu) := by
        simpa only [c, x, y, mu] using H.centeredFourth_le_mixedTraceTwo
      _ ≤ 6 * (a ^ 2 * b) := by gcongr
  by_cases ha : a = 0
  · change a ≤ h9InverseWishartMomentConstant
    rw [ha]
    norm_num [h9InverseWishartMomentConstant]
  have haPos : 0 < a := lt_of_le_of_ne ha0 (Ne.symm ha)
  have haSqPos : 0 < a ^ 2 := sq_pos_of_pos haPos
  have hcaSq : c * a ^ 2 ≤ 6 * b := by
    apply le_of_mul_le_mul_right _ haSqPos
    calc
      (c * a ^ 2) * a ^ 2 = c * a ^ 4 := by ring
      _ ≤ 6 * (a ^ 2 * b) := hrec
      _ = (6 * b) * a ^ 2 := by ring
  have h13 : 13 * (N : ℝ) * a ^ 2 ≤ 6 * b := by
    calc
      13 * (N : ℝ) * a ^ 2 ≤ c * a ^ 2 := by
        exact mul_le_mul_of_nonneg_right hcLower (sq_nonneg a)
      _ ≤ 6 * b := hcaSq
  have hcoarse : a ^ 2 ≤ 4096 ^ 2 := by
    have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    nlinarith
  change a ≤ 4096
  nlinarith

/-- Exact constructor for the formerly conditional U08 package from the
single centered Stein contraction.  Every other field is already proved. -/
theorem h9U08InverseWishartContract_of_steinContraction
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (H : H9CenteredTraceSteinContraction N K) :
    H9InverseWishartDenominatorPackage N K := by
  apply h9U08InverseWishartContract_of_centeredTraceFourthBound hN hgap
  refine ⟨?_⟩
  intro hdense
  exact h9CenteredInverseTrace_lpNorm_four_le_of_steinContraction hN hdense H

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08
