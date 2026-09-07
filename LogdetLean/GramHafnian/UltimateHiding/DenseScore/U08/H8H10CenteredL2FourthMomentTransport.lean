import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.H14_DenominatorFourthTraceContraction
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.H14_FiniteGaussianFourthWickFormula
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.FiniteGaussianWishartSecondMoment
import Mathlib.Probability.Moments.Variance

/-!
# Exact centered-L2 and fourth-moment transport for H8/H10

This module stays on the frozen U08 route.  It changes neither paper endpoint,
uses no A7-style interface, and never invokes the quarantined raw `O(N^2)`
trace majorant.  The project-side inverse-Wishart matrix and all variables are
left exactly as declared by U08.

The proved part has three layers.

* A general centered `L2` norm is represented exactly by the square root of
  `ProbabilityTheory.variance`.
* The two H8/H10 source variances are transported exactly to differences of
  inverse-Wishart trace-polynomial moments, using the checked second-order
  Wick formula and the existing order-four fiber interface.
* The literal beta-prime endpoint packages follow from one narrow record.  Its
  only quantitative fields are the two cancellation inequalities that an A4
  evaluation must supply.  Thus this is an intermediate reduction, not a new
  endpoint axiom and not a claim that A4 has already been transcribed.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08

noncomputable section

private abbrev sourceLaw (N K : ℕ) := realBetaPrimeGaussianSourceLaw N K

private abbrev inverseLaw (N K : ℕ) :=
  standardRealGaussianMatrixMeasure (K - N) N

/-! ## Exact denominator-side raw moments -/

def h8DenominatorSecondRawMoment (N K : ℕ) : ℝ :=
  (((N + 1 : ℕ) : ℝ) ^ 2) *
      (∫ H : Matrix (Fin (K - N)) (Fin N) ℝ,
        Matrix.trace (scaledInverseWishartMatrix N K H) ^ 2 ∂inverseLaw N K)
    + 2 * ((N + 1 : ℕ) : ℝ) *
      (∫ H : Matrix (Fin (K - N)) (Fin N) ℝ,
        Matrix.trace ((scaledInverseWishartMatrix N K H) ^ 2) ∂inverseLaw N K)

def h8DenominatorFourthRawMoment (N K : ℕ) : ℝ :=
  ∫ H : Matrix (Fin (K - N)) (Fin N) ℝ,
    h14TraceOneFourthWickPolynomial (N + 1) (scaledInverseWishartMatrix N K H)
    ∂inverseLaw N K

def h10DenominatorFirstRawMoment (N K : ℕ) : ℝ :=
  ((N + 1 : ℕ) : ℝ) * ((N + 2 : ℕ) : ℝ) *
      (∫ H : Matrix (Fin (K - N)) (Fin N) ℝ,
        Matrix.trace ((scaledInverseWishartMatrix N K H) ^ 2) ∂inverseLaw N K)
    + ((N + 1 : ℕ) : ℝ) *
      (∫ H : Matrix (Fin (K - N)) (Fin N) ℝ,
        Matrix.trace (scaledInverseWishartMatrix N K H) ^ 2 ∂inverseLaw N K)

def h10DenominatorSecondRawMoment (N K : ℕ) : ℝ :=
  ∫ H : Matrix (Fin (K - N)) (Fin N) ℝ,
    h14TraceTwoSquareWickPolynomial (N + 1) (scaledInverseWishartMatrix N K H)
    ∂inverseLaw N K

def h8DenominatorCenteredVariance (N K : ℕ) : ℝ :=
  h8DenominatorFourthRawMoment N K - h8DenominatorSecondRawMoment N K ^ 2

def h10DenominatorCenteredVariance (N K : ℕ) : ℝ :=
  h10DenominatorSecondRawMoment N K - h10DenominatorFirstRawMoment N K ^ 2

/-! ## Centered `L2` representation -/

theorem lpNorm_centered_two_eq_sqrt_variance
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : MemLp X 2 μ) :
    lpNorm (fun ω => X ω - ∫ z, X z ∂μ) 2 μ =
      Real.sqrt (ProbabilityTheory.variance X μ) := by
  have hCentered : AEStronglyMeasurable
      (fun ω => X ω - ∫ z, X z ∂μ) μ :=
    hX.aestronglyMeasurable.sub aestronglyMeasurable_const
  rw [lpNorm_eq_integral_norm_rpow_toReal
    (p := (2 : ENNReal)) (by norm_num) (by norm_num) hCentered]
  rw [ProbabilityTheory.variance_eq_integral hX.aemeasurable]
  rw [Real.sqrt_eq_rpow]
  norm_num [Real.norm_eq_abs, Real.rpow_two, sq_abs]

/-! ## Foundations-only fourth inverse-Wishart ledger -/

theorem h8H10_scaledInverseFourthTraceMomentLedger_internal
    (N K : ℕ) (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    H14ScaledInverseFourthTraceMomentLedger N K :=
  h14_scaledInverseFourthTraceMomentLedger_of_matsumotoTraceFour_conditional
    hN hdense (h14MatsumotoIdentityTraceFourBoundContract_internal N K)

/-! ## Qualitative source integrability -/

private theorem betaPrimeTraceOneSource_memLp_four
    (N K : ℕ) (hgap : 2 * N + 8 ≤ K) :
    MemLp (betaPrimeTraceOneSource N K) 4 (sourceLaw N K) := by
  have hmeas :
      AEStronglyMeasurable (betaPrimeTraceOneSource N K) (sourceLaw N K) := by
    exact ((measurable_const.mul (measurable_pi_apply _)).comp
      (measurable_realBetaPrimeTracePowerVector_internal 4 N K)).aestronglyMeasurable
  apply (integrable_norm_rpow_iff hmeas (by norm_num) (by norm_num)).mp
  simpa [Real.rpow_natCast, norm_pow] using
    (integrable_betaPrimeTraceOneSource_fourth_h14_low (N := N) (K := K) hgap).norm

private theorem betaPrimeTraceOneSquareSource_memLp_two
    (N K : ℕ) (hgap : 2 * N + 8 ≤ K) :
    MemLp (fun source => betaPrimeTraceOneSource N K source ^ 2) 2
      (sourceLaw N K) :=
  memLp_sq_two_of_memLp_four (betaPrimeTraceOneSource_memLp_four N K hgap)

private theorem betaPrimeTraceTwoSource_memLp_two
    (N K : ℕ) (hgap : 2 * N + 8 ≤ K) :
    MemLp (betaPrimeTraceTwoSource N K) 2 (sourceLaw N K) := by
  have hmeas :
      AEStronglyMeasurable (betaPrimeTraceTwoSource N K) (sourceLaw N K) := by
    exact (((measurable_const.pow_const 2).mul (measurable_pi_apply _)).comp
      (measurable_realBetaPrimeTracePowerVector_internal 4 N K)).aestronglyMeasurable
  apply (integrable_norm_rpow_iff hmeas (by norm_num) (by norm_num)).mp
  simpa [Real.rpow_natCast, norm_pow] using
    (integrable_betaPrimeTraceTwoSource_square_h14_low (N := N) (K := K) hgap).norm

/-! ## Exact source-to-denominator moment transport -/

theorem betaPrimeTraceOneSource_square_integral_eq_denominator_internal
    (N K : ℕ) (hgap : 2 * N + 8 ≤ K) :
    (∫ source, betaPrimeTraceOneSource N K source ^ 2 ∂sourceLaw N K) =
      h8DenominatorSecondRawMoment N K := by
  simpa [h8DenominatorSecondRawMoment] using
    (betaPrimeSecondOrderFiniteWickFormula_internal (N := N) (K := K) hgap).2

theorem betaPrimeTraceTwoSource_integral_eq_denominator_internal
    (N K : ℕ) (hgap : 2 * N + 8 ≤ K) :
    (∫ source, betaPrimeTraceTwoSource N K source ∂sourceLaw N K) =
      h10DenominatorFirstRawMoment N K := by
  simpa [h10DenominatorFirstRawMoment, Nat.cast_add, Nat.cast_one, add_assoc] using
    (betaPrimeSecondOrderFiniteWickFormula_internal (N := N) (K := K) hgap).1

theorem betaPrimeTraceOneSource_fourth_integral_eq_denominator_internal
    (N K : ℕ) (hgap : 2 * N + 8 ≤ K)
    (hWick : H14FiniteGaussianFourthWickFormula N K) :
    (∫ source, betaPrimeTraceOneSource N K source ^ 4 ∂sourceLaw N K) =
      h8DenominatorFourthRawMoment N K := by
  let μA := standardRealGaussianMatrixMeasure (N + 1) N
  let μB := inverseLaw N K
  letI : IsProbabilityMeasure μA :=
    standardRealGaussianMatrixMeasure_isProbability_internal _ _
  letI : IsProbabilityMeasure μB :=
    standardRealGaussianMatrixMeasure_isProbability_internal _ _
  have hInt := integrable_betaPrimeTraceOneSource_fourth_h14_low
    (N := N) (K := K) hgap
  calc
    (∫ source, betaPrimeTraceOneSource N K source ^ 4 ∂sourceLaw N K) =
        ∫ H, ∫ G, betaPrimeTraceOneSource N K (G, H) ^ 4 ∂μA ∂μB := by
          change (∫ source, betaPrimeTraceOneSource N K source ^ 4 ∂(μA.prod μB)) = _
          exact integral_prod_symm _ hInt
    _ = ∫ H, h14TraceOneFourthWickPolynomial (N + 1)
          (scaledInverseWishartMatrix N K H) ∂μB := by
          apply integral_congr_ae
          filter_upwards [] with H
          exact hWick.traceOne_fourth_fiber_eq H
    _ = h8DenominatorFourthRawMoment N K := rfl

theorem betaPrimeTraceTwoSource_square_integral_eq_denominator_internal
    (N K : ℕ) (hgap : 2 * N + 8 ≤ K)
    (hWick : H14FiniteGaussianFourthWickFormula N K) :
    (∫ source, betaPrimeTraceTwoSource N K source ^ 2 ∂sourceLaw N K) =
      h10DenominatorSecondRawMoment N K := by
  let μA := standardRealGaussianMatrixMeasure (N + 1) N
  let μB := inverseLaw N K
  letI : IsProbabilityMeasure μA :=
    standardRealGaussianMatrixMeasure_isProbability_internal _ _
  letI : IsProbabilityMeasure μB :=
    standardRealGaussianMatrixMeasure_isProbability_internal _ _
  have hInt := integrable_betaPrimeTraceTwoSource_square_h14_low
    (N := N) (K := K) hgap
  calc
    (∫ source, betaPrimeTraceTwoSource N K source ^ 2 ∂sourceLaw N K) =
        ∫ H, ∫ G, betaPrimeTraceTwoSource N K (G, H) ^ 2 ∂μA ∂μB := by
          change (∫ source, betaPrimeTraceTwoSource N K source ^ 2 ∂(μA.prod μB)) = _
          exact integral_prod_symm _ hInt
    _ = ∫ H, h14TraceTwoSquareWickPolynomial (N + 1)
          (scaledInverseWishartMatrix N K H) ∂μB := by
          apply integral_congr_ae
          filter_upwards [] with H
          exact hWick.traceTwo_square_fiber_eq H
    _ = h10DenominatorSecondRawMoment N K := rfl

theorem betaPrimeTraceOneSquareSource_variance_eq_denominator_internal
    (N K : ℕ) (hgap : 2 * N + 8 ≤ K)
    (hWick : H14FiniteGaussianFourthWickFormula N K) :
    ProbabilityTheory.variance
        (fun source => betaPrimeTraceOneSource N K source ^ 2) (sourceLaw N K) =
      h8DenominatorCenteredVariance N K := by
  letI := realBetaPrimeGaussianSourceLaw_isProbability N K
  have hMem := betaPrimeTraceOneSquareSource_memLp_two N K hgap
  rw [ProbabilityTheory.variance_eq_sub hMem]
  simp only [Pi.pow_apply]
  rw [show (fun source => (betaPrimeTraceOneSource N K source ^ 2) ^ 2) =
      (fun source => betaPrimeTraceOneSource N K source ^ 4) by
        funext source
        ring]
  rw [betaPrimeTraceOneSource_fourth_integral_eq_denominator_internal N K hgap hWick]
  rw [betaPrimeTraceOneSource_square_integral_eq_denominator_internal N K hgap]
  rfl

theorem betaPrimeTraceTwoSource_variance_eq_denominator_internal
    (N K : ℕ) (hgap : 2 * N + 8 ≤ K)
    (hWick : H14FiniteGaussianFourthWickFormula N K) :
    ProbabilityTheory.variance (betaPrimeTraceTwoSource N K) (sourceLaw N K) =
      h10DenominatorCenteredVariance N K := by
  letI := realBetaPrimeGaussianSourceLaw_isProbability N K
  have hMem := betaPrimeTraceTwoSource_memLp_two N K hgap
  rw [ProbabilityTheory.variance_eq_sub hMem]
  simp only [Pi.pow_apply]
  rw [betaPrimeTraceTwoSource_square_integral_eq_denominator_internal N K hgap hWick]
  rw [betaPrimeTraceTwoSource_integral_eq_denominator_internal N K hgap]
  rfl

theorem betaPrimeTraceOneSquareSource_centered_lpNorm_eq_internal
    (N K : ℕ) (hgap : 2 * N + 8 ≤ K)
    (hWick : H14FiniteGaussianFourthWickFormula N K) :
    lpNorm
        (fun source => betaPrimeTraceOneSource N K source ^ 2 -
          ∫ z, betaPrimeTraceOneSource N K z ^ 2 ∂sourceLaw N K)
        2 (sourceLaw N K) =
      Real.sqrt (h8DenominatorCenteredVariance N K) := by
  letI := realBetaPrimeGaussianSourceLaw_isProbability N K
  rw [lpNorm_centered_two_eq_sqrt_variance
    (betaPrimeTraceOneSquareSource_memLp_two N K hgap)]
  rw [betaPrimeTraceOneSquareSource_variance_eq_denominator_internal N K hgap hWick]

theorem betaPrimeTraceTwoSource_centered_lpNorm_eq_internal
    (N K : ℕ) (hgap : 2 * N + 8 ≤ K)
    (hWick : H14FiniteGaussianFourthWickFormula N K) :
    lpNorm
        (fun source => betaPrimeTraceTwoSource N K source -
          ∫ z, betaPrimeTraceTwoSource N K z ∂sourceLaw N K)
        2 (sourceLaw N K) =
      Real.sqrt (h10DenominatorCenteredVariance N K) := by
  letI := realBetaPrimeGaussianSourceLaw_isProbability N K
  rw [lpNorm_centered_two_eq_sqrt_variance
    (betaPrimeTraceTwoSource_memLp_two N K hgap)]
  rw [betaPrimeTraceTwoSource_variance_eq_denominator_internal N K hgap hWick]

/-!
The following record is deliberately below endpoint level.  The fourth-Wick
field is the finite Gaussian identity; the two scalar fields are the exact
post-cancellation inverse-Wishart inequalities.  In particular, neither field
may be replaced by a bound on a raw trace polynomial.
-/

structure H8H10ExactFourthMomentTransport (N K : ℕ) : Prop where
  finiteGaussianFourthWick : H14FiniteGaussianFourthWickFormula N K
  traceOneSquare_centeredVariance_le :
    16 * N ≤ K →
      h8DenominatorCenteredVariance N K ≤
        (denseClassicalMomentConstant * (N : ℝ) ^ 3) ^ 2
  traceTwo_centeredVariance_le :
    16 * N ≤ K →
      h10DenominatorCenteredVariance N K ≤
        (denseClassicalMomentConstant * (N : ℝ) ^ 2) ^ 2

/-! ## Direct pushforward, with no H6 or A7 detour -/

private theorem memLp_betaPrime_of_source_comp_internal
    {N K : ℕ} {p : ℝ≥0∞} {g : (Fin 4 → ℝ) → ℝ}
    (hg : AEStronglyMeasurable g (betaPrimeTraceFourLaw N K))
    (hsource : MemLp (g ∘ realBetaPrimeTracePowerVector 4 N K) p
      (sourceLaw N K)) :
    MemLp g p (betaPrimeTraceFourLaw N K) := by
  let f := realBetaPrimeTracePowerVector 4 N K
  let μ := sourceLaw N K
  have hmap : Measure.map f μ = betaPrimeTraceFourLaw N K := rfl
  have hgMap : AEStronglyMeasurable g (Measure.map f μ) := by
    simpa only [hmap] using hg
  have hf : AEMeasurable f μ :=
    (measurable_realBetaPrimeTracePowerVector_internal 4 N K).aemeasurable
  have hraw : MemLp g p (Measure.map f μ) :=
    (memLp_map_measure_iff hgMap hf).2 hsource
  simpa only [hmap] using hraw

private theorem lpNorm_betaPrime_eq_source_comp_internal
    {N K : ℕ} {p : ℝ≥0∞} {g : (Fin 4 → ℝ) → ℝ}
    (hg : AEStronglyMeasurable g (betaPrimeTraceFourLaw N K)) :
    lpNorm g p (betaPrimeTraceFourLaw N K) =
      lpNorm (g ∘ realBetaPrimeTracePowerVector 4 N K) p (sourceLaw N K) := by
  let f := realBetaPrimeTracePowerVector 4 N K
  let μ := sourceLaw N K
  have hmap : Measure.map f μ = betaPrimeTraceFourLaw N K := rfl
  have hgMap : AEStronglyMeasurable g (Measure.map f μ) := by
    simpa only [hmap] using hg
  have hf : AEMeasurable f μ :=
    (measurable_realBetaPrimeTracePowerVector_internal 4 N K).aemeasurable
  have hgComp : AEStronglyMeasurable (g ∘ f) μ :=
    hgMap.comp_aemeasurable hf
  rw [← hmap]
  unfold lpNorm
  rw [if_pos hgMap, if_pos hgComp]
  exact congrArg ENNReal.toReal (eLpNorm_map_measure (p := p) hgMap hf)

private theorem betaPrimeTraceFour_integral_eq_source_comp_internal
    {N K : ℕ} {g : (Fin 4 → ℝ) → ℝ}
    (hg : AEStronglyMeasurable g (betaPrimeTraceFourLaw N K)) :
    (∫ u, g u ∂betaPrimeTraceFourLaw N K) =
      ∫ source, g (realBetaPrimeTracePowerVector 4 N K source) ∂sourceLaw N K := by
  unfold betaPrimeTraceFourLaw
  rw [integral_map
    (measurable_realBetaPrimeTracePowerVector_internal 4 N K).aemeasurable hg]

/-! ## All-dimensional qualitative closure and exact norm identities -/

/-- Direct pushforward proves the qualitative H8 statement in every
dimension in the moment range, and identifies its norm with the exact
centered denominator variance. -/
theorem betaPrimeYTraceOneSquare_centered_memLp_two_and_lpNorm_eq_sqrt_internal
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K)
    (hWick : H14FiniteGaussianFourthWickFormula N K) :
    MemLp
        (fun u => betaPrimeYTraceOne N K u ^ 2 -
          ∫ z, betaPrimeYTraceOne N K z ^ 2 ∂betaPrimeTraceFourLaw N K)
        2 (betaPrimeTraceFourLaw N K) ∧
      lpNorm
          (fun u => betaPrimeYTraceOne N K u ^ 2 -
            ∫ z, betaPrimeYTraceOne N K z ^ 2 ∂betaPrimeTraceFourLaw N K)
          2 (betaPrimeTraceFourLaw N K) =
        Real.sqrt (h8DenominatorCenteredVariance N K) := by
  letI := realBetaPrimeGaussianSourceLaw_isProbability N K
  let g : (Fin 4 → ℝ) → ℝ := fun u => betaPrimeYTraceOne N K u ^ 2
  have hg : AEStronglyMeasurable g (betaPrimeTraceFourLaw N K) := by
    apply Measurable.aestronglyMeasurable
    dsimp [g]
    unfold betaPrimeYTraceOne
    fun_prop
  have hMean := betaPrimeTraceFour_integral_eq_source_comp_internal hg
  have hComp :
      (fun u => g u - ∫ z, g z ∂betaPrimeTraceFourLaw N K) ∘
          realBetaPrimeTracePowerVector 4 N K =
        fun source => betaPrimeTraceOneSource N K source ^ 2 -
          ∫ z, betaPrimeTraceOneSource N K z ^ 2 ∂sourceLaw N K := by
    funext source
    simp only [Function.comp_apply]
    rw [hMean]
    rfl
  have hSourceRaw := betaPrimeTraceOneSquareSource_memLp_two N K hgap
  have hSourceCentered : MemLp
      (fun source => betaPrimeTraceOneSource N K source ^ 2 -
        ∫ z, betaPrimeTraceOneSource N K z ^ 2 ∂sourceLaw N K)
      2 (sourceLaw N K) :=
    hSourceRaw.sub (memLp_const _)
  have hgCentered : AEStronglyMeasurable
      (fun u => g u - ∫ z, g z ∂betaPrimeTraceFourLaw N K)
      (betaPrimeTraceFourLaw N K) := hg.sub aestronglyMeasurable_const
  have hTarget := memLp_betaPrime_of_source_comp_internal hgCentered (by
    rw [hComp]
    exact hSourceCentered)
  have hTargetFrozen : MemLp
      (fun u => betaPrimeYTraceOne N K u ^ 2 -
        ∫ z, betaPrimeYTraceOne N K z ^ 2 ∂betaPrimeTraceFourLaw N K)
      2 (betaPrimeTraceFourLaw N K) := by
    simpa only [g] using hTarget
  refine ⟨hTargetFrozen, ?_⟩
  have hNorm := lpNorm_betaPrime_eq_source_comp_internal (p := 2) hgCentered
  rw [hComp] at hNorm
  calc
    lpNorm
        (fun u => betaPrimeYTraceOne N K u ^ 2 -
          ∫ z, betaPrimeYTraceOne N K z ^ 2 ∂betaPrimeTraceFourLaw N K)
        2 (betaPrimeTraceFourLaw N K) =
      lpNorm
        (fun source => betaPrimeTraceOneSource N K source ^ 2 -
          ∫ z, betaPrimeTraceOneSource N K z ^ 2 ∂sourceLaw N K)
        2 (sourceLaw N K) := by simpa only [g] using hNorm
    _ = Real.sqrt (h8DenominatorCenteredVariance N K) :=
      betaPrimeTraceOneSquareSource_centered_lpNorm_eq_internal
        N K hgap hWick

/-- Direct pushforward proves the qualitative H10 statement in every
dimension in the moment range, and identifies its norm with the exact
centered denominator variance. -/
theorem betaPrimeYTraceTwo_centered_memLp_two_and_lpNorm_eq_sqrt_internal
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K)
    (hWick : H14FiniteGaussianFourthWickFormula N K) :
    MemLp
        (fun u => betaPrimeYTraceTwo N K u -
          ∫ z, betaPrimeYTraceTwo N K z ∂betaPrimeTraceFourLaw N K)
        2 (betaPrimeTraceFourLaw N K) ∧
      lpNorm
          (fun u => betaPrimeYTraceTwo N K u -
            ∫ z, betaPrimeYTraceTwo N K z ∂betaPrimeTraceFourLaw N K)
          2 (betaPrimeTraceFourLaw N K) =
        Real.sqrt (h10DenominatorCenteredVariance N K) := by
  letI := realBetaPrimeGaussianSourceLaw_isProbability N K
  let g : (Fin 4 → ℝ) → ℝ := betaPrimeYTraceTwo N K
  have hg : AEStronglyMeasurable g (betaPrimeTraceFourLaw N K) := by
    apply Measurable.aestronglyMeasurable
    dsimp [g]
    unfold betaPrimeYTraceTwo
    fun_prop
  have hMean := betaPrimeTraceFour_integral_eq_source_comp_internal hg
  have hComp :
      (fun u => g u - ∫ z, g z ∂betaPrimeTraceFourLaw N K) ∘
          realBetaPrimeTracePowerVector 4 N K =
        fun source => betaPrimeTraceTwoSource N K source -
          ∫ z, betaPrimeTraceTwoSource N K z ∂sourceLaw N K := by
    funext source
    simp only [Function.comp_apply]
    rw [hMean]
    rfl
  have hSourceRaw := betaPrimeTraceTwoSource_memLp_two N K hgap
  have hSourceCentered : MemLp
      (fun source => betaPrimeTraceTwoSource N K source -
        ∫ z, betaPrimeTraceTwoSource N K z ∂sourceLaw N K)
      2 (sourceLaw N K) :=
    hSourceRaw.sub (memLp_const _)
  have hgCentered : AEStronglyMeasurable
      (fun u => g u - ∫ z, g z ∂betaPrimeTraceFourLaw N K)
      (betaPrimeTraceFourLaw N K) := hg.sub aestronglyMeasurable_const
  have hTarget := memLp_betaPrime_of_source_comp_internal hgCentered (by
    rw [hComp]
    exact hSourceCentered)
  have hTargetFrozen : MemLp
      (fun u => betaPrimeYTraceTwo N K u -
        ∫ z, betaPrimeYTraceTwo N K z ∂betaPrimeTraceFourLaw N K)
      2 (betaPrimeTraceFourLaw N K) := by
    simpa only [g] using hTarget
  refine ⟨hTargetFrozen, ?_⟩
  have hNorm := lpNorm_betaPrime_eq_source_comp_internal (p := 2) hgCentered
  rw [hComp] at hNorm
  calc
    lpNorm
        (fun u => betaPrimeYTraceTwo N K u -
          ∫ z, betaPrimeYTraceTwo N K z ∂betaPrimeTraceFourLaw N K)
        2 (betaPrimeTraceFourLaw N K) =
      lpNorm
        (fun source => betaPrimeTraceTwoSource N K source -
          ∫ z, betaPrimeTraceTwoSource N K z ∂sourceLaw N K)
        2 (sourceLaw N K) := by simpa only [g] using hNorm
    _ = Real.sqrt (h10DenominatorCenteredVariance N K) :=
      betaPrimeTraceTwoSource_centered_lpNorm_eq_internal N K hgap hWick

/-! ## Literal H8/H10 packages from the exact lower-level record -/

theorem betaPrimeYTraceOneSquare_centered_two_momentPackage_of_exactTransport
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (hTransport : H8H10ExactFourthMomentTransport N K) :
    MemLp
        (fun u => betaPrimeYTraceOne N K u ^ 2 -
          ∫ z, betaPrimeYTraceOne N K z ^ 2 ∂betaPrimeTraceFourLaw N K)
        2 (betaPrimeTraceFourLaw N K)
      ∧
    (16 * N ≤ K →
      lpNorm
          (fun u => betaPrimeYTraceOne N K u ^ 2 -
            ∫ z, betaPrimeYTraceOne N K z ^ 2 ∂betaPrimeTraceFourLaw N K)
          2 (betaPrimeTraceFourLaw N K)
        ≤ denseClassicalMomentConstant * (N : ℝ) ^ 3) := by
  letI := realBetaPrimeGaussianSourceLaw_isProbability N K
  let g : (Fin 4 → ℝ) → ℝ := fun u => betaPrimeYTraceOne N K u ^ 2
  have hg : AEStronglyMeasurable g (betaPrimeTraceFourLaw N K) := by
    apply Measurable.aestronglyMeasurable
    dsimp [g]
    unfold betaPrimeYTraceOne
    fun_prop
  have hMean := betaPrimeTraceFour_integral_eq_source_comp_internal hg
  have hComp :
      (fun u => g u - ∫ z, g z ∂betaPrimeTraceFourLaw N K) ∘
          realBetaPrimeTracePowerVector 4 N K =
        fun source => betaPrimeTraceOneSource N K source ^ 2 -
          ∫ z, betaPrimeTraceOneSource N K z ^ 2 ∂sourceLaw N K := by
    funext source
    simp only [Function.comp_apply]
    rw [hMean]
    rfl
  have hSourceRaw := betaPrimeTraceOneSquareSource_memLp_two N K hgap
  have hSourceCentered : MemLp
      (fun source => betaPrimeTraceOneSource N K source ^ 2 -
        ∫ z, betaPrimeTraceOneSource N K z ^ 2 ∂sourceLaw N K)
      2 (sourceLaw N K) :=
    hSourceRaw.sub (memLp_const _)
  have hgCentered : AEStronglyMeasurable
      (fun u => g u - ∫ z, g z ∂betaPrimeTraceFourLaw N K)
      (betaPrimeTraceFourLaw N K) := hg.sub (aestronglyMeasurable_const)
  have hTarget := memLp_betaPrime_of_source_comp_internal hgCentered (by
    rw [hComp]
    exact hSourceCentered)
  have hTargetFrozen : MemLp
      (fun u => betaPrimeYTraceOne N K u ^ 2 -
        ∫ z, betaPrimeYTraceOne N K z ^ 2 ∂betaPrimeTraceFourLaw N K)
      2 (betaPrimeTraceFourLaw N K) := by
    simpa only [g] using hTarget
  refine ⟨hTargetFrozen, ?_⟩
  intro hdense
  have hNorm := lpNorm_betaPrime_eq_source_comp_internal (p := 2) hgCentered
  rw [hComp] at hNorm
  have hNormFrozen :
      lpNorm
          (fun u => betaPrimeYTraceOne N K u ^ 2 -
            ∫ z, betaPrimeYTraceOne N K z ^ 2 ∂betaPrimeTraceFourLaw N K)
          2 (betaPrimeTraceFourLaw N K) =
        lpNorm
          (fun source => betaPrimeTraceOneSource N K source ^ 2 -
            ∫ z, betaPrimeTraceOneSource N K z ^ 2 ∂sourceLaw N K)
          2 (sourceLaw N K) := by
    simpa only [g] using hNorm
  rw [hNormFrozen]
  rw [betaPrimeTraceOneSquareSource_centered_lpNorm_eq_internal N K hgap
    hTransport.finiteGaussianFourthWick]
  exact Real.sqrt_le_iff.mpr ⟨by
      exact mul_nonneg (by norm_num [denseClassicalMomentConstant])
        (pow_nonneg (by positivity) 3),
    hTransport.traceOneSquare_centeredVariance_le hdense⟩

theorem betaPrimeYTraceTwo_centered_two_momentPackage_of_exactTransport
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (hTransport : H8H10ExactFourthMomentTransport N K) :
    MemLp
        (fun u => betaPrimeYTraceTwo N K u -
          ∫ z, betaPrimeYTraceTwo N K z ∂betaPrimeTraceFourLaw N K)
        2 (betaPrimeTraceFourLaw N K)
      ∧
    (16 * N ≤ K →
      lpNorm
          (fun u => betaPrimeYTraceTwo N K u -
            ∫ z, betaPrimeYTraceTwo N K z ∂betaPrimeTraceFourLaw N K)
          2 (betaPrimeTraceFourLaw N K)
        ≤ denseClassicalMomentConstant * (N : ℝ) ^ 2) := by
  letI := realBetaPrimeGaussianSourceLaw_isProbability N K
  let g : (Fin 4 → ℝ) → ℝ := betaPrimeYTraceTwo N K
  have hg : AEStronglyMeasurable g (betaPrimeTraceFourLaw N K) := by
    apply Measurable.aestronglyMeasurable
    dsimp [g]
    unfold betaPrimeYTraceTwo
    fun_prop
  have hMean := betaPrimeTraceFour_integral_eq_source_comp_internal hg
  have hComp :
      (fun u => g u - ∫ z, g z ∂betaPrimeTraceFourLaw N K) ∘
          realBetaPrimeTracePowerVector 4 N K =
        fun source => betaPrimeTraceTwoSource N K source -
          ∫ z, betaPrimeTraceTwoSource N K z ∂sourceLaw N K := by
    funext source
    simp only [Function.comp_apply]
    rw [hMean]
    rfl
  have hSourceRaw := betaPrimeTraceTwoSource_memLp_two N K hgap
  have hSourceCentered : MemLp
      (fun source => betaPrimeTraceTwoSource N K source -
        ∫ z, betaPrimeTraceTwoSource N K z ∂sourceLaw N K)
      2 (sourceLaw N K) :=
    hSourceRaw.sub (memLp_const _)
  have hgCentered : AEStronglyMeasurable
      (fun u => g u - ∫ z, g z ∂betaPrimeTraceFourLaw N K)
      (betaPrimeTraceFourLaw N K) := hg.sub (aestronglyMeasurable_const)
  have hTarget := memLp_betaPrime_of_source_comp_internal hgCentered (by
    rw [hComp]
    exact hSourceCentered)
  have hTargetFrozen : MemLp
      (fun u => betaPrimeYTraceTwo N K u -
        ∫ z, betaPrimeYTraceTwo N K z ∂betaPrimeTraceFourLaw N K)
      2 (betaPrimeTraceFourLaw N K) := by
    simpa only [g] using hTarget
  refine ⟨hTargetFrozen, ?_⟩
  intro hdense
  have hNorm := lpNorm_betaPrime_eq_source_comp_internal (p := 2) hgCentered
  rw [hComp] at hNorm
  have hNormFrozen :
      lpNorm
          (fun u => betaPrimeYTraceTwo N K u -
            ∫ z, betaPrimeYTraceTwo N K z ∂betaPrimeTraceFourLaw N K)
          2 (betaPrimeTraceFourLaw N K) =
        lpNorm
          (fun source => betaPrimeTraceTwoSource N K source -
            ∫ z, betaPrimeTraceTwoSource N K z ∂sourceLaw N K)
          2 (sourceLaw N K) := by
    simpa only [g] using hNorm
  rw [hNormFrozen]
  rw [betaPrimeTraceTwoSource_centered_lpNorm_eq_internal N K hgap
    hTransport.finiteGaussianFourthWick]
  exact Real.sqrt_le_iff.mpr ⟨by
      exact mul_nonneg (by norm_num [denseClassicalMomentConstant])
        (pow_nonneg (by positivity) 2),
    hTransport.traceTwo_centeredVariance_le hdense⟩

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08
