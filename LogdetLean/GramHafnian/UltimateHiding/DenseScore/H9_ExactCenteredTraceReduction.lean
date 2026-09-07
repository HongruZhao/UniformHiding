import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H9_Conditional
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H9_U03GaussianFourth
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.H9CenteredTraceSteinClosure

/-!
# Exact H9 reduction to the centered inverse-trace Stein contraction

The completed fixed-denominator standard-Gaussian fourth-Wick theorem gives
the numerator `L^4` package directly by Fubini.  This avoids the older
conditional positive-ridge numerator package: no differentiation with
respect to the denominator matrix is needed when the numerator Gaussian is
integrated first.

Consequently the literal frozen H9 statement follows from the single scalar
centered inverse-Wishart contraction isolated in
`H9CenteredTraceSteinClosure`.  No endpoint axiom, `sorry`, or replacement
statement is used here.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.Wishart
open LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08

private theorem h9ScaledInverseWishart_transpose
    {N K : ℕ} (B : H9InverseWishartSample N K) :
    (h9ScaledInverseWishart N K B).transpose =
      h9ScaledInverseWishart N K B := by
  unfold h9ScaledInverseWishart
  rw [Matrix.transpose_smul]
  congr 1
  exact realWishartGram_inv_isSymm B

/-- The source numerator fluctuation is exactly the fixed-denominator
quadratic form proved in the U03 Wick module. -/
theorem h9SourceNumeratorFluctuation_eq_u03FixedDenominator
    (N K : ℕ) (p : H9BetaPrimeGaussianSource N K) :
    h9SourceNumeratorFluctuation N K p =
      h9U03FixedDenominatorGaussianFluctuation
        (h9ScaledInverseWishart N K p.2) p.1 := by
  simp [h9SourceNumeratorFluctuation,
    h9U03FixedDenominatorGaussianFluctuation,
    h9SourceInverseTrace, h9ScaledInverseWishart,
    realMatrixBetaPrimeOfGaussianSource,
    Matrix.trace_smul]
  ring

/-- The squared trace occurring in the U03 contraction is literally the
denominator observable already controlled by U08. -/
private theorem h9TraceScaledInverseWishartSq_eq
    {N K : ℕ} (B : H9InverseWishartSample N K) :
    Matrix.trace ((h9ScaledInverseWishart N K B) ^ 2) =
      h9InverseTraceSquare N K B := by
  simp [h9InverseTraceSquare, pow_two]

private theorem h9FixedDenominatorFourthContraction_le
    (m : ℕ) (hm : 2 ≤ m) (T2 T4 : ℝ) (hT4 : T4 ≤ T2 ^ 2) :
    48 * (m : ℝ) * T4 + 12 * (m : ℝ) ^ 2 * T2 ^ 2 ≤
      36 * (m : ℝ) ^ 2 * T2 ^ 2 := by
  have hm0 : 0 ≤ (m : ℝ) := by positivity
  have hm2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hfirst : 48 * (m : ℝ) * T4 ≤ 48 * (m : ℝ) * T2 ^ 2 :=
    mul_le_mul_of_nonneg_left hT4 (mul_nonneg (by norm_num) hm0)
  calc
    _ ≤ 48 * (m : ℝ) * T2 ^ 2 + 12 * (m : ℝ) ^ 2 * T2 ^ 2 :=
      by nlinarith
    _ = (48 * (m : ℝ) + 12 * (m : ℝ) ^ 2) * T2 ^ 2 := by ring
    _ ≤ 36 * (m : ℝ) ^ 2 * T2 ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      nlinarith

private theorem h9LpNormTwo_sq_eq_integral_sq
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

private theorem lpNorm_comp_measurePreserving_h9
    {Alpha Beta E : Type*} [MeasurableSpace Alpha] [MeasurableSpace Beta]
    [NormedAddCommGroup E] {mu : Measure Alpha} {nu : Measure Beta}
    {p : ENNReal} {f : Alpha → Beta} {g : Beta → E}
    (hg : AEStronglyMeasurable g nu) (hf : MeasurePreserving f mu nu) :
    lpNorm (g ∘ f) p mu = lpNorm g p nu := by
  have hgf : AEStronglyMeasurable (g ∘ f) mu :=
    (hf.map_eq ▸ hg).comp_aemeasurable hf.aemeasurable
  have he := congrArg ENNReal.toReal
    (eLpNorm_comp_measurePreserving (p := p) hg hf)
  simpa only [toReal_eLpNorm hgf, toReal_eLpNorm hg] using he

/-- Pull the centered inverse trace through the independent numerator
Gaussian marginal and apply the deterministic `(N+1)` scaling. -/
private theorem h9SourceDenominatorPackage_of_inverseWishart_exact
    {N K : ℕ} (hN : 1 ≤ N)
    (hinv : H9InverseWishartDenominatorPackage N K) :
    MemLp (h9SourceDenominatorFluctuation N K) 4
        (realBetaPrimeGaussianSourceLaw N K) ∧
      (16 * N ≤ K →
        lpNorm (h9SourceDenominatorFluctuation N K) 4
            (realBetaPrimeGaussianSourceLaw N K) ≤
          8192 * (N : ℝ)) := by
  let muG := standardRealGaussianMatrixMeasure (N + 1) N
  let muB := standardRealGaussianMatrixMeasure (K - N) N
  let x := h9CenteredInverseTrace N K
  letI : IsProbabilityMeasure muG :=
    standardRealGaussianMatrixMeasure_isProbability_internal _ _
  letI : IsProbabilityMeasure muB :=
    standardRealGaussianMatrixMeasure_isProbability_internal _ _
  have hx : MemLp x 4 muB := by
    simpa only [x, muB, h9InverseWishartDenominatorLaw] using
      hinv.centeredTrace_memLp_four
  have hcomp : MemLp
      (fun p : H9BetaPrimeGaussianSource N K => x p.2) 4
      (muG.prod muB) := hx.comp_snd muG
  have hpoint : h9SourceDenominatorFluctuation N K =
      fun p : H9BetaPrimeGaussianSource N K =>
        (((N + 1 : ℕ) : ℝ)) * x p.2 := by
    funext p
    simp [h9SourceDenominatorFluctuation, h9CenteredInverseTrace,
      h9ScaledInverseWishart, h9SourceInverseTrace, x, Matrix.trace_smul]
  have hnormComp :
      lpNorm (fun p : H9BetaPrimeGaussianSource N K => x p.2) 4
          (muG.prod muB) = lpNorm x 4 muB := by
    have hpres : MeasurePreserving
        (Prod.snd : H9BetaPrimeGaussianSource N K →
          H9InverseWishartSample N K) (muG.prod muB) muB := by
      exact measurePreserving_snd
    change lpNorm
      (x ∘ (Prod.snd : H9BetaPrimeGaussianSource N K →
        H9InverseWishartSample N K)) 4 (muG.prod muB) = lpNorm x 4 muB
    exact lpNorm_comp_measurePreserving_h9
      (p := (4 : ENNReal)) hx.aestronglyMeasurable hpres
  constructor
  · rw [hpoint]
    simpa only [muG, muB, realBetaPrimeGaussianSourceLaw] using
      hcomp.const_mul (((N + 1 : ℕ) : ℝ))
  · intro hdense
    have hxBound : lpNorm x 4 muB ≤ 4096 := by
      simpa only [x, muB, h9InverseWishartDenominatorLaw,
        h9InverseWishartMomentConstant] using (hinv.dense_bounds hdense).1
    have hscaleNorm :
        lpNorm (h9SourceDenominatorFluctuation N K) 4
            (muG.prod muB) =
          (((N + 1 : ℕ) : ℝ)) * lpNorm x 4 muB := by
      rw [hpoint]
      calc
        lpNorm (fun p : H9BetaPrimeGaussianSource N K =>
            (((N + 1 : ℕ) : ℝ)) * x p.2) 4 (muG.prod muB) =
            (((N + 1 : ℕ) : ℝ)) *
              lpNorm (fun p : H9BetaPrimeGaussianSource N K => x p.2) 4
                (muG.prod muB) := by
          simpa using lpNorm_fun_natCast_mul (N + 1)
            (fun p : H9BetaPrimeGaussianSource N K => x p.2)
            4 (muG.prod muB)
        _ = _ := by rw [hnormComp]
    have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    simpa only [muG, muB, realBetaPrimeGaussianSourceLaw] using
      (show lpNorm (h9SourceDenominatorFluctuation N K) 4 (muG.prod muB) ≤
          8192 * (N : ℝ) by
        rw [hscaleNorm]
        calc
          (((N + 1 : ℕ) : ℝ)) * lpNorm x 4 muB ≤
              (((N + 1 : ℕ) : ℝ)) * 4096 :=
            mul_le_mul_of_nonneg_left hxBound (by positivity)
          _ ≤ 8192 * (N : ℝ) := by
            push_cast
            nlinarith)

/-- Direct Fubini/Wick numerator package.  The only denominator input is
`Tr(D^2) in L^2`; the centered first-trace field is not used. -/
theorem h9SourceNumeratorPackage_of_fixedGaussianWick
    {N K : ℕ} (hN : 1 ≤ N) (_hgap : 2 * N + 8 ≤ K)
    (hinv : H9InverseWishartDenominatorPackage N K) :
    MemLp (h9SourceNumeratorFluctuation N K) 4
        (realBetaPrimeGaussianSourceLaw N K) ∧
      (16 * N ≤ K →
        lpNorm (h9SourceNumeratorFluctuation N K) 4
            (realBetaPrimeGaussianSourceLaw N K) ≤
          1024 * (N : ℝ)) := by
  let muG := standardRealGaussianMatrixMeasure (N + 1) N
  let muB := h9InverseWishartDenominatorLaw N K
  let Q := h9SourceNumeratorFluctuation N K
  let F : H9BetaPrimeGaussianSource N K → ℝ := fun p => Q p ^ 4
  let envelope : H9InverseWishartSample N K → ℝ := fun B =>
    36 * (((N + 1 : ℕ) : ℝ)) ^ 2 *
      h9InverseTraceSquare N K B ^ 2
  let hwick := h9U03GaussianFourthContractExactReduction_standardGaussianWick N
  letI : IsProbabilityMeasure muG :=
    standardRealGaussianMatrixMeasure_isProbability_internal _ _
  letI : IsProbabilityMeasure muB :=
    h9InverseWishartDenominatorLaw_isProbability N K
  have hQMeas : AEStronglyMeasurable Q (muG.prod muB) := by
    have htraceY : Measurable (fun p : H9BetaPrimeGaussianSource N K =>
        Matrix.trace (realMatrixBetaPrimeOfGaussianSource p)) := by
      have hcoord : Measurable (fun p : H9BetaPrimeGaussianSource N K =>
          realBetaPrimeTracePowerVector 4 N K p (0 : Fin 4)) :=
        (measurable_pi_apply (0 : Fin 4)).comp
          (measurable_realBetaPrimeTracePowerVector_external 4 N K)
      simpa [realBetaPrimeTracePowerVector] using hcoord
    have htraceInv : Measurable (h9SourceInverseTrace N K) := by
      exact (measurable_trace_nonsingInv_realWishartGram (K - N) N).comp
        measurable_snd
    apply Measurable.aestronglyMeasurable
    dsimp only [Q]
    unfold h9SourceNumeratorFluctuation
    exact measurable_const.mul
      (htraceY.sub (measurable_const.mul htraceInv))
  have hFMeas : AEStronglyMeasurable F (muG.prod muB) := by
    exact hQMeas.pow 4
  have hFiberMem (B : H9InverseWishartSample N K) :
      MemLp (fun G => Q (G, B)) 4 muG := by
    have h := hwick.fixedDenominator_memLp_four
      (h9ScaledInverseWishart N K B) (h9ScaledInverseWishart_transpose B)
    apply h.ae_eq
    filter_upwards [] with G
    exact (h9SourceNumeratorFluctuation_eq_u03FixedDenominator N K (G, B)).symm
  have hFiberInt (B : H9InverseWishartSample N K) :
      Integrable (fun G => F (G, B)) muG := by
    have h := (hFiberMem B).integrable_norm_rpow (by norm_num) (by norm_num)
    apply h.congr
    filter_upwards [] with G
    simp only [F, Q, Real.norm_eq_abs]
    norm_num
    have hfour : 0 ≤ Q (G, B) ^ 4 := by
      nlinarith [sq_nonneg (Q (G, B) ^ 2)]
    rw [← abs_pow, abs_of_nonneg hfour]
  have hFiberIntegral (B : H9InverseWishartSample N K) :
      (∫ G, F (G, B) ∂muG) =
        48 * (((N + 1 : ℕ) : ℝ)) *
            Matrix.trace ((h9ScaledInverseWishart N K B) ^ 4) +
          12 * (((N + 1 : ℕ) : ℝ)) ^ 2 *
            h9InverseTraceSquare N K B ^ 2 := by
    calc
      (∫ G, F (G, B) ∂muG) =
          ∫ G, h9U03FixedDenominatorGaussianFluctuation
              (h9ScaledInverseWishart N K B) G ^ 4 ∂muG := by
            apply integral_congr_ae
            filter_upwards [] with G
            dsimp only [F, Q]
            rw [h9SourceNumeratorFluctuation_eq_u03FixedDenominator]
      _ = 48 * (((N + 1 : ℕ) : ℝ)) *
            Matrix.trace ((h9ScaledInverseWishart N K B) ^ 4) +
          12 * (((N + 1 : ℕ) : ℝ)) ^ 2 *
            (Matrix.trace ((h9ScaledInverseWishart N K B) ^ 2)) ^ 2 :=
        hwick.fixedDenominator_fourth_integral
          (h9ScaledInverseWishart N K B) (h9ScaledInverseWishart_transpose B)
      _ = _ := by rw [h9TraceScaledInverseWishartSq_eq]
  have hFiberLe (B : H9InverseWishartSample N K) :
      (∫ G, ‖F (G, B)‖ ∂muG) ≤ envelope B := by
    have hnonneg (G : Matrix (Fin (N + 1)) (Fin N) ℝ) :
        0 ≤ F (G, B) := by positivity
    rw [show (∫ G, ‖F (G, B)‖ ∂muG) = ∫ G, F (G, B) ∂muG by
      apply integral_congr_ae
      filter_upwards [] with G
      rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg G)]]
    rw [hFiberIntegral]
    dsimp only [envelope]
    apply h9FixedDenominatorFourthContraction_le
      (N + 1) (by omega)
    simpa only [h9TraceScaledInverseWishartSq_eq] using
      hwick.symmetric_trace_four_le_trace_two_sq
        (h9ScaledInverseWishart N K B) (h9ScaledInverseWishart_transpose B)
  have hEnvelopeInt : Integrable envelope muB := by
    exact (hinv.traceSquare_memLp_two.integrable_sq.const_mul
      (36 * (((N + 1 : ℕ) : ℝ)) ^ 2))
  have hInnerMeas : AEStronglyMeasurable
      (fun B => ∫ G, ‖F (G, B)‖ ∂muG) muB := by
    simpa using hFMeas.norm.prod_swap.integral_prod_right'
  have hInnerInt : Integrable
      (fun B => ∫ G, ‖F (G, B)‖ ∂muG) muB := by
    apply hEnvelopeInt.mono hInnerMeas
    filter_upwards [] with B
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    rw [Real.norm_eq_abs, abs_of_nonneg]
    exact hFiberLe B
    dsimp only [envelope]
    positivity
  have hFInt : Integrable F (muG.prod muB) := by
    apply (integrable_prod_iff' hFMeas).2
    exact ⟨Filter.Eventually.of_forall hFiberInt, hInnerInt⟩
  have hQMem : MemLp Q 4 (muG.prod muB) := by
    apply (integrable_norm_rpow_iff hQMeas (by norm_num) (by norm_num)).mp
    simpa [F, Real.rpow_natCast, norm_pow] using hFInt.norm
  have hFourthIntegralLe :
      (∫ p, Q p ^ 4 ∂(muG.prod muB)) ≤ ∫ B, envelope B ∂muB := by
    calc
      (∫ p, Q p ^ 4 ∂(muG.prod muB)) =
          ∫ B, ∫ G, F (G, B) ∂muG ∂muB := by
            simpa only [F] using integral_prod_symm F hFInt
      _ ≤ ∫ B, envelope B ∂muB := by
        apply integral_mono_ae
        · exact hFInt.integral_prod_right
        · exact hEnvelopeInt
        · exact Filter.Eventually.of_forall fun B => by
            have hnorm := hFiberLe B
            change (∫ G, F (G, B) ∂muG) ≤ envelope B
            rw [show (∫ G, F (G, B) ∂muG) =
                ∫ G, ‖F (G, B)‖ ∂muG by
              apply integral_congr_ae
              filter_upwards [] with G
              rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]]
            exact hnorm
  constructor
  · simpa only [Q, muG, muB, realBetaPrimeGaussianSourceLaw,
      h9InverseWishartDenominatorLaw] using hQMem
  · intro hdense
    have htrace :
        lpNorm (h9InverseTraceSquare N K) 2 muB ≤ 4096 * (N : ℝ) := by
      simpa only [muB, h9InverseWishartMomentConstant] using
        (hinv.dense_bounds hdense).2
    have htraceSq :
        (∫ B, h9InverseTraceSquare N K B ^ 2 ∂muB) ≤
          (4096 * (N : ℝ)) ^ 2 := by
      rw [← h9LpNormTwo_sq_eq_integral_sq hinv.traceSquare_memLp_two]
      have hnorm0 : 0 ≤ lpNorm (h9InverseTraceSquare N K) 2 muB :=
        lpNorm_nonneg
      have hright0 : 0 ≤ 4096 * (N : ℝ) := by positivity
      nlinarith
    have hEnv :
        (∫ B, envelope B ∂muB) ≤
          36 * (((N + 1 : ℕ) : ℝ)) ^ 2 *
            (4096 * (N : ℝ)) ^ 2 := by
      rw [show (∫ B, envelope B ∂muB) =
          36 * (((N + 1 : ℕ) : ℝ)) ^ 2 *
            ∫ B, h9InverseTraceSquare N K B ^ 2 ∂muB by
        dsimp only [envelope]
        rw [integral_const_mul]]
      gcongr
    have hpow : lpNorm Q 4 (muG.prod muB) ^ 4 ≤
        36 * (((N + 1 : ℕ) : ℝ)) ^ 2 *
          (4096 * (N : ℝ)) ^ 2 := by
      rw [lpNorm_four_pow_four_eq_integral_pow_four_h9 hQMem]
      exact hFourthIntegralLe.trans (hEnv)
    have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hbudget :
        36 * (((N + 1 : ℕ) : ℝ)) ^ 2 * (4096 * (N : ℝ)) ^ 2 ≤
          (1024 * (N : ℝ)) ^ 4 := by
      push_cast
      nlinarith [sq_nonneg ((N : ℝ) - 1), sq_nonneg (N : ℝ),
        sq_nonneg ((N : ℝ) ^ 2 - 1)]
    have hcoarse : lpNorm Q 4 (muG.prod muB) ≤ 1024 * (N : ℝ) := by
      apply le_of_pow_le_pow_left₀ (by norm_num : (4 : ℕ) ≠ 0) (by positivity)
      exact hpow.trans hbudget
    simpa only [Q, muG, muB, realBetaPrimeGaussianSourceLaw,
      h9InverseWishartDenominatorLaw] using hcoarse

/-- Strongest exact endpoint reduction currently available: the literal H9
package follows from the single centered inverse-Wishart Stein contraction.
All numerator and remaining denominator fields are theorems. -/
theorem betaPrimeYTraceOne_centered_three_momentPackage_of_centeredTraceStein
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (H : H9CenteredTraceSteinContraction N K) :
    MemLp (fun u ↦ betaPrimeYTraceOne N K u -
      ∫ z, betaPrimeYTraceOne N K z ∂(betaPrimeTraceFourLaw N K)) 3
        (betaPrimeTraceFourLaw N K) ∧
      (16 * N ≤ K →
        lpNorm (fun u ↦ betaPrimeYTraceOne N K u -
          ∫ z, betaPrimeYTraceOne N K z ∂(betaPrimeTraceFourLaw N K)) 3
            (betaPrimeTraceFourLaw N K) ≤
          denseClassicalMomentConstant * (N : ℝ)) := by
  let hinv := h9U08InverseWishartContract_of_steinContraction hN hgap H
  obtain ⟨hNumMem, hNumDense⟩ :=
    h9SourceNumeratorPackage_of_fixedGaussianWick hN hgap hinv
  obtain ⟨hDenMem, hDenDense⟩ :=
    h9SourceDenominatorPackage_of_inverseWishart_exact hN hinv
  apply betaPrimeYTraceOne_centered_three_momentPackage_of_sourceL4
    hN hgap hNumMem hDenMem
  · intro hdense
    calc
      lpNorm (h9SourceNumeratorFluctuation N K) 4
          (realBetaPrimeGaussianSourceLaw N K) ≤
        1024 * (N : ℝ) := hNumDense hdense
      _ ≤ denseClassicalMomentConstant / 2 * (N : ℝ) := by
        unfold denseClassicalMomentConstant
        have hN0 : 0 ≤ (N : ℝ) := by positivity
        nlinarith
  · intro hdense
    calc
      lpNorm (h9SourceDenominatorFluctuation N K) 4
          (realBetaPrimeGaussianSourceLaw N K) ≤
        8192 * (N : ℝ) := hDenDense hdense
      _ ≤ denseClassicalMomentConstant / 2 * (N : ℝ) := by
        unfold denseClassicalMomentConstant
        have hN0 : 0 ≤ (N : ℝ) := by positivity
        nlinarith

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
