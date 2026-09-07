import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H12_ExactMomentEndpointA4
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.H12_RawFourthExactRecurrenceBound
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.H12_SourceProjectiveTraceInequalities
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# Sharp H12 projective fourth bound

The exact sphere ledger gives coefficient `16 * 9 = 144`; the older endpoint
rounded this to `1024`.  On the Gaussian source the traceless bracket retains
the factor `(N-1)/N`, whose exact recurrence moment is at most `22*N^6`.
Keeping `144` inside the exact recurrence certificate lowers the integer
constant further, from `144 * 22 = 3168` to `3151`.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.LocalAnticoncentration
open U08
open Matrix Unitary

set_option maxHeartbeats 7200000
set_option maxRecDepth 100000

def h12SharpProjectiveFourthMomentConstant : ℝ := 3151

theorem h12SharpProjectiveFourthMomentConstant_eq :
    h12SharpProjectiveFourthMomentConstant = 3151 := rfl

/-- Exact fixed-sphere H12 envelope. -/
def h12SharpProjectiveFourthEnvelope (N K : ℕ)
    (A : ConcreteMatrixState N) : ℝ :=
  144 * h12ConcreteTracelessBracket N K A ^ 2 / (N : ℝ) ^ 4

theorem h12SharpProjectiveFourthEnvelope_nonneg
    (N K : ℕ) (A : ConcreteMatrixState N) :
    0 ≤ h12SharpProjectiveFourthEnvelope N K A := by
  unfold h12SharpProjectiveFourthEnvelope
  positivity

/-- Beta-prime trace-vector form of the exact envelope. -/
def h12SharpBetaPrimeProjectiveFourthEnvelope (N K : ℕ)
    (u : Fin 4 → ℝ) : ℝ :=
  144 *
      (betaPrimeYTraceTwo N K u -
        (N : ℝ)⁻¹ * betaPrimeYTraceOne N K u ^ 2) ^ 2 /
    (N : ℝ) ^ 4

theorem h12SharpBetaPrimeProjectiveFourthEnvelope_nonneg
    (N K : ℕ) (u : Fin 4 → ℝ) :
    0 ≤ h12SharpBetaPrimeProjectiveFourthEnvelope N K u := by
  unfold h12SharpBetaPrimeProjectiveFourthEnvelope
  positivity

/-! ## Exact fixed-sphere coefficient -/

/-- The fixed-matrix H12 fibre package with the exact coefficient `144`. -/
theorem h12_fixedMatrix_projectiveFourth_package_sharp_internal
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (A : ConcreteMatrixState N)
    (hsymm : (unscaleCOECorner K A).IsSymm)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    Integrable (fun v : ComplexUnitSphere N ↦
        concreteCenteredEll 1 N K (A, v) ^ 4)
        (complexUnitSphereProbabilityMeasure N) ∧
      (∫ v : ComplexUnitSphere N,
        ‖concreteCenteredEll 1 N K (A, v) ^ 4‖
          ∂(complexUnitSphereProbabilityMeasure N)) ≤
        h12SharpProjectiveFourthEnvelope N K A := by
  let Y := concreteCOEY N K A
  let A0 := h14ProjectiveTraceZeroPart Y
  let sphere := complexUnitSphereProbabilityMeasure N
  have hA0 : A0.IsHermitian := by
    simpa only [A0, Y] using
      h12_traceZeroPart_isHermitian_of_support hN A hsupport
  have htr0 : Matrix.trace A0 = 0 := by
    simpa only [A0, Y] using trace_h14ProjectiveTraceZeroPart hN Y
  have hpair (v : ComplexUnitSphere N) :
      concreteCenteredEll 1 N K (A, v) =
        2 * (complexProjectiveTracePair v A0).re := by
    rw [concreteCenteredEll_one_eq_centeredTracePair_re_h12_internal
      hN hgap A v hsymm hsupport]
    rw [show A0 = h14ProjectiveTraceZeroPart Y by rfl,
      complexProjectiveTracePair_h14ProjectiveTraceZeroPart hN v Y]
  have hbase := integrable_complexProjectiveTracePair_fourth hN A0
  have hreal : Integrable (fun v : ComplexUnitSphere N ↦
      (complexProjectiveTracePair v A0).re ^ 4) sphere := by
    apply hbase.re.congr
    filter_upwards [] with v
    have him :=
      complexProjectiveTracePair_im_eq_zero_of_isHermitian_h12_low v A0 hA0
    simp [pow_succ, Complex.mul_re, him]
  have hscore : Integrable (fun v : ComplexUnitSphere N ↦
      concreteCenteredEll 1 N K (A, v) ^ 4) sphere := by
    apply (hreal.const_mul 16).congr
    filter_upwards [] with v
    rw [hpair v]
    ring
  refine ⟨hscore, ?_⟩
  have hexact := integral_complexProjectiveTracePair_re_fourth_eq_h12_low
    hN A0 hA0
  rw [htr0] at hexact
  simp only [Complex.zero_re, zero_pow (by norm_num : 4 ≠ 0),
    zero_pow (by norm_num : 2 ≠ 0), zero_mul, mul_zero, zero_add] at hexact
  let n : ℝ := N
  let t2 : ℝ := h12ConcreteTracelessBracket N K A
  let t4 : ℝ := (Matrix.trace (A0 * A0 * A0 * A0)).re
  have hn : 0 < n := by
    dsimp only [n]
    exact_mod_cast (show 0 < N by omega)
  have ht2eq : (Matrix.trace (A0 * A0)).re = t2 := by
    simpa only [A0, Y, t2] using
      trace_traceZeroPart_sq_re_eq_h12ConcreteTracelessBracket hN A hsupport
  have ht4le : t4 ≤ t2 ^ 2 := by
    simpa only [A0, Y, t4, t2] using
      trace_traceZeroPart_four_re_le_sq_h12 hN A hsupport
  have hD : n ^ 4 ≤ n * (n + 1) * (n + 2) * (n + 3) := by
    have hn0 : 0 ≤ n := hn.le
    calc
      n ^ 4 = n * n * n * n := by ring
      _ ≤ n * (n + 1) * (n + 2) * (n + 3) := by
        gcongr <;> linarith
  have hDpos : 0 < n * (n + 1) * (n + 2) * (n + 3) := by positivity
  have hinv :
      (n * (n + 1) * (n + 2) * (n + 3))⁻¹ ≤ (n ^ 4)⁻¹ :=
    (inv_le_inv₀ hDpos (by positivity)).2 hD
  calc
    (∫ v : ComplexUnitSphere N,
        ‖concreteCenteredEll 1 N K (A, v) ^ 4‖ ∂sphere) =
        ∫ v : ComplexUnitSphere N,
          concreteCenteredEll 1 N K (A, v) ^ 4 ∂sphere := by
      apply integral_congr_ae
      filter_upwards [] with v
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    _ = 16 * ∫ v : ComplexUnitSphere N,
          (complexProjectiveTracePair v A0).re ^ 4 ∂sphere := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with v
      rw [hpair v]
      ring
    _ = 16 * ((n * (n + 1) * (n + 2) * (n + 3))⁻¹ *
          (3 * t2 ^ 2 + 6 * t4)) := by
      rw [hexact]
      rw [ht2eq]
      dsimp only [n, t4]
      ring
    _ ≤ 16 * ((n * (n + 1) * (n + 2) * (n + 3))⁻¹ *
          (9 * t2 ^ 2)) := by
      gcongr
      nlinarith
    _ ≤ 16 * ((n ^ 4)⁻¹ * (9 * t2 ^ 2)) := by
      gcongr
    _ = 144 * t2 ^ 2 / n ^ 4 := by
      rw [inv_eq_one_div]
      field_simp [ne_of_gt hn]
      ring
    _ = h12SharpProjectiveFourthEnvelope N K A := rfl

/-! ## Source envelope and exact `22` integration -/

private theorem betaPrimeYTraceOne_comp_concreteTraceFour_h12_sharp
    (N K : ℕ) (A : ConcreteMatrixState N) :
    betaPrimeYTraceOne N K (concreteCOETracePowerVector 4 N K A) =
      concreteCOETraceOne N K A := by
  unfold betaPrimeYTraceOne concreteCOETracePowerVector concreteCOETraceOne
    concreteCOEY concreteRealTrace
  simp [pow_succ, Complex.mul_re]

private theorem betaPrimeYTraceTwo_comp_concreteTraceFour_h12_sharp
    (N K : ℕ) (A : ConcreteMatrixState N) :
    betaPrimeYTraceTwo N K (concreteCOETracePowerVector 4 N K A) =
      concreteCOETraceTwo N K A := by
  unfold betaPrimeYTraceTwo concreteCOETracePowerVector concreteCOETraceTwo
    concreteCOEY concreteRealTrace
  simp [pow_succ, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul,
    smul_smul, Complex.mul_re]

theorem h12_sharpBetaPrimeProjectiveFourthEnvelope_comp_traceFour_internal
    (N K : ℕ) (A : ConcreteMatrixState N) :
    h12SharpBetaPrimeProjectiveFourthEnvelope N K
        (concreteCOETracePowerVector 4 N K A) =
      h12SharpProjectiveFourthEnvelope N K A := by
  unfold h12SharpBetaPrimeProjectiveFourthEnvelope
    h12SharpProjectiveFourthEnvelope h12ConcreteTracelessBracket
  rw [betaPrimeYTraceOne_comp_concreteTraceFour_h12_sharp,
    betaPrimeYTraceTwo_comp_concreteTraceFour_h12_sharp]

private theorem measurable_h12SharpBetaPrimeProjectiveFourthEnvelope
    (N K : ℕ) :
    Measurable (h12SharpBetaPrimeProjectiveFourthEnvelope N K) := by
  unfold h12SharpBetaPrimeProjectiveFourthEnvelope betaPrimeYTraceOne
    betaPrimeYTraceTwo
  fun_prop

private theorem h12SharpBetaPrimeProjectiveFourthEnvelope_le_sourceMajorant
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (source : BetaPrimeGaussianSource N K) :
    h12SharpBetaPrimeProjectiveFourthEnvelope N K
        (realBetaPrimeTracePowerVector 4 N K source) ≤
      (144 / (N : ℝ) ^ 4) *
        (((((N : ℝ) - 1) / (N : ℝ)) ^ 2) *
          betaPrimeTraceTwoSource N K source ^ 2) := by
  let n : ℝ := N
  let tOne : ℝ := betaPrimeTraceOneSource N K source
  let tTwo : ℝ := betaPrimeTraceTwoSource N K source
  have hn : 0 < n := by
    dsimp only [n]
    exact_mod_cast (show 0 < N by omega)
  have hc : 0 ≤ concreteCOEExponent N K := by
    have hgapR : ((2 * N + 8 : ℕ) : ℝ) ≤ (K : ℝ) := by
      exact_mod_cast hgap
    push_cast at hgapR
    unfold concreteCOEExponent
    linarith
  have hsq := betaPrimeTracelessSourceBracket_sq_le_projectiveTraceTwo_sq
    hN hc source
  change 144 * (tTwo - n⁻¹ * tOne ^ 2) ^ 2 / n ^ 4 ≤
    (144 / n ^ 4) * (((n - 1) / n) ^ 2 * tTwo ^ 2)
  calc
    144 * (tTwo - n⁻¹ * tOne ^ 2) ^ 2 / n ^ 4 ≤
        144 * ((((n - 1) / n) * tTwo) ^ 2) / n ^ 4 := by
      gcongr
    _ = (144 / n ^ 4) * (((n - 1) / n) ^ 2 * tTwo ^ 2) := by
      ring

theorem integrable_h12SharpBetaPrimeProjectiveFourthEnvelope_source_internal
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    Integrable
      (h12SharpBetaPrimeProjectiveFourthEnvelope N K ∘
        realBetaPrimeTracePowerVector 4 N K)
      (realBetaPrimeGaussianSourceLaw N K) := by
  let n : ℝ := N
  let factor : ℝ := (n - 1) / n
  let sourceLaw := realBetaPrimeGaussianSourceLaw N K
  let tTwo : BetaPrimeGaussianSource N K → ℝ :=
    betaPrimeTraceTwoSource N K
  have hTwo : Integrable (fun source ↦ tTwo source ^ 2) sourceLaw := by
    simpa only [tTwo, sourceLaw] using
      (integrable_betaPrimeTraceTwoSource_square_h14_low
        (N := N) (K := K) hgap)
  have hMajor : Integrable
      (fun source ↦ (144 / n ^ 4) *
        (factor ^ 2 * tTwo source ^ 2)) sourceLaw :=
    ((hTwo.const_mul (factor ^ 2)).const_mul (144 / n ^ 4))
  have hEnvelopeMeas : AEStronglyMeasurable
      (h12SharpBetaPrimeProjectiveFourthEnvelope N K ∘
        realBetaPrimeTracePowerVector 4 N K) sourceLaw :=
    (measurable_h12SharpBetaPrimeProjectiveFourthEnvelope N K)
      |>.aestronglyMeasurable
      |>.comp_aemeasurable
        (measurable_realBetaPrimeTracePowerVector_internal 4 N K).aemeasurable
  apply Integrable.mono' hMajor hEnvelopeMeas
  filter_upwards [] with source
  change ‖h12SharpBetaPrimeProjectiveFourthEnvelope N K
      (realBetaPrimeTracePowerVector 4 N K source)‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg
    (h12SharpBetaPrimeProjectiveFourthEnvelope_nonneg N K _)]
  simpa only [n, factor, tTwo] using
    h12SharpBetaPrimeProjectiveFourthEnvelope_le_sourceMajorant
      hN hgap source

theorem integral_h12SharpBetaPrimeProjectiveFourthEnvelope_source_le_internal
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (hdense : 16 * N ≤ K) :
    (∫ source,
        h12SharpBetaPrimeProjectiveFourthEnvelope N K
          (realBetaPrimeTracePowerVector 4 N K source)
        ∂(realBetaPrimeGaussianSourceLaw N K)) ≤
      h12SharpProjectiveFourthMomentConstant * (N : ℝ) ^ 2 := by
  let n : ℝ := N
  let factor : ℝ := (n - 1) / n
  let sourceLaw := realBetaPrimeGaussianSourceLaw N K
  let tTwo : BetaPrimeGaussianSource N K → ℝ :=
    betaPrimeTraceTwoSource N K
  have hn : 0 < n := by
    dsimp only [n]
    exact_mod_cast (show 0 < N by omega)
  have hTwo : Integrable (fun source ↦ tTwo source ^ 2) sourceLaw := by
    simpa only [tTwo, sourceLaw] using
      (integrable_betaPrimeTraceTwoSource_square_h14_low
        (N := N) (K := K) hgap)
  have hMajor : Integrable
      (fun source ↦ (144 / n ^ 4) *
        (factor ^ 2 * tTwo source ^ 2)) sourceLaw :=
    ((hTwo.const_mul (factor ^ 2)).const_mul (144 / n ^ 4))
  have hEnvelopeInt : Integrable
      (fun source ↦ h12SharpBetaPrimeProjectiveFourthEnvelope N K
        (realBetaPrimeTracePowerVector 4 N K source)) sourceLaw := by
    have h := integrable_h12SharpBetaPrimeProjectiveFourthEnvelope_source_internal
      hN hgap
    change Integrable
      (fun source ↦ h12SharpBetaPrimeProjectiveFourthEnvelope N K
        (realBetaPrimeTracePowerVector 4 N K source)) sourceLaw at h
    exact h
  have hPoint : ∀ source,
      h12SharpBetaPrimeProjectiveFourthEnvelope N K
          (realBetaPrimeTracePowerVector 4 N K source) ≤
        (144 / n ^ 4) * (factor ^ 2 * tTwo source ^ 2) := by
    intro source
    simpa only [n, factor, tTwo] using
      h12SharpBetaPrimeProjectiveFourthEnvelope_le_sourceMajorant
        hN hgap source
  have hMono :
      (∫ source,
          h12SharpBetaPrimeProjectiveFourthEnvelope N K
            (realBetaPrimeTracePowerVector 4 N K source) ∂sourceLaw) ≤
        ∫ source, (144 / n ^ 4) *
          (factor ^ 2 * tTwo source ^ 2) ∂sourceLaw :=
    integral_mono hEnvelopeInt hMajor hPoint
  have hProjective : 144 * factor ^ 2 *
      (∫ source, tTwo source ^ 2 ∂sourceLaw) ≤ 3151 * n ^ 6 := by
    by_cases hNOne : N = 1
    · subst N
      norm_num [factor, n]
    · have hNTwo : 2 ≤ N := by omega
      simpa only [factor, n, tTwo, sourceLaw,
        h12CompleteProjectiveFourthConstantTwoPlus] using
        betaPrimeTraceTwoSource_square_integral_projective_144_le_3151_internal
          hNTwo hdense
  calc
    (∫ source,
        h12SharpBetaPrimeProjectiveFourthEnvelope N K
          (realBetaPrimeTracePowerVector 4 N K source) ∂sourceLaw) ≤
        ∫ source, (144 / n ^ 4) *
          (factor ^ 2 * tTwo source ^ 2) ∂sourceLaw := hMono
    _ = (144 / n ^ 4) *
          (factor ^ 2 * (∫ source, tTwo source ^ 2 ∂sourceLaw)) := by
      rw [integral_const_mul, integral_const_mul]
    _ = (1 / n ^ 4) *
          (144 * factor ^ 2 *
            (∫ source, tTwo source ^ 2 ∂sourceLaw)) := by ring
    _ ≤ (1 / n ^ 4) * (3151 * n ^ 6) := by
      exact mul_le_mul_of_nonneg_left hProjective (by positivity)
    _ = h12SharpProjectiveFourthMomentConstant * n ^ 2 := by
      unfold h12SharpProjectiveFourthMomentConstant
      field_simp [ne_of_gt hn]

/-! ## Pushforward and exact H6 transport -/

theorem h12SharpBetaPrimeProjectiveFourthEnvelope_momentPackage_internal
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    Integrable (h12SharpBetaPrimeProjectiveFourthEnvelope N K)
        (betaPrimeTraceFourLaw N K) ∧
      (16 * N ≤ K →
        (∫ u, h12SharpBetaPrimeProjectiveFourthEnvelope N K u
          ∂(betaPrimeTraceFourLaw N K)) ≤
          h12SharpProjectiveFourthMomentConstant * (N : ℝ) ^ 2) := by
  have hMap : AEMeasurable (realBetaPrimeTracePowerVector 4 N K)
      (realBetaPrimeGaussianSourceLaw N K) :=
    (measurable_realBetaPrimeTracePowerVector_internal 4 N K).aemeasurable
  have hEnvelopeMeas : AEStronglyMeasurable
      (h12SharpBetaPrimeProjectiveFourthEnvelope N K)
      (betaPrimeTraceFourLaw N K) :=
    (measurable_h12SharpBetaPrimeProjectiveFourthEnvelope N K)
      |>.aestronglyMeasurable
  constructor
  · unfold betaPrimeTraceFourLaw
    apply (integrable_map_measure
      (measurable_h12SharpBetaPrimeProjectiveFourthEnvelope N K).aestronglyMeasurable
      hMap).2
    exact integrable_h12SharpBetaPrimeProjectiveFourthEnvelope_source_internal
      hN hgap
  · intro hdense
    have hPush :
        (∫ u, h12SharpBetaPrimeProjectiveFourthEnvelope N K u
          ∂(betaPrimeTraceFourLaw N K)) =
        ∫ source,
          h12SharpBetaPrimeProjectiveFourthEnvelope N K
            (realBetaPrimeTracePowerVector 4 N K source)
          ∂(realBetaPrimeGaussianSourceLaw N K) := by
      unfold betaPrimeTraceFourLaw
      exact integral_map hMap hEnvelopeMeas
    rw [hPush]
    exact integral_h12SharpBetaPrimeProjectiveFourthEnvelope_source_le_internal
      hN hgap hdense

theorem h12SharpProjectiveFourthEnvelope_momentPackage_of_H6_internal
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (hH6 :
      Measure.map (concreteCOETracePowerVector 4 N K)
          (concreteScaledCOECornerLaw
            canonicalUnitaryHaarProbabilityFamily N K) =
        betaPrimeTraceFourLaw N K) :
    Integrable (h12SharpProjectiveFourthEnvelope N K)
        (concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K) ∧
      (16 * N ≤ K →
        (∫ A, h12SharpProjectiveFourthEnvelope N K A
          ∂(concreteScaledCOECornerLaw
            canonicalUnitaryHaarProbabilityFamily N K)) ≤
          h12SharpProjectiveFourthMomentConstant * (N : ℝ) ^ 2) := by
  let mu : Measure (ConcreteMatrixState N) :=
    concreteScaledCOECornerLaw canonicalUnitaryHaarProbabilityFamily N K
  let f : ConcreteMatrixState N → Fin 4 → ℝ :=
    concreteCOETracePowerVector 4 N K
  let b : (Fin 4 → ℝ) → ℝ :=
    h12SharpBetaPrimeProjectiveFourthEnvelope N K
  have hBeta :=
    h12SharpBetaPrimeProjectiveFourthEnvelope_momentPackage_internal hN hgap
  have hf : AEMeasurable f mu := by
    simpa only [f, mu] using
      (measurable_concreteCOETracePowerVector_internal 4 N K).aemeasurable
  have hmap : Measure.map f mu = betaPrimeTraceFourLaw N K := by
    simpa only [f, mu] using hH6
  have hbMap : AEStronglyMeasurable b (Measure.map f mu) := by
    rw [hmap]
    simpa only [b] using hBeta.1.aestronglyMeasurable
  have hPullInt : Integrable (b ∘ f) mu := by
    apply (integrable_map_measure hbMap hf).1
    simpa only [hmap, b] using hBeta.1
  have hPullIntegral :
      (∫ A, (b ∘ f) A ∂mu) =
        ∫ u, b u ∂(betaPrimeTraceFourLaw N K) := by
    calc
      (∫ A, (b ∘ f) A ∂mu) =
          ∫ u, b u ∂(Measure.map f mu) :=
        (integral_map hf hbMap).symm
      _ = ∫ u, b u ∂(betaPrimeTraceFourLaw N K) := by rw [hmap]
  have hfun : b ∘ f = h12SharpProjectiveFourthEnvelope N K := by
    funext A
    exact h12_sharpBetaPrimeProjectiveFourthEnvelope_comp_traceFour_internal
      N K A
  constructor
  · rw [← hfun]
    exact hPullInt
  · intro hdense
    rw [← hfun, hPullIntegral]
    simpa only [b] using hBeta.2 hdense

theorem h12SharpProjectiveFourthEnvelope_momentPackage_proved_A2A3A4
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    Integrable (h12SharpProjectiveFourthEnvelope N K)
        (concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K) ∧
      (16 * N ≤ K →
        (∫ A, h12SharpProjectiveFourthEnvelope N K A
          ∂(concreteScaledCOECornerLaw
            canonicalUnitaryHaarProbabilityFamily N K)) ≤
          h12SharpProjectiveFourthMomentConstant * (N : ℝ) ^ 2) := by
  have hH6 :
      Measure.map (concreteCOETracePowerVector 4 N K)
          (concreteScaledCOECornerLaw
            canonicalUnitaryHaarProbabilityFamily N K) =
        betaPrimeTraceFourLaw N K := by
    simpa only [betaPrimeTraceFourLaw] using
      (coeTakagiMuirhead_traceVector_betaPrime_A1A2PrimeA3
        (r := 4) hN (by omega : 2 * N ≤ K))
  exact h12SharpProjectiveFourthEnvelope_momentPackage_of_H6_internal
    hN hgap hH6

/-! ## Product-law H12 endpoint -/

theorem centeredLogScore_oneFourth_momentPackage_sharp_proved_A1A2A3A4
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (fun p ↦ concreteCenteredEll 1 N K p ^ 4) 1
        (concreteCenteredScoreProductLaw N K) ∧
      (16 * N ≤ K →
        lpNorm (fun p ↦ concreteCenteredEll 1 N K p ^ 4) 1
            (concreteCenteredScoreProductLaw N K) ≤
          h12SharpProjectiveFourthMomentConstant * (N : ℝ) ^ 2) := by
  let mu : Measure (ConcreteMatrixState N) :=
    concreteScaledCOECornerLaw canonicalUnitaryHaarProbabilityFamily N K
  let sphere : Measure (ComplexUnitSphere N) :=
    complexUnitSphereProbabilityMeasure N
  let f : ConcreteMatrixState N × ComplexUnitSphere N → ℝ :=
    fun p ↦ concreteCenteredEll 1 N K p ^ 4
  let envelope : ConcreteMatrixState N → ℝ :=
    h12SharpProjectiveFourthEnvelope N K
  letI : IsProbabilityMeasure mu :=
    canonicalScaledCOECornerLaw_isProbability (by omega)
  letI : IsProbabilityMeasure sphere :=
    complexUnitSphereProbabilityMeasure_isProbability hN
  have hSupport : ∀ᵐ A ∂mu,
      (unscaleCOECorner K A).IsSymm ∧
        coeCornerSupport (unscaleCOECorner K A) := by
    simpa only [mu] using
      (friedmanMello1985_scaledCOECorner_ae_support_from_density
        hN (by omega : 2 * N ≤ K))
  have hSupportProd : ∀ᵐ p ∂(mu.prod sphere),
      (unscaleCOECorner K p.1).IsSymm ∧
        coeCornerSupport (unscaleCOECorner K p.1) :=
    Measure.quasiMeasurePreserving_fst.ae hSupport
  have hfEq : f =ᵐ[mu.prod sphere]
      (fun p : ConcreteMatrixState N × ComplexUnitSphere N ↦
        concreteCenteredRankOneFirstDensityScore N K p.2 p.1 ^ 4) := by
    filter_upwards [hSupportProd] with p hp
    have hell : concreteCenteredEll 1 N K p =
        concreteCenteredRankOneFirstDensityScore N K p.2 p.1 := by
      unfold concreteCenteredEll
      calc
        concreteCenteredLogScore 1 N K p.2 p.1 =
            concreteCenteredDensityScore 1 N K p.2 p.1 :=
          (coeCorner_centeredDensityScore_one_eq_logScore
            hN p.2 p.1 hp.2).symm
        _ = concreteCenteredRankOneFirstDensityScore N K p.2 p.1 :=
          coeCorner_centeredDensityScore_one_eq_explicit_external_derived
            hN hgap p.2 p.1 hp.1 hp.2
    simp only [f, hell]
  have hfMeas : AEStronglyMeasurable f (mu.prod sphere) := by
    have hexplicit : AEStronglyMeasurable
        (fun p : ConcreteMatrixState N × ComplexUnitSphere N ↦
          concreteCenteredRankOneFirstDensityScore N K p.2 p.1 ^ 4)
        (mu.prod sphere) :=
      (measurable_concreteCenteredRankOneFirstDensityScore_product N K)
        |>.pow_const 4
        |>.aestronglyMeasurable
    exact hexplicit.congr hfEq.symm
  have hSlices : ∀ᵐ A ∂mu,
      Integrable (fun v ↦ f (A, v)) sphere ∧
        (∫ v, ‖f (A, v)‖ ∂sphere) ≤ envelope A := by
    filter_upwards [hSupport] with A hA
    simpa only [f, sphere, envelope] using
      (h12_fixedMatrix_projectiveFourth_package_sharp_internal
        hN hgap A hA.1 hA.2)
  have hEnvelope :=
    h12SharpProjectiveFourthEnvelope_momentPackage_proved_A2A3A4 hN hgap
  have hEnvelopeInt : Integrable envelope mu := by
    simpa only [envelope, mu] using hEnvelope.1
  have hInnerMeas : AEStronglyMeasurable
      (fun A ↦ ∫ v, ‖f (A, v)‖ ∂sphere) mu :=
    hfMeas.norm.integral_prod_right'
  have hInnerInt : Integrable
      (fun A ↦ ∫ v, ‖f (A, v)‖ ∂sphere) mu := by
    apply hEnvelopeInt.mono hInnerMeas
    filter_upwards [hSlices] with A hA
    rw [Real.norm_eq_abs,
      abs_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _)]
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact hA.2
    · exact h12SharpProjectiveFourthEnvelope_nonneg N K A
  have hfInt : Integrable f (mu.prod sphere) := by
    apply (integrable_prod_iff hfMeas).2
    constructor
    · filter_upwards [hSlices] with A hA
      exact hA.1
    · exact hInnerInt
  constructor
  · have hfMem : MemLp f 1 (mu.prod sphere) :=
      memLp_one_iff_integrable.mpr hfInt
    simpa only [f, mu, sphere, concreteCenteredScoreProductLaw] using hfMem
  · intro hdense
    have hbound : lpNorm f 1 (mu.prod sphere) ≤
        h12SharpProjectiveFourthMomentConstant * (N : ℝ) ^ 2 := by
      calc
        lpNorm f 1 (mu.prod sphere) =
            ∫ A, ∫ v, ‖f (A, v)‖ ∂sphere ∂mu := by
          rw [lpNorm_one_eq_integral_norm hfMeas]
          exact integral_prod (fun p ↦ ‖f p‖) hfInt.norm
        _ ≤ ∫ A, envelope A ∂mu := by
          apply integral_mono_ae hInnerInt hEnvelopeInt
          filter_upwards [hSlices] with A hA
          exact hA.2
        _ ≤ h12SharpProjectiveFourthMomentConstant * (N : ℝ) ^ 2 := by
          simpa only [envelope, mu] using hEnvelope.2 hdense
    simpa only [f, mu, sphere, concreteCenteredScoreProductLaw] using hbound

theorem centeredLogScore_oneFourth_memLp_one_sharp_proved_A1A2A3A4
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (fun p ↦ concreteCenteredEll 1 N K p ^ 4) 1
      (concreteCenteredScoreProductLaw N K) :=
  (centeredLogScore_oneFourth_momentPackage_sharp_proved_A1A2A3A4
    hN hgap).1

theorem centeredLogScore_oneFourth_lpNorm_one_le_sharp_proved_A1A2A3A4
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (fun p ↦ concreteCenteredEll 1 N K p ^ 4) 1
        (concreteCenteredScoreProductLaw N K) ≤
      h12SharpProjectiveFourthMomentConstant * (N : ℝ) ^ 2 :=
  (centeredLogScore_oneFourth_momentPackage_sharp_proved_A1A2A3A4
    hN (by omega)).2 hdense

end


end LogdetLean.GramHafnian.UltimateHiding.DenseScore
