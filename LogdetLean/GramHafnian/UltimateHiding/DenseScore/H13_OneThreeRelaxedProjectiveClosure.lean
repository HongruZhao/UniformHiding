import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H13_MixedProjectiveHolderContraction
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H13_RelaxedProjectiveEnvelopeTransport
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H13_FullSixWordProjectivePolynomial
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H13_OneThreeProjectiveReductionA4
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# Unconditional relaxed projective closure for H13

The exact support normal form is one pure projective word and three copies of
one mixed word.  The two sharp fixed-sphere Holder packages bound these by
`128` each in the common radial basis.  Restoring the literal score coefficient
therefore costs at most `16 * (128 + 3 * 128) = 8192`, below the relaxed
coefficient `2^16`.
-/

open MeasureTheory
open scoped ComplexOrder MatrixOrder

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.CurrentPRL

set_option maxHeartbeats 4800000

/-- Relaxed analogue of the original H13 fixed-matrix contraction contract. -/
def H13OneThreeRelaxedTraceWordProjectiveContractionContract
    (N K : ℕ) : Prop :=
  ∀ (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (A : ConcreteMatrixState N)
    (hsymm : (unscaleCOECorner K A).IsSymm)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)),
    let C := unscaleCOECorner K A
    let Y := concreteCOEY N K A
    let ledger : ComplexUnitSphere N → ℝ := fun v =>
      -8 * concreteCOEExponent N K *
        h13OneThreeTraceWordLedger
          (concreteCenteredOrbitalDirection N v) C Y
    Integrable ledger (higherScoreSphereLaw N) ∧
      (∫ v, ‖ledger v‖ ∂(higherScoreSphereLaw N)) ≤
        h13RelaxedProjectiveEnvelope N K A

/-- On support, the relaxed radial envelope is exactly `2^16 c^2` times the
fixed-sphere trace basis of `Z`. -/
theorem h13RelaxedProjectiveEnvelope_eq_supportBasis
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    let C := unscaleCOECorner K A
    let Z := h13LedgerZ C
    let c := concreteCOEExponent N K
    h13RelaxedProjectiveEnvelope N K A =
      (2 : ℝ) ^ 16 * c ^ 2 *
        (((Matrix.trace Z).re ^ 2 + (Matrix.trace (Z ^ 2)).re) /
            (N : ℝ) ^ 2 +
          (Matrix.trace Z).re ^ 4 / (N : ℝ) ^ 4 +
          (Matrix.trace (Z ^ 2)).re ^ 2 / (N : ℝ) ^ 2) := by
  let C := unscaleCOECorner K A
  let Z := h13LedgerZ C
  let c := concreteCOEExponent N K
  have hc : 0 < c := by
    simpa only [c] using concreteCOEExponent_pos_of_higherScoreGap hgap
  have hY : concreteCOEY N K A = ((c : ℝ) : ℂ) • Z := by
    rfl
  have ht1 : concreteCOETraceOne N K A =
      c * (Matrix.trace Z).re := by
    unfold concreteCOETraceOne concreteRealTrace
    rw [hY, Matrix.trace_smul]
    simp only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
  have ht2 : concreteCOETraceTwo N K A =
      c ^ 2 * (Matrix.trace (Z ^ 2)).re := by
    unfold concreteCOETraceTwo concreteRealTrace
    rw [hY]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Matrix.trace_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    rw [show Z * Z = Z ^ 2 by noncomm_ring]
    have hcim : (((c : ℂ) * (c : ℂ)).im) = 0 := by simp
    rw [hcim, zero_mul, sub_zero]
    ring
  rw [h13RelaxedProjectiveEnvelope_eq_twoPow16_basis, ht1, ht2]
  have hu : 0 ≤ (Matrix.trace (Z ^ 2)).re := by
    have hZ : Z.PosSemidef := by
      simpa only [Z, C] using h13LedgerZ_posSemidef C hsupport
    exact (Complex.nonneg_iff.mp (hZ.pow 2).trace_nonneg).1
  rw [abs_of_nonneg (mul_nonneg (sq_nonneg c) hu)]
  rw [show concreteCOEExponent N K = c by rfl]
  dsimp only
  field_simp [ne_of_gt hc]
  ring

/-- Exact pure-plus-three-mixed collection at a fixed supported matrix.  The
explicit pure integrability hypothesis is discharged by the companion pure
Holder package; keeping it visible here isolates the only analytic input from
the coefficient collection. -/
theorem centeredPair_mul_h13Full_support_package_of_pureIntegrable
    {N : ℕ} (hN : 1 ≤ N) (C : ConcreteMatrixState N) (hC : C.IsSymm)
    (hsupport : coeCornerSupport C)
    (hpureInt : Integrable (fun v : ComplexUnitSphere N ↦
      complexCenteredProjectiveTracePair v (h13LedgerZ C) *
        h13PureSixWordProjectiveExpansion v
          (1 + h13LedgerZ C) (h13LedgerZ C))
        (higherScoreSphereLaw N)) :
    let Z := h13LedgerZ C
    let basis :=
      (((Matrix.trace Z).re ^ 2 + (Matrix.trace (Z ^ 2)).re) /
          (N : ℝ) ^ 2 +
        (Matrix.trace Z).re ^ 4 / (N : ℝ) ^ 4 +
        (Matrix.trace (Z ^ 2)).re ^ 2 / (N : ℝ) ^ 2)
    Integrable (fun v : ComplexUnitSphere N ↦
        complexCenteredProjectiveTracePair v Z *
          h13FullSixWordProjectiveExpansion v C)
        (higherScoreSphereLaw N) ∧
      (∫ v : ComplexUnitSphere N,
        ‖complexCenteredProjectiveTracePair v Z *
          h13FullSixWordProjectiveExpansion v C‖
          ∂(higherScoreSphereLaw N)) ≤ 512 * basis := by
  let Z := h13LedgerZ C
  let pure : ComplexUnitSphere N → ℂ := fun v ↦
    h13PureSixWordProjectiveExpansion v (1 + Z) Z
  let mixed : ComplexUnitSphere N → ℂ := fun v ↦
    h13CenteredTripleMixedTransposeExpansion v
      (h13LedgerT C) (h13LedgerT C).conjTranspose (1 + 2 • Z)
  let q : ComplexUnitSphere N → ℂ := fun v ↦
    complexCenteredProjectiveTracePair v Z
  let basis :=
    (((Matrix.trace Z).re ^ 2 + (Matrix.trace (Z ^ 2)).re) /
        (N : ℝ) ^ 2 +
      (Matrix.trace Z).re ^ 4 / (N : ℝ) ^ 4 +
      (Matrix.trace (Z ^ 2)).re ^ 2 / (N : ℝ) ^ 2)
  have hpureInt' : Integrable (fun v ↦ q v * pure v)
      (higherScoreSphereLaw N) := by
    simpa only [q, pure, Z, higherScoreSphereLaw] using hpureInt
  have hpureBound :
      (∫ v, ‖q v * pure v‖ ∂(higherScoreSphereLaw N)) ≤
        128 * basis := by
    simpa only [q, pure, Z, basis, higherScoreSphereLaw] using
      integral_norm_centeredPair_mul_pureSixWord_le_halfEnvelope_h13
        hN Z (h13LedgerZ_posSemidef C hsupport)
  have hmixed := centeredPair_mul_h13Mixed_support_package hN C hC hsupport
  dsimp only at hmixed
  have hmixedInt : Integrable (fun v ↦ q v * mixed v)
      (higherScoreSphereLaw N) := by
    simpa only [q, mixed, Z, higherScoreSphereLaw] using hmixed.1
  have hmixedBound :
      (∫ v, ‖q v * mixed v‖ ∂(higherScoreSphereLaw N)) ≤
        128 * basis := by
    simpa only [q, mixed, Z, basis, higherScoreSphereLaw] using hmixed.2
  have hfull (v : ComplexUnitSphere N) :
      q v * h13FullSixWordProjectiveExpansion v C =
        q v * pure v + (3 : ℂ) * (q v * mixed v) := by
    rw [h13FullSixWordProjectiveExpansion_support_simplified_h13
      v C hC hsupport]
    rw [← h13PureSixWordProjectiveExpansion_eq_single_h13]
    dsimp only [q, pure, mixed, Z]
    ring
  have hfullInt : Integrable (fun v : ComplexUnitSphere N ↦
      q v * h13FullSixWordProjectiveExpansion v C)
      (higherScoreSphereLaw N) := by
    have hsum := hpureInt'.add (hmixedInt.const_mul (3 : ℂ))
    apply hsum.congr
    filter_upwards [] with v
    exact (hfull v).symm
  have hmajorInt : Integrable (fun v : ComplexUnitSphere N ↦
      ‖q v * pure v‖ + 3 * ‖q v * mixed v‖)
      (higherScoreSphereLaw N) :=
    hpureInt'.norm.add (hmixedInt.norm.const_mul 3)
  have hpoint (v : ComplexUnitSphere N) :
      ‖q v * h13FullSixWordProjectiveExpansion v C‖ ≤
        ‖q v * pure v‖ + 3 * ‖q v * mixed v‖ := by
    rw [hfull v]
    calc
      _ ≤ ‖q v * pure v‖ + ‖(3 : ℂ) * (q v * mixed v)‖ :=
        norm_add_le _ _
      _ = _ := by norm_num [norm_mul]
  have hmono :
      (∫ v, ‖q v * h13FullSixWordProjectiveExpansion v C‖
          ∂(higherScoreSphereLaw N)) ≤
        ∫ v, (‖q v * pure v‖ + 3 * ‖q v * mixed v‖)
          ∂(higherScoreSphereLaw N) :=
    integral_mono hfullInt.norm hmajorInt hpoint
  have hmajorValue :
      (∫ v, (‖q v * pure v‖ + 3 * ‖q v * mixed v‖)
          ∂(higherScoreSphereLaw N)) =
        (∫ v, ‖q v * pure v‖ ∂(higherScoreSphereLaw N)) +
          3 * (∫ v, ‖q v * mixed v‖ ∂(higherScoreSphereLaw N)) := by
    rw [show (fun v ↦ ‖q v * pure v‖ + 3 * ‖q v * mixed v‖) =
        (fun v ↦ ‖q v * pure v‖) +
          (fun v ↦ 3 * ‖q v * mixed v‖) by rfl]
    rw [integral_add' hpureInt'.norm (hmixedInt.norm.const_mul 3),
      integral_const_mul]
  constructor
  · simpa only [q, Z] using hfullInt
  · calc
      (∫ v, ‖q v * h13FullSixWordProjectiveExpansion v C‖
          ∂(higherScoreSphereLaw N)) ≤
        ∫ v, (‖q v * pure v‖ + 3 * ‖q v * mixed v‖)
          ∂(higherScoreSphereLaw N) := hmono
      _ = (∫ v, ‖q v * pure v‖ ∂(higherScoreSphereLaw N)) +
          3 * (∫ v, ‖q v * mixed v‖ ∂(higherScoreSphereLaw N)) :=
        hmajorValue
      _ ≤ 512 * basis := by linarith

/-- The literal relaxed H13 contraction follows from the pure integrability
companion and the two already proved quantitative Holder contractions. -/
theorem h13OneThreeRelaxedTraceWordProjectiveContraction_of_pureIntegrable
    {N K : ℕ}
    (Hpure : ∀ {d : ℕ} (hd : 1 ≤ d) (Z : ConcreteMatrixState d),
      Z.PosSemidef →
        Integrable (fun v : ComplexUnitSphere d ↦
          complexCenteredProjectiveTracePair v Z *
            h13PureSixWordProjectiveExpansion v (1 + Z) Z)
          (higherScoreSphereLaw d)) :
    H13OneThreeRelaxedTraceWordProjectiveContractionContract N K := by
  intro hN hgap A hsymm hsupport
  dsimp only
  let C := unscaleCOECorner K A
  let Z := h13LedgerZ C
  let Y := concreteCOEY N K A
  let c := concreteCOEExponent N K
  let q : ComplexUnitSphere N → ℂ := fun v ↦
    complexCenteredProjectiveTracePair v Z
  let full : ComplexUnitSphere N → ℂ := fun v ↦
    h13FullSixWordProjectiveExpansion v C
  let realProduct : ComplexUnitSphere N → ℝ := fun v ↦
    (q v).re * (full v).re
  let ledger : ComplexUnitSphere N → ℝ := fun v ↦
    -8 * c * h13OneThreeTraceWordLedger
      (concreteCenteredOrbitalDirection N v) C Y
  let basis : ℝ :=
    (((Matrix.trace Z).re ^ 2 + (Matrix.trace (Z ^ 2)).re) /
        (N : ℝ) ^ 2 +
      (Matrix.trace Z).re ^ 4 / (N : ℝ) ^ 4 +
      (Matrix.trace (Z ^ 2)).re ^ 2 / (N : ℝ) ^ 2)
  have hc : 0 < c := by
    simpa only [c] using concreteCOEExponent_pos_of_higherScoreGap hgap
  have hZ : Z.PosSemidef := by
    simpa only [Z, C] using h13LedgerZ_posSemidef C hsupport
  have hfull := centeredPair_mul_h13Full_support_package_of_pureIntegrable
    hN C hsymm hsupport (Hpure hN Z hZ)
  dsimp only at hfull
  have hfullInt : Integrable (fun v ↦ q v * full v)
      (higherScoreSphereLaw N) := by
    simpa only [q, full, Z, C] using hfull.1
  have hfullBound :
      (∫ v, ‖q v * full v‖ ∂(higherScoreSphereLaw N)) ≤
        512 * basis := by
    simpa only [q, full, Z, C, basis] using hfull.2
  have hqim (v : ComplexUnitSphere N) : (q v).im = 0 := by
    dsimp only [q]
    exact complexCenteredProjectiveTracePair_im_zero_internal v Z
      hZ.isHermitian
  have hrealInt : Integrable realProduct (higherScoreSphereLaw N) := by
    have H := hfullInt.re
    apply H.congr
    filter_upwards [] with v
    dsimp only [realProduct]
    change (q v * full v).re = (q v).re * (full v).re
    rw [Complex.mul_re, hqim v, zero_mul, sub_zero]
  have hY : Y = ((c : ℝ) : ℂ) • Z := by rfl
  have hledger (v : ComplexUnitSphere N) :
      ledger v = 16 * c ^ 2 * realProduct v := by
    dsimp only [ledger]
    rw [negEightExponent_mul_h13Ledger_eq_fullProjectivePolynomial
      v C Y hsupport]
    change 16 * concreteCOEExponent N K *
      ((complexCenteredProjectiveTracePair v Y).re * (full v).re) = _
    rw [show concreteCOEExponent N K = c by rfl]
    rw [hY, complexCenteredProjectiveTracePair_smul]
    dsimp only [realProduct, q]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    ring
  have hledgerInt : Integrable ledger (higherScoreSphereLaw N) := by
    have H := hrealInt.const_mul (16 * c ^ 2)
    apply H.congr
    filter_upwards [] with v
    exact (hledger v).symm
  have hscale : 0 ≤ 16 * c ^ 2 := by positivity
  have hpoint (v : ComplexUnitSphere N) :
      ‖ledger v‖ ≤ (16 * c ^ 2) * ‖q v * full v‖ := by
    rw [hledger v]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hscale, abs_mul,
      norm_mul]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul (Complex.abs_re_le_norm (q v))
        (Complex.abs_re_le_norm (full v)) (abs_nonneg _) (norm_nonneg _))
      hscale
  have hmajorInt : Integrable (fun v ↦
      (16 * c ^ 2) * ‖q v * full v‖) (higherScoreSphereLaw N) :=
    hfullInt.norm.const_mul (16 * c ^ 2)
  have hmono :
      (∫ v, ‖ledger v‖ ∂(higherScoreSphereLaw N)) ≤
        ∫ v, (16 * c ^ 2) * ‖q v * full v‖
          ∂(higherScoreSphereLaw N) :=
    integral_mono hledgerInt.norm hmajorInt hpoint
  have ht : 0 ≤ (Matrix.trace Z).re :=
    (Complex.nonneg_iff.mp hZ.trace_nonneg).1
  have hu : 0 ≤ (Matrix.trace (Z ^ 2)).re :=
    (Complex.nonneg_iff.mp (hZ.pow 2).trace_nonneg).1
  have hbasis : 0 ≤ basis := by
    dsimp only [basis]
    positivity
  have hrelaxed := h13RelaxedProjectiveEnvelope_eq_supportBasis
    hN hgap A hsupport
  dsimp only at hrelaxed
  constructor
  · simpa only [ledger, c, C, Y] using hledgerInt
  · calc
      (∫ v, ‖ledger v‖ ∂(higherScoreSphereLaw N)) ≤
          ∫ v, (16 * c ^ 2) * ‖q v * full v‖
            ∂(higherScoreSphereLaw N) := hmono
      _ = (16 * c ^ 2) *
          (∫ v, ‖q v * full v‖ ∂(higherScoreSphereLaw N)) := by
        rw [integral_const_mul]
      _ ≤ (16 * c ^ 2) * (512 * basis) :=
        mul_le_mul_of_nonneg_left hfullBound hscale
      _ ≤ (2 : ℝ) ^ 16 * c ^ 2 * basis := by
        have hcb : 0 ≤ c ^ 2 * basis := mul_nonneg (sq_nonneg c) hbasis
        norm_num
        nlinarith
      _ = h13RelaxedProjectiveEnvelope N K A := hrelaxed.symm

/-- A relaxed trace-word contract supplies the concrete projective-first H13
interface. -/
theorem h13HigherScoreProjectiveFirstEnvelope_of_relaxedTraceWordContract
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (Hcontract :
      H13OneThreeRelaxedTraceWordProjectiveContractionContract N K) :
    H13HigherScoreProjectiveFirstEnvelope N K
      (h13RelaxedProjectiveEnvelope N K) := by
  refine
    { measurable_score :=
        (measurable_concreteCenteredEll_one hN).mul
          (measurable_concreteCenteredEll_three hN)
      envelope_nonneg := h13RelaxedProjectiveEnvelope_nonneg N K
      fixedMatrix_package := ?_ }
  intro A hsymm hsupport
  let C := unscaleCOECorner K A
  let Y := concreteCOEY N K A
  let ledger : ComplexUnitSphere N → ℝ := fun v ↦
    -8 * concreteCOEExponent N K *
      h13OneThreeTraceWordLedger
        (concreteCenteredOrbitalDirection N v) C Y
  have H := Hcontract hN hgap A hsymm hsupport
  dsimp only at H
  have heq : (fun v : ComplexUnitSphere N ↦
      concreteCenteredEll 1 N K (A, v) *
        concreteCenteredEll 3 N K (A, v)) = ledger := by
    funext v
    simpa only [ledger, C, Y] using
      concreteCenteredEll_one_mul_three_eq_traceWordLedger_h13_internal
        hN hgap A v hsymm hsupport
  have heq_apply (v : ComplexUnitSphere N) :
      concreteCenteredEll 1 N K (A, v) *
        concreteCenteredEll 3 N K (A, v) = ledger v := congrFun heq v
  constructor
  · simpa only [heq_apply] using H.1
  · simpa only [heq_apply] using H.2

/-- Public H13 endpoint from the relaxed deterministic contract. -/
theorem centeredLogScore_oneThree_momentPackage_of_relaxedTraceWord_A1A2A3A4
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (Hcontract :
      H13OneThreeRelaxedTraceWordProjectiveContractionContract N K) :
    MemLp (fun p ↦ concreteCenteredEll 1 N K p *
      concreteCenteredEll 3 N K p) 1
        (concreteCenteredScoreProductLaw N K) ∧
      (16 * N ≤ K →
        lpNorm (fun p ↦ concreteCenteredEll 1 N K p *
          concreteCenteredEll 3 N K p) 1
            (concreteCenteredScoreProductLaw N K) ≤
          centeredLogScoreFourthMomentConstant * (N : ℝ) ^ 2) :=
  centeredLogScore_oneThree_momentPackage_of_projectiveFirst
    hN hgap (h13RelaxedProjectiveEnvelope N K)
    (h13HigherScoreProjectiveFirstEnvelope_of_relaxedTraceWordContract
      hN hgap Hcontract)
    (h13RelaxedTraceEnvelopeL1Package_A2A3 hN hgap)

/-- Strong H13 product package retaining the actual relaxed-envelope
expectation constant needed by the H11 Bell budget. -/
theorem centeredLogScore_oneThree_momentPackage_relaxed_strong_of_contract
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (Hcontract :
      H13OneThreeRelaxedTraceWordProjectiveContractionContract N K) :
    MemLp (fun p ↦ concreteCenteredEll 1 N K p *
      concreteCenteredEll 3 N K p) 1
        (concreteCenteredScoreProductLaw N K) ∧
      (16 * N ≤ K →
        lpNorm (fun p ↦ concreteCenteredEll 1 N K p *
          concreteCenteredEll 3 N K p) 1
            (concreteCenteredScoreProductLaw N K) ≤
          h13RelaxedProjectiveEnvelopeStrongConstant * (N : ℝ) ^ 2) := by
  let μ : Measure (ConcreteMatrixState N) := higherScoreMatrixLaw N K
  let sphere : Measure (ComplexUnitSphere N) := higherScoreSphereLaw N
  let score : ConcreteMatrixState N × ComplexUnitSphere N → ℝ := fun p ↦
    concreteCenteredEll 1 N K p * concreteCenteredEll 3 N K p
  let envelope : ConcreteMatrixState N → ℝ :=
    h13RelaxedProjectiveEnvelope N K
  letI : IsProbabilityMeasure μ :=
    canonicalScaledCOECornerLaw_isProbability (by omega)
  letI : IsProbabilityMeasure sphere :=
    complexUnitSphereProbabilityMeasure_isProbability hN
  have Hprojective :=
    h13HigherScoreProjectiveFirstEnvelope_of_relaxedTraceWordContract
      hN hgap Hcontract
  have hscoreMeas : AEStronglyMeasurable score (μ.prod sphere) :=
    Hprojective.measurable_score.aestronglyMeasurable
  have hSupport : ∀ᵐ A ∂μ,
      (unscaleCOECorner K A).IsSymm ∧
        coeCornerSupport (unscaleCOECorner K A) := by
    simpa only [μ, higherScoreMatrixLaw] using
      friedmanMello1985_scaledCOECorner_ae_support_from_density
        hN (by omega : 2 * N ≤ K)
  have hSlices : ∀ᵐ A ∂μ,
      Integrable (fun v ↦ score (A, v)) sphere ∧
        (∫ v, ‖score (A, v)‖ ∂sphere) ≤ envelope A := by
    filter_upwards [hSupport] with A hA
    simpa only [score, sphere, envelope] using
      Hprojective.fixedMatrix_package A hA.1 hA.2
  have hEnvelope :=
    h13RelaxedProjectiveEnvelope_momentPackage_strong_A2A3 hN hgap
  have hEnvelopeInt : Integrable envelope μ := by
    simpa only [envelope, μ, higherScoreMatrixLaw] using hEnvelope.1
  have hInnerMeas : AEStronglyMeasurable
      (fun A ↦ ∫ v, ‖score (A, v)‖ ∂sphere) μ :=
    hscoreMeas.norm.integral_prod_right'
  have hInnerInt : Integrable
      (fun A ↦ ∫ v, ‖score (A, v)‖ ∂sphere) μ := by
    apply hEnvelopeInt.mono hInnerMeas
    filter_upwards [hSlices] with A hA
    rw [Real.norm_eq_abs,
      abs_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _),
      Real.norm_eq_abs,
      abs_of_nonneg (h13RelaxedProjectiveEnvelope_nonneg N K A)]
    exact hA.2
  have hscoreInt : Integrable score (μ.prod sphere) := by
    apply (integrable_prod_iff hscoreMeas).2
    exact ⟨hSlices.mono fun _ hA ↦ hA.1, hInnerInt⟩
  constructor
  · have hmem : MemLp score 1 (μ.prod sphere) :=
      memLp_one_iff_integrable.mpr hscoreInt
    simpa only [score, μ, sphere, higherScoreMatrixLaw, higherScoreSphereLaw,
      concreteCenteredScoreProductLaw] using hmem
  · intro hdense
    have hbound : lpNorm score 1 (μ.prod sphere) ≤
        h13RelaxedProjectiveEnvelopeStrongConstant * (N : ℝ) ^ 2 := by
      calc
        lpNorm score 1 (μ.prod sphere) =
            ∫ A, ∫ v, ‖score (A, v)‖ ∂sphere ∂μ := by
          rw [lpNorm_one_eq_integral_norm hscoreMeas]
          exact integral_prod (fun p ↦ ‖score p‖) hscoreInt.norm
        _ ≤ ∫ A, envelope A ∂μ := by
          apply integral_mono_ae hInnerInt hEnvelopeInt
          filter_upwards [hSlices] with A hA
          exact hA.2
        _ ≤ h13RelaxedProjectiveEnvelopeStrongConstant * (N : ℝ) ^ 2 := by
          simpa only [envelope, μ, higherScoreMatrixLaw] using
            hEnvelope.2 hdense
    simpa only [score, μ, sphere, higherScoreMatrixLaw, higherScoreSphereLaw,
      concreteCenteredScoreProductLaw] using hbound

/-- No-premise fixed-sphere H13 contraction with the relaxed radial
coefficient. -/
theorem h13OneThreeRelaxedTraceWordProjectiveContraction_proved
    (N K : ℕ) :
    H13OneThreeRelaxedTraceWordProjectiveContractionContract N K := by
  apply h13OneThreeRelaxedTraceWordProjectiveContraction_of_pureIntegrable
  intro d hd Z hZ
  simpa only [higherScoreSphereLaw] using
    integrable_centeredPair_mul_pureSixWord_h13 hd Z hZ

/-- No-premise strong H13 endpoint, retaining the explicit relaxed-envelope
constant for the H11 lower-Bell assembly. -/
theorem centeredLogScore_oneThree_momentPackage_relaxed_strong_proved_A1A2A3A4
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (fun p ↦ concreteCenteredEll 1 N K p *
      concreteCenteredEll 3 N K p) 1
        (concreteCenteredScoreProductLaw N K) ∧
      (16 * N ≤ K →
        lpNorm (fun p ↦ concreteCenteredEll 1 N K p *
          concreteCenteredEll 3 N K p) 1
            (concreteCenteredScoreProductLaw N K) ≤
          h13RelaxedProjectiveEnvelopeStrongConstant * (N : ℝ) ^ 2) :=
  centeredLogScore_oneThree_momentPackage_relaxed_strong_of_contract
    hN hgap (h13OneThreeRelaxedTraceWordProjectiveContraction_proved N K)

/-- Literal all-dimensional public H13 endpoint under the approved A1--A4
inputs, with no residual deterministic premise. -/
theorem centeredLogScore_oneThree_momentPackage_proved_A1A2A3A4
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (fun p ↦ concreteCenteredEll 1 N K p *
      concreteCenteredEll 3 N K p) 1
        (concreteCenteredScoreProductLaw N K) ∧
      (16 * N ≤ K →
        lpNorm (fun p ↦ concreteCenteredEll 1 N K p *
          concreteCenteredEll 3 N K p) 1
            (concreteCenteredScoreProductLaw N K) ≤
          centeredLogScoreFourthMomentConstant * (N : ℝ) ^ 2) :=
  centeredLogScore_oneThree_momentPackage_of_relaxedTraceWord_A1A2A3A4
    hN hgap (h13OneThreeRelaxedTraceWordProjectiveContraction_proved N K)

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
