import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H13_CombinedSharpScalarEnvelope
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H13_ScaleTwoProjectiveBound

/-!
# Combined-sharp H13 projective bound

This module keeps the exact pure and three mixed Holder ledgers together.
The scalar certificate in `H13_CombinedSharpScalarEnvelope` replaces the old
fixed-sphere coefficient `512` by `1038 / 5`.  The outer radial expectation is
then obtained by scaling the already verified `8192`/`52204` envelope, so no
new inverse-Wishart recurrence is introduced.
-/

open MeasureTheory
open scoped ComplexOrder MatrixOrder

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.LocalAnticoncentration

set_option maxHeartbeats 7200000
set_option maxRecDepth 100000

/-! ## Exact combined fixed-sphere closure -/

/-- Exact pure-plus-three-mixed fixed-sphere package with coefficient
`1038 / 5` in the common radial basis. -/
theorem centeredPair_mul_h13Full_support_package_combinedSharp
    {N : ℕ} (hN : 2 ≤ N) (C : ConcreteMatrixState N) (hC : C.IsSymm)
    (hsupport : coeCornerSupport C) :
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
          ∂(higherScoreSphereLaw N)) ≤
        h13CombinedSharpScalarEnvelopeConstant * basis := by
  let Z := h13LedgerZ C
  let pure : ComplexUnitSphere N → ℂ := fun v ↦
    h13PureSixWordProjectiveExpansion v (1 + Z) Z
  let mixed : ComplexUnitSphere N → ℂ := fun v ↦
    h13CenteredTripleMixedTransposeExpansion v
      (h13LedgerT C) (h13LedgerT C).conjTranspose (1 + 2 • Z)
  let q : ComplexUnitSphere N → ℂ := fun v ↦
    complexCenteredProjectiveTracePair v Z
  let n : ℝ := N
  let t : ℝ := (Matrix.trace Z).re
  let u : ℝ := (Matrix.trace (Z ^ 2)).re
  let v3 : ℝ := (Matrix.trace (Z ^ 3)).re
  let basis : ℝ :=
    (((Matrix.trace Z).re ^ 2 + (Matrix.trace (Z ^ 2)).re) /
        (N : ℝ) ^ 2 +
      (Matrix.trace Z).re ^ 4 / (N : ℝ) ^ 4 +
      (Matrix.trace (Z ^ 2)).re ^ 2 / (N : ℝ) ^ 2)
  have hNOne : 1 ≤ N := by omega
  have hn : 0 < n := by
    dsimp only [n]
    exact_mod_cast (Nat.zero_lt_of_lt hNOne)
  have hnTwo : 2 ≤ n := by
    dsimp only [n]
    exact_mod_cast hN
  have hZ : Z.PosSemidef := by
    simpa only [Z] using h13LedgerZ_posSemidef C hsupport
  have ht : 0 ≤ t := (Complex.nonneg_iff.mp hZ.trace_nonneg).1
  have hu : 0 ≤ u :=
    (Complex.nonneg_iff.mp (hZ.pow 2).trace_nonneg).1
  have htlow : t ^ 2 ≤ n * u := by
    simpa only [t, u, n, pow_two] using
      posSemidef_trace_re_sq_le_card_mul_trace_square_re_h13_pure Z hZ
  have hv3le : v3 ≤ t * u := by
    simpa only [v3, t, u] using
      posSemidef_trace_cube_re_le_trace_re_mul_trace_square_re_h13 Z hZ
  have hpureInt : Integrable (fun v ↦ q v * pure v)
      (higherScoreSphereLaw N) := by
    simpa only [q, pure, Z, higherScoreSphereLaw] using
      integrable_centeredPair_mul_pureSixWord_h13 hNOne Z hZ
  have hpureBound :
      (∫ v, ‖q v * pure v‖ ∂higherScoreSphereLaw N) ≤
        h13PureHolderRadialPolynomial N Z := by
    simpa only [q, pure, Z, higherScoreSphereLaw] using
      integral_norm_centeredPair_mul_pureSixWord_le_holderPolynomial_h13
        hNOne Z hZ
  have hmixed := centeredPair_mul_h13Mixed_support_package_raw
    hNOne C hC hsupport
  dsimp only at hmixed
  have hmixedInt : Integrable (fun v ↦ q v * mixed v)
      (higherScoreSphereLaw N) := by
    simpa only [q, mixed, Z, higherScoreSphereLaw] using hmixed.1
  have hmixedBound :
      (∫ v, ‖q v * mixed v‖ ∂higherScoreSphereLaw N) ≤
        h13MixedHolderRadialPolynomial N C := by
    simpa only [q, mixed, Z, higherScoreSphereLaw] using hmixed.2
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
    have hsum := hpureInt.add (hmixedInt.const_mul (3 : ℂ))
    apply hsum.congr
    filter_upwards [] with v
    exact (hfull v).symm
  have hmajorInt : Integrable (fun v : ComplexUnitSphere N ↦
      ‖q v * pure v‖ + 3 * ‖q v * mixed v‖)
      (higherScoreSphereLaw N) :=
    hpureInt.norm.add (hmixedInt.norm.const_mul 3)
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
          ∂higherScoreSphereLaw N) ≤
        ∫ v, (‖q v * pure v‖ + 3 * ‖q v * mixed v‖)
          ∂higherScoreSphereLaw N :=
    integral_mono hfullInt.norm hmajorInt hpoint
  have hmajorValue :
      (∫ v, (‖q v * pure v‖ + 3 * ‖q v * mixed v‖)
          ∂higherScoreSphereLaw N) =
        (∫ v, ‖q v * pure v‖ ∂higherScoreSphereLaw N) +
          3 * (∫ v, ‖q v * mixed v‖ ∂higherScoreSphereLaw N) := by
    rw [show (fun v ↦ ‖q v * pure v‖ + 3 * ‖q v * mixed v‖) =
        (fun v ↦ ‖q v * pure v‖) +
          (fun v ↦ 3 * ‖q v * mixed v‖) by rfl]
    rw [integral_add' hpureInt.norm (hmixedInt.norm.const_mul 3),
      integral_const_mul]
  have hscalar := h13CombinedSharpScalarEnvelope
    n t u v3 hnTwo ht hu htlow hv3le
  have hpureEq :
      h13PureHolderRadialPolynomial N Z =
        h13CombinedSharpPurePolynomial n t u v3 / n ^ 4 := by
    rfl
  have hmixedEq :
      h13MixedHolderRadialPolynomial N C =
        h13CombinedSharpMixedPolynomial n t u v3 / n ^ 4 := by
    rfl
  have hbasisEq :
      basis = h13CombinedSharpRadialBasis n t u / n ^ 4 := by
    dsimp only [basis, n, t, u, Z, h13CombinedSharpRadialBasis]
    field_simp [ne_of_gt hn]
  have hn4 : 0 < n ^ 4 := pow_pos hn 4
  have hscalarDiv :
      h13PureHolderRadialPolynomial N Z +
          3 * h13MixedHolderRadialPolynomial N C ≤
        h13CombinedSharpScalarEnvelopeConstant * basis := by
    rw [hpureEq, hmixedEq, hbasisEq]
    calc
      h13CombinedSharpPurePolynomial n t u v3 / n ^ 4 +
          3 * (h13CombinedSharpMixedPolynomial n t u v3 / n ^ 4) =
        (h13CombinedSharpPurePolynomial n t u v3 +
          3 * h13CombinedSharpMixedPolynomial n t u v3) / n ^ 4 := by
            ring
      _ ≤ (h13CombinedSharpScalarEnvelopeConstant *
          h13CombinedSharpRadialBasis n t u) / n ^ 4 :=
        (div_le_div_iff_of_pos_right hn4).2 hscalar
      _ = h13CombinedSharpScalarEnvelopeConstant *
          (h13CombinedSharpRadialBasis n t u / n ^ 4) := by ring
  constructor
  · simpa only [q, Z] using hfullInt
  · calc
      (∫ v, ‖q v * h13FullSixWordProjectiveExpansion v C‖
          ∂higherScoreSphereLaw N) ≤
        ∫ v, (‖q v * pure v‖ + 3 * ‖q v * mixed v‖)
          ∂higherScoreSphereLaw N := hmono
      _ = (∫ v, ‖q v * pure v‖ ∂higherScoreSphereLaw N) +
          3 * (∫ v, ‖q v * mixed v‖ ∂higherScoreSphereLaw N) :=
        hmajorValue
      _ ≤ h13PureHolderRadialPolynomial N Z +
          3 * h13MixedHolderRadialPolynomial N C := by linarith
      _ ≤ h13CombinedSharpScalarEnvelopeConstant * basis := hscalarDiv

/-! ## Scaled reuse of the exact radial recurrence -/

/-- Ratio between the combined-sharp fibre envelope and the former `512`
fibre envelope. -/
def h13CombinedSharpEnvelopeScale : ℝ :=
  h13CombinedSharpScalarEnvelopeConstant / 512

/-- Exact all-matrix H13 coefficient after scaling the verified `52204`
radial recurrence. -/
def h13CombinedSharpProjectiveEnvelopeConstant : ℝ :=
  h13CombinedSharpEnvelopeScale * h13ScaleTwoProjectiveEnvelopeConstant

theorem h13CombinedSharpProjectiveEnvelopeConstant_eq :
    h13CombinedSharpProjectiveEnvelopeConstant = 6773469 / 320 := by
  norm_num [h13CombinedSharpProjectiveEnvelopeConstant,
    h13CombinedSharpEnvelopeScale,
    h13CombinedSharpScalarEnvelopeConstant,
    h13ScaleTwoProjectiveEnvelopeConstant]

theorem h13CombinedSharpEnvelopeScale_nonneg :
    0 ≤ h13CombinedSharpEnvelopeScale := by
  norm_num [h13CombinedSharpEnvelopeScale,
    h13CombinedSharpScalarEnvelopeConstant]

/-- The combined-sharp matrix envelope is a nonnegative scalar multiple of
the already transported scale-two envelope. -/
def h13CombinedSharpProjectiveEnvelope (N K : ℕ)
    (A : ConcreteMatrixState N) : ℝ :=
  h13CombinedSharpEnvelopeScale * h13ScaleTwoProjectiveEnvelope N K A

theorem h13CombinedSharpProjectiveEnvelope_momentPackage_A2A3
    {N K : ℕ} (hN : 2 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    Integrable (h13CombinedSharpProjectiveEnvelope N K)
        (higherScoreMatrixLaw N K) ∧
      (16 * N ≤ K →
        (∫ A, h13CombinedSharpProjectiveEnvelope N K A
            ∂higherScoreMatrixLaw N K) ≤
          h13CombinedSharpProjectiveEnvelopeConstant * (N : ℝ) ^ 2) := by
  have hOld := h13ScaleTwoProjectiveEnvelope_momentPackage_A2A3 hN hgap
  have hscale : 0 ≤ h13CombinedSharpEnvelopeScale :=
    h13CombinedSharpEnvelopeScale_nonneg
  constructor
  · change Integrable
      (fun A ↦ h13CombinedSharpEnvelopeScale *
        h13ScaleTwoProjectiveEnvelope N K A)
      (higherScoreMatrixLaw N K)
    exact hOld.1.const_mul h13CombinedSharpEnvelopeScale
  · intro hdense
    calc
      (∫ A, h13CombinedSharpProjectiveEnvelope N K A
          ∂higherScoreMatrixLaw N K) =
        h13CombinedSharpEnvelopeScale *
          (∫ A, h13ScaleTwoProjectiveEnvelope N K A
            ∂higherScoreMatrixLaw N K) := by
              simp only [h13CombinedSharpProjectiveEnvelope,
                integral_const_mul]
      _ ≤ h13CombinedSharpEnvelopeScale *
          (h13ScaleTwoProjectiveEnvelopeConstant * (N : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left (hOld.2 hdense) hscale
      _ = h13CombinedSharpProjectiveEnvelopeConstant * (N : ℝ) ^ 2 := by
        unfold h13CombinedSharpProjectiveEnvelopeConstant
        ring

/-! ## Deterministic fixed-matrix contraction -/

theorem h13OneThreeCombinedSharp_fixedMatrix_package
    {N K : ℕ} (hN : 2 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (A : ConcreteMatrixState N)
    (hsymm : (unscaleCOECorner K A).IsSymm)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    Integrable (fun v : ComplexUnitSphere N ↦
      concreteCenteredEll 1 N K (A, v) *
        concreteCenteredEll 3 N K (A, v))
        (higherScoreSphereLaw N) ∧
      (∫ v, ‖concreteCenteredEll 1 N K (A, v) *
          concreteCenteredEll 3 N K (A, v)‖
        ∂higherScoreSphereLaw N) ≤
          h13CombinedSharpProjectiveEnvelope N K A := by
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
  have hNOne : 1 ≤ N := by omega
  have hc : 0 < c := by
    simpa only [c] using concreteCOEExponent_pos_of_higherScoreGap hgap
  have hZ : Z.PosSemidef := by
    simpa only [Z, C] using h13LedgerZ_posSemidef C hsupport
  have hfull := centeredPair_mul_h13Full_support_package_combinedSharp
    hN C hsymm hsupport
  dsimp only at hfull
  have hfullInt : Integrable (fun v ↦ q v * full v)
      (higherScoreSphereLaw N) := by
    simpa only [q, full, Z, C] using hfull.1
  have hfullBound :
      (∫ v, ‖q v * full v‖ ∂higherScoreSphereLaw N) ≤
        h13CombinedSharpScalarEnvelopeConstant * basis := by
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
  have hmajorInt : Integrable
      (fun v ↦ (16 * c ^ 2) * ‖q v * full v‖)
      (higherScoreSphereLaw N) :=
    hfullInt.norm.const_mul (16 * c ^ 2)
  have hmono :
      (∫ v, ‖ledger v‖ ∂higherScoreSphereLaw N) ≤
        ∫ v, (16 * c ^ 2) * ‖q v * full v‖
          ∂higherScoreSphereLaw N :=
    integral_mono hledgerInt.norm hmajorInt hpoint
  have hOldEnvelope := h13ScaleTwoProjectiveEnvelope_eq_supportBasis
    hNOne hgap A hsupport
  dsimp only at hOldEnvelope
  have hscoreEq : (fun v : ComplexUnitSphere N ↦
      concreteCenteredEll 1 N K (A, v) *
        concreteCenteredEll 3 N K (A, v)) = ledger := by
    funext v
    simpa only [ledger, C, Y] using
      concreteCenteredEll_one_mul_three_eq_traceWordLedger_h13_internal
        hNOne hgap A v hsymm hsupport
  have hledgerBound :
      (∫ v, ‖ledger v‖ ∂higherScoreSphereLaw N) ≤
        h13CombinedSharpProjectiveEnvelope N K A := by
    calc
      _ ≤ ∫ v, (16 * c ^ 2) * ‖q v * full v‖
          ∂higherScoreSphereLaw N := hmono
      _ = (16 * c ^ 2) *
          (∫ v, ‖q v * full v‖ ∂higherScoreSphereLaw N) := by
        rw [integral_const_mul]
      _ ≤ (16 * c ^ 2) *
          (h13CombinedSharpScalarEnvelopeConstant * basis) :=
        mul_le_mul_of_nonneg_left hfullBound hscale
      _ = h13CombinedSharpEnvelopeScale * (8192 * c ^ 2 * basis) := by
        norm_num [h13CombinedSharpEnvelopeScale,
          h13CombinedSharpScalarEnvelopeConstant]
        ring
      _ = h13CombinedSharpEnvelopeScale *
          h13ScaleTwoProjectiveEnvelope N K A := by rw [hOldEnvelope]
      _ = h13CombinedSharpProjectiveEnvelope N K A := rfl
  constructor
  · rw [hscoreEq]
    exact hledgerInt
  · rw [show (fun v ↦ ‖concreteCenteredEll 1 N K (A, v) *
        concreteCenteredEll 3 N K (A, v)‖) = fun v ↦ ‖ledger v‖ by
      funext v
      exact congrArg norm (congrFun hscoreEq v)]
    exact hledgerBound

/-! ## Product-law endpoint -/

theorem centeredLogScore_oneThree_momentPackage_combinedSharp_NGeTwo_A1A2A3A4
    {N K : ℕ} (hN : 2 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (fun p ↦ concreteCenteredEll 1 N K p *
      concreteCenteredEll 3 N K p) 1
        (concreteCenteredScoreProductLaw N K) ∧
      (16 * N ≤ K →
        lpNorm (fun p ↦ concreteCenteredEll 1 N K p *
          concreteCenteredEll 3 N K p) 1
            (concreteCenteredScoreProductLaw N K) ≤
          h13CombinedSharpProjectiveEnvelopeConstant * (N : ℝ) ^ 2) := by
  let μ : Measure (ConcreteMatrixState N) := higherScoreMatrixLaw N K
  let sphere : Measure (ComplexUnitSphere N) := higherScoreSphereLaw N
  let score : ConcreteMatrixState N × ComplexUnitSphere N → ℝ := fun p ↦
    concreteCenteredEll 1 N K p * concreteCenteredEll 3 N K p
  let envelope : ConcreteMatrixState N → ℝ :=
    h13CombinedSharpProjectiveEnvelope N K
  have hNOne : 1 ≤ N := by omega
  letI : IsProbabilityMeasure μ :=
    canonicalScaledCOECornerLaw_isProbability (by omega)
  letI : IsProbabilityMeasure sphere :=
    complexUnitSphereProbabilityMeasure_isProbability hNOne
  have hscoreMeas : AEStronglyMeasurable score (μ.prod sphere) :=
    ((measurable_concreteCenteredEll_one (N := N) (K := K) hNOne).mul
      (measurable_concreteCenteredEll_three (N := N) (K := K) hNOne))
      |>.aestronglyMeasurable
  have hSupport : ∀ᵐ A ∂μ,
      (unscaleCOECorner K A).IsSymm ∧
        coeCornerSupport (unscaleCOECorner K A) := by
    simpa only [μ, higherScoreMatrixLaw] using
      friedmanMello1985_scaledCOECorner_ae_support_from_density
        hNOne (by omega : 2 * N ≤ K)
  have hSlices : ∀ᵐ A ∂μ,
      Integrable (fun v ↦ score (A, v)) sphere ∧
        (∫ v, ‖score (A, v)‖ ∂sphere) ≤ envelope A := by
    filter_upwards [hSupport] with A hA
    simpa only [score, sphere, envelope] using
      h13OneThreeCombinedSharp_fixedMatrix_package hN hgap A hA.1 hA.2
  have hEnvelope :=
    h13CombinedSharpProjectiveEnvelope_momentPackage_A2A3 hN hgap
  have hEnvelopeInt : Integrable envelope μ := by
    simpa only [envelope, μ, higherScoreMatrixLaw] using hEnvelope.1
  have hInnerMeas : AEStronglyMeasurable
      (fun A ↦ ∫ v, ‖score (A, v)‖ ∂sphere) μ :=
    hscoreMeas.norm.integral_prod_right'
  have hInnerInt : Integrable
      (fun A ↦ ∫ v, ‖score (A, v)‖ ∂sphere) μ := by
    apply hEnvelopeInt.mono hInnerMeas
    filter_upwards [hSlices] with A hA
    have hInnerNonneg : 0 ≤ ∫ v, ‖score (A, v)‖ ∂sphere :=
      integral_nonneg fun _ ↦ norm_nonneg _
    have hEnvelopeNonneg : 0 ≤ envelope A := hInnerNonneg.trans hA.2
    rw [Real.norm_eq_abs, abs_of_nonneg hInnerNonneg,
      Real.norm_eq_abs, abs_of_nonneg hEnvelopeNonneg]
    exact hA.2
  have hscoreInt : Integrable score (μ.prod sphere) := by
    apply (integrable_prod_iff hscoreMeas).2
    exact ⟨hSlices.mono fun _ hA ↦ hA.1, hInnerInt⟩
  constructor
  · have hmem : MemLp score 1 (μ.prod sphere) :=
      memLp_one_iff_integrable.mpr hscoreInt
    simpa only [score, μ, sphere, higherScoreMatrixLaw,
      higherScoreSphereLaw, concreteCenteredScoreProductLaw] using hmem
  · intro hdense
    have hbound : lpNorm score 1 (μ.prod sphere) ≤
        h13CombinedSharpProjectiveEnvelopeConstant * (N : ℝ) ^ 2 := by
      calc
        lpNorm score 1 (μ.prod sphere) =
            ∫ A, ∫ v, ‖score (A, v)‖ ∂sphere ∂μ := by
          rw [lpNorm_one_eq_integral_norm hscoreMeas]
          exact integral_prod (fun p ↦ ‖score p‖) hscoreInt.norm
        _ ≤ ∫ A, envelope A ∂μ := by
          apply integral_mono_ae hInnerInt hEnvelopeInt
          filter_upwards [hSlices] with A hA
          exact hA.2
        _ ≤ h13CombinedSharpProjectiveEnvelopeConstant * (N : ℝ) ^ 2 := by
          simpa only [envelope, μ, higherScoreMatrixLaw] using
            hEnvelope.2 hdense
    simpa only [score, μ, sphere, higherScoreMatrixLaw,
      higherScoreSphereLaw, concreteCenteredScoreProductLaw] using hbound

/-- All-positive-dimensional H13 package with exact rational constant
`6773469 / 320`. -/
theorem centeredLogScore_oneThree_momentPackage_combinedSharp_A1A2A3A4
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (fun p ↦ concreteCenteredEll 1 N K p *
      concreteCenteredEll 3 N K p) 1
        (concreteCenteredScoreProductLaw N K) ∧
      (16 * N ≤ K →
        lpNorm (fun p ↦ concreteCenteredEll 1 N K p *
          concreteCenteredEll 3 N K p) 1
            (concreteCenteredScoreProductLaw N K) ≤
          h13CombinedSharpProjectiveEnvelopeConstant * (N : ℝ) ^ 2) := by
  by_cases hOne : N = 1
  · subst N
    have hzero : (fun p ↦ concreteCenteredEll 1 1 K p *
        concreteCenteredEll 3 1 K p) = 0 := by
      funext p
      rw [show concreteCenteredEll 1 1 K p = 0 by
        exact concreteCenteredLogScore_fin_one_eq_zero (by omega) p.2 p.1]
      simp
    rw [hzero]
    constructor
    · exact MemLp.zero'
    · intro _
      rw [lpNorm_zero]
      norm_num [h13CombinedSharpProjectiveEnvelopeConstant,
        h13CombinedSharpEnvelopeScale,
        h13CombinedSharpScalarEnvelopeConstant,
        h13ScaleTwoProjectiveEnvelopeConstant]
  · exact
      centeredLogScore_oneThree_momentPackage_combinedSharp_NGeTwo_A1A2A3A4
        (by omega) hgap

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
